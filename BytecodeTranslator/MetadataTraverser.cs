﻿//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using Microsoft.Cci;
using Microsoft.Cci.MetadataReader;
using Microsoft.Cci.MutableCodeModel;
using Microsoft.Cci.Contracts;
using Microsoft.Cci.ILToCodeModel;

using Bpl = Microsoft.Boogie;
using System.Diagnostics.Contracts;


namespace BytecodeTranslator {

  /// <summary>
  /// Responsible for traversing all metadata elements (i.e., everything exclusive
  /// of method bodies).
  /// </summary>
  public class MetadataTraverser : BaseMetadataTraverser {

    readonly Sink sink;

    public readonly TraverserFactory factory;

    public readonly PdbReader/*?*/ PdbReader;

    public MetadataTraverser(Sink sink, PdbReader/*?*/ pdbReader)
      : base() {
      this.sink = sink;
      this.factory = sink.Factory;
      this.PdbReader = pdbReader;
    }

    #region Overrides

    public override void Visit(IModule module) {
      base.Visit(module);
    }

    public override void Visit(IAssembly assembly) {
      base.Visit(assembly);
    }

    /// <summary>
    /// Translate the type definition.
    /// </summary>
    /// 
    public override void Visit(ITypeDefinition typeDefinition) {

      if (typeDefinition.IsClass) {
        bool savedSawCctor = this.sawCctor;
        this.sawCctor = false;
        sink.FindOrCreateType(typeDefinition);
        base.Visit(typeDefinition);
        if (!this.sawCctor) {
          CreateStaticConstructor(typeDefinition);
        }
        this.sawCctor = savedSawCctor;
      } else if (typeDefinition.IsDelegate) {
        sink.AddDelegateType(typeDefinition);
      } else if (typeDefinition.IsInterface) {
        sink.FindOrCreateType(typeDefinition);
        base.Visit(typeDefinition);
      } else if (typeDefinition.IsEnum) {
        return; // enums just are translated as ints
      } else if (typeDefinition.IsStruct) {
        sink.FindOrCreateType(typeDefinition);
        //CreateDefaultStructConstructor(typeDefinition);
        base.Visit(typeDefinition);
      } else {
        Console.WriteLine("Unknown kind of type definition '{0}' was found",
          TypeHelper.GetTypeName(typeDefinition));
        throw new NotImplementedException(String.Format("Unknown kind of type definition '{0}'.", TypeHelper.GetTypeName(typeDefinition)));
      }
    }

    private void CreateDefaultStructConstructor(ITypeDefinition typeDefinition) {
      Contract.Requires(typeDefinition.IsStruct);

      var proc = this.sink.FindOrCreateProcedureForDefaultStructCtor(typeDefinition);

      var stmtBuilder = new Bpl.StmtListBuilder();

      foreach (var f in typeDefinition.Fields) {
        var e = this.sink.DefaultValue(f.Type);
        var fExp = Bpl.Expr.Ident(this.sink.FindOrCreateFieldVariable(f));
        var o = Bpl.Expr.Ident(proc.OutParams[0]);
        var boogieType = sink.CciTypeToBoogie(f.Type);
        var c = this.sink.Heap.WriteHeap(Bpl.Token.NoToken, o, fExp, e, AccessType.Struct, boogieType);
        stmtBuilder.Add(c);
      }

      var attrib = new Bpl.QKeyValue(typeDefinition.Token(), "inline", new List<object>(1), null); // TODO: Need to have it be {:inine 1} (and not just {:inline})?
      Bpl.Implementation impl =
        new Bpl.Implementation(Bpl.Token.NoToken,
        proc.Name,
        new Bpl.TypeVariableSeq(),
        proc.InParams,
        proc.OutParams,
        new Bpl.VariableSeq(),
        stmtBuilder.Collect(Bpl.Token.NoToken),
        attrib,
        new Bpl.Errors()
        );

      impl.Proc = (Bpl.Procedure) proc; // TODO: get rid of cast
      this.sink.TranslatedProgram.TopLevelDeclarations.Add(impl);
    }

    private bool sawCctor = false;

    private void CreateStaticConstructor(ITypeDefinition typeDefinition) {
      var typename = TypeHelper.GetTypeName(typeDefinition);
      typename = TranslationHelper.TurnStringIntoValidIdentifier(typename);
      var proc = new Bpl.Procedure(Bpl.Token.NoToken, typename + ".#cctor",
          new Bpl.TypeVariableSeq(),
          new Bpl.VariableSeq(), // in
          new Bpl.VariableSeq(), // out
          new Bpl.RequiresSeq(),
          new Bpl.IdentifierExprSeq(), // modifies
          new Bpl.EnsuresSeq()
          );

      this.sink.TranslatedProgram.TopLevelDeclarations.Add(proc);

      var stmtBuilder = new Bpl.StmtListBuilder();
      foreach (var f in typeDefinition.Fields) {
        if (f.IsStatic) {

          var e = this.sink.DefaultValue(f.Type);
          stmtBuilder.Add(
            TranslationHelper.BuildAssignCmd(
            Bpl.Expr.Ident(this.sink.FindOrCreateFieldVariable(f)), 
            e
            ));
        }
      }
      Bpl.Implementation impl =
        new Bpl.Implementation(Bpl.Token.NoToken,
        proc.Name,
        new Bpl.TypeVariableSeq(),
        proc.InParams,
        proc.OutParams,
        new Bpl.VariableSeq(),
        stmtBuilder.Collect(Bpl.Token.NoToken)
        );

      impl.Proc = proc;
      this.sink.TranslatedProgram.TopLevelDeclarations.Add(impl);


    }

    /// <summary>
    /// 
    /// </summary>
    public override void Visit(IMethodDefinition method) {

      if (method.IsStaticConstructor) this.sawCctor = true;

      bool isEventAddOrRemove = method.IsSpecialName && (method.Name.Value.StartsWith("add_") || method.Name.Value.StartsWith("remove_"));
      if (isEventAddOrRemove)
        return;

      this.sink.BeginMethod();

      Sink.ProcedureInfo procAndFormalMap;
      IMethodDefinition stubMethod = null;
      if (IsStubMethod(method, out stubMethod)) {
        procAndFormalMap = this.sink.FindOrCreateProcedureAndReturnProcAndFormalMap(stubMethod);
      } else {
        procAndFormalMap = this.sink.FindOrCreateProcedureAndReturnProcAndFormalMap(method);
      }

      if (method.IsAbstract) { // we're done, just define the procedure
        return;
      }

      var decl = procAndFormalMap.Decl;
      var proc = decl as Bpl.Procedure;
      var formalMap = procAndFormalMap.FormalMap;
      this.sink.RetVariable = procAndFormalMap.ReturnVariable;

      try {

        StatementTraverser stmtTraverser = this.factory.MakeStatementTraverser(this.sink, this.PdbReader, false);

        #region Add assignments from In-Params to local-Params

        foreach (MethodParameter mparam in formalMap.Values) {
          if (mparam.inParameterCopy != null) {
            Bpl.IToken tok = method.Token();
            stmtTraverser.StmtBuilder.Add(Bpl.Cmd.SimpleAssign(tok,
              new Bpl.IdentifierExpr(tok, mparam.outParameterCopy),
              new Bpl.IdentifierExpr(tok, mparam.inParameterCopy)));
          }
        }

        if (!method.IsStatic && method.ContainingType.ResolvedType.IsStruct) {
          Bpl.IToken tok = method.Token();
          stmtTraverser.StmtBuilder.Add(Bpl.Cmd.SimpleAssign(tok,
              new Bpl.IdentifierExpr(tok, proc.OutParams[0]),
              new Bpl.IdentifierExpr(tok, proc.InParams[0])));
        }

        #endregion

        #region For non-deferring ctors and all cctors, initialize all fields to null-equivalent values
        var inits = InitializeFieldsInConstructor(method);
        if (0 < inits.Count) {
          new BlockStatement() { Statements = inits, }.Dispatch(stmtTraverser);
        }
        #endregion

        try {
          method.Body.Dispatch(stmtTraverser);
        } catch (TranslationException te) {
          throw new NotImplementedException("No Errorhandling in Methodvisitor / " + te.ToString());
        } catch {
          throw;
        }

        #region Create Local Vars For Implementation
        List<Bpl.Variable> vars = new List<Bpl.Variable>();
        foreach (MethodParameter mparam in formalMap.Values) {
          if (!(mparam.underlyingParameter.IsByReference || mparam.underlyingParameter.IsOut))
            vars.Add(mparam.outParameterCopy);
        }
        foreach (Bpl.Variable v in this.sink.LocalVarMap.Values) {
          vars.Add(v);
        }

        Bpl.VariableSeq vseq = new Bpl.VariableSeq(vars.ToArray());
        #endregion

        if (proc != null) {
          Bpl.Implementation impl =
              new Bpl.Implementation(method.Token(),
                  decl.Name,
                  new Microsoft.Boogie.TypeVariableSeq(),
                  decl.InParams,
                  decl.OutParams,
                  vseq,
                  stmtTraverser.StmtBuilder.Collect(Bpl.Token.NoToken));

          impl.Proc = proc;
          this.sink.TranslatedProgram.TopLevelDeclarations.Add(impl);
        } else { // method is translated as a function
          //Bpl.Function func = decl as Bpl.Function;
          //func.Body = new Bpl.CodeExpr(new Bpl.VariableSeq(), new List<Bpl.Block>{ new Bpl.Block(
        }

        #region Translate method attributes
        // Don't need an expression translator because there is a limited set of things
        // that can appear as arguments to custom attributes
        foreach (var a in method.Attributes) {
          var attrName = TypeHelper.GetTypeName(a.Type);
          if (attrName.EndsWith("Attribute"))
            attrName = attrName.Substring(0, attrName.Length - 9);
          var args = new object[IteratorHelper.EnumerableCount(a.Arguments)];
          int argIndex = 0;
          foreach (var c in a.Arguments) {
            var mdc = c as IMetadataConstant;
            if (mdc != null) {
              object o;
              switch (mdc.Type.TypeCode) {
                case PrimitiveTypeCode.Boolean:
                  o = (bool)mdc.Value ? Bpl.Expr.True : Bpl.Expr.False;
                  break;
                case PrimitiveTypeCode.Int32:
                  var lit = Bpl.Expr.Literal((int)mdc.Value);
                  lit.Type = Bpl.Type.Int;
                  o = lit;
                  break;
                case PrimitiveTypeCode.String:
                  o = mdc.Value;
                  break;
                default:
                  throw new InvalidCastException("Invalid metadata constant type");
              }
              args[argIndex++] = o;
            }
          }
          decl.AddAttribute(attrName, args);
        }
        #endregion


      } catch (TranslationException te) {
        throw new NotImplementedException(te.ToString());
      } catch {
        throw;
      } finally {
        // Maybe this is a good place to add the procedure to the toplevel declarations
      }
    }

    private static List<IStatement> InitializeFieldsInConstructor(IMethodDefinition method) {
      Contract.Ensures(Contract.Result<List<IStatement>>() != null);
      var inits = new List<IStatement>();
      if (method.IsConstructor || method.IsStaticConstructor) {
        var smb = method.Body as ISourceMethodBody;
        if (method.IsStaticConstructor || (smb != null && !FindCtorCall.IsDeferringCtor(method, smb.Block))) {
          var thisExp = new ThisReference() { Type = method.ContainingTypeDefinition, };
          foreach (var f in method.ContainingTypeDefinition.Fields) {
            if (f.IsStatic == method.IsStatic) {
              var a = new Assignment() {
                Source = new DefaultValue() { DefaultValueType = f.Type, Type = f.Type, },
                Target = new TargetExpression() { Definition = f, Instance = method.IsConstructor ? thisExp : null, Type = f.Type },
                Type = f.Type,
              };
              inits.Add(new ExpressionStatement() { Expression = a, });
            }
          }
        }
      }
      return inits;
    }
    // TODO: do a type test, not a string test for the attribute
    private bool IsStubMethod(IMethodDefinition methodDefinition, out IMethodDefinition/*?*/ stubMethod) {
      stubMethod = null;
      var td = GetTypeDefinitionFromAttribute(methodDefinition.Attributes, "BytecodeTranslator.StubAttribute");
      if (td == null)
        td = GetTypeDefinitionFromAttribute(methodDefinition.ContainingTypeDefinition.Attributes, "BytecodeTranslator.StubAttribute");
      if (td != null) {
        foreach (var mem in td.GetMatchingMembersNamed(methodDefinition.Name, false,
          tdm => {
            var md = tdm as IMethodDefinition;
            return md != null && MemberHelper.MethodsAreEquivalent(methodDefinition, md);
          })) {
          stubMethod = mem as IMethodDefinition;
          return true;
        }
      }
      return false;
    }
    public static ITypeDefinition/*?*/ GetTypeDefinitionFromAttribute(IEnumerable<ICustomAttribute> attributes, string attributeName) {
      ICustomAttribute foundAttribute = null;
      foreach (ICustomAttribute attribute in attributes) {
        if (TypeHelper.GetTypeName(attribute.Type) == attributeName) {
          foundAttribute = attribute;
          break;
        }
      }
      if (foundAttribute == null) return null;
      List<IMetadataExpression> args = new List<IMetadataExpression>(foundAttribute.Arguments);
      if (args.Count < 1) return null;
      IMetadataTypeOf abstractTypeMD = args[0] as IMetadataTypeOf;
      if (abstractTypeMD == null) return null;
      ITypeReference referencedTypeReference = Microsoft.Cci.MutableContracts.ContractHelper.Unspecialized(abstractTypeMD.TypeToGet);
      ITypeDefinition referencedTypeDefinition = referencedTypeReference.ResolvedType;
      return referencedTypeDefinition;
    }

    public override void Visit(IFieldDefinition fieldDefinition) {
      this.sink.FindOrCreateFieldVariable(fieldDefinition);
    }

    #endregion

    private class FindCtorCall : BaseCodeTraverser {
      private bool isDeferringCtor = false;
      public ITypeReference containingType;
      public static bool IsDeferringCtor(IMethodDefinition method, IBlockStatement body) {
        var fcc = new FindCtorCall(method.ContainingType);
        fcc.Visit(body);
        return fcc.isDeferringCtor;
      }
      private FindCtorCall(ITypeReference containingType) {
        this.containingType = containingType;
      }
      public override void Visit(IMethodCall methodCall) {
        var md = methodCall.MethodToCall.ResolvedMethod;
        if (md != null && md.IsConstructor && methodCall.ThisArgument is IThisReference) {
          this.isDeferringCtor = TypeHelper.TypesAreEquivalent(md.ContainingType, containingType);
          this.stopTraversal = true;
          return;
        }
        base.Visit(methodCall);
      }
    }
  }
}