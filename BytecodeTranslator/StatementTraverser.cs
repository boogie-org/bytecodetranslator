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
using TranslationPlugins;
using BytecodeTranslator.Phone;


namespace BytecodeTranslator
{
  public class MostNestedTryStatementTraverser : BaseCodeTraverser {
    Dictionary<IName, ITryCatchFinallyStatement> mostNestedTryStatement = new Dictionary<IName, ITryCatchFinallyStatement>();
    ITryCatchFinallyStatement currStatement = null;
    public override void Visit(ILabeledStatement labeledStatement) {
      if (currStatement != null)
        mostNestedTryStatement.Add(labeledStatement.Label, currStatement);
      base.Visit(labeledStatement);
    }
    public override void Visit(ITryCatchFinallyStatement tryCatchFinallyStatement) {
      ITryCatchFinallyStatement savedStatement = currStatement;
      currStatement = tryCatchFinallyStatement;
      base.Visit(tryCatchFinallyStatement);
      currStatement = savedStatement;
    }
    public ITryCatchFinallyStatement MostNestedTryStatement(IName label) {
      if (!mostNestedTryStatement.ContainsKey(label))
        return null;
      return mostNestedTryStatement[label];
    }
  }

  public class StatementTraverser : BaseCodeTraverser {

    public readonly TraverserFactory factory;

    readonly Sink sink;

    public readonly PdbReader/*?*/ PdbReader;

    public readonly Bpl.StmtListBuilder StmtBuilder = new Bpl.StmtListBuilder();
    private bool contractContext;
    internal readonly Stack<IExpression> operandStack = new Stack<IExpression>();
    private bool captureState;
    private static int captureStateCounter = 0;

    #region Constructors
    public StatementTraverser(Sink sink, PdbReader/*?*/ pdbReader, bool contractContext) {
      this.sink = sink;
      this.factory = sink.Factory;
      PdbReader = pdbReader;
      this.contractContext = contractContext;
      this.captureState = sink.Options.captureState;
    }
    #endregion

    #region Helper Methods

    Bpl.Expr ExpressionFor(IExpression expression) {
      ExpressionTraverser etrav = this.factory.MakeExpressionTraverser(this.sink, this, this.contractContext);
      etrav.Visit(expression);
      Contract.Assert(etrav.TranslatedExpressions.Count == 1);
      return etrav.TranslatedExpressions.Pop();
    }

    public ICollection<ITypeDefinition>/*?*/ TranslateMethod(IMethodDefinition method) {
      var methodBody = method.Body as ISourceMethodBody;
      if (methodBody == null) return null;
      var block = methodBody.Block as BlockStatement;
      // TODO: Error if cast fails?

      ICollection<ITypeDefinition> newTypes = null;
      if (block != null) {
        var remover = new AnonymousDelegateRemover(this.sink.host, this.PdbReader);
        newTypes = remover.RemoveAnonymousDelegates(methodBody.MethodDefinition, block);
      }
      this.Visit(methodBody);
      return newTypes;
    }
    #endregion

    //public override void Visit(ISourceMethodBody methodBody) {
    //  var block = methodBody.Block as BlockStatement;
    //  // TODO: Error if cast fails?

    //  if (block != null) {
    //    var remover = new AnonymousDelegateRemover(this.sink.host, this.PdbReader);
    //    var newTypes = remover.RemoveAnonymousDelegates(methodBody.MethodDefinition, block);
    //  }
    //  base.Visit(methodBody);
    //}

    public override void Visit(IBlockStatement block) {
      foreach (var s in block.Statements) {
        this.Visit(s);
      }
    }

    public override void Visit(IStatement statement) {
      EmitSourceContext(statement);
      if (this.sink.Options.captureState) {
        var tok = statement.Token();
        var state = String.Format("s{0}", StatementTraverser.captureStateCounter++);
        var attrib = new Bpl.QKeyValue(tok, "captureState ", new List<object> { state }, null);
        StmtBuilder.Add(
          new Bpl.AssumeCmd(tok, Bpl.Expr.True, attrib)
          );
      }
      base.Visit(statement);
    }

    private void EmitSourceContext(IStatement statement) {
      if (statement is IEmptyStatement) return;
      var tok = statement.Token();
      string fileName = null;
      int lineNumber = 0;
      if (this.PdbReader != null) {
        var slocs = this.PdbReader.GetClosestPrimarySourceLocationsFor(statement.Locations);
        foreach (var sloc in slocs) {
          fileName = sloc.Document.Location;
          lineNumber = sloc.StartLine;
          break;
        }
        if (fileName != null) {
          var attrib = new Bpl.QKeyValue(tok, "sourceLine", new List<object> { Bpl.Expr.Literal((int)lineNumber) }, null);
          attrib = new Bpl.QKeyValue(tok, "sourceFile", new List<object> { fileName }, attrib);
          StmtBuilder.Add(
            new Bpl.AssertCmd(tok, Bpl.Expr.True, attrib)
            );
        }
      }
    }

    #region Basic Statements

    public override void Visit(IAssertStatement assertStatement) {
      Bpl.Expr conditionExpr = ExpressionFor(assertStatement.Condition);
      Bpl.Type conditionType = this.sink.CciTypeToBoogie(assertStatement.Condition.Type);
      if (conditionType == this.sink.Heap.RefType) {
        conditionExpr = Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Neq, conditionExpr, Bpl.Expr.Ident(this.sink.Heap.NullRef));
      }
      else if (conditionType == Bpl.Type.Int) {
        conditionExpr = Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Neq, conditionExpr, Bpl.Expr.Literal(0));
      }
      else {
        System.Diagnostics.Debug.Assert(conditionType == Bpl.Type.Bool);
      }
      if (this.sink.Options.getMeHere) {
        StmtBuilder.Add(new Bpl.AssumeCmd(assertStatement.Token(), conditionExpr));
      } else {
        StmtBuilder.Add(new Bpl.AssertCmd(assertStatement.Token(), conditionExpr));
      }
    }

    public override void Visit(IAssumeStatement assumeStatement) {
      Bpl.Expr conditionExpr = ExpressionFor(assumeStatement.Condition);
      Bpl.Type conditionType = this.sink.CciTypeToBoogie(assumeStatement.Condition.Type);
      if (conditionType == this.sink.Heap.RefType) {
        conditionExpr = Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Neq, conditionExpr, Bpl.Expr.Ident(this.sink.Heap.NullRef));
      }
      else if (conditionType == Bpl.Type.Int) {
        conditionExpr = Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Neq, conditionExpr, Bpl.Expr.Literal(0));
      }
      else {
        System.Diagnostics.Debug.Assert(conditionType == Bpl.Type.Bool);
      }
      StmtBuilder.Add(new Bpl.AssumeCmd(assumeStatement.Token(), conditionExpr));
    }

    /// <summary>
    /// 
    /// </summary>
    /// <remarks>(mschaef) Works, but still a stub</remarks>
    /// <param name="conditionalStatement"></param>
    public override void Visit(IConditionalStatement conditionalStatement) {
      StatementTraverser thenTraverser = this.factory.MakeStatementTraverser(this.sink, this.PdbReader, this.contractContext);
      StatementTraverser elseTraverser = this.factory.MakeStatementTraverser(this.sink, this.PdbReader, this.contractContext);
      ExpressionTraverser condTraverser = this.factory.MakeExpressionTraverser(this.sink, this, this.contractContext);
      condTraverser.Visit(conditionalStatement.Condition);
      thenTraverser.Visit(conditionalStatement.TrueBranch);
      elseTraverser.Visit(conditionalStatement.FalseBranch);

      Bpl.Expr conditionExpr = condTraverser.TranslatedExpressions.Pop();
      Bpl.Type conditionType = this.sink.CciTypeToBoogie(conditionalStatement.Condition.Type);
      if (conditionType == this.sink.Heap.RefType) {
        conditionExpr = Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Neq, conditionExpr, Bpl.Expr.Ident(this.sink.Heap.NullRef));
      }
      else if (conditionType == Bpl.Type.Int) {
        conditionExpr = Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Neq, conditionExpr, Bpl.Expr.Literal(0));
      }
      else {
        System.Diagnostics.Debug.Assert(conditionType == Bpl.Type.Bool);
      }

      Bpl.IfCmd ifcmd = new Bpl.IfCmd(conditionalStatement.Token(),
          conditionExpr,
          thenTraverser.StmtBuilder.Collect(conditionalStatement.TrueBranch.Token()),
          null,
          elseTraverser.StmtBuilder.Collect(conditionalStatement.FalseBranch.Token())
          );

      StmtBuilder.Add(ifcmd);

    }

    /// <summary>
    /// 
    /// </summary>
    /// <param name="expressionStatement"></param>
    /// <remarks> TODO: might be wrong for the general case</remarks>
    public override void Visit(IExpressionStatement expressionStatement) {
      ExpressionTraverser etrav = this.factory.MakeExpressionTraverser(this.sink, this, this.contractContext);
      etrav.Visit(expressionStatement.Expression);
    }

    /// <summary>
    /// 
    /// </summary>
    /// <remarks>(mschaef) Not Implemented</remarks>
    /// <param name="breakStatement"></param>
    public override void Visit(IBreakStatement breakStatement) {
      throw new TranslationException("Break statements are not handled");
      //StmtBuilder.Add(new Bpl.BreakCmd(breakStatement.Token(), "I dont know"));
    }

    public override void Visit(IContinueStatement continueStatement) {
      throw new TranslationException("Continue statements are not handled");
    }

    public override void Visit(ISwitchStatement switchStatement) {
      var eTraverser = this.factory.MakeExpressionTraverser(this.sink, this, this.contractContext);
      eTraverser.Visit(switchStatement.Expression);
      var conditionExpr = eTraverser.TranslatedExpressions.Pop();

      // Can't depend on default case existing or its index in the collection.
      var switchCases = new List<ISwitchCase>();
      ISwitchCase defaultCase = null;
      foreach (var switchCase in switchStatement.Cases) {
        if (switchCase.IsDefault) {
          defaultCase = switchCase;
        } else {
          switchCases.Add(switchCase);
        }
      }
      Bpl.StmtList defaultStmts = null;
      if (defaultCase != null) {
        var defaultBodyTraverser = this.factory.MakeStatementTraverser(this.sink, this.PdbReader, this.contractContext);
        defaultBodyTraverser.Visit(defaultCase.Body);
        defaultStmts = defaultBodyTraverser.StmtBuilder.Collect(defaultCase.Token());
      }

      Bpl.IfCmd ifCmd = null;

      for (int i = switchCases.Count-1; 0 <= i; i--) {

        var switchCase = switchCases[i];

        var scTraverser = this.factory.MakeExpressionTraverser(this.sink, this, this.contractContext);
        scTraverser.Visit(switchCase.Expression);
        var scConditionExpr = scTraverser.TranslatedExpressions.Pop();
        var condition = Bpl.Expr.Eq(conditionExpr, scConditionExpr);

        var scBodyTraverser = this.factory.MakeStatementTraverser(this.sink, this.PdbReader, this.contractContext);
        scBodyTraverser.Visit(switchCase.Body);

        ifCmd = new Bpl.IfCmd(switchCase.Token(),
          condition,
          scBodyTraverser.StmtBuilder.Collect(switchCase.Token()),
          ifCmd,
          defaultStmts);
        defaultStmts = null; // default body goes only into the innermost if-then-else

      }
      StmtBuilder.Add(ifCmd);
    }

    /// <summary>
    /// If the local declaration has an initial value, then generate the
    /// statement "loc := e" from it. Otherwise ignore it.
    /// </summary>
    public override void Visit(ILocalDeclarationStatement localDeclarationStatement) {
      var initVal = localDeclarationStatement.InitialValue;
      if (initVal == null) return;
      var boogieLocal = this.sink.FindOrCreateLocalVariable(localDeclarationStatement.LocalVariable);
      var boogieLocalExpr = Bpl.Expr.Ident(boogieLocal);
      var tok = localDeclarationStatement.Token();
      var e = ExpressionFor(initVal);

      var typ = initVal.Type;
      var structCopy = TranslationHelper.IsStruct(typ) && !(initVal is IDefaultValue);
      // then a struct value of type S is being assigned: "lhs := s"
      // model this as the statement "call lhs := S..#copy_ctor(s)" that does the bit-wise copying
      Bpl.DeclWithFormals proc = null;
      if (structCopy) {
        var defaultValue = new DefaultValue() {
          DefaultValueType = typ,
          Locations = new List<ILocation>(localDeclarationStatement.Locations),
          Type = typ,
        };
        var e2 = ExpressionFor(defaultValue);
        StmtBuilder.Add(Bpl.Cmd.SimpleAssign(tok, boogieLocalExpr, e2));
        proc = this.sink.FindOrCreateProcedureForStructCopy(typ);
        StmtBuilder.Add(new Bpl.CallCmd(tok, proc.Name, new List<Bpl.Expr> { e, boogieLocalExpr, }, new List<Bpl.IdentifierExpr>()));
      } else {
        StmtBuilder.Add(Bpl.Cmd.SimpleAssign(tok, boogieLocalExpr, e));
      }
      return;
    }

    public override void Visit(IPushStatement pushStatement) {
      var tok = pushStatement.Token();
      var val = pushStatement.ValueToPush;
      var dup = val as IDupValue;
      IExpression e;
      if (dup != null) {
        e = this.operandStack.Peek();
      } else {
        e = val;
      }
      this.operandStack.Push(e);
      return;
    }

    /// <summary>
    /// 
    /// </summary>
    /// <remarks>(mschaef) not implemented</remarks>
    /// <param name="returnStatement"></param>
    public override void Visit(IReturnStatement returnStatement) {
      Bpl.IToken tok = returnStatement.Token();

      if (returnStatement.Expression != null) {
        ExpressionTraverser etrav = this.factory.MakeExpressionTraverser(this.sink, this, this.contractContext);
        etrav.Visit(returnStatement.Expression);

        if (this.sink.ReturnVariable == null || etrav.TranslatedExpressions.Count < 1) {
          throw new TranslationException(String.Format("{0} returns a value that is not supported by the function", returnStatement.ToString()));
        }

        StmtBuilder.Add(Bpl.Cmd.SimpleAssign(tok,
            new Bpl.IdentifierExpr(tok, this.sink.ReturnVariable), etrav.TranslatedExpressions.Pop()));
      }


      // FEEDBACK TODO extract into a method
      if (PhoneCodeHelper.instance().PhoneFeedbackToggled) {
        IMethodDefinition methodTranslated = sink.getMethodBeingTranslated();
        if (methodTranslated != null && PhoneCodeHelper.instance().isMethodInputHandlerOrFeedbackOverride(methodTranslated) &&
            !PhoneCodeHelper.instance().isMethodIgnoredForFeedback(methodTranslated)) {
          Bpl.AssertCmd falseAssertion = new Bpl.AssertCmd(Bpl.Token.NoToken, Bpl.LiteralExpr.False);
          StmtBuilder.Add(falseAssertion);
        }
      }

      StmtBuilder.Add(new Bpl.ReturnCmd(returnStatement.Token()));
    }
    #endregion

    #region Goto and Labels

    public override void Visit(IGotoStatement gotoStatement) {
      IName target = gotoStatement.TargetStatement.Label;
      ITryCatchFinallyStatement targetStatement = this.sink.MostNestedTryStatement(target);
      int count = 0;
      while (count < this.sink.nestedTryCatchFinallyStatements.Count) {
        int index = this.sink.nestedTryCatchFinallyStatements.Count - count - 1;
        ITryCatchFinallyStatement nestedStatement = this.sink.nestedTryCatchFinallyStatements[index].Item1;
        if (targetStatement == nestedStatement)
          break;
        int labelId;
        string label;
        this.sink.AddEscapingEdge(nestedStatement, out labelId, out label);
        StmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(this.sink.LabelVariable), Bpl.Expr.Literal(labelId)));
        string finallyLabel = this.sink.FindOrCreateFinallyLabel(nestedStatement);
        StmtBuilder.Add(new Bpl.GotoCmd(gotoStatement.Token(), new Bpl.StringSeq(finallyLabel)));
        StmtBuilder.AddLabelCmd(label);
        count++;
      }
      StmtBuilder.Add(new Bpl.GotoCmd(gotoStatement.Token(), new Bpl.StringSeq(target.Value)));
    }

    /// <summary>
    /// 
    /// </summary>
    /// <remarks> (mschaef) not sure if there is more work to do</remarks>
    /// <param name="labeledStatement"></param>
    public override void Visit(ILabeledStatement labeledStatement) {
      StmtBuilder.AddLabelCmd(labeledStatement.Label.Value);
      base.Visit(labeledStatement.Statement);
    }

    #endregion

    #region Looping Statements

    public override void Visit(IWhileDoStatement whileDoStatement) {
      throw new TranslationException("WhileDo statements are not handled");
    }

    public override void Visit(IForEachStatement forEachStatement) {
      throw new TranslationException("ForEach statements are not handled");
    }

    public override void Visit(IForStatement forStatement) {
      throw new TranslationException("For statements are not handled");
    }

    #endregion

    public void GenerateDispatchContinuation(ITryCatchFinallyStatement tryCatchFinallyStatement) {
      string continuationLabel = this.sink.FindOrCreateContinuationLabel(tryCatchFinallyStatement);
      Bpl.IfCmd elseIfCmd = new Bpl.IfCmd(Bpl.Token.NoToken, Bpl.Expr.Literal(true),
        TranslationHelper.BuildStmtList(new Bpl.GotoCmd(Bpl.Token.NoToken, new Bpl.StringSeq(continuationLabel))), null, null);
      List<string> edges = sink.EscapingEdges(tryCatchFinallyStatement);
      Bpl.IdentifierExpr labelExpr = Bpl.Expr.Ident(this.sink.LabelVariable);
      for (int i = 0; i < edges.Count; i++) {
        string label = edges[i];
        Bpl.GotoCmd gotoCmd = new Bpl.GotoCmd(Bpl.Token.NoToken, new Bpl.StringSeq(label));
        Bpl.Expr targetExpr = Bpl.Expr.Literal(i);
        elseIfCmd = new Bpl.IfCmd(Bpl.Token.NoToken, Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Eq, labelExpr, targetExpr),
          TranslationHelper.BuildStmtList(gotoCmd), elseIfCmd, null);
      }
      this.StmtBuilder.Add(elseIfCmd);
    }

    private void RaiseExceptionHelper(Bpl.StmtListBuilder builder) {
      int count = this.sink.nestedTryCatchFinallyStatements.Count;
      if (count == 0) {
        // FEEDBACK TODO unfortunately return statements are created here too 
        // FEEDBACK TODO extract into a method
        if (PhoneCodeHelper.instance().PhoneFeedbackToggled) {
          IMethodDefinition methodTranslated = sink.getMethodBeingTranslated();
          if (methodTranslated != null && PhoneCodeHelper.instance().isMethodInputHandlerOrFeedbackOverride(methodTranslated) &&
              !PhoneCodeHelper.instance().isMethodIgnoredForFeedback(methodTranslated)) {
            Bpl.AssertCmd falseAssertion = new Bpl.AssertCmd(Bpl.Token.NoToken, Bpl.LiteralExpr.False);
            builder.Add(falseAssertion);
          }
        }

        builder.Add(new Bpl.ReturnCmd(Bpl.Token.NoToken));
      }
      else {
        Tuple<ITryCatchFinallyStatement, Sink.TryCatchFinallyContext> topOfStack = this.sink.nestedTryCatchFinallyStatements[count - 1];
        string exceptionTarget; 
        if (topOfStack.Item2 == Sink.TryCatchFinallyContext.InTry) {
          exceptionTarget = this.sink.FindOrCreateCatchLabel(topOfStack.Item1);
        }
        else if (topOfStack.Item2 == Sink.TryCatchFinallyContext.InCatch) {
          builder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(this.sink.LabelVariable), Bpl.Expr.Literal(-1)));
          exceptionTarget = this.sink.FindOrCreateFinallyLabel(topOfStack.Item1);
        }
        else {
          exceptionTarget = this.sink.FindOrCreateContinuationLabel(topOfStack.Item1);
        }
        builder.Add(new Bpl.GotoCmd(Bpl.Token.NoToken, new Bpl.StringSeq(exceptionTarget)));
      }
    }

    public void RaiseException() {
      RaiseExceptionHelper(StmtBuilder);
    }
    
    public void RaiseException(Bpl.Expr e) {
      Bpl.StmtListBuilder builder = new Bpl.StmtListBuilder();
      RaiseExceptionHelper(builder);
      Bpl.IfCmd ifCmd = new Bpl.IfCmd(Bpl.Token.NoToken, e, builder.Collect(Bpl.Token.NoToken), null, null);
      StmtBuilder.Add(ifCmd);
    }

    public override void Visit(ITryCatchFinallyStatement tryCatchFinallyStatement) {
      this.sink.nestedTryCatchFinallyStatements.Add(new Tuple<ITryCatchFinallyStatement, Sink.TryCatchFinallyContext>(tryCatchFinallyStatement, Sink.TryCatchFinallyContext.InTry));
      this.Visit(tryCatchFinallyStatement.TryBody);
      StmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(this.sink.LabelVariable), Bpl.Expr.Literal(-1)));
      StmtBuilder.Add(new Bpl.GotoCmd(Bpl.Token.NoToken, new Bpl.StringSeq(this.sink.FindOrCreateFinallyLabel(tryCatchFinallyStatement))));
      this.sink.nestedTryCatchFinallyStatements.RemoveAt(this.sink.nestedTryCatchFinallyStatements.Count - 1);

      StmtBuilder.AddLabelCmd(this.sink.FindOrCreateCatchLabel(tryCatchFinallyStatement));
      StmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(this.sink.LocalExcVariable), Bpl.Expr.Ident(this.sink.Heap.ExceptionVariable)));
      StmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(this.sink.Heap.ExceptionVariable), Bpl.Expr.Ident(this.sink.Heap.NullRef)));
      List<Bpl.StmtList> catchStatements = new List<Bpl.StmtList>();
      List<Bpl.Expr> typeReferences = new List<Bpl.Expr>();
      this.sink.nestedTryCatchFinallyStatements.Add(new Tuple<ITryCatchFinallyStatement, Sink.TryCatchFinallyContext>(tryCatchFinallyStatement, Sink.TryCatchFinallyContext.InCatch));
      foreach (ICatchClause catchClause in tryCatchFinallyStatement.CatchClauses) {
        typeReferences.Insert(0, this.sink.FindOrCreateType(catchClause.ExceptionType));
        StatementTraverser catchTraverser = this.factory.MakeStatementTraverser(this.sink, this.PdbReader, this.contractContext);
        if (catchClause.ExceptionContainer != Dummy.LocalVariable) {
          Bpl.Variable catchClauseVariable = this.sink.FindOrCreateLocalVariable(catchClause.ExceptionContainer);
          catchTraverser.StmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(catchClauseVariable), Bpl.Expr.Ident(this.sink.LocalExcVariable)));
        }
        catchTraverser.Visit(catchClause.Body);
        catchTraverser.StmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(this.sink.LabelVariable), Bpl.Expr.Literal(-1)));
        catchTraverser.StmtBuilder.Add(new Bpl.GotoCmd(Bpl.Token.NoToken, new Bpl.StringSeq(this.sink.FindOrCreateFinallyLabel(tryCatchFinallyStatement))));
        catchStatements.Insert(0, catchTraverser.StmtBuilder.Collect(catchClause.Token()));
      }
      Bpl.IfCmd elseIfCmd = new Bpl.IfCmd(Bpl.Token.NoToken, Bpl.Expr.Literal(false), TranslationHelper.BuildStmtList(new Bpl.ReturnCmd(Bpl.Token.NoToken)), null, null);
      Bpl.Expr dynTypeOfOperand = this.sink.Heap.DynamicType(Bpl.Expr.Ident(this.sink.LocalExcVariable));
      for (int i = 0; i < catchStatements.Count; i++) {
        Bpl.Expr expr = new Bpl.NAryExpr(Bpl.Token.NoToken, new Bpl.FunctionCall(this.sink.Heap.Subtype), new Bpl.ExprSeq(dynTypeOfOperand, typeReferences[i]));
        elseIfCmd = new Bpl.IfCmd(Bpl.Token.NoToken, expr, catchStatements[i], elseIfCmd, null);
      }
      this.StmtBuilder.Add(elseIfCmd);
      this.StmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(this.sink.Heap.ExceptionVariable), Bpl.Expr.Ident(this.sink.LocalExcVariable)));
      RaiseException();
      this.sink.nestedTryCatchFinallyStatements.RemoveAt(this.sink.nestedTryCatchFinallyStatements.Count - 1);

      this.StmtBuilder.AddLabelCmd(this.sink.FindOrCreateFinallyLabel(tryCatchFinallyStatement));
      if (tryCatchFinallyStatement.FinallyBody != null) {
        this.sink.nestedTryCatchFinallyStatements.Add(new Tuple<ITryCatchFinallyStatement, Sink.TryCatchFinallyContext>(tryCatchFinallyStatement, Sink.TryCatchFinallyContext.InFinally));
        Bpl.Variable savedExcVariable = this.sink.CreateFreshLocal(this.sink.Heap.RefType);
        Bpl.Variable savedLabelVariable = this.sink.CreateFreshLocal(Bpl.Type.Int);
        StmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(savedExcVariable), Bpl.Expr.Ident(this.sink.Heap.ExceptionVariable)));
        StmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(savedLabelVariable), Bpl.Expr.Ident(this.sink.LabelVariable)));
        Visit(tryCatchFinallyStatement.FinallyBody);
        StmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(this.sink.Heap.ExceptionVariable), Bpl.Expr.Ident(savedExcVariable)));
        StmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(this.sink.LabelVariable), Bpl.Expr.Ident(savedLabelVariable)));
        this.sink.nestedTryCatchFinallyStatements.RemoveAt(this.sink.nestedTryCatchFinallyStatements.Count - 1);
      }
      GenerateDispatchContinuation(tryCatchFinallyStatement);
      StmtBuilder.AddLabelCmd(this.sink.FindOrCreateContinuationLabel(tryCatchFinallyStatement));
      Bpl.Expr raiseExpr = Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Neq, Bpl.Expr.Ident(this.sink.Heap.ExceptionVariable), Bpl.Expr.Ident(this.sink.Heap.NullRef));
      RaiseException(raiseExpr);
    }

    public override void Visit(IThrowStatement throwStatement) {
      ExpressionTraverser exceptionTraverser = this.factory.MakeExpressionTraverser(this.sink, this, this.contractContext);
      exceptionTraverser.Visit(throwStatement.Exception);
      StmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(this.sink.Heap.ExceptionVariable), exceptionTraverser.TranslatedExpressions.Pop()));
      RaiseException();
    }

    public override void Visit(IRethrowStatement rethrowStatement) {
      StmtBuilder.Add(TranslationHelper.BuildAssignCmd(Bpl.Expr.Ident(this.sink.Heap.ExceptionVariable), Bpl.Expr.Ident(this.sink.LocalExcVariable)));
      RaiseException();
    }

  }

}
