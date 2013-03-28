//-----------------------------------------------------------------------------
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

namespace BytecodeTranslator {

  /// <summary>
  /// Implementations of this interface determine how the heap is represented in
  /// the translated Boogie program.
  /// </summary>
  public interface IHeap {

    /// <summary>
    /// Creates a fresh BPL variable to represent <paramref name="field"/>, deciding
    /// on its type based on the heap representation.
    /// </summary>
    Bpl.Variable CreateFieldVariable(IFieldReference field);

    /// Creates a fresh BPL variable to represent <paramref name="type"/>, deciding
    /// on its type based on the heap representation. I.e., the value of this
    /// variable represents the value of the expression "typeof(type)".
    /// </summary>
    Bpl.Variable CreateTypeVariable(ITypeReference type, List<Bpl.ConstantParent> parents);

    Bpl.Variable CreateEventVariable(IEventDefinition e);

    /// <summary>
    /// Returns the (typed) BPL expression that corresponds to the value of the field
    /// <paramref name="f"/> belonging to the object <paramref name="o"/> (which should be non-null).
    /// </summary>
    /// <param name="o">The expression that represents the object to be dereferenced.
    /// </param>
    /// <param name="f">The field that is used to dereference the object <paramref name="o"/>.
    /// </param>
    Bpl.Expr ReadHeap(Bpl.Expr/*?*/ o, Bpl.Expr f, AccessType accessType, Bpl.Type unboxType);

    /// <summary>
    /// Returns the BPL command that corresponds to assigning the value <paramref name="value"/>
    /// to the field <paramref name="f"/> of the object <paramref name="o"/> (which should be non-null).
    /// </summary>
    void WriteHeap(Bpl.IToken tok, Bpl.Expr/*?*/ o, Bpl.Expr f, Bpl.Expr value, AccessType accessType, Bpl.Type boxType, Bpl.StmtListBuilder builder);

    /// <summary>
    /// Returns the BPL expression that corresponds to the value of the dynamic type
    /// of the object represented by the expression <paramref name="o"/>.
    /// </summary>
    Bpl.Expr DynamicType(Bpl.Expr o);

  }
  
  public enum AccessType { Array, Heap, Struct };

  public abstract class Heap : HeapFactory, IHeap
  {
    [RepresentationFor("$ArrayContents", "var $ArrayContents: [Ref][int]Union;")]
    public Bpl.Variable ArrayContentsVariable = null;
    [RepresentationFor("$ArrayLength", "function $ArrayLength(Ref): int;")]
    public Bpl.Function ArrayLengthFunction = null;

    public abstract Bpl.Variable CreateFieldVariable(IFieldReference field);

    #region Boogie Types

    [RepresentationFor("Field", "type Field;")]
    public Bpl.TypeCtorDecl FieldTypeDecl = null;
    public Bpl.CtorType FieldType;

    [RepresentationFor("Union", "type Union;")]
    public Bpl.TypeCtorDecl UnionTypeDecl = null;
    public Bpl.CtorType UnionType;

    [RepresentationFor("$DefaultHeapValue", "const unique $DefaultHeapValue : Union;")]
    public Bpl.Constant DefaultHeapValue;

    [RepresentationFor("Ref", "type Ref;")]
    public Bpl.TypeCtorDecl RefTypeDecl = null;
    public Bpl.CtorType RefType;
    [RepresentationFor("null", "const unique null : Ref;")]
    public Bpl.Constant NullRef;

    [RepresentationFor("Type", "type Type = Ref;")]
    public Bpl.TypeSynonymDecl TypeTypeDecl = null;
    public Bpl.Type TypeType { get { return TypeTypeDecl.Body; } }

    [RepresentationFor("$TypeConstructor", "function $TypeConstructor(Ref): int;")]
    public Bpl.Function TypeConstructorFunction = null;

    [RepresentationFor("$UnionConstructor", "function $UnionConstructor(Union): int;")]
    public Bpl.Function UnionConstructorFunction = null;

    [RepresentationFor("Real", "type Real;")]
    protected Bpl.TypeCtorDecl RealTypeDecl = null;
    public Bpl.CtorType RealType;
    [RepresentationFor("$DefaultReal", "const unique $DefaultReal : Real;")]
    public Bpl.Constant DefaultReal;

    #endregion

    #region CLR Boxing

    [RepresentationFor("$BoxFromBool", "procedure {:inline 1} $BoxFromBool(b: bool) returns (r: Ref) { call r := Alloc(); assume $TypeConstructor($DynamicType(r)) == $BoxedType; assume Union2Bool($BoxedValue(r)) == b; }")]
    public Bpl.Procedure BoxFromBool = null;

    [RepresentationFor("$BoxFromInt", "procedure {:inline 1} $BoxFromInt(i: int) returns (r: Ref) { call r := Alloc(); assume $TypeConstructor($DynamicType(r)) == $BoxedType; assume Union2Int($BoxedValue(r)) == i; }")]
    public Bpl.Procedure BoxFromInt = null;

    [RepresentationFor("$BoxFromReal", "procedure {:inline 1} $BoxFromReal(r: Real) returns (rf: Ref) { call rf := Alloc(); assume $TypeConstructor($DynamicType(rf)) == $BoxedType; assume Union2Real($BoxedValue(rf)) == r; }")]
    public Bpl.Procedure BoxFromReal = null;

    [RepresentationFor("$BoxFromStruct", "procedure {:inline 1} $BoxFromStruct(s: Ref) returns (r: Ref) { call r := Alloc(); assume $TypeConstructor($DynamicType(r)) == $BoxedType; assume Union2Struct($BoxedValue(r)) == s; }")]
    public Bpl.Procedure BoxFromStruct = null;

    [RepresentationFor("$BoxFromUnion", "procedure {:inline 1} $BoxFromUnion(u: Union) returns (r: Ref) { if ($UnionConstructor(u) == $RefValueType) { r := Union2Ref(u); } else { call r := Alloc(); assume $TypeConstructor($DynamicType(r)) == $BoxedType; assume $BoxedValue(r) == u; } }")]
    public Bpl.Procedure BoxFromUnion = null;

    [RepresentationFor("$BoxedValue", "function $BoxedValue(r: Ref): Union;")]
    public Bpl.Function BoxedValue = null;

    [RepresentationFor("$BoxedType", "const unique $BoxedType: int;")]
    public Bpl.Constant BoxedType = null;

    [RepresentationFor("$BoolValueType", "const unique $BoolValueType: int;")]
    public Bpl.Constant BoolValueType = null;

    [RepresentationFor("$IntValueType", "const unique $IntValueType: int;")]
    public Bpl.Constant IntValueType = null;

    [RepresentationFor("$RealValueType", "const unique $RealValueType: int;")]
    public Bpl.Constant RealValueType = null;

    [RepresentationFor("$RefValueType", "const unique $RefValueType: int;")]
    public Bpl.Constant RefValueType = null;

    [RepresentationFor("$StructValueType", "const unique $StructValueType: int;")]
    public Bpl.Constant StructValueType = null;

    [RepresentationFor("$Unbox2Bool", "function {:inline true} $Unbox2Bool(r: Ref): (bool) { Union2Bool($BoxedValue(r)) }")]
    public Bpl.Function Unbox2Bool = null;

    [RepresentationFor("$Unbox2Int", "function {:inline true} $Unbox2Int(r: Ref): (int) { Union2Int($BoxedValue(r)) }")]
    public Bpl.Function Unbox2Int = null;

    [RepresentationFor("$Unbox2Real", "function {:inline true} $Unbox2Real(r: Ref): (Real) { Union2Real($BoxedValue(r)) }")]
    public Bpl.Function Unbox2Real = null;

    [RepresentationFor("$Unbox2Struct", "function {:inline true} $Unbox2Struct(r: Ref): (Ref) { Union2Struct($BoxedValue(r)) }")]
    public Bpl.Function Unbox2Struct = null;

    [RepresentationFor("$Unbox2Union", "function {:inline true} $Unbox2Union(r: Ref): (Union) { $BoxedValue(r) }")]
    public Bpl.Function Unbox2Union = null;

    #endregion

    #region Conversions

    #region Heap values

    [RepresentationFor("Union2Bool", "function Union2Bool(u: Union): (bool);")]
    public Bpl.Function Union2Bool = null;

    [RepresentationFor("Union2Int", "function Union2Int(u: Union): (int);")]
    public Bpl.Function Union2Int = null;

    [RepresentationFor("Union2Ref", "function Union2Ref(u: Union): (Ref);")]
    public Bpl.Function Union2Ref = null;

    [RepresentationFor("Union2Real", "function Union2Real(u: Union): (Real);")]
    public Bpl.Function Union2Real = null;

    [RepresentationFor("Union2Struct", "function Union2Struct(u: Union): (Ref);")]
    public Bpl.Function Union2Struct = null;

    [RepresentationFor("Bool2Union", "function Bool2Union(boolValue: bool): Union;")]
    public Bpl.Function Bool2Union = null;

    [RepresentationFor("Int2Union", "function Int2Union(intValue: int): Union;")]
    public Bpl.Function Int2Union = null;

    [RepresentationFor("Ref2Union", "function Ref2Union(refValue: Ref): Union;")]
    public Bpl.Function Ref2Union = null;

    [RepresentationFor("Real2Union", "function Real2Union(realValue: Real): Union;")]
    public Bpl.Function Real2Union = null;

    [RepresentationFor("Struct2Union", "function Struct2Union(structValue: Ref): Union;")]
    public Bpl.Function Struct2Union = null;

    public Bpl.Expr ToUnion(Bpl.IToken tok, Bpl.Type boogieType, Bpl.Expr expr, bool isStruct, Bpl.StmtListBuilder builder)
    {
        if (boogieType == UnionType)
            return expr;

        Bpl.Expr callConversion;
        if (boogieType == Bpl.Type.Bool)
        {
            callConversion = new Bpl.NAryExpr(tok, new Bpl.FunctionCall(this.Bool2Union), new Bpl.ExprSeq(expr));
            builder.Add(
                new Bpl.AssumeCmd(tok,
                    Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Eq,
                    new Bpl.NAryExpr(tok, new Bpl.FunctionCall(this.UnionConstructorFunction), new Bpl.ExprSeq(callConversion)),
                    Bpl.Expr.Ident(this.BoolValueType))));
            builder.Add(
                new Bpl.AssumeCmd(tok,
                Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Eq,
                                new Bpl.NAryExpr(tok, new Bpl.FunctionCall(this.Union2Bool), new Bpl.ExprSeq(callConversion)),
                                expr)));
        }
        else if (boogieType == Bpl.Type.Int)
        {
            callConversion = new Bpl.NAryExpr(tok, new Bpl.FunctionCall(this.Int2Union), new Bpl.ExprSeq(expr));
            builder.Add(
                new Bpl.AssumeCmd(tok,
                    Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Eq,
                    new Bpl.NAryExpr(tok, new Bpl.FunctionCall(this.UnionConstructorFunction), new Bpl.ExprSeq(callConversion)),
                    Bpl.Expr.Ident(this.IntValueType)))); 
            builder.Add(
                new Bpl.AssumeCmd(tok,
                Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Eq,
                                new Bpl.NAryExpr(tok, new Bpl.FunctionCall(this.Union2Int), new Bpl.ExprSeq(callConversion)),
                                expr)));
        }
        else if (boogieType == RefType)
        {
            callConversion = new Bpl.NAryExpr(tok, new Bpl.FunctionCall(isStruct ? this.Struct2Union : this.Ref2Union), new Bpl.ExprSeq(expr));
            builder.Add(
                new Bpl.AssumeCmd(tok,
                    Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Eq,
                    new Bpl.NAryExpr(tok, new Bpl.FunctionCall(this.UnionConstructorFunction), new Bpl.ExprSeq(callConversion)),
                    Bpl.Expr.Ident(isStruct ? this.StructValueType : this.RefValueType)))); 
            builder.Add(
                new Bpl.AssumeCmd(tok,
                Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Eq,
                                new Bpl.NAryExpr(tok, new Bpl.FunctionCall(isStruct ? this.Union2Struct : this.Union2Ref), new Bpl.ExprSeq(callConversion)),
                                expr)));
        }
        else if (boogieType == RealType)
        {
            callConversion = new Bpl.NAryExpr(tok, new Bpl.FunctionCall(this.Real2Union), new Bpl.ExprSeq(expr));
            builder.Add(
                new Bpl.AssumeCmd(tok,
                    Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Eq,
                    new Bpl.NAryExpr(tok, new Bpl.FunctionCall(this.UnionConstructorFunction), new Bpl.ExprSeq(callConversion)),
                    Bpl.Expr.Ident(this.RealValueType)))); 
            builder.Add(
                new Bpl.AssumeCmd(tok,
                Bpl.Expr.Binary(Bpl.BinaryOperator.Opcode.Eq,
                                new Bpl.NAryExpr(tok, new Bpl.FunctionCall(this.Union2Real), new Bpl.ExprSeq(callConversion)),
                                expr)));
        }
        else
        {
            throw new InvalidOperationException(String.Format("Unknown Boogie type: '{0}'", boogieType.ToString()));
        }
        return callConversion;
    }

    public Bpl.Expr FromUnion(Bpl.IToken tok, Bpl.Type boogieType, Bpl.Expr expr, bool isStruct) {
      if (boogieType == UnionType)
          return expr;

      Bpl.Function conversion = null;
      if (boogieType == Bpl.Type.Bool)
        conversion = this.Union2Bool;
      else if (boogieType == Bpl.Type.Int)
        conversion = this.Union2Int;
      else if (boogieType == RefType)
        conversion = isStruct ? this.Union2Struct : this.Union2Ref;
      else if (boogieType == RealType)
          conversion = this.Union2Real;
      else
          throw new InvalidOperationException(String.Format("Unknown Boogie type: '{0}'", boogieType.ToString()));

      var callExpr = new Bpl.NAryExpr(
        tok,
        new Bpl.FunctionCall(conversion),
        new Bpl.ExprSeq(expr)
        );
      callExpr.Type = boogieType;
      return callExpr;
    }

    #endregion

    #region Real number conversions
    [RepresentationFor("Int2Real", "function Int2Real(int): Real;")]
    public Bpl.Function Int2Real = null;
    [RepresentationFor("Real2Int", "function Real2Int(Real): int;")]
    public Bpl.Function Real2Int = null;
    #endregion

    #region Real number operations
    [RepresentationFor("RealPlus", "function RealPlus(Real, Real): Real;")]
    public Bpl.Function RealPlus = null;
    [RepresentationFor("RealMinus", "function RealMinus(Real, Real): Real;")]
    public Bpl.Function RealMinus = null;
    [RepresentationFor("RealTimes", "function RealTimes(Real, Real): Real;")]
    public Bpl.Function RealTimes = null;
    [RepresentationFor("RealDivide", "function RealDivide(Real, Real): Real;")]
    public Bpl.Function RealDivide = null;
    [RepresentationFor("RealModulus", "function RealModulus(Real, Real): Real;")]
    public Bpl.Function RealModulus = null;
    [RepresentationFor("RealLessThan", "function RealLessThan(Real, Real): bool;")]
    public Bpl.Function RealLessThan = null;
    [RepresentationFor("RealLessThanOrEqual", "function RealLessThanOrEqual(Real, Real): bool;")]
    public Bpl.Function RealLessThanOrEqual = null;
    [RepresentationFor("RealGreaterThan", "function RealGreaterThan(Real, Real): bool;")]
    public Bpl.Function RealGreaterThan = null;
    [RepresentationFor("RealGreaterThanOrEqual", "function RealGreaterThanOrEqual(Real, Real): bool;")]
    public Bpl.Function RealGreaterThanOrEqual = null;
    #endregion

    #region Bitwise operations
    [RepresentationFor("BitwiseAnd", "function BitwiseAnd(int, int): int;")]
    public Bpl.Function BitwiseAnd = null;
    [RepresentationFor("BitwiseOr", "function BitwiseOr(int, int): int;")]
    public Bpl.Function BitwiseOr = null;
    [RepresentationFor("BitwiseExclusiveOr", "function BitwiseExclusiveOr(int, int): int;")]
    public Bpl.Function BitwiseExclusiveOr = null;
    [RepresentationFor("BitwiseNegation", "function BitwiseNegation(int): int;")]
    public Bpl.Function BitwiseNegation = null;
    [RepresentationFor("RightShift", "function RightShift(int,int): int;")]
    public Bpl.Function RightShift = null;
    [RepresentationFor("LeftShift", "function LeftShift(int,int): int;")]
    public Bpl.Function LeftShift = null;
    #endregion

    #endregion

    /// <summary>
    /// Creates a fresh BPL variable to represent <paramref name="type"/>, deciding
    /// on its type based on the heap representation. I.e., the value of this
    /// variable represents the value of the expression "typeof(type)".
    /// </summary>
    public Bpl.Variable CreateTypeVariable(ITypeReference type, List<Bpl.ConstantParent> parents)
    {
      string typename = TypeHelper.GetTypeName(type, NameFormattingOptions.DocumentationId);
        typename = TranslationHelper.TurnStringIntoValidIdentifier(typename);
        Bpl.IToken tok = type.Token();
        Bpl.TypedIdent tident = new Bpl.TypedIdent(tok, typename, this.TypeType);
        Bpl.Constant v = new Bpl.Constant(tok, tident, true /*unique*/, parents, false, null);
        return v;
    }

    public Bpl.Function CreateTypeFunction(ITypeReference type, int parameterCount) {
      System.Diagnostics.Debug.Assert(parameterCount >= 0);
      string typename = TypeHelper.GetTypeName(type, NameFormattingOptions.DocumentationId);
      typename = TranslationHelper.TurnStringIntoValidIdentifier(typename);
      Bpl.IToken tok = type.Token();
      Bpl.VariableSeq inputs = new Bpl.VariableSeq();
      //for (int i = 0; i < parameterCount; i++) {
      //  inputs.Add(new Bpl.Formal(tok, new Bpl.TypedIdent(tok, "arg"+i, this.TypeType), true));
      //}
      foreach (var t in TranslationHelper.ConsolidatedGenericParameters(type)) {
        var n = t.Name.Value;
        var n2 = TranslationHelper.TurnStringIntoValidIdentifier(n);
        inputs.Add(new Bpl.Formal(Bpl.Token.NoToken, new Bpl.TypedIdent(Bpl.Token.NoToken, n2, this.TypeType), true));
      }
      Bpl.Variable output = new Bpl.Formal(tok, new Bpl.TypedIdent(tok, "result", this.TypeType), false);
      Bpl.Function func = new Bpl.Function(tok, typename, inputs, output);
      var attrib = new Bpl.QKeyValue(Bpl.Token.NoToken, "constructor", new List<object>(1), null);
      func.Attributes = attrib;
      return func;
    }
    

    public abstract Bpl.Variable CreateEventVariable(IEventDefinition e);

    public abstract Bpl.Expr ReadHeap(Bpl.Expr o, Bpl.Expr f, AccessType accessType, Bpl.Type unboxType);

    public abstract void WriteHeap(Bpl.IToken tok, Bpl.Expr o, Bpl.Expr f, Bpl.Expr value, AccessType accessType, Bpl.Type boxType, Bpl.StmtListBuilder builder);

    [RepresentationFor("$DynamicType", "function $DynamicType(Ref): Type;")]
    protected Bpl.Function DynamicTypeFunction = null;

    /// <summary>
    /// Returns the BPL expression that corresponds to the value of the dynamic type
    /// of the object represented by the expression <paramref name="o"/>.
    /// </summary>
    public Bpl.Expr DynamicType(Bpl.Expr o) {
      // $DymamicType(o)
      var callDynamicType = new Bpl.NAryExpr(
        o.tok,
        new Bpl.FunctionCall(this.DynamicTypeFunction),
        new Bpl.ExprSeq(o)
        );
      return callDynamicType;
    }

    [RepresentationFor("$As", "function $As(Ref, Type): Ref;")]
    public Bpl.Function AsFunction = null;

    [RepresentationFor("$Subtype", "function $Subtype(Type, Type): bool;")]
    public Bpl.Function Subtype = null;

    [RepresentationFor("$DisjointSubtree", "function $DisjointSubtree(Type, Type): bool;")]
    public Bpl.Function DisjointSubtree = null;

    [RepresentationFor("$Alloc", "var $Alloc: [Ref] bool;")]
    public Bpl.Variable AllocVariable = null;

    [RepresentationFor("$allocImp", "function {:builtin \"MapImp\"} $allocImp([Ref]bool, [Ref]bool) : [Ref]bool;")]
    public Bpl.Function AllocImplies = null;
    [RepresentationFor("$allocConstBool", "function {:builtin \"MapConst\"} $allocConstBool(bool) : [Ref]bool;")]
    public Bpl.Function AllocConstBool = null;



    protected readonly string CommonText =
      @"//var $Alloc: [Ref] bool;

procedure {:inline 1} Alloc() returns (x: Ref)
  modifies $Alloc;
{
  assume $Alloc[x] == false && x != null;
  $Alloc[x] := true;
}

procedure {:inline 1} System.Object.GetType(this: Ref) returns ($result: Ref)
{
  $result := $DynamicType(this);
}

axiom Union2Int($DefaultHeapValue) == 0;
axiom Union2Bool($DefaultHeapValue) == false;
axiom Union2Ref($DefaultHeapValue) == null;

function $ThreadDelegate(Ref) : Ref;

procedure {:inline 1} System.Threading.Thread.#ctor$System.Threading.ParameterizedThreadStart(this: Ref, start$in: Ref)
{
  assume $ThreadDelegate(this) == start$in;
}
procedure {:inline 1} System.Threading.Thread.Start$System.Object(this: Ref, parameter$in: Ref)
{
  async call Wrapper_System.Threading.ParameterizedThreadStart.Invoke$System.Object($ThreadDelegate(this), parameter$in);
}
procedure Wrapper_System.Threading.ParameterizedThreadStart.Invoke$System.Object(this: Ref, obj$in: Ref) {
  $Exception := null;
  call System.Threading.ParameterizedThreadStart.Invoke$System.Object(this, obj$in);
}
procedure {:extern} System.Threading.ParameterizedThreadStart.Invoke$System.Object(this: Ref, obj$in: Ref);

procedure {:inline 1} System.Threading.Thread.#ctor$System.Threading.ThreadStart(this: Ref, start$in: Ref) 
{
  assume $ThreadDelegate(this) == start$in;
}
procedure {:inline 1} System.Threading.Thread.Start(this: Ref) 
{
  async call Wrapper_System.Threading.ThreadStart.Invoke($ThreadDelegate(this));
}
procedure Wrapper_System.Threading.ThreadStart.Invoke(this: Ref) {
  $Exception := null;
  call System.Threading.ThreadStart.Invoke(this);
}
procedure {:extern} System.Threading.ThreadStart.Invoke(this: Ref);

procedure {:inline 1} System.String.op_Equality$System.String$System.String(a$in: Ref, b$in: Ref) returns ($result: bool);
procedure {:inline 1} System.String.op_Inequality$System.String$System.String(a$in: Ref, b$in: Ref) returns ($result: bool);

implementation System.String.op_Equality$System.String$System.String(a$in: Ref, b$in: Ref) returns ($result: bool) 
{
  $result := (a$in == b$in);
}

implementation System.String.op_Inequality$System.String$System.String(a$in: Ref, b$in: Ref) returns ($result: bool) 
{
  $result := (a$in != b$in);
}

";

    [RepresentationFor("$RefToDelegateMethod", "function $RefToDelegateMethod(int, Ref): bool;")]
    public Bpl.Function RefToDelegateMethod = null;

    [RepresentationFor("$RefToDelegateReceiver", "function $RefToDelegateReceiver(int, Ref): Ref;")]
    public Bpl.Function RefToDelegateReceiver = null;

    [RepresentationFor("$RefToDelegateTypeParameters", "function $RefToDelegateTypeParameters(int, Ref): Type;")]
    public Bpl.Function RefToDelegateTypeParameters = null;
    
    [RepresentationFor("$Exception", "var {:thread_local} $Exception: Ref;")]
    public Bpl.GlobalVariable ExceptionVariable = null;
  }

  public abstract class HeapFactory {

    /// <summary>
    /// Returns two things: an object that determines the heap representation,
    /// and (optionally) an initial program that contains declarations needed
    /// for the heap representation.
    /// </summary>
    /// <param name="sink">
    /// The heap might need to generate declarations so it needs access to the Sink.
    /// </param>
    /// <returns>
    /// false if and only if an error occurrs and the heap and/or program are not in a
    /// good state to be used.
    /// </returns>
    public abstract bool MakeHeap(Sink sink, out Heap heap, out Bpl.Program/*?*/ program);
  }

}