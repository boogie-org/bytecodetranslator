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
using System.Text.RegularExpressions;

namespace BytecodeTranslator {

  public class MethodParameter {
    
    /// <summary>
    /// All parameters of the method get an associated in parameter
    /// in the Boogie procedure except for out parameters.
    /// </summary>
    public Bpl.Formal/*?*/ inParameterCopy;
    
    /// <summary>
    /// A local variable when the underlyingParameter is an in parameter
    /// and a formal (out) parameter when the underlyingParameter is
    /// a ref or out parameter.
    /// </summary>
    public Bpl.Variable outParameterCopy;

    public IParameterDefinition underlyingParameter;

    public MethodParameter(IParameterDefinition parameterDefinition, Bpl.Type ptype) {
      this.underlyingParameter = parameterDefinition;

      var parameterToken = parameterDefinition.Token();
      var typeToken = parameterDefinition.Type.Token();
      var parameterName = TranslationHelper.TurnStringIntoValidIdentifier(parameterDefinition.Name.Value);
      if (String.IsNullOrWhiteSpace(parameterName)) parameterName = "P" + parameterDefinition.Index.ToString();

      this.inParameterCopy = new Bpl.Formal(parameterToken, new Bpl.TypedIdent(typeToken, parameterName + "$in", ptype), true);
      if (parameterDefinition.IsByReference) {
        this.outParameterCopy = new Bpl.Formal(parameterToken, new Bpl.TypedIdent(typeToken, parameterName + "$out", ptype), false);
      } else {
        this.outParameterCopy = new Bpl.LocalVariable(parameterToken, new Bpl.TypedIdent(typeToken, parameterName, ptype));
      }
    }

    public override string ToString() {
      return this.underlyingParameter.Name.Value;
    }
  }

    /// <summary>
    /// Class containing several static helper functions to convert
    /// from Cci to Boogie
    /// </summary>
  static class TranslationHelper {
    public static Bpl.StmtList BuildStmtList(Bpl.Cmd cmd, Bpl.TransferCmd tcmd) {
      Bpl.StmtListBuilder builder = new Bpl.StmtListBuilder();
      builder.Add(cmd);
      builder.Add(tcmd);
      return builder.Collect(Bpl.Token.NoToken);
    }

    public static Bpl.StmtList BuildStmtList(Bpl.TransferCmd tcmd) {
      Bpl.StmtListBuilder builder = new Bpl.StmtListBuilder();
      builder.Add(tcmd);
      return builder.Collect(Bpl.Token.NoToken);
    }

    public static Bpl.StmtList BuildStmtList(params Bpl.Cmd[] cmds) {
      Bpl.StmtListBuilder builder = new Bpl.StmtListBuilder();
      foreach (Bpl.Cmd cmd in cmds)
        builder.Add(cmd);
      return builder.Collect(Bpl.Token.NoToken);
    }

    public static Bpl.AssignCmd BuildAssignCmd(Bpl.IdentifierExpr lhs, Bpl.Expr rhs)
    {
      List<Bpl.AssignLhs> lhss = new List<Bpl.AssignLhs>();
      lhss.Add(new Bpl.SimpleAssignLhs(lhs.tok, lhs));
      List<Bpl.Expr> rhss = new List<Bpl.Expr>();
      rhss.Add(rhs);
      return new Bpl.AssignCmd(lhs.tok, lhss, rhss);
    }

    public static Bpl.AssignCmd BuildAssignCmd(List<Bpl.IdentifierExpr> lexprs, List<Bpl.Expr> rexprs) {
      List<Bpl.AssignLhs> lhss = new List<Bpl.AssignLhs>();
      foreach (Bpl.IdentifierExpr lexpr in lexprs) {
        lhss.Add(new Bpl.SimpleAssignLhs(lexpr.tok, lexpr));
      }
      List<Bpl.Expr> rhss = new List<Bpl.Expr>();
      return new Bpl.AssignCmd(Bpl.Token.NoToken, lhss, rexprs);
    }

    public static Bpl.IToken Token(this IObjectWithLocations objectWithLocations) {
      //TODO: use objectWithLocations.Locations!
      Bpl.IToken tok = Bpl.Token.NoToken;
      return tok;
    }

    internal static int tmpVarCounter = 0;
    public static string GenerateTempVarName() {
      return "$tmp" + (tmpVarCounter++).ToString();
    }

    internal static int catchClauseCounter = 0;
    public static string GenerateCatchClauseName() {
      return "catch" + (catchClauseCounter++).ToString();
    }

    internal static int finallyClauseCounter = 0;
    public static string GenerateFinallyClauseName() {
      return "finally" + (finallyClauseCounter++).ToString();
    }

    public static string CreateUniqueMethodName(IMethodReference method) {
      var containingTypeName = TypeHelper.GetTypeName(method.ContainingType, NameFormattingOptions.None);
      var s = MemberHelper.GetMethodSignature(method, NameFormattingOptions.DocumentationId);
      s = s.Substring(2);
      s = s.TrimEnd(')');
      s = TurnStringIntoValidIdentifier(s);
      return s;
    }

    public static string TurnStringIntoValidIdentifier(string s) {

      // Do this specially just to make the resulting string a little bit more readable.
      // REVIEW: Just let the main replacement take care of it?
      s = s.Replace("[0:,0:]", "2DArray"); // TODO: Do this programmatically to handle arbitrary arity
      s = s.Replace("[0:,0:,0:]", "3DArray");
      s = s.Replace("[0:,0:,0:,0:]", "4DArray");
      s = s.Replace("[0:,0:,0:,0:,0:]", "5DArray");
      s = s.Replace("[]", "array");

      // The definition of a Boogie identifier is from BoogiePL.atg.
      // Just negate that to get which characters should be replaced with a dollar sign.

      // letter = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz".
      // digit = "0123456789".
      // special = "'~#$^_.?`".
      // nondigit = letter + special.
      // ident =  [ '\\' ] nondigit {nondigit | digit}.

      s = Regex.Replace(s, "[^A-Za-z0-9'~#$^_.?`]", "$");
      
      s = GetRidOfSurrogateCharacters(s);
      return s;
    }

    /// <summary>
    /// Unicode surrogates cannot be handled by Boogie.
    /// http://msdn.microsoft.com/en-us/library/dd374069(v=VS.85).aspx
    /// </summary>
    private static string GetRidOfSurrogateCharacters(string s) {
      //  TODO this is not enough! Actually Boogie cannot support UTF8
      var cs = s.ToCharArray();
      var okayChars = new char[cs.Length];
      for (int i = 0, j = 0; i < cs.Length; i++) {
        if (Char.IsSurrogate(cs[i])) continue;
        okayChars[j++] = cs[i];
      }
      var raw = String.Concat(okayChars);
      return raw.Trim(new char[] { '\0' });
    }

    public static bool IsStruct(ITypeReference typ) {
      return typ.IsValueType && !typ.IsEnum && typ.TypeCode == PrimitiveTypeCode.NotPrimitive;
    }

  }
}
