using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny.Core {
  class Converter {
    public static Core.Program ConvertProgram(Dafny.Program program) {
      return new Converter().Convert(program);
    }

    public Core.Program Convert(Dafny.Program program) {
      //TODO
      Contract.Assert(false);
      throw new cce.UnreachableException();
    }

    public Core.Statement Convert(Dafny.Statement stmt) {
      Core.Statement r;
      if (stmt is Dafny.AssertStmt) {
        var s = (Dafny.AssertStmt)stmt;
        r = new Core.AssertStmt(Convert(s.Expr), Convert(s.Proof), s.Label == null ? null : new Core.AssertLabel(s.Label.Name), null);

      } else if (stmt is Dafny.AssumeStmt) {
        var s = (Dafny.AssumeStmt)stmt;
        r = new Core.AssumeStmt(Convert(s.Expr), null);

      } else if (stmt is Dafny.PrintStmt) {
        var s = (Dafny.PrintStmt)stmt;
        r = new Core.PrintStmt(s.Args.ConvertAll(Convert));

      } else if (stmt is Dafny.RevealStmt) {
        var s = (Dafny.RevealStmt)stmt;
        r = new Core.RevealStmt(s.Exprs.ConvertAll(Convert));

      } else if (stmt is Dafny.BreakStmt) {
        var s = (Dafny.BreakStmt)stmt;
        if (s.TargetLabel != null) {
          r = new Core.BreakStmt(s.TargetLabel);
        } else {
          r = new Core.BreakStmt(s.BreakCount);
        }

      } else if (stmt is Dafny.ReturnStmt) {
        var s = (Dafny.ReturnStmt)stmt;
        r = new Core.ReturnStmt(s.rhss == null ? null : s.rhss.ConvertAll(Convert));

      } else if (stmt is Dafny.YieldStmt) {
        var s = (Dafny.YieldStmt)stmt;
        r = new Core.YieldStmt(s.rhss == null ? null : s.rhss.ConvertAll(Convert));

      } else if (stmt is Dafny.AssignStmt) {
        var s = (Dafny.AssignStmt)stmt;
        r = new Core.AssignStmt(Convert(s.Lhs), Convert(s.Rhs));

      } else if (stmt is Dafny.DividedBlockStmt) {
        r = Convert((Dafny.DividedBlockStmt)stmt);

      } else if (stmt is Dafny.BlockStmt) {
        r = Convert((Dafny.BlockStmt)stmt);

      } else if (stmt is Dafny.IfStmt) {
        var s = (Dafny.IfStmt)stmt;
        r = new Core.IfStmt(s.IsBindingGuard, Convert(s.Guard), Convert(s.Thn), Convert(s.Els));

      } else if (stmt is Dafny.AlternativeStmt) {
        var s = (Dafny.AlternativeStmt)stmt;
        r = new Core.AlternativeStmt(s.Alternatives.ConvertAll(Convert), s.UsesOptionalBraces);

      } else if (stmt is Dafny.WhileStmt) {
        var s = (Dafny.WhileStmt)stmt;
        r = new Core.WhileStmt(Convert(s.Guard), s.Invariants.ConvertAll(Converter), CloneSpecExpr(s.Decreases), CloneSpecFrameExpr(s.Mod), Convert(s.Body));

      } else if (stmt is Dafny.AlternativeLoopStmt) {
        var s = (Dafny.AlternativeLoopStmt)stmt;
        r = new Core.AlternativeLoopStmt(s.Invariants.ConvertAll(Convert), CloneSpecExpr(s.Decreases), CloneSpecFrameExpr(s.Mod), s.Alternatives.ConvertAll(CloneGuardedAlternative), s.UsesOptionalBraces);

      } else if (stmt is Dafny.ForallStmt) {
        var s = (Dafny.ForallStmt)stmt;
        r = new Core.ForallStmt(s.BoundVars.ConvertAll(Convert), null, Convert(s.Range), s.Ens.ConvertAll(Convert), Convert(s.Body));
      } else if (stmt is Dafny.CalcStmt) {
        var s = (Dafny.CalcStmt)stmt;
        // calc statements have the unusual property that the last line is duplicated.  If that is the case (which
        // we expect it to be here), we share the conversion of that line as well.
        var lineCount = s.Lines.Count;
        var lines = new List<Expression>(lineCount);
        for (int i = 0; i < lineCount; i++) {
          lines.Add(i == lineCount - 1 && 2 <= lineCount && s.Lines[i] == s.Lines[i - 1] ? lines[i - 1] : Convert(s.Lines[i]));
        }
        Contract.Assert(lines.Count == lineCount);
        r = new Core.CalcStmt(Convert(s.UserSuppliedOp), lines, s.Hints.ConvertAll(Convert), s.StepOps.ConvertAll(Convert), Convert(s.Attributes));

      } else if (stmt is Dafny.MatchStmt) {
        var s = (Dafny.MatchStmt)stmt;
        r = new Core.MatchStmt(Convert(s.Source), s.Cases.ConvertAll(Convert), s.UsesOptionalBraces);

      } else if (stmt is Dafny.AssignSuchThatStmt) {
        var s = (Dafny.AssignSuchThatStmt)stmt;
        r = new Core.AssignSuchThatStmt(s.Lhss.ConvertAll(Convert), Convert(s.Expr), s.AssumeToken != null, null);

      } else if (stmt is Dafny.UpdateStmt) {
        var s = (Dafny.UpdateStmt)stmt;
        r = new Core.BlockStmt(s.ResolvedStatements.ConvertAll(Convert));

      } else if (stmt is Dafny.AssignOrReturnStmt) {
        var s = (Dafny.AssignOrReturnStmt)stmt;
        r = new Core.BlockStmt(s.ResolvedStatements.ConvertAll(Convert));

      } else if (stmt is Dafny.VarDeclStmt) {
        var s = (Dafny.VarDeclStmt)stmt;
        var lhss = s.Locals.ConvertAll(c => new LocalVariable(c.Name, Convert(c.OptionalType), c.IsGhost));
        r = new Core.VarDeclStmt(lhss, (Core.ConcreteUpdateStatement)Convert(s.Update));

      } else if (stmt is Dafny.LetStmt) {
        var s = (Dafny.LetStmt) stmt;
        r = new Core.LetStmt(Convert(s.LHS), Convert(s.RHS));

      } else if (stmt is Dafny.ModifyStmt) {
        var s = (Dafny.ModifyStmt)stmt;
        var mod = Convert(s.Mod);
        var body = s.Body == null ? null : Convert(s.Body);
        r = new Core.ModifyStmt(mod.Expressions, mod.Attributes, body);

      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected statement
      }
    }

    public Core.BlockStmt Convert(Dafny.BlockStmt stmt) {
      Contract.Requires(!(stmt is Dafny.DividedBlockStmt));

      return stmt == null ? null : new Core.BlockStmt(stmt.Body.ConvertAll(Convert));
    }

    public Core.DividedBlockStmt Convert(Dafny.DividedBlockStmt stmt) {
      return stmt == null ? null : new Core.DividedBlockStmt(stmt.BodyInit.ConvertAll(Convert), stmt.BodyProper.ConvertAll(Convert));
    }

    public Core.Expression Convert(Dafny.Expression expr) {

    }

    public Core.AssignmentRhs Convert(Dafny.AssignmentRhs rhs) {
    }

    public Core.Specification<Core.Expression> Convert(Dafny.Specification<Dafny.Expression> specExpr) {
      return new Core.Specification<Core.Expression>(specExpr.Expressions.ConvertAll(Convert), Convert(specExpr.Attributes));
    }

    public Core.Attributes Convert(Dafny.Attributes attrs) {
      if (attrs is Dafny.UserSuppliedAttributes usa) {
        return new Core.UserSuppliedAttributes(usa.Name, usa.Args.ConvertAll(Convert), Convert(usa.Prev));
      } else {
        return new Core.Attributes(attrs.Name, attrs.Args.ConvertAll(Convert), Convert(attrs.Prev));
      }
    }

    public Core.BoundVar Convert(Dafny.BoundVar bv) {
      
    }
  }
}