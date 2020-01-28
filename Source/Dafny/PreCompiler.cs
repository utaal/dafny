using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

using Token = Microsoft.Boogie.Token;

namespace Microsoft.Dafny {
  class PreCompiler {
    private readonly FreshIdGenerator IdGen;

    private PreCompiler(FreshIdGenerator idGen) {
      IdGen = idGen;

      Sequentializer = MakeSequentalizer();
    }

    public static void PreCompile(Program prog, FreshIdGenerator idGen) {
      new PreCompiler(idGen).PreCompile(prog);
    }

    void PreCompile(Program prog) {
      Main.MaybePrintProgram(prog, "-", afterResolver: true, forCompilation: true);
      SequentializeAssignments(prog);
      Main.MaybePrintProgram(prog, "-", afterResolver: true, forCompilation: true);
    }

    void SequentializeAssignments(Program prog) {
      foreach (var module in prog.CompileModules) {
        foreach (var decl in module.TopLevelDecls.OfType<TopLevelDeclWithMembers>()) {
          foreach (var method in decl.Members.OfType<Method>()) {
            SequentializeAssignments(method.Body);
          }
        }
      }
    }

    readonly Transformer<Statement> Sequentializer;

    Transformer<Statement> MakeSequentalizer() {
      return new Transformer<Statement>(Sequentialize);
    }

    void SequentializeAssignments(Statement stmt) {
      stmt.TransformSubStatements(Sequentializer);
    }

    Statement Sequentialize(Statement stmt) {
      if (!(stmt is UpdateStmt update) || update.Lhss.Count == 1) {
        SequentializeAssignments(stmt);
        return stmt;
      } else {
        Contract.Assert(update.Lhss.Count == update.Rhss.Count);
        var rhsDecls = new List<Statement>();
        var lhsDecls = new List<Statement>();
        var assigns = new List<Statement>();
        for (var i = 0; i < update.Lhss.Count; i++) {
          var lhs = update.Lhss[i];
          var rhs = update.Rhss[i];
          var type = lhs.Type;
          var isGhost = update.ResolvedStatements[i].IsGhost;

          var rhsVar = DeclareLocalVariable("_rhs", lhs.Type, rhs, isGhost, out var decl);
          rhsDecls.Add(decl);

          var stableLhs = EvaluateLhs(lhs, isGhost, out var decls);
          lhsDecls.AddRange(decls);

          var assign = new AssignStmt(update.Tok, update.EndTok, stableLhs, new ExprRhs(rhsVar));
          assigns.Add(assign);
        }

        return new BlockStmt(stmt.Tok, stmt.EndTok, Util.Concat(rhsDecls, lhsDecls, assigns));
      }
    }

    Expression EvaluateLhs(Expression lhs, bool isGhost, out List<Statement> stmts) {
      // Given the statement
      //   xs, xs.next := ys, zs;
      // we want to evaluate xs.next before assigning to xs.  The naive solution
      //   var _lhs0 := xs.next;
      //   xs := ys;
      //   _lhs0 := zs;
      // only manages to declare a local variable and change its value. C# and
      // Go do offer workarounds (with ref variables and pointers,
      // respectively), but in general, we need to keep the top-level AST node
      // intact and only evaluate its children:
      //   xs.next => _obj42.next // where _obj42 = xs
      //   xs.next.next => _obj43.next // where _obj43 = xs.next
      //   xs[i] => _arr44[_index45] // where _arr44 = xs and _index45 = i
      lhs = lhs.Resolved;
      if (lhs is IdentifierExpr) {
        // This can't be changed by a previous LHS because LHSes must be distinct
        stmts = new List<Statement>();
        return lhs;
      } else if (lhs is MemberSelectExpr) {
        var ll = (MemberSelectExpr)lhs;
        Contract.Assert(!ll.Member.IsInstanceIndependentConstant);  // instance-independent const's don't have assignment statements
        var obj = EvaluateExpr(ll.Obj, "_obj", isGhost, out stmts);
        return new MemberSelectExpr(lhs.tok, obj, (Field) ll.Member); // must be field to be LHS
      } else if (lhs is SeqSelectExpr) {
        var ll = (SeqSelectExpr)lhs;
        var arr = EvaluateExpr(ll.Seq, "_arr", isGhost, out var arrayStmts);
        var index = EvaluateExpr(ll.E0, "_index", isGhost, out var indexStmts);
        stmts = Util.Concat(arrayStmts, indexStmts);
        return new SeqSelectExpr(lhs.tok, selectOne: true, arr, index, null) { Type = lhs.Type };
      } else {
        Contract.Assert(lhs is MultiSelectExpr, lhs.GetType() + " \"" + Printer.ExprToString(lhs) + "\": " + lhs.Type);
        var ll = (MultiSelectExpr)lhs;
        var arr = EvaluateExpr(ll.Array, "_arr", isGhost, out stmts);
        var indices = new List<Expression>();
        int i = 0;
        foreach (var idx in ll.Indices) {
          indices.Add(EvaluateExpr(idx, "_index" + i, isGhost, out var indexStmts));
          stmts.AddRange(indexStmts);
          i++;
        }
        return new MultiSelectExpr(lhs.tok, arr, indices) { Type = lhs.Type };
      }
    }

    Expression EvaluateExpr(Expression expr, string prefix, bool isGhost, out List<Statement> stmts) {
      stmts = new List<Statement>();
      if (expr is ThisExpr || expr is LiteralExpr) {
        return expr;
      } else {
        var x = DeclareLocalVariable(prefix, expr.Type, new ExprRhs(expr), isGhost, out var stmt);
        stmts = new List<Statement>() { stmt };
        return x;
      }
    }

    Expression DeclareLocalVariable(string prefix, Type type, AssignmentRhs rhs, bool isGhost, out Statement decl) {
      var x = new LocalVariable(Token.NoToken, Token.NoToken, IdGen.FreshId(prefix), type, isGhost);
      x.type = type; // constructor argument sets OptionalType, not type
      var expr = new IdentifierExpr(Token.NoToken, x);
      var setX = new UpdateStmt(Token.NoToken, Token.NoToken, new List<Expression>() { expr }, new List<AssignmentRhs>() { rhs });
      setX.ResolvedStatements.Add(new AssignStmt(Token.NoToken, Token.NoToken, expr, rhs));
      decl = new VarDeclStmt(Token.NoToken, Token.NoToken, new List<LocalVariable>() { x }, setX);
      return expr;
    }
  }
}