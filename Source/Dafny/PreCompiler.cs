using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Linq;

using IToken = Microsoft.Boogie.IToken;
using Token = Microsoft.Boogie.Token;

namespace Microsoft.Dafny {
  class PreCompiler {
    // TODO Make this a command-line option
    private bool Verbose = false; // not const to avoid silly compiler warning

    private readonly Program Program;
    private readonly TargetLanguage Target;
    private readonly FreshIdGenerator IdGen;

    #region Construction and invocation

    private PreCompiler(Program prog, TargetLanguage target, FreshIdGenerator idGen) {
      this.Program = prog;
      Target = target;
      IdGen = idGen;

      Sequentializer = MakeSequentalizer();
    }

    public static void PreCompile(Program prog, TargetLanguage target, FreshIdGenerator idGen) {
      new PreCompiler(prog, target, idGen).Run();
    }

    #endregion

    #region Main pre-compiler engine

    void Run() {
      AnnouncePass("Resolver");

      Preprocess();
      AnnouncePass("Preprocessing");

      if (Target.MultipleReturnStyle == TargetLanguage.MultipleReturnStyleEnum.Tuple) {
        TupleReturns();
        AnnouncePass("Tuple Returns");
      }

      SequentializeAssignments();
      AnnouncePass("Sequentialize Assignments");
    }

    #endregion

    #region Output

    void AnnouncePass(string header) {
      if (!Verbose) {
        return;
      }

      // TODO: More control over output, including which passes to dump and into
      // what file or files (see GHC options for dumping core-to-core passes into
      // different files).

      var dashes = new string('-', header.Length + 4);

      System.Console.WriteLine();
      System.Console.WriteLine(dashes);
      System.Console.WriteLine($"| {header} |");
      System.Console.WriteLine(dashes);
      System.Console.WriteLine();

      Main.MaybePrintProgram(Program, "-", afterResolver: true, forCompilation: true);
    }
    #endregion

    #region Passes

    #region Preprocessing

    /// Simplify the AST in ways that make transformations easier.  In
    /// particular, some AST classes have fields of type UpdateStmt (namely
    /// ProduceStmt.hiddenUpdate and VarDeclStmt.Update), and this is a pain
    /// as we'd like to replace some UpdateStmts with BlockStmts.
    ///
    /// Unfortunately, not much can be done about VarDeclStmt.Update, since
    /// `var x := 42;` and `var x : int; x := 42;` don't generate the same
    /// code. Specifically, the latter generates two assignments to `x`, the
    /// first giving a default value, and Java cares which variables are
    /// assigned to exactly once (such variables are "effectively final" and
    /// may be used from inside a lambda or local class).
    ///
    /// TODO?: Create an AssignmentRhs subclass that specifically *suppresses*
    /// the assignment of a default value, allowed only when the variable won't
    /// be read before it's next written to.  If we wrote this RHS as
    /// `undefined`, then we could write `var x := undefined; x := 42;` which
    /// would indeed be equivalent to `var x := 42`.
    ///
    /// Also adds explicit return statements to methods in which control may
    /// fall off the end.
    void Preprocess() {
      foreach (Method method in AllMethods) {
        if (method.Body == null) {
          continue;
        }

        method.Body.TransformSubStatements(Transformer<Statement>.CreateRecursive((self, stmt) => {
          if (stmt is ProduceStmt produce) {
            // return x, y; ==> out1, out2 := x, y; return
            var update = produce.hiddenUpdate;
            if (update != null) {
              produce.hiddenUpdate = null;
              produce.rhss = null;
              return new BlockStmt(NT, NT, new List<Statement>() { update, produce });
            } else {
              return stmt;
            }
          } else {
            stmt.TransformSubStatements(self);
            return stmt;
          }
        }));

        // Ensure that no method ends with an implicit return
        if (MayFallThrough(method.Body)) {
          method.Body.AppendStmt(new ReturnStmt(NT, NT, rhss: null));
        }
      }
    }

    // Whether control may pass through the given statement to the next (or
    // the end of the method)
    static bool MayFallThrough(Statement stmt) {
      switch (stmt) {
        case BreakStmt _:
        case ReturnStmt _:
          return false;
        case BlockStmt block:
          return MayFallThroughAll(block.Body);
        case IfStmt ifStmt:
          return MayFallThrough(ifStmt.Thn) && MayFallThrough(ifStmt.Els);
        case WhileStmt whileStmt:
          if (whileStmt.Guard is LiteralExpr lit && lit.Value == (object) true) {
            return MayBreak(whileStmt.Body, whileStmt);
          } else {
            return true;
          }
        case AlternativeLoopStmt loop:
          return loop.Alternatives.All(alt => MayFallThroughAll(alt.Body));
        case MatchStmt match:
          return match.Cases.All(c => MayFallThroughAll(c.Body));
        case SkeletonStatement skel:
          return MayFallThrough(skel.S);
        default:
          return true;
      }
    }

    static bool MayFallThroughAll(List<Statement> stmts) {
      // Assume there's no dead code.  (The purpose here is to avoid adding
      // dead code, so if there's already dead code, we're not making the
      // situation worse.)

      return stmts.Count == 0 || MayFallThrough(stmts.Last());
    }

    // Whether the statement may cause a break targeting the given statement,
    // assuming there's no dead code
    static bool MayBreak(Statement stmt, Statement target) {
      switch (stmt) {
        case BreakStmt brk:
          return brk.TargetStmt == target;
        case ReturnStmt _:
          return false;
        case BlockStmt block:
          return block.Body.Any(s => MayBreak(s, target));
        case IfStmt ifStmt:
          return MayBreak(ifStmt.Thn, target) || MayBreak(ifStmt.Els, target);
        case WhileStmt whileStmt:
          return MayBreak(whileStmt.Body, target);
        case AlternativeLoopStmt loop:
          return loop.Alternatives.Any(alt => alt.Body.Any(s => MayBreak(s, target)));
        case MatchStmt match:
          return match.Cases.Any(c => c.Body.Any(s => MayBreak(s, target)));
        case SkeletonStatement skel:
          return MayBreak(skel.S, target);
        default:
          return true;
      }
    }

    #endregion Preprocessing

    #region Return tupling
    void TupleReturns() {
      // First, tuple all method calls in the whole program that need it, since this
      // step needs the methods to still have the original form, then tuple all the
      // method declarations in a second step.

      foreach (var method in AllMethods) {
        if (method.Body != null) {
          TupleMethodCalls(method.Body);
        }
      }

      foreach (var method in AllMethods) {
        if (method.Outs.Count(f => !f.IsGhost) > 1) {
          TupleMethodDecl(method);
        }
      }
    }

    void TupleMethodDecl(Method method) {
      var origOuts = method.Outs.FindAll(f => !f.IsGhost);
      var outTypes = origOuts.ConvertAll(f => f.Type);

      var tupleOut = new Formal(NT, IdGen.FreshId("_tuple"), TupleType(outTypes), inParam: false, isGhost: false);

      // Arbitrarily, make the tuple the first out parameter (followed only by
      // ghost outs).
      var newOuts = new List<Formal>();
      newOuts.Add(tupleOut);
      newOuts.AddRange(method.Outs.FindAll(f => f.IsGhost));
      method.Outs.Clear();
      method.Outs.AddRange(newOuts);

      Contract.Assert(!(method.Body is DividedBlockStmt)); // constructors don't have out parameters

      // Turn each original out parameter into a local variable
      var locals = new List<LocalVariable>();
      var outsToLocals = new Dictionary<Formal, LocalVariable>();
      foreach (var outParam in origOuts) {
        Contract.Assert(!outParam.IsGhost);
        var local = new LocalVariable(outParam.Tok, NT, outParam.Name, outParam.Type, isGhost: false);
        local.type = outParam.Type; // setting it in the constructor only sets OptionalType
        locals.Add(local);
        outsToLocals[outParam] = local;
      }

      if (method.Body != null) {
        var oldOutDecl = new VarDeclStmt(NT, NT, outsToLocals.Values.ToList(), update: null);
        var renamer = InPlaceRenamer(outsToLocals);
        foreach (var stmt in method.Body.Body) {
          stmt.TransformDeepSubExpressions(renamer);
        }
        method.Body.Body.Insert(0, oldOutDecl);

        // Wherever there is a return or yield, add an update to the tuple out
        // from the locals
        var returnXform = Transformer<Statement>.CreateRecursive((self, stmt) => {
          if (stmt is ProduceStmt produce) {
            // If the outs are o, p, and q, turn
            //   return;
            // into
            //   tuple := (o, p, q);
            //   return;
            // (Note that there are no returns with RHSes anymore since we
            // transformed them earlier.)

            // Create the assignment statement `tuple := (o, p, q)`
            var tupleExpr = TupleExpr(locals.ConvertAll(l => (Expression) new IdentifierExpr(NT, l)));
            var assignStmt = new AssignStmt(NT, NT, new IdentifierExpr(NT, tupleOut), new ExprRhs(tupleExpr));

            return new BlockStmt(NT, NT, new List<Statement>() { assignStmt, produce });
          } else {
            stmt.TransformSubStatements(self);
            return stmt;
          }
        });
        method.Body.TransformSubStatements(returnXform);
      }
    }

    void TupleMethodCalls(BlockStmt block) {
      var xform = Transformer<Statement>.CreateRecursive((self, stmt) => {
        // Look for an UpdateStmt either in stmt itself or in the Update0 field
        // of a VarDeclStmt
        UpdateStmt update;
        if (stmt is UpdateStmt u) {
          update = u;
        } else if (stmt is VarDeclStmt varDecl) {
          update = varDecl.Update as UpdateStmt;
        } else {
          update = null;
        }

        if (update == null) {
          stmt.TransformSubStatements(self);
          return stmt;
        }

        if (!(update.ResolvedStatements.Count == 1 &&
            update.ResolvedStatements[0] is CallStmt call &&
            call.Method.Outs.Count(f => !f.IsGhost) > 1)) {
          // Don't recurse; in the VarDeclStmt case, we already know we're not
          // interested in the sub-statement
          return stmt;
        }

        var realOuts = call.Method.Outs.FindAll(f => !f.IsGhost);
        var typeSubst = call.MethodSelect.TypeArgumentSubstitutions();
        var realOutTypes = realOuts.ConvertAll(e => Resolver.SubstType(e.Type, typeSubst));
        Statement tupleDecl;
        var tupleVar = DeclareLocalVariable("_outcollector", TupleType(realOutTypes), rhs: null, isGhost: false, out tupleDecl);

        // The new LHSes consist of a single tuple followed by any number of
        // ghost LHSes from the original statement
        var newLhss = new List<Expression>() { new IdentifierExpr(NT, tupleVar) };
        var origRealLhss = new List<Expression>();
        for (var i = 0; i < call.Method.Outs.Count; i++) {
          if (call.Method.Outs[i].IsGhost) {
            newLhss.Add(call.Lhs[i]);
          } else {
            origRealLhss.Add(call.Lhs[i]);
          }
        }
        call.Lhs.Clear();
        call.Lhs.AddRange(newLhss);

        var newStmts = new List<Statement>() { tupleDecl, stmt };
        for (var i = 0; i < origRealLhss.Count; i++) {
          var lhs = origRealLhss[i];
          // origRealLhss has the LHSes for non-ghost out parameters, but some
          // of those LHSes might be ghost variables themselves
          if (Compiler.IsGhostLHS(lhs)) {
            continue;
          }

          var rhs = new ExprRhs(TupleProjExpr(new IdentifierExpr(NT, tupleVar), i));
          newStmts.Add(new AssignStmt(NT, NT, lhs, rhs));
        }

        return new BlockStmt(NT, NT, newStmts) {
          Scoped = false // allow a VarDeclStmt to be visible outside the block
        };
      });
      block.TransformSubStatements(xform);
    }
    #endregion Return tupling

    #region Assignment sequentialization

    void SequentializeAssignments() {
      foreach (var module in Program.CompileModules) {
        foreach (var decl in module.TopLevelDecls.OfType<TopLevelDeclWithMembers>()) {
          foreach (var method in decl.Members.OfType<Method>()) {
            if (method.Body != null) {
              SequentializeAssignments(method.Body);
            }
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
      if (stmt is VarDeclStmt varDecl) {
        // A VarDeclStmt can contain an UpdateStmt, which is troublesome because
        // it can only be replaced by another UpdateStmt, and our usual
        // replacement procedure replaces an UpdateStmt with a BlockStmt.
        // Fortunately, the particular update statement that a VarDeclStmt
        // contains only ever updates distinct, fresh variables, so it's always
        // safe to sequentialize naively.
        if (varDecl.Update is UpdateStmt update && update.ResolvedStatements.Count != 1) {
          Contract.Assert(varDecl.Locals.Count == update.ResolvedStatements.Count);
          var stmts = new List<Statement>();
          for (var i = 0; i < varDecl.Locals.Count; i++) {
            var local = varDecl.Locals[i];
            var resolved = update.ResolvedStatements[i];
            stmts.Add(new VarDeclStmt(Token.NoToken, Token.NoToken, new List<LocalVariable>() { local }, update: null));
            stmts.Add(resolved);
          }
          return new BlockStmt(varDecl.Tok, varDecl.EndTok, stmts) {
            // This "block" is just a convenient way to return a bunch of
            // statements in something of type Statement; make sure it doesn't
            // get rendered as an actual block, since then the variable
            // declarations won't be visible outside it
            Scoped = false
          };
        } else {
          return stmt;
        }
      } else if (stmt is UpdateStmt update && update.ResolvedStatements.Count != 1) {
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

          var assign = new AssignStmt(update.Tok, update.EndTok, stableLhs, new ExprRhs(new IdentifierExpr(NT, rhsVar))) {
            IsGhost = isGhost
          };
          assigns.Add(assign);
        }

        return new BlockStmt(stmt.Tok, stmt.EndTok, Util.Concat(rhsDecls, lhsDecls, assigns));
      } else {
        SequentializeAssignments(stmt);
        return stmt;
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
        return new IdentifierExpr(NT, x);
      }
    }

    #endregion Assignment sequentialization

    #endregion Passes

    #region Utilities
    static readonly IToken NT = Token.NoToken;

    IEnumerable<Method> AllMethods {
      get {
        foreach (var module in Program.CompileModules) {
          foreach (var decl in module.TopLevelDecls.OfType<TopLevelDeclWithMembers>()) {
            foreach (var method in decl.Members.OfType<Method>()) {
              yield return method;
            }
          }
        }
      }
    }

    LocalVariable DeclareLocalVariable(string prefix, Type type, AssignmentRhs/*?*/ rhs, bool isGhost, out Statement decl) {
      var x = new LocalVariable(NT, NT, IdGen.FreshId(prefix), type, isGhost);
      x.type = type; // constructor argument sets OptionalType, not type
      UpdateStmt update;
      if (rhs != null) {
        update = new UpdateStmt(NT, NT, new List<Expression>() { new IdentifierExpr(NT, x) }, new List<AssignmentRhs>() { rhs });
        update.ResolvedStatements.Add(new AssignStmt(NT, NT, new IdentifierExpr(NT, x), rhs) { IsGhost = isGhost });
      } else {
        update = null;
      }
      decl = new VarDeclStmt(NT, NT, new List<LocalVariable>() { x }, update);
      return x;
    }

    Type TupleType(params Type[] types) {
      return TupleType(types.ToList());
    }

    Type TupleType(List<Type> types) {
      var decl = TupleTypeDecl(types.Count);
      return new UserDefinedType(NT, decl.Name, decl, types.ToList());
    }

    TupleTypeDecl TupleTypeDecl(int length) {
      // FIXME: We should set allowCreationOfNewType to true, but since the resolver
      // hasn't run, doing so may give us an unresolved TupleTypeDecl (which, for
      // instance, has no destructors).
      return Program.BuiltIns.TupleType(NT, length, allowCreationOfNewType: false);
    }

    Expression TupleExpr(params Expression[] exprs) {
      return TupleExpr(exprs.ToList());
    }

    Expression TupleExpr(List<Expression> exprs) {
      var decl = TupleTypeDecl(exprs.Count);
      return new DatatypeValue(NT, decl.DefaultCtor, exprs.ConvertAll(expr => expr.Type), exprs, isCoCall: false);
    }

    Expression TupleProjExpr(Expression tuple, int index) {
      return new MemberSelectExpr(NT, tuple, tuple.Type.AsDatatype.Ctors[0].Destructors[index]);
    }

    Transformer<Expression> InPlaceRenamer<K, V>(Dictionary<K, V> dict) where V : class, IVariable {
      return InPlaceRenamer(v => {
        return v is K k && dict.TryGetValue(k, out var val) ? val : null;
      });
    }

    Transformer<Expression> InPlaceRenamer(Func<IVariable, IVariable/*?*/> f) {
      return InPlaceSubstituter(var => {
        var newVar = f(var);
        if (newVar == null) {
          return null;
        } else {
          return new IdentifierExpr(NT, newVar);
        }
      });
    }

    Transformer<Expression> InPlaceSubstituter(Func<IVariable, Expression/*?*/> f) {
      return Transformer<Expression>.CreateRecursive((self, expr) => {
        var idExpr = expr as IdentifierExpr ?? (expr as ConcreteSyntaxExpression)?.ResolvedExpression as IdentifierExpr;
        if (idExpr != null) {
          return f(idExpr.Var) ?? idExpr;
        } else {
          expr.TransformSubExpressions(self);
          return expr;
        }
      });
    }
    #endregion
  }
}