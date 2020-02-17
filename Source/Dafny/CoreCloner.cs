using System;
using System.Collections.Generic;
using System.Numerics;
using System.Diagnostics.Contracts;
using Bpl = Microsoft.Boogie;

namespace Microsoft.Dafny.Core
{
  class Cloner
  {


    public virtual ModuleDefinition CloneModuleDefinition(ModuleDefinition m, string name) {
      ModuleDefinition nw;
      if (m is DefaultModuleDecl) {
        nw = new DefaultModuleDecl();
      } else {
        nw = new ModuleDefinition(name, m.PrefixIds, m.IsAbstract, m.IsProtected, m.IsFacade, m.RefinementBaseName, m.Module, CloneAttributes(m.Attributes), true);
      }
      foreach (var d in m.TopLevelDecls) {
        nw.TopLevelDecls.Add(CloneDeclaration(d, nw));
      }
      foreach (var tup in m.PrefixNamedModules) {
        var newTup = new Tuple<List<string>, LiteralModuleDecl>(tup.Item1, (LiteralModuleDecl)CloneDeclaration(tup.Item2, nw));
        nw.PrefixNamedModules.Add(newTup);
      }
      if (null != m.RefinementBase) {
        nw.RefinementBase = GetRefinementBase(m);
      }
      nw.Height = m.Height;
      return nw;
    }


    public virtual ModuleDefinition GetRefinementBase(ModuleDefinition m) {
      Contract.Requires(m != null);
      return m.RefinementBase;
    }

    public virtual TopLevelDecl CloneDeclaration(TopLevelDecl d, ModuleDefinition m) {
      Contract.Requires(d != null);
      Contract.Requires(m != null);

      if (d is OpaqueTypeDecl) {
        var dd = (OpaqueTypeDecl)d;
        return new OpaqueTypeDecl(dd.Name, m, CloneTPChar(dd.TheType.Characteristics), dd.TypeArgs.ConvertAll(CloneTypeParam), CloneAttributes(dd.Attributes));
      } else if (d is SubsetTypeDecl) {
        Contract.Assume(!(d is NonNullTypeDecl));  // don't clone the non-null type declaration; close the class, which will create a new non-null type declaration
        var dd = (SubsetTypeDecl)d;
        var tps = dd.TypeArgs.ConvertAll(CloneTypeParam);
        return new SubsetTypeDecl(dd.Name, CloneTPChar(dd.Characteristics), tps, m, CloneType(dd.Rhs), dd.WitnessKind, CloneExpr(dd.Witness), CloneAttributes(dd.Attributes));
      } else if (d is TypeSynonymDecl) {
        var dd = (TypeSynonymDecl)d;
        var tps = dd.TypeArgs.ConvertAll(CloneTypeParam);
        return new TypeSynonymDecl(dd.Name, CloneTPChar(dd.Characteristics), tps, m, CloneType(dd.Rhs), CloneAttributes(dd.Attributes));
      } else if (d is NewtypeDecl) {
        var dd = (NewtypeDecl)d;
        return new NewtypeDecl(dd.Name, m, CloneType(dd.BaseType), dd.WitnessKind, CloneExpr(dd.Witness), dd.Members.ConvertAll(CloneMember), CloneAttributes(dd.Attributes));
      } else if (d is TupleTypeDecl) {
        var dd = (TupleTypeDecl)d;
        return new TupleTypeDecl(dd.Dims, dd.Module, dd.Attributes);
      } else if (d is IndDatatypeDecl) {
        var dd = (IndDatatypeDecl)d;
        var tps = dd.TypeArgs.ConvertAll(CloneTypeParam);
        var ctors = dd.Ctors.ConvertAll(CloneCtor);
        var dt = new IndDatatypeDecl(dd.Name, m, tps, ctors, dd.Members.ConvertAll(CloneMember), CloneAttributes(dd.Attributes));
        return dt;
      } else if (d is CoDatatypeDecl) {
        var dd = (CoDatatypeDecl)d;
        var tps = dd.TypeArgs.ConvertAll(CloneTypeParam);
        var ctors = dd.Ctors.ConvertAll(CloneCtor);
        var dt = new CoDatatypeDecl(dd.Name, m, tps, ctors, dd.Members.ConvertAll(CloneMember), CloneAttributes(dd.Attributes));
        return dt;
      } else if (d is IteratorDecl) {
        var dd = (IteratorDecl)d;
        var tps = dd.TypeArgs.ConvertAll(CloneTypeParam);
        var ins = dd.Ins.ConvertAll(CloneFormal);
        var outs = dd.Outs.ConvertAll(CloneFormal);
        var body = CloneBlockStmt(dd.Body);
        var iter = new IteratorDecl(dd.Name, dd.Module,
          tps, ins, outs,
          body, CloneAttributes(dd.Attributes), dd.SignatureIsOmitted);
        return iter;
      } else if (d is TraitDecl) {
        var dd = (TraitDecl)d;
        var tps = dd.TypeArgs.ConvertAll(CloneTypeParam);
        var mm = dd.Members.ConvertAll(CloneMember);
        var cl = new TraitDecl(dd.Name, m, tps, mm, CloneAttributes(dd.Attributes));
        return cl;
      } else if (d is ClassDecl) {
        var dd = (ClassDecl)d;
        var tps = dd.TypeArgs.ConvertAll(CloneTypeParam);
        var mm = dd.Members.ConvertAll(CloneMember);
        if (d is DefaultClassDecl) {
          return new DefaultClassDecl(m, mm);
        } else {
          return new ClassDecl(dd.Name, m, tps, mm, CloneAttributes(dd.Attributes), dd.TraitsTyp.ConvertAll(CloneType));
        }
      } else if (d is ModuleDecl) {
        if (d is LiteralModuleDecl) {
          return new LiteralModuleDecl(((LiteralModuleDecl)d).ModuleDef, m);
        } else if (d is AliasModuleDecl) {
          var a = (AliasModuleDecl)d;
          return new AliasModuleDecl(a.Path, a.Name, m, a.Opened, a.Exports);
        } else if (d is ModuleFacadeDecl) {
          var a = (ModuleFacadeDecl)d;
          return new ModuleFacadeDecl(a.Path, a.Name, m, a.Opened, a.Exports);
        } else if (d is ModuleExportDecl) {
          var a = (ModuleExportDecl)d;
          return new ModuleExportDecl(a.Name, m, a.Exports, a.Extends, a.ProvideAll, a.RevealAll, a.IsDefault);
        } else {
          Contract.Assert(false);  // unexpected declaration
          return null;  // to please compiler
        }
      } else {
        Contract.Assert(false);  // unexpected declaration
        return null;  // to please compiler
      }
    }

    public TypeParameter.TypeParameterCharacteristics CloneTPChar(TypeParameter.TypeParameterCharacteristics characteristics) {
      TypeParameter.EqualitySupportValue eqSupport;
      if (characteristics.EqualitySupport == TypeParameter.EqualitySupportValue.InferredRequired) {
        eqSupport = TypeParameter.EqualitySupportValue.Unspecified;
      } else {
        eqSupport = characteristics.EqualitySupport;
      }
      return new TypeParameter.TypeParameterCharacteristics(eqSupport, characteristics.MustSupportZeroInitialization, characteristics.DisallowReferenceTypes);
    }

    public DatatypeCtor CloneCtor(DatatypeCtor ct) {
      return new DatatypeCtor(ct.Name, ct.Formals.ConvertAll(CloneFormal), CloneAttributes(ct.Attributes));
    }

    public TypeParameter CloneTypeParam(TypeParameter tp) {
      return new TypeParameter(tp.Name, tp.VarianceSyntax, CloneTPChar(tp.Characteristics));
    }

    public virtual MemberDecl CloneMember(MemberDecl member) {
      if (member is Field) {
        var f = (Field)member;
        return CloneField(f);
      } else if (member is Function) {
        var f = (Function)member;
        return CloneFunction(f);
      } else {
        var m = (Method)member;
        return CloneMethod(m);
      }
    }

    public virtual Type CloneType(Type t) {
      if (t is BasicType) {
        return t;
      } else if (t is SetType) {
        var tt = (SetType)t;
        return new SetType(tt.Finite, CloneType(tt.Arg));
      } else if (t is SeqType) {
        var tt = (SeqType)t;
        return new SeqType(CloneType(tt.Arg));
      } else if (t is MultiSetType) {
        var tt = (MultiSetType)t;
        return new MultiSetType(CloneType(tt.Arg));
      } else if (t is MapType) {
        var tt = (MapType)t;
        return new MapType(tt.Finite, CloneType(tt.Domain), CloneType(tt.Range));
      } else if (t is ArrowType) {
        var tt = (ArrowType)t;
        return new ArrowType((ArrowTypeDecl) tt.ResolvedClass, tt.Args.ConvertAll(CloneType), CloneType(tt.Result));
      } else if (t is UserDefinedType) {
        var tt = (UserDefinedType)t;
#if TEST_TYPE_SYNONYM_TRANSPARENCY
        if (tt.Name == "type#synonym#transparency#test") {
          // time to drop the synonym wrapper
          var syn = (TypeSynonymDecl)tt.ResolvedClass;
          return CloneType(syn.Rhs);
        }
#endif
        return new UserDefinedType(tt.Name, tt.ResolvedClass, tt.TypeArgs.ConvertAll(CloneType)) {
          ResolvedParam = tt.ResolvedParam
        };
      } else {
        Contract.Assert(false);  // unexpected type
        return null;  // to please compiler
      }
    }

    public Formal CloneFormal(Formal formal) {
      Formal f = new Formal(formal.Name, CloneType(formal.Type), formal.InParam, formal.IsOld);
      //if (f.Type is UserDefinedType && formal.Type is UserDefinedType)
      //    ((UserDefinedType)f.Type).ResolvedClass = ((UserDefinedType)(formal.Type)).ResolvedClass;
      return f;
    }

    public virtual BoundVar CloneBoundVar(BoundVar bv) {
      return new BoundVar(bv.Name, CloneType(bv.Type));
    }

    public VT CloneIVariable<VT>(VT v) where VT: IVariable {
      var iv = (IVariable)v;
      if (iv is Formal) {
        iv = CloneFormal((Formal)iv);
      } else if (iv is BoundVar) {
        iv = CloneBoundVar((BoundVar)iv);
      } else if (iv is LocalVariable) {
        var local = (LocalVariable)iv;
        iv = new LocalVariable(local.Name, CloneType(local.Type));
      } else {
        Contract.Assume(false);  // unexpected IVariable
        iv = null;  // please compiler
      }
      return (VT)iv;
    }

    public Specification<Expression> CloneSpecExpr(Specification<Expression> spec) {
      var ee = spec.Expressions == null ? null : spec.Expressions.ConvertAll(CloneExpr);
      return new Specification<Expression>(ee, CloneAttributes(spec.Attributes));
    }

    public Specification<FrameExpression> CloneSpecFrameExpr(Specification<FrameExpression> frame) {
      var ee = frame.Expressions == null ? null : frame.Expressions.ConvertAll(CloneFrameExpr);
      return new Specification<FrameExpression>(ee, CloneAttributes(frame.Attributes));
    }

    public FrameExpression CloneFrameExpr(FrameExpression frame) {
      return new FrameExpression(CloneExpr(frame.E), frame.FieldName);
    }
    public Attributes CloneAttributes(Attributes attrs) {
      if (attrs == null) {
        return null;
      } else if (attrs.Name.StartsWith("_")) {
        // skip this attribute, since it would have been produced during resolution
        return CloneAttributes(attrs.Prev);
      } else if (attrs is UserSuppliedAttributes) {
        var usa = (UserSuppliedAttributes)attrs;
        return new UserSuppliedAttributes(usa.Name, attrs.Args.ConvertAll(CloneExpr), CloneAttributes(attrs.Prev));
      } else {
        return new Attributes(attrs.Name, attrs.Args.ConvertAll(CloneExpr), CloneAttributes(attrs.Prev));
      }
    }

    public MaybeFreeExpression CloneMayBeFreeExpr(MaybeFreeExpression expr) {
      var mfe = new MaybeFreeExpression(CloneExpr(expr.E), expr.IsFree, expr.Label == null ? null : new AssertLabel(expr.Label.Name), CloneAttributes(expr.Attributes));
      mfe.Attributes = CloneAttributes(expr.Attributes);
      return mfe;
    }

    public virtual Expression CloneExpr(Expression expr) {
      if (expr == null) {
        return null;
      } else if (expr is LiteralExpr) {
        var e = (LiteralExpr)expr;
        if (e is StaticReceiverExpr) {
          var ee = (StaticReceiverExpr)e;
          return new StaticReceiverExpr(CloneType(ee.UnresolvedType), ee.IsImplicit);
        } else if (e.Value == null) {
          return new LiteralExpr();
        } else if (e.Value is bool) {
          return new LiteralExpr((bool)e.Value);
        } else if (e is CharLiteralExpr) {
          return new CharLiteralExpr((string)e.Value);
        } else if (e is StringLiteralExpr) {
          var str = (StringLiteralExpr)e;
          return new StringLiteralExpr((string)e.Value, str.IsVerbatim);
        } else if (e.Value is Basetypes.BigDec) {
          return new LiteralExpr((Basetypes.BigDec)e.Value);
        } else {
          return new LiteralExpr((BigInteger)e.Value);
        }

      } else if (expr is ThisExpr) {
        if (expr is ImplicitThisExpr_ConstructorCall) {
          return new ImplicitThisExpr_ConstructorCall();
        } else if (expr is ImplicitThisExpr) {
          return new ImplicitThisExpr();
        } else {
          return new ThisExpr();
        }

      } else if (expr is IdentifierExpr) {
        var e = (IdentifierExpr)expr;
        return new IdentifierExpr(e.Var);

      } else if (expr is DatatypeValue) {
        var e = (DatatypeValue)expr;
        return new DatatypeValue(e.DatatypeName, e.MemberName, e.Arguments.ConvertAll(CloneExpr));

      } else if (expr is DisplayExpression) {
        DisplayExpression e = (DisplayExpression)expr;
        if (expr is SetDisplayExpr) {
          return new SetDisplayExpr(((SetDisplayExpr)expr).Finite, e.Elements.ConvertAll(CloneExpr));
        } else if (expr is MultiSetDisplayExpr) {
          return new MultiSetDisplayExpr(e.Elements.ConvertAll(CloneExpr));
        } else {
          Contract.Assert(expr is SeqDisplayExpr);
          return new SeqDisplayExpr(e.Elements.ConvertAll(CloneExpr));
        }

      } else if (expr is MapDisplayExpr) {
        MapDisplayExpr e = (MapDisplayExpr)expr;
        List<ExpressionPair> pp = new List<ExpressionPair>();
        foreach (ExpressionPair p in e.Elements) {
          pp.Add(new ExpressionPair(CloneExpr(p.A), CloneExpr(p.B)));
        }
        return new MapDisplayExpr(e.Finite, pp);

      } else if (expr is NameSegment) {
        return CloneNameSegment(expr);
      } else if (expr is ExprDotName) {
        var e = (ExprDotName)expr;
        return new ExprDotName(CloneExpr(e.Lhs), e.SuffixName, e.OptTypeArguments == null ? null : e.OptTypeArguments.ConvertAll(CloneType));
      } else if (expr is RevealExpr) {
        var e = (RevealExpr) expr;
        return new RevealExpr(CloneExpr(e.Expr));
      } else if (expr is MemberSelectExpr) {
        var e = (MemberSelectExpr)expr;
        return new MemberSelectExpr(CloneExpr(e.Obj), e.MemberName);

      } else if (expr is SeqSelectExpr) {
        var e = (SeqSelectExpr)expr;
        return new SeqSelectExpr(e.SelectOne, CloneExpr(e.Seq), CloneExpr(e.E0), CloneExpr(e.E1));

      } else if (expr is MultiSelectExpr) {
        var e = (MultiSelectExpr)expr;
        return new MultiSelectExpr(CloneExpr(e.Array), e.Indices.ConvertAll(CloneExpr));

      } else if (expr is SeqUpdateExpr) {
        var e = (SeqUpdateExpr)expr;
        return new SeqUpdateExpr(CloneExpr(e.Seq), CloneExpr(e.Index), CloneExpr(e.Value));

      } else if (expr is FunctionCallExpr) {
        var e = (FunctionCallExpr)expr;
        return new FunctionCallExpr(e.Name, CloneExpr(e.Receiver), e.Args.ConvertAll(CloneExpr));

      } else if (expr is ApplyExpr) {
        var e = (ApplyExpr)expr;
        return new ApplyExpr(CloneExpr(e.Function), e.Args.ConvertAll(CloneExpr));

      } else if (expr is SeqConstructionExpr) {
        var e = (SeqConstructionExpr)expr;
        return new SeqConstructionExpr(CloneExpr(e.N), CloneExpr(e.Initializer));

      } else if (expr is MultiSetFormingExpr) {
        var e = (MultiSetFormingExpr)expr;
        return new MultiSetFormingExpr(CloneExpr(e.E));

      } else if (expr is OldExpr) {
        var e = (OldExpr)expr;
        return new OldExpr(CloneExpr(e.E), e.At);

      } else if (expr is UnchangedExpr) {
        var e = (UnchangedExpr)expr;
        return new UnchangedExpr(e.Frame.ConvertAll(CloneFrameExpr), e.At);

      } else if (expr is UnaryOpExpr) {
        var e = (UnaryOpExpr)expr;
        return new UnaryOpExpr(e.Op, CloneExpr(e.E));

      } else if (expr is ConversionExpr) {
        var e = (ConversionExpr)expr;
        return new ConversionExpr(CloneExpr(e.E), CloneType(e.ToType));

      } else if (expr is BinaryExpr) {
        var e = (BinaryExpr)expr;
        return new BinaryExpr(e.Op, CloneExpr(e.E0), CloneExpr(e.E1));

      } else if (expr is TernaryExpr) {
        var e = (TernaryExpr)expr;
        return new TernaryExpr(e.Op, CloneExpr(e.E0), CloneExpr(e.E1), CloneExpr(e.E2));

      } else if (expr is LetExpr) {
        var e = (LetExpr)expr;
        return new LetExpr(e.LHSs.ConvertAll(CloneCasePattern), e.RHSs.ConvertAll(CloneExpr), CloneExpr(e.Body), e.Exact, e.Attributes);

      } else if (expr is NamedExpr) {
        var e = (NamedExpr)expr;
        return new NamedExpr(e.Name, CloneExpr(e.Body));
      } else if (expr is ComprehensionExpr) {
        var e = (ComprehensionExpr)expr;
        var bvs = e.BoundVars.ConvertAll(CloneBoundVar);
        var range = CloneExpr(e.Range);
        var term = CloneExpr(e.Term);
        if (e is QuantifierExpr) {
          var q = (QuantifierExpr)e;
          var tvs = q.TypeArgs.ConvertAll(CloneTypeParam);
          if (e is ForallExpr) {
            return new ForallExpr(tvs, bvs, range, term, CloneAttributes(e.Attributes));
          } else if (e is ExistsExpr) {
            return new ExistsExpr(tvs, bvs, range, term, CloneAttributes(e.Attributes));
          } else {
            Contract.Assert(false); throw new cce.UnreachableException();  // unexpected quantifier expression
          }
        } else if (e is MapComprehension) {
          var mc = (MapComprehension)e;
          return new MapComprehension(mc.Finite, bvs, range, mc.TermLeft == null ? null : CloneExpr(mc.TermLeft), term, CloneAttributes(e.Attributes));
        } else if (e is LambdaExpr) {
          var l = (LambdaExpr)e;
          return new LambdaExpr(bvs, range, l.Reads.ConvertAll(CloneFrameExpr), term);
        } else {
          Contract.Assert(e is SetComprehension);
          var tt = (SetComprehension)e;
          return new SetComprehension(tt.Finite, bvs, range, tt.TermIsImplicit ? null : term, CloneAttributes(e.Attributes));
        }

      } else if (expr is WildcardExpr) {
        return new WildcardExpr();

      } else if (expr is StmtExpr) {
        var e = (StmtExpr)expr;
        return new StmtExpr(CloneStmt(e.S), CloneExpr(e.E));

      } else if (expr is ITEExpr) {
        var e = (ITEExpr)expr;
        return new ITEExpr(e.IsBindingGuard, CloneExpr(e.Test), CloneExpr(e.Thn), CloneExpr(e.Els));

      } else if (expr is MatchExpr) {
        var e = (MatchExpr)expr;
        return new MatchExpr(CloneExpr(e.Source), e.Cases.ConvertAll(CloneMatchCaseExpr), e.UsesOptionalBraces);

      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected expression
      }
    }

    public MatchCaseExpr CloneMatchCaseExpr(MatchCaseExpr c) {
      Contract.Requires(c != null);
      if (c.Arguments != null) {
        Contract.Assert(c.CasePatterns == null);
        return new MatchCaseExpr(c.Id, c.Arguments.ConvertAll(CloneBoundVar), CloneExpr(c.Body));
      } else {
        Contract.Assert(c.Arguments == null);
        Contract.Assert(c.CasePatterns != null);
        return new MatchCaseExpr(c.Id, c.CasePatterns.ConvertAll(CloneCasePattern), CloneExpr(c.Body));
      }
    }

    public virtual CasePattern<VT> CloneCasePattern<VT>(CasePattern<VT> pat) where VT: IVariable {
      Contract.Requires(pat != null);
      if (pat.Var != null) {
        return new CasePattern<VT>(CloneIVariable(pat.Var));
      } else if (pat.Arguments == null) {
        return new CasePattern<VT>(pat.Id, null);
      } else {
        return new CasePattern<VT>(pat.Id, pat.Arguments.ConvertAll(CloneCasePattern));
      }
    }

    public virtual NameSegment CloneNameSegment(Expression expr) {
      var e = (NameSegment)expr;
      return new NameSegment(e.Name, e.OptTypeArguments == null ? null : e.OptTypeArguments.ConvertAll(CloneType));
    }

    public virtual AssignmentRhs CloneRHS(AssignmentRhs rhs) {
      AssignmentRhs c;
      if (rhs is ExprRhs) {
        var r = (ExprRhs)rhs;
        c = new ExprRhs(CloneExpr(r.Expr));
      } else if (rhs is HavocRhs) {
        c = new HavocRhs();
      } else {
        var r = (TypeRhs)rhs;
        if (r.ArrayDimensions != null) {
          if (r.InitDisplay != null) {
            Contract.Assert(r.ArrayDimensions.Count == 1);
            c = new TypeRhs(CloneType(r.EType), CloneExpr(r.ArrayDimensions[0]), r.InitDisplay.ConvertAll(CloneExpr));
          } else {
            c = new TypeRhs(CloneType(r.EType), r.ArrayDimensions.ConvertAll(CloneExpr), CloneExpr(r.ElementInit));
          }
        } else if (r.Arguments == null) {
          c = new TypeRhs(CloneType(r.EType));
        } else {
          c = new TypeRhs(CloneType(r.Path), r.Arguments.ConvertAll(CloneExpr), false);
        }
      }
      c.Attributes = CloneAttributes(rhs.Attributes);
      return c;
    }

    public virtual BlockStmt CloneBlockStmt(BlockStmt stmt) {
      Contract.Requires(!(stmt is DividedBlockStmt));  // for blocks that may be DividedBlockStmt's, call CloneDividedBlockStmt instead
      if (stmt == null) {
        return null;
      } else {
        return new BlockStmt(stmt.Body.ConvertAll(CloneStmt));
      }
    }

    public virtual DividedBlockStmt CloneDividedBlockStmt(DividedBlockStmt stmt) {
      if (stmt == null) {
        return null;
      } else {
        return new DividedBlockStmt(stmt.BodyInit.ConvertAll(CloneStmt), stmt.BodyProper.ConvertAll(CloneStmt));
      }
    }

    public virtual Statement CloneStmt(Statement stmt) {
      if (stmt == null) {
        return null;
      }

      Statement r;
      if (stmt is AssertStmt) {
        var s = (AssertStmt)stmt;
        r = new AssertStmt(CloneExpr(s.Expr), CloneBlockStmt(s.Proof), s.Label == null ? null : new AssertLabel(s.Label.Name), null);

      } else if (stmt is AssumeStmt) {
        var s = (AssumeStmt)stmt;
        r = new AssumeStmt(CloneExpr(s.Expr), null);

      } else if (stmt is PrintStmt) {
        var s = (PrintStmt)stmt;
        r = new PrintStmt(s.Args.ConvertAll(CloneExpr));

      } else if (stmt is RevealStmt) {
        var s = (RevealStmt)stmt;
        r = new RevealStmt(s.Exprs.ConvertAll(CloneExpr));

      } else if (stmt is BreakStmt) {
        var s = (BreakStmt)stmt;
        if (s.TargetLabel != null) {
          r = new BreakStmt(s.TargetLabel);
        } else {
          r = new BreakStmt(s.BreakCount);
        }

      } else if (stmt is ReturnStmt) {
        var s = (ReturnStmt)stmt;
        r = new ReturnStmt(s.rhss == null ? null : s.rhss.ConvertAll(CloneRHS));

      } else if (stmt is YieldStmt) {
        var s = (YieldStmt)stmt;
        r = new YieldStmt(s.rhss == null ? null : s.rhss.ConvertAll(CloneRHS));

      } else if (stmt is AssignStmt) {
        var s = (AssignStmt)stmt;
        r = new AssignStmt(CloneExpr(s.Lhs), CloneRHS(s.Rhs));

      } else if (stmt is DividedBlockStmt) {
        r = CloneDividedBlockStmt((DividedBlockStmt)stmt);

      } else if (stmt is BlockStmt) {
        r = CloneBlockStmt((BlockStmt)stmt);

      } else if (stmt is IfStmt) {
        var s = (IfStmt)stmt;
        r = new IfStmt(s.IsBindingGuard, CloneExpr(s.Guard), CloneBlockStmt(s.Thn), CloneStmt(s.Els));

      } else if (stmt is AlternativeStmt) {
        var s = (AlternativeStmt)stmt;
        r = new AlternativeStmt(s.Alternatives.ConvertAll(CloneGuardedAlternative), s.UsesOptionalBraces);

      } else if (stmt is WhileStmt) {
        var s = (WhileStmt)stmt;
        r = new WhileStmt(CloneExpr(s.Guard), s.Invariants.ConvertAll(CloneMayBeFreeExpr), CloneSpecExpr(s.Decreases), CloneSpecFrameExpr(s.Mod), CloneBlockStmt(s.Body));

      } else if (stmt is AlternativeLoopStmt) {
        var s = (AlternativeLoopStmt)stmt;
        r = new AlternativeLoopStmt(s.Invariants.ConvertAll(CloneMayBeFreeExpr), CloneSpecExpr(s.Decreases), CloneSpecFrameExpr(s.Mod), s.Alternatives.ConvertAll(CloneGuardedAlternative), s.UsesOptionalBraces);

      } else if (stmt is ForallStmt) {
        var s = (ForallStmt)stmt;
        r = new ForallStmt(s.BoundVars.ConvertAll(CloneBoundVar), null, CloneExpr(s.Range), s.Ens.ConvertAll(CloneMayBeFreeExpr), CloneStmt(s.Body));
      } else if (stmt is CalcStmt) {
        var s = (CalcStmt)stmt;
        // calc statements have the unusual property that the last line is duplicated.  If that is the case (which
        // we expect it to be here), we share the clone of that line as well.
        var lineCount = s.Lines.Count;
        var lines = new List<Expression>(lineCount);
        for (int i = 0; i < lineCount; i++) {
          lines.Add(i == lineCount - 1 && 2 <= lineCount && s.Lines[i] == s.Lines[i - 1] ? lines[i - 1] : CloneExpr(s.Lines[i]));
        }
        Contract.Assert(lines.Count == lineCount);
        r = new CalcStmt(CloneCalcOp(s.UserSuppliedOp), lines, s.Hints.ConvertAll(CloneBlockStmt), s.StepOps.ConvertAll(CloneCalcOp), CloneAttributes(s.Attributes));

      } else if (stmt is MatchStmt) {
        var s = (MatchStmt)stmt;
        r = new MatchStmt(CloneExpr(s.Source), s.Cases.ConvertAll(CloneMatchCaseStmt), s.UsesOptionalBraces);

      } else if (stmt is AssignSuchThatStmt) {
        var s = (AssignSuchThatStmt)stmt;
        r = new AssignSuchThatStmt(s.Lhss.ConvertAll(CloneExpr), CloneExpr(s.Expr), s.HasAssume, null);

      } else if (stmt is UpdateStmt) {
        var s = (UpdateStmt)stmt;
        r = new UpdateStmt(s.Lhss.ConvertAll(CloneExpr), s.Rhss.ConvertAll(CloneRHS), s.CanMutateKnownState);

      } else if (stmt is VarDeclStmt) {
        var s = (VarDeclStmt)stmt;
        var lhss = s.Locals.ConvertAll(c => new LocalVariable(c.Name, CloneType(c.Type)));
        r = new VarDeclStmt(lhss, (ConcreteUpdateStatement)CloneStmt(s.Update));

      } else if (stmt is LetStmt) {
        var s = (LetStmt) stmt;
        r = new LetStmt(CloneCasePattern(s.LHS), CloneExpr(s.RHS));

      } else if (stmt is ModifyStmt) {
        var s = (ModifyStmt)stmt;
        var mod = CloneSpecFrameExpr(s.Mod);
        var body = s.Body == null ? null : CloneBlockStmt(s.Body);
        r = new ModifyStmt(mod.Expressions, mod.Attributes, body);

      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected statement
      }

      // add labels to the cloned statement
      AddStmtLabels(r, stmt.Labels);
      r.Attributes = CloneAttributes(stmt.Attributes);

      return r;
    }

    public MatchCaseStmt CloneMatchCaseStmt(MatchCaseStmt c) {
      Contract.Requires(c != null);
      if (c.Arguments != null) {
        Contract.Assert(c.CasePatterns == null);
        return new MatchCaseStmt(c.Id, c.Arguments.ConvertAll(CloneBoundVar), c.Body.ConvertAll(CloneStmt));
      } else {
        Contract.Assert(c.Arguments == null);
        Contract.Assert(c.CasePatterns != null);
        return new MatchCaseStmt(c.Id, c.CasePatterns.ConvertAll(CloneCasePattern), c.Body.ConvertAll(CloneStmt));
      }
    }

    public CalcStmt.CalcOp CloneCalcOp(CalcStmt.CalcOp op) {
      if (op == null) {
        return null;
      } else if (op is CalcStmt.BinaryCalcOp) {
        return new CalcStmt.BinaryCalcOp(((CalcStmt.BinaryCalcOp) op).Op);
      } else if (op is CalcStmt.TernaryCalcOp) {
        return new CalcStmt.TernaryCalcOp(CloneExpr(((CalcStmt.TernaryCalcOp) op).Index));
      } else {
        Contract.Assert(false);
        throw new cce.UnreachableException();
      }
    }

    public void AddStmtLabels(Statement s, LList<Label> node) {
      if (node != null) {
        AddStmtLabels(s, node.Next);
        if (node.Data.Name == null) {
          // this indicates an implicit-target break statement that has been resolved; don't add it
        } else {
          s.Labels = new LList<Label>(new Label(node.Data.Name), s.Labels);
        }
      }
    }

    public GuardedAlternative CloneGuardedAlternative(GuardedAlternative alt) {
      return new GuardedAlternative(alt.IsBindingGuard, CloneExpr(alt.Guard), alt.Body.ConvertAll(CloneStmt));
    }

    public virtual Field CloneField(Field f) {
      Contract.Requires(f != null);
      if (f is ConstantField) {
        var c = (ConstantField)f;
        return new ConstantField(c.Name, CloneExpr(c.Rhs), c.IsStatic, CloneType(c.Type), CloneAttributes(c.Attributes));
      } else if (f is SpecialField) {
        // We don't expect a SpecialField to ever be cloned. However, it can happen for malformed programs, for example if
        // an iterator in a refined module is replaced by a class in the refining module.
        var s = (SpecialField)f;
        return new SpecialField(s.Name, s.SpecialId, s.IdParam, s.IsMutable, s.IsUserMutable, CloneType(s.Type), CloneAttributes(s.Attributes));
      } else {
        return new Field(f.Name, f.HasStaticKeyword, f.IsMutable, f.IsUserMutable, CloneType(f.Type), CloneAttributes(f.Attributes));
      }
    }

    public virtual Function CloneFunction(Function f, string newName = null) {
      var tps = f.TypeArgs.ConvertAll(CloneTypeParam);
      var formals = f.Formals.ConvertAll(CloneFormal);
      var req = f.Req.ConvertAll(CloneMayBeFreeExpr);
      var reads = f.Reads.ConvertAll(CloneFrameExpr);
      var decreases = CloneSpecExpr(f.Decreases);
      var ens = f.Ens.ConvertAll(CloneMayBeFreeExpr);
      Expression body;
      body = CloneExpr(f.Body);

      if (newName == null) {
        newName = f.Name;
      }

      if (f is Predicate) {
        return new Predicate(newName, f.HasStaticKeyword, f.IsProtected, tps, formals,
          body, Predicate.BodyOriginKind.OriginalOrInherited, CloneAttributes(f.Attributes));
      } else {
        return new Function(newName, f.HasStaticKeyword, f.IsProtected, tps, formals, f.Result == null ? null : CloneFormal(f.Result), CloneType(f.ResultType),
          body, CloneAttributes(f.Attributes));
      }
    }

    public virtual Method CloneMethod(Method m) {
      Contract.Requires(m != null);

      var tps = m.TypeArgs.ConvertAll(CloneTypeParam);
      var ins = m.Ins.ConvertAll(CloneFormal);

      BlockStmt body = CloneMethodBody(m);

      if (m is Constructor) {
        return new Constructor(m.Name, tps, ins,
          (DividedBlockStmt)body, CloneAttributes(m.Attributes), false);
      } else {
        return new Method(m.Name, m.HasStaticKeyword, tps, ins, m.Outs.ConvertAll(CloneFormal),
          body, CloneAttributes(m.Attributes), false);
      }
    }

    public virtual BlockStmt CloneMethodBody(Method m) {
      if (m.Body is DividedBlockStmt) {
        return CloneDividedBlockStmt((DividedBlockStmt)m.Body);
      } else {
        return CloneBlockStmt(m.Body);
      }
    }
  }


  /// <summary>
  /// This cloner copies the origin module signatures to their cloned declarations
  /// </summary>
  class DeepModuleSignatureCloner : Cloner {
    public override TopLevelDecl CloneDeclaration(TopLevelDecl d, ModuleDefinition m) {
      var dd = base.CloneDeclaration(d, m);
      if (d is ModuleDecl) {
        ((ModuleDecl)dd).Signature = ((ModuleDecl)d).Signature;
        if (d is ModuleFacadeDecl) {
          var sourcefacade = (ModuleFacadeDecl)d;

          ((ModuleFacadeDecl)dd).OriginalSignature = sourcefacade.OriginalSignature;
          if (sourcefacade.Root != null) {
            ((ModuleFacadeDecl)dd).Root = (ModuleDecl)CloneDeclaration(sourcefacade.Root, m);
          }
        } else if (d is AliasModuleDecl) {
          var sourcealias = (AliasModuleDecl)d;

          if (sourcealias.Root != null) {
            ((AliasModuleDecl)dd).Root = (ModuleDecl)CloneDeclaration(sourcealias.Root, m);
          }
        }
      }
      return dd;
    }
  }


  class ScopeCloner : DeepModuleSignatureCloner {
    private VisibilityScope scope = null;

    private Dictionary<Declaration, Declaration> reverseMap = new Dictionary<Declaration, Declaration>();

    private HashSet<AliasModuleDecl> extraProvides = new HashSet<AliasModuleDecl>();

    private bool isInvisibleClone(Declaration d) {
      Contract.Assert(reverseMap.ContainsKey(d));
      return !reverseMap[d].IsVisibleInScope(scope);
    }

    public ScopeCloner(VisibilityScope scope) {
      this.scope = scope;
    }

    private bool RevealedInScope(Declaration d) {
      return d.IsRevealedInScope(scope);
    }

    private bool VisibleInScope(Declaration d) {
      return d.IsVisibleInScope(scope);
    }

    public override ModuleDefinition CloneModuleDefinition(ModuleDefinition m, string name) {
      var basem = base.CloneModuleDefinition(m, name);


      //Merge signatures for imports which point to the same module
      //This makes the consistency check understand that the same element
      //may be referred to via different qualifications.
      var sigmap = new Dictionary<ModuleDefinition, ModuleSignature>();
      var declmap = new Dictionary<ModuleDefinition, List<AliasModuleDecl>>();
      var vismap = new Dictionary<ModuleDefinition, VisibilityScope>();

      foreach (var top in basem.TopLevelDecls) {
        var import = reverseMap[top] as AliasModuleDecl;
        if (import == null)
          continue;

        var def = import.Signature.ModuleDef;
        if (!declmap.ContainsKey(def)) {
          declmap.Add(def, new List<AliasModuleDecl>());
          sigmap.Add(def, new ModuleSignature());
          vismap.Add(def, new VisibilityScope());
        }


        sigmap[def] = ModuleSignature.Merge(sigmap[def], import.Signature);
        sigmap[def].ModuleDef = def;
        declmap[def].Add((AliasModuleDecl)top);
        if (VisibleInScope(import)) {
          vismap[def].Augment(import.Signature.VisibilityScope);
        }

      }

      foreach (var decls in declmap) {
        sigmap[decls.Key].VisibilityScope = vismap[decls.Key];
        foreach (var decl in decls.Value) {
          decl.Signature = sigmap[decls.Key];
        }
      }

      basem.TopLevelDecls.RemoveAll(t => t is AliasModuleDecl ?
        vismap[((AliasModuleDecl)t).Signature.ModuleDef].IsEmpty() : isInvisibleClone(t));

      basem.TopLevelDecls.FindAll(t => t is ClassDecl).
        ForEach(t => ((ClassDecl)t).Members.RemoveAll(isInvisibleClone));

      return basem;
    }

    public override TopLevelDecl CloneDeclaration(TopLevelDecl d, ModuleDefinition m) {

      var based = base.CloneDeclaration(d, m);

      if (d is RevealableTypeDecl && !RevealedInScope(d)) {
        var dd = (RevealableTypeDecl)d;
        var tps = d.TypeArgs.ConvertAll(CloneTypeParam);
        var characteristics = TypeParameter.GetExplicitCharacteristics(d);
        based = new OpaqueTypeDecl(d.Name, m, characteristics, tps, CloneAttributes(d.Attributes));
      }

      reverseMap.Add(based, d);

      return based;

    }

    public override Field CloneField(Field f) {
      var cf = f as ConstantField;
      if (cf != null && cf.Rhs != null && !RevealedInScope(f)) {
        // We erase the RHS value. While we do that, we must also make sure the declaration does have a type, so instead of
        // cloning cf.Type, we assume "f" has been resolved and clone cf.Type.NormalizeExpandKeepConstraints().
        return new ConstantField(cf.Name, null, cf.IsStatic, CloneType(cf.Type.NormalizeExpandKeepConstraints()), CloneAttributes(cf.Attributes));
      }
      return base.CloneField(f);
    }

    public override Function CloneFunction(Function f, string newName = null) {
      var basef = base.CloneFunction(f, newName);
      if (!RevealedInScope(f)) {
        basef.Body = null;
      }
      return basef;
    }

    public override Method CloneMethod(Method m) {
      var basem = base.CloneMethod(m);
      basem.Body = null; //exports never reveal method bodies
      return basem;
    }

    public override MemberDecl CloneMember(MemberDecl member) {
      var basem = base.CloneMember(member);
      reverseMap.Add(basem, member);
      return basem;
    }

  }

  /// <summary>
  /// This cloner is used during the creation of a module signature for a method facade.
  /// It does not clone method bodies, and it copies module signatures.
  /// </summary>
  class ClonerButDropMethodBodies : DeepModuleSignatureCloner
  {
    public ClonerButDropMethodBodies()
      : base() {
    }

    public override BlockStmt CloneBlockStmt(BlockStmt stmt) {
      return null;
    }
  }

  class AbstractSignatureCloner : ScopeCloner {

    public AbstractSignatureCloner(VisibilityScope scope)
      : base(scope) {
    }

    public override ModuleDefinition CloneModuleDefinition(ModuleDefinition m, string name) {
      var basem = base.CloneModuleDefinition(m, name);
      basem.TopLevelDecls.RemoveAll(t => t is ModuleExportDecl);
      return basem;
    }

    public override BlockStmt CloneBlockStmt(BlockStmt stmt) {
      return null;
    }
  }
}
