#define TI_DEBUG_PRINT
//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System;
using System.Text;
using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Numerics;
using System.Linq;
using Microsoft.Boogie;
using System.Diagnostics;

namespace Microsoft.Dafny.Core {
  public class Program {
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(FullName != null);
      Contract.Invariant(DefaultModule != null);
    }

    public readonly string FullName;
    public Dictionary<ModuleDefinition,ModuleSignature> ModuleSigs; // filled in during resolution.
                                                     // Resolution essentially flattens the module hierarchy, for
                                                     // purposes of translation and compilation.
    public List<ModuleDefinition> CompileModules; // filled in during resolution.
                                                  // Contains the definitions to be used for compilation.

    public readonly ModuleDecl DefaultModule;
    public readonly ModuleDefinition DefaultModuleDef;
    public readonly BuiltIns BuiltIns;
    public readonly ErrorReporter reporter;

    public Program(string name, [Captured] ModuleDecl module, [Captured] BuiltIns builtIns, ErrorReporter reporter) {
      Contract.Requires(name != null);
      Contract.Requires(module != null);
      Contract.Requires(module is LiteralModuleDecl);
      Contract.Requires(reporter != null);
      FullName = name;
      DefaultModule = module;
      DefaultModuleDef = (DefaultModuleDecl)((LiteralModuleDecl)module).ModuleDef;
      BuiltIns = builtIns;
      this.reporter = reporter;
      ModuleSigs = new Dictionary<ModuleDefinition,ModuleSignature>();
      CompileModules = new List<ModuleDefinition>();
    }

    //Set appropriate visibilty before presenting module
    public IEnumerable<ModuleDefinition> Modules() {

      foreach (var msig in ModuleSigs) {
        Type.PushScope(msig.Value.VisibilityScope);
        yield return msig.Key;
        Type.PopScope(msig.Value.VisibilityScope);
      }

    }

    public IEnumerable<ModuleDefinition> RawModules() {
      return ModuleSigs.Keys;
    }

    public string Name
    {
      get
      {
        try
        {
          return System.IO.Path.GetFileName(FullName);
        }
        catch (ArgumentException)
        {
          return FullName;
        }
      }
    }
  }


  public class Include : IComparable
  {
    public readonly string includerFilename;
    public readonly string includedFilename;
    public readonly string includedFullPath;
    public bool ErrorReported;

    public Include(string includer, string theFilename, string fullPath) {
      this.includerFilename = includer;
      this.includedFilename = theFilename;
      this.includedFullPath = fullPath;
      this.ErrorReported = false;
    }

    public int CompareTo(object obj) {
      var i = obj as Include;
      if (i != null) {
        return this.includedFullPath.CompareTo(i.includedFullPath);
      } else {
        throw new NotImplementedException();
      }
    }
  }

  public class BuiltIns
  {
    public readonly ModuleDefinition SystemModule;
    readonly Dictionary<int, ClassDecl> arrayTypeDecls = new Dictionary<int, ClassDecl>();
    public readonly Dictionary<int, ArrowTypeDecl> ArrowTypeDecls = new Dictionary<int, ArrowTypeDecl>();
    public readonly Dictionary<int, SubsetTypeDecl> PartialArrowTypeDecls = new Dictionary<int, SubsetTypeDecl>();  // same keys as arrowTypeDecl
    public readonly Dictionary<int, SubsetTypeDecl> TotalArrowTypeDecls = new Dictionary<int, SubsetTypeDecl>();  // same keys as arrowTypeDecl
    readonly Dictionary<int, TupleTypeDecl> tupleTypeDecls = new Dictionary<int, TupleTypeDecl>();
    public readonly ISet<int> Bitwidths = new HashSet<int>();
    public SpecialField ORDINAL_Offset;  // filled in by the resolver, used by the translator

    public readonly SubsetTypeDecl NatDecl;
    public UserDefinedType Nat() { return new UserDefinedType("nat", NatDecl, new List<Type>()); }
    public readonly TraitDecl ObjectDecl;
    public UserDefinedType ObjectQ() {
      Contract.Assume(ObjectDecl != null);
      return new UserDefinedType("object?", ObjectDecl, null);
    }

    public BuiltIns(Program program) {
      SystemModule = new ModuleDefinition("_System", program, new List<string>(), false, false, false, null, null, null, true);
      SystemModule.Height = -1;  // the system module doesn't get a height assigned later, so we set it here to something below everything else
      // create type synonym 'string'
      var str = new TypeSynonymDecl("string", new TypeParameter.TypeParameterCharacteristics(TypeParameter.EqualitySupportValue.InferredRequired, false, false), new List<TypeParameter>(), SystemModule, new SeqType(new CharType()), null);
      SystemModule.TopLevelDecls.Add(str);
      // create subset type 'nat'
      var ax = AxiomAttribute();
      NatDecl = new SubsetTypeDecl("nat", new TypeParameter.TypeParameterCharacteristics(TypeParameter.EqualitySupportValue.InferredRequired, false, false), new List<TypeParameter>(), SystemModule, Type.Int, SubsetTypeDecl.WKind.None, null, ax);
      SystemModule.TopLevelDecls.Add(NatDecl);
      // create trait 'object'
      ObjectDecl = new TraitDecl("object", SystemModule, new List<TypeParameter>(), new List<MemberDecl>(), DontCompile());
      SystemModule.TopLevelDecls.Add(ObjectDecl);
      // add one-dimensional arrays, since they may arise during type checking
      // Arrays of other dimensions may be added during parsing as the parser detects the need for these
      UserDefinedType tmp = ArrayType(1, Type.Int, true);
      // Arrow types of other dimensions may be added during parsing as the parser detects the need for these.  For the 0-arity
      // arrow type, the resolver adds a Valid() predicate for iterators, whose corresponding arrow type is conveniently created here.
      CreateArrowTypeDecl(0);
      // Note, in addition to these types, the _System module contains tuple types.  These tuple types are added to SystemModule
      // by the parser as the parser detects the need for these.
    }

    private Attributes DontCompile() {
      var flse = Expression.CreateBoolLiteral(false);
      return new Attributes("compile", new List<Expression>() { flse }, null);
    }

    public static Attributes AxiomAttribute() {
      return new Attributes("axiom", new List<Expression>(), null);
    }

    public UserDefinedType ArrayType(int dims, Type arg, bool allowCreationOfNewClass) {
      Contract.Requires(1 <= dims);
      Contract.Requires(arg != null);
      return ArrayType(dims, new List<Type>() { arg }, allowCreationOfNewClass);
    }
    public UserDefinedType ArrayType(int dims, List<Type> optTypeArgs, bool allowCreationOfNewClass, bool useClassNameType = false) {
      Contract.Requires(1 <= dims);
      Contract.Requires(optTypeArgs == null || optTypeArgs.Count > 0);  // ideally, it is 1, but more will generate an error later, and null means it will be filled in automatically
      Contract.Ensures(Contract.Result<UserDefinedType>() != null);

      var arrayName = ArrayClassName(dims);
      if (useClassNameType) {
        arrayName = arrayName + "?";
      }
      ClassDecl arrayClass;
      if (!arrayTypeDecls.ContainsKey(dims)) {
        arrayClass = new ArrayClassDecl(dims, SystemModule, DontCompile());
        for (int d = 0; d < dims; d++) {
          string name = dims == 1 ? "Length" : "Length" + d;
          Field len = new SpecialField(name, SpecialField.ID.ArrayLength, dims == 1 ? null : (object)d, false, false, false, Type.Int, null);
          len.EnclosingClass = arrayClass;  // resolve here
          arrayClass.Members.Add(len);
        }
        arrayTypeDecls.Add(dims, arrayClass);
        SystemModule.TopLevelDecls.Add(arrayClass);
      } else {
        arrayClass = arrayTypeDecls[dims];
      }
      UserDefinedType udt = new UserDefinedType(arrayName, arrayClass, optTypeArgs);
      return udt;
    }

    public static string ArrayClassName(int dims) {
      Contract.Requires(1 <= dims);
      if (dims == 1) {
        return "array";
      } else {
        return "array" + dims;
      }
    }

    /// <summary>
    /// Idempotently add an arrow type with arity 'arity' to the system module, and along
    /// with this arrow type, the two built-in subset types based on the arrow type.
    /// </summary>
    public void CreateArrowTypeDecl(int arity) {
      Contract.Requires(0 <= arity);
      if (!ArrowTypeDecls.ContainsKey(arity)) {
        var tps = Util.Map(Enumerable.Range(0, arity + 1), x => x < arity ?
          new TypeParameter("T" + x, TypeParameter.TPVarianceSyntax.Contravariance) :
          new TypeParameter("R", TypeParameter.TPVarianceSyntax.Covariant_Strict));
        var tys = tps.ConvertAll(tp => (Type)(new UserDefinedType(tp)));
        var args = Util.Map(Enumerable.Range(0, arity), i => new Formal("x" + i, tys[i], true, false));
        var argExprs = args.ConvertAll(a =>
              (Expression)new IdentifierExpr(a));
        var arrowDecl = new ArrowTypeDecl(tps, SystemModule, DontCompile());
        ArrowTypeDecls.Add(arity, arrowDecl);
        SystemModule.TopLevelDecls.Add(arrowDecl);

        // declaration of read-effect-free arrow-type, aka heap-independent arrow-type, aka partial-function arrow-type
        tps = Util.Map(Enumerable.Range(0, arity + 1), x => x < arity ?
          new TypeParameter("T" + x, TypeParameter.TPVarianceSyntax.Contravariance) :
          new TypeParameter("R", TypeParameter.TPVarianceSyntax.Covariant_Strict));
        tys = tps.ConvertAll(tp => (Type)(new UserDefinedType(tp)));
        var partialArrow = new SubsetTypeDecl(ArrowType.PartialArrowTypeName(arity),
          new TypeParameter.TypeParameterCharacteristics(false), tps, SystemModule,
          new ArrowType(arrowDecl, tys), SubsetTypeDecl.WKind.Special, null, DontCompile());
        PartialArrowTypeDecls.Add(arity, partialArrow);
        SystemModule.TopLevelDecls.Add(partialArrow);

        // declaration of total arrow-type

        tps = Util.Map(Enumerable.Range(0, arity + 1), x => x < arity ?
          new TypeParameter("T" + x, TypeParameter.TPVarianceSyntax.Contravariance) :
          new TypeParameter("R", TypeParameter.TPVarianceSyntax.Covariant_Strict));
        tys = tps.ConvertAll(tp => (Type)(new UserDefinedType(tp)));
        var totalArrow = new SubsetTypeDecl(ArrowType.TotalArrowTypeName(arity),
          new TypeParameter.TypeParameterCharacteristics(false), tps, SystemModule,
          new UserDefinedType(partialArrow.Name, partialArrow, tys), SubsetTypeDecl.WKind.Special, null, DontCompile());
        TotalArrowTypeDecls.Add(arity, totalArrow);
        SystemModule.TopLevelDecls.Add(totalArrow);
      }
    }

    public TupleTypeDecl TupleType(int dims, bool allowCreationOfNewType) {
      Contract.Requires(0 <= dims);
      Contract.Ensures(Contract.Result<TupleTypeDecl>() != null);

      TupleTypeDecl tt;
      if (!tupleTypeDecls.TryGetValue(dims, out tt)) {
        Contract.Assume(allowCreationOfNewType);  // the parser should ensure that all needed tuple types exist by the time of resolution
        if (dims == 2) {
          // tuple#2 is already defined in DafnyRuntime.cs
          tt = new TupleTypeDecl(dims, SystemModule, DontCompile());
        } else {
          tt = new TupleTypeDecl(dims, SystemModule, null);
        }
        tupleTypeDecls.Add(dims, tt);
        SystemModule.TopLevelDecls.Add(tt);
      }
      return tt;
    }

    public static string TupleTypeName(int dims) {
      Contract.Requires(0 <= dims);
      return "_tuple#" + dims;
    }
    public static bool IsTupleTypeName(string s) {
      Contract.Requires(s != null);
      return s.StartsWith("_tuple#");
    }
    public const string TupleTypeCtorNamePrefix = "_#Make";  // the printer wants this name prefix to be uniquely recognizable
  }

  /// <summary>
  /// A class implementing this interface is one that can carry attributes.
  /// </summary>
  public interface IAttributeBearingDeclaration
  {
  }

  public class Attributes {
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Name != null);
      Contract.Invariant(cce.NonNullElements(Args));
    }

    public string Name;
    /*Frozen*/
    public readonly List<Expression> Args;
    public readonly Attributes Prev;

    public Attributes(string name, [Captured] List<Expression> args, Attributes prev) {
      Contract.Requires(name != null);
      Contract.Requires(cce.NonNullElements(args));
      Name = name;
      Args = args;
      Prev = prev;
    }

    public static IEnumerable<Expression> SubExpressions(Attributes attrs) {
      return attrs.AsEnumerable().SelectMany(aa => aa.Args);
    }

    public static bool Contains(Attributes attrs, string nm) {
      Contract.Requires(nm != null);
      return attrs.AsEnumerable().Any(aa => aa.Name == nm);
    }

    /// <summary>
    /// Returns true if "nm" is a specified attribute.  If it is, then:
    /// - if the attribute is {:nm true}, then value==true
    /// - if the attribute is {:nm false}, then value==false
    /// - if the attribute is anything else, then value returns as whatever it was passed in as.
    /// </summary>
    [Pure]
    public static bool ContainsBool(Attributes attrs, string nm, ref bool value) {
      Contract.Requires(nm != null);
      foreach (var attr in attrs.AsEnumerable()) {
        if (attr.Name == nm) {
          if (attr.Args.Count == 1) {
            var arg = attr.Args[0] as LiteralExpr;
            if (arg != null && arg.Value is bool) {
              value = (bool)arg.Value;
            }
          }
          return true;
        }
      }
      return false;
    }

    /// <summary>
    /// Checks whether a Boolean attribute has been set on the declaration itself,
    /// the enclosing class, or any enclosing module.  Settings closer to the declaration
    /// override those further away.
    /// </summary>
    public static bool ContainsBoolAtAnyLevel(MemberDecl decl, string attribName) {
      bool setting = true;
      if (Attributes.ContainsBool(decl.Attributes, attribName, ref setting)) {
        return setting;
      }

      if (Attributes.ContainsBool(decl.EnclosingClass.Attributes, attribName, ref setting)) {
        return setting;
      }

      // Check the entire stack of modules
      var mod = decl.EnclosingClass.Module;
      while (mod != null) {
        if (Attributes.ContainsBool(mod.Attributes, attribName, ref setting)) {
          return setting;
        }
        mod = mod.Module;
      }

      return false;
    }

    /// <summary>
    /// Returns list of expressions if "nm" is a specified attribute:
    /// - if the attribute is {:nm e1,...,en}, then returns (e1,...,en)
    /// Otherwise, returns null.
    /// </summary>
    public static List<Expression> FindExpressions(Attributes attrs, string nm) {
      Contract.Requires(nm != null);
      foreach (var attr in attrs.AsEnumerable()) {
        if (attr.Name == nm) {
          return attr.Args;
        }
      }
      return null;
    }


    /// <summary>
    /// Same as FindExpressions, but returns all matches
    /// </summary>
    public static List<List<Expression>> FindAllExpressions(Attributes attrs, string nm) {
      Contract.Requires(nm != null);
      List<List<Expression>> ret = null;
      for (; attrs != null; attrs = attrs.Prev) {
        if (attrs.Name == nm) {
          ret = ret ?? new List<List<Expression>>();   // Avoid allocating the list in the common case where we don't find nm
          ret.Add(attrs.Args);
        }
      }
      return ret;
    }

    /// <summary>
    /// Returns true if "nm" is a specified attribute whose arguments match the "allowed" parameter.
    /// - if "nm" is not found in attrs, return false and leave value unmodified.  Otherwise,
    /// - if "allowed" contains Empty and the Args contains zero elements, return true and leave value unmodified.  Otherwise,
    /// - if "allowed" contains Bool and Args contains one bool literal, return true and set value to the bool literal.  Otherwise,
    /// - if "allowed" contains Int and Args contains one BigInteger literal, return true and set value to the BigInteger literal.  Otherwise,
    /// - if "allowed" contains String and Args contains one string literal, return true and set value to the string literal.  Otherwise,
    /// - if "allowed" contains Expression and Args contains one element, return true and set value to the one element (of type Expression).  Otherwise,
    /// - return false, leave value unmodified, and call reporter with an error string.
    /// </summary>
    public enum MatchingValueOption { Empty, Bool, Int, String, Expression }
    public static bool ContainsMatchingValue(Attributes attrs, string nm, ref object value, IEnumerable<MatchingValueOption> allowed, Action<string> reporter) {
      Contract.Requires(nm != null);
      Contract.Requires(allowed != null);
      Contract.Requires(reporter != null);
      List<Expression> args = FindExpressions(attrs, nm);
      if (args == null) {
        return false;
      } else if (args.Count == 0) {
        if (allowed.Contains(MatchingValueOption.Empty)) {
          return true;
        } else {
          reporter("Attribute " + nm + " requires one argument");
          return false;
        }
      } else if (args.Count == 1) {
        Expression arg = args[0];
        StringLiteralExpr stringLiteral = arg as StringLiteralExpr;
        LiteralExpr literal = arg as LiteralExpr;
        if (literal != null && literal.Value is bool && allowed.Contains(MatchingValueOption.Bool)) {
          value = literal.Value;
          return true;
        } else if (literal != null && literal.Value is BigInteger && allowed.Contains(MatchingValueOption.Int)) {
          value = literal.Value;
          return true;
        } else if (stringLiteral != null && stringLiteral.Value is string && allowed.Contains(MatchingValueOption.String)) {
          value = stringLiteral.Value;
          return true;
        } else if (allowed.Contains(MatchingValueOption.Expression)) {
          value = arg;
          return true;
        } else {
          reporter("Attribute " + nm + " expects an argument in one of the following categories: " + String.Join(", ", allowed));
          return false;
        }
      } else {
        reporter("Attribute " + nm + " cannot have more than one argument");
        return false;
      }
    }
  }

  public static class AttributesExtensions {
    /// <summary>
    /// By making this an extension method, it can also be invoked for a null receiver.
    /// </summary>
    public static IEnumerable<Attributes> AsEnumerable(this Attributes attr) {
      while (attr != null) {
        yield return attr;
        attr = attr.Prev;
      }
    }
  }

  public class UserSuppliedAttributes : Attributes
  {
    public bool Recognized;  // set to true to indicate an attribute that is processed by some part of Dafny; this allows it to be colored in the IDE
    public UserSuppliedAttributes(string name, List<Expression> args, Attributes prev)
      : base(name, args, prev) {
      Contract.Requires(args != null);
    }
  }


  public class VisibilityScope {
    private static uint maxScopeID = 0;

    private SortedSet<uint> scopeTokens = new SortedSet<uint>();

    // Only for debugging
    private SortedSet<string> scopeIds = new SortedSet<string>();

    private bool overlaps(SortedSet<uint> set1, SortedSet<uint> set2) {
      if (set1.Count < set2.Count) {
        return set2.Overlaps(set1);
      } else {
        return set1.Overlaps(set2);
      }
    }

    private Dictionary<VisibilityScope, Tuple<int, bool>> cached = new Dictionary<VisibilityScope, Tuple<int, bool>>();

    //By convention, the "null" scope sees all
    public bool VisibleInScope(VisibilityScope other) {
      if (other != null) {
        Tuple<int, bool> result;
        if (cached.TryGetValue(other, out result)) {
          if (result.Item1 == other.scopeTokens.Count()) {
            return result.Item2;
          } else {
            if (result.Item2) {
              return true;
            }
          }
        }
        var isoverlap = overlaps(other.scopeTokens, this.scopeTokens);
        cached[other] = new Tuple<int, bool>(other.scopeTokens.Count(), isoverlap);
        return isoverlap;

      }
      return true;
    }

    [Pure]
    public bool IsEmpty() {
      return scopeTokens.Count == 0;
    }


    //However augmenting with a null scope does nothing
    public void Augment(VisibilityScope other) {
      if (other != null) {
        scopeTokens.UnionWith(other.scopeTokens);
        scopeIds.UnionWith(other.scopeIds);
        cached.Clear();
      }
    }

    public VisibilityScope(bool newScope, string name) {
      scopeTokens.Add(maxScopeID);
      scopeIds.Add(name);
      if (maxScopeID == uint.MaxValue) {
        Contract.Assert(false);
      }
      maxScopeID++;
    }

    public VisibilityScope() {
    }

  }


  // ------------------------------------------------------------------------------------------------------

  public abstract class Type {
    public static readonly BoolType Bool = new BoolType();
    public static readonly CharType Char = new CharType();
    public static readonly IntType Int = new IntType();
    public static readonly RealType Real = new RealType();
    public static readonly BigOrdinalType BigOrdinal = new BigOrdinalType();

    [ThreadStatic]
    private static List<VisibilityScope> scopes = new List<VisibilityScope>();

    [ThreadStatic]
    private static bool scopesEnabled = false;

    public static void PushScope(VisibilityScope scope) {
      scopes.Add(scope);
    }

    public static void ResetScopes() {
      scopes = new List<VisibilityScope>();
      scopesEnabled = false;
    }


    public static void PopScope() {
      Contract.Assert(scopes.Count > 0);
      scopes.RemoveAt(scopes.Count - 1);
    }

    public static void PopScope(VisibilityScope expected) {
      Contract.Assert(scopes.Count > 0);
      Contract.Assert(scopes[scopes.Count - 1] == expected);
      PopScope();
    }

    public static VisibilityScope GetScope() {
      if (scopes.Count > 0 && scopesEnabled) {
        return scopes[scopes.Count - 1];
      }
      return null;
    }

    public static void EnableScopes() {
      Contract.Assert(!scopesEnabled);
      scopesEnabled = true;
    }

    public static void DisableScopes() {
      Contract.Assert(scopesEnabled);
      scopesEnabled = false;
    }


    public static string TypeArgsToString(ModuleDefinition/*?*/ context, List<Type> typeArgs, bool parseAble = false) {
      Contract.Requires(typeArgs == null ||
        (typeArgs.All(ty => ty != null && ty.TypeName(context, parseAble) != null) &&
         (typeArgs.All(ty => ty.TypeName(context, parseAble).StartsWith("_")) ||
          typeArgs.All(ty => !ty.TypeName(context, parseAble).StartsWith("_")))));

      if (typeArgs != null && typeArgs.Count > 0 &&
          (!parseAble || !typeArgs[0].TypeName(context, parseAble).StartsWith("_"))){
        return string.Format("<{0}>",Util.Comma(", ", typeArgs, ty => ty.TypeName(context, parseAble)));
      }
      return "";
    }

    public static string TypeArgsToString(List<Type> typeArgs, bool parseAble = false) {
      return TypeArgsToString(null, typeArgs, parseAble);
    }

    public string TypeArgsToString(ModuleDefinition/*?*/ context, bool parseAble = false) {
      return Type.TypeArgsToString(context, this.TypeArgs, parseAble);
    }

    // Type arguments to the type
    public List<Type> TypeArgs = new List<Type>();

    [Pure]
    public abstract string TypeName(ModuleDefinition/*?*/ context, bool parseAble = false);
    [Pure]
    public override string ToString() {
      return TypeName(null, false);
    }

    /// <summary>
    /// Return the type that "this" stands for, following type synonyms.
    /// </summary>
    [Pure]
    public Type NormalizeExpand(bool keepConstraints = false) {
      Contract.Ensures(Contract.Result<Type>() != null);
      Type type = this;
      while (true) {

        var scope = Type.GetScope();
        var rtd = type.AsRevealableType;
        if (rtd != null) {
          var udt = (UserDefinedType)type;

          if (!rtd.AsTopLevelDecl.IsVisibleInScope(scope)) {
            Contract.Assert(false);
          }

          if (rtd.IsRevealedInScope(scope)) {
            if (rtd is TypeSynonymDecl && (!(rtd is SubsetTypeDecl) || !keepConstraints)) {
              type = ((TypeSynonymDecl)rtd).RhsWithArgumentIgnoringScope(udt.TypeArgs);
              continue;
            } else {
              return type;
            }
          } else { // type is hidden, no more normalization is possible
            return rtd.SelfSynonym(type.TypeArgs);
          }
        }

        //A hidden type may become visible in another scope
        var isyn = type.AsInternalTypeSynonym;
        if (isyn != null) {
          Contract.Assert(isyn.IsVisibleInScope(scope));
          if (isyn.IsRevealedInScope(scope)) {
            var udt = (UserDefinedType)type;
            type = isyn.RhsWithArgument(udt.TypeArgs);
            continue;
          } else {
            return type;
          }
        }

        return type;
      }
    }

    /// <summary>
    /// Return the type that "this" stands for, getting to the bottom of proxies and following type synonyms, but does
    /// not follow subset types.
    /// </summary>
    [Pure]
    public Type NormalizeExpandKeepConstraints() {
      return NormalizeExpand(true);
    }

    /// <summary>
    /// Returns whether or not "this" and "that" denote the same type, module proxies and type synonyms and subset types.
    /// </summary>
    [Pure]
    public abstract bool Equals(Type that);

    public bool IsBoolType { get { return NormalizeExpand() is BoolType; } }
    public bool IsCharType { get { return NormalizeExpand() is CharType; } }
    public bool IsIntegerType { get { return NormalizeExpand() is IntType; } }
    public bool IsRealType { get { return NormalizeExpand() is RealType; } }
    public bool IsBigOrdinalType { get { return NormalizeExpand() is BigOrdinalType; } }
    public bool IsBitVectorType { get { return AsBitVectorType != null; } }
    public BitvectorType AsBitVectorType { get { return NormalizeExpand() as BitvectorType; } }
    public bool IsNumericBased() {
      var t = NormalizeExpand();
      return t.IsIntegerType || t.IsRealType || t.AsNewtype != null;
    }
    public enum NumericPersuation { Int, Real }
    [Pure]
    public bool IsNumericBased(NumericPersuation p) {
      Type t = this;
      while (true) {
        t = t.NormalizeExpand();
        if (t.IsIntegerType) {
          return p == NumericPersuation.Int;
        } else if (t.IsRealType) {
          return p == NumericPersuation.Real;
        }
        var d = t.AsNewtype;
        if (d == null) {
          return false;
        }
        t = d.BaseType;
      }
    }

    public bool HasFinitePossibleValues {
      get {
        if (IsBoolType || IsCharType || IsRefType) {
          return true;
        }
        var st = AsSetType;
        if (st != null && st.Arg.HasFinitePossibleValues) {
          return true;
        }
        var mt = AsMapType;
        if (mt != null && mt.Domain.HasFinitePossibleValues) {
          return true;
        }
        var dt = AsDatatype;
        if (dt != null && dt.HasFinitePossibleValues) {
          return true;
        }
        return false;
      }
    }

    public bool IsAllocFree {
      get {
        if (IsRefType) {
          return false;
        } else if (IsTypeParameter) {
          return AsTypeParameter.Characteristics.DisallowReferenceTypes;
        } else {
          return TypeArgs.All(ta => ta.IsAllocFree);
        }
      }
    }

    public CollectionType AsCollectionType { get { return NormalizeExpand() as CollectionType; } }
    public SetType AsSetType { get { return NormalizeExpand() as SetType; } }
    public MultiSetType AsMultiSetType { get { return NormalizeExpand() as MultiSetType; } }
    public SeqType AsSeqType { get { return NormalizeExpand() as SeqType; } }
    public MapType AsMapType { get { return NormalizeExpand() as MapType; } }

    public bool IsRefType {
      get {
        var udt = NormalizeExpand() as UserDefinedType;
        return udt != null && udt.ResolvedParam == null && udt.ResolvedClass is ClassDecl
          && !(udt.ResolvedClass is ArrowTypeDecl);
      }
    }
    public bool IsTopLevelTypeWithMembers {
      get {
        return AsTopLevelTypeWithMembers != null;
      }
    }
    public TopLevelDeclWithMembers/*?*/ AsTopLevelTypeWithMembers {
      get {
        var udt = NormalizeExpand() as UserDefinedType;
        return udt != null && udt.ResolvedParam == null ? udt.ResolvedClass as TopLevelDeclWithMembers : null;
      }
    }
    /// <summary>
    /// Returns "true" if the type represents the "object?".
    /// </summary>
    public bool IsObjectQ {
      get {
        var udt = NormalizeExpandKeepConstraints() as UserDefinedType;
        return udt != null && udt.ResolvedClass is ClassDecl && ((ClassDecl)udt.ResolvedClass).Name == "object";
      }
    }
    /// <summary>
    /// Returns "true" if the type is a non-null type or any subset type thereof.
    /// </summary>
    public bool IsNonNullRefType {
      get {
        return AsNonNullRefType != null;
      }
    }
    /// <summary>
    /// If the type is a non-null type or any subset type thereof, return the UserDefinedType whose
    /// .ResolvedClass value is a NonNullTypeDecl.
    /// Otherwise, return "null".
    /// </summary>
    public UserDefinedType AsNonNullRefType {
      get {
        var t = this;
        while (true) {
          var udt = t.NormalizeExpandKeepConstraints() as UserDefinedType;
          if (udt == null) {
            return null;
          }
          if (udt.ResolvedClass is NonNullTypeDecl) {
            return udt;
          }
          var sst = udt.ResolvedClass as SubsetTypeDecl;
          if (sst != null) {
            t = sst.RhsWithArgument(udt.TypeArgs);  // continue the search up the chain of subset types
          } else {
            return null;
          }
        }
      }
    }
    public bool IsTraitType {
      get {
        var udt = NormalizeExpand() as UserDefinedType;
        return udt != null && udt.ResolvedParam == null && udt.ResolvedClass is TraitDecl;
      }
    }
    public bool IsArrayType {
      get {
        return AsArrayType != null;
      }
    }
    public ArrayClassDecl/*?*/ AsArrayType {
      get {
        var t = NormalizeExpand();
        var udt = UserDefinedType.DenotesClass(t);
        return udt == null ? null : udt.ResolvedClass as ArrayClassDecl;
      }
    }
    /// <summary>
    /// Returns "true" if the type is one of the 3 built-in arrow types.
    /// </summary>
    public bool IsBuiltinArrowType {
      get {
        // don't expand synonyms or strip off constraints
        if (this is ArrowType) {
          return true;
        }
        var udt = this as UserDefinedType;
        return udt != null && (ArrowType.IsPartialArrowTypeName(udt.Name) || ArrowType.IsTotalArrowTypeName(udt.Name));
      }
    }
    /// <summary>
    /// Returns "true" if the type is a partial arrow or any subset type thereof.
    /// </summary>
    public bool IsArrowTypeWithoutReadEffects {
      get {
        var t = this;
        while (true) {
          var udt = t.NormalizeExpandKeepConstraints() as UserDefinedType;
          if (udt == null) {
            return false;
          } else if (ArrowType.IsPartialArrowTypeName(udt.Name)) {
            return true;
          }
          var sst = udt.ResolvedClass as SubsetTypeDecl;
          if (sst != null) {
            t = sst.RhsWithArgument(udt.TypeArgs);  // continue the search up the chain of subset types
          } else {
            return false;
          }
        }
      }
    }
    /// <summary>
    /// Returns "true" if the type is a total arrow or any subset type thereof.
    /// </summary>
    public bool IsArrowTypeWithoutPreconditions {
      get {
        var t = this;
        while (true) {
          var udt = t.NormalizeExpandKeepConstraints() as UserDefinedType;
          if (udt == null) {
            return false;
          } else if (ArrowType.IsTotalArrowTypeName(udt.Name)) {
            return true;
          }
          var sst = udt.ResolvedClass as SubsetTypeDecl;
          if (sst != null) {
            t = sst.RhsWithArgument(udt.TypeArgs);  // continue the search up the chain of subset types
          } else {
            return false;
          }
        }
      }
    }
    public bool IsArrowType {
      get { return AsArrowType != null; }
    }
    public ArrowType AsArrowType {
      get {
        var t = NormalizeExpand();
        return t as ArrowType;
      }
    }
    public bool IsMapType {
      get {
        var t = NormalizeExpand() as MapType;
        return t != null && t.Finite;
      }
    }

    public bool IsIMapType {
      get {
        var t = NormalizeExpand() as MapType;
        return t != null && !t.Finite;
      }
    }
    public bool IsISetType {
      get {
        var t = NormalizeExpand() as SetType;
        return t != null && !t.Finite;
      }
    }
    public NewtypeDecl AsNewtype {
      get {
        var udt = NormalizeExpand() as UserDefinedType;
        return udt == null ? null : udt.ResolvedClass as NewtypeDecl;
      }
    }
    public TypeSynonymDecl AsTypeSynonym {
      get {
        var udt = this as UserDefinedType;  // note, it is important to use 'this' here, not 'this.NormalizeExpand()'
        if (udt == null) {
          return null;
        } else {
          return udt.ResolvedClass as TypeSynonymDecl;
        }
      }
    }
    public InternalTypeSynonymDecl AsInternalTypeSynonym {
      get {
        var udt = this as UserDefinedType;  // note, it is important to use 'this' here, not 'this.NormalizeExpand()'
        if (udt == null) {
          return null;
        } else {
          return udt.ResolvedClass as InternalTypeSynonymDecl;
        }
      }
    }
    public RedirectingTypeDecl AsRedirectingType {
      get {
        var udt = this as UserDefinedType;  // Note, it is important to use 'this' here, not 'this.NormalizeExpand()'.  This property getter is intended to be used during resolution, or with care thereafter.
        if (udt == null) {
          return null;
        } else {
          return (RedirectingTypeDecl)(udt.ResolvedClass as TypeSynonymDecl) ?? udt.ResolvedClass as NewtypeDecl;
        }
      }
    }
    public RevealableTypeDecl AsRevealableType {
      get {
        var udt = this as UserDefinedType;
        if (udt == null) {
          return null;
        } else {
          return (udt.ResolvedClass as RevealableTypeDecl);
        }
      }
    }
    public bool IsRevealableType {
      get { return AsRevealableType != null; }
    }
    public bool IsDatatype {
      get {
        return AsDatatype != null;
      }
    }
    public DatatypeDecl AsDatatype {
      get {
        var udt = NormalizeExpand() as UserDefinedType;
        if (udt == null) {
          return null;
        } else {
          return udt.ResolvedClass as DatatypeDecl;
        }
      }
    }
    public bool IsIndDatatype {
      get {
        return AsIndDatatype != null;
      }
    }
    public IndDatatypeDecl AsIndDatatype {
      get {
        var udt = NormalizeExpand() as UserDefinedType;
        if (udt == null) {
          return null;
        } else {
          return udt.ResolvedClass as IndDatatypeDecl;
        }
      }
    }
    public bool IsCoDatatype {
      get {
        return AsCoDatatype != null;
      }
    }
    public CoDatatypeDecl AsCoDatatype {
      get {
        var udt = NormalizeExpand() as UserDefinedType;
        if (udt == null) {
          return null;
        } else {
          return udt.ResolvedClass as CoDatatypeDecl;
        }
      }
    }
    public bool InvolvesCoDatatype {
      get {
        return IsCoDatatype;  // TODO: should really check structure of the type recursively
      }
    }
    public bool IsTypeParameter {
      get {
        return AsTypeParameter != null;
      }
    }
    public bool IsInternalTypeSynonym {
      get { return AsInternalTypeSynonym != null; }
    }
    public TypeParameter AsTypeParameter {
      get {
        var ct = NormalizeExpandKeepConstraints() as UserDefinedType;
        return ct == null ? null : ct.ResolvedParam;
      }
    }
    public bool IsOpaqueType {
      get {
        var udt = this as UserDefinedType;  // note, it is important not to use 'this.NormalizeExpand()' here
        return udt != null && udt.ResolvedClass is OpaqueTypeDecl;
      }
    }
    public virtual bool SupportsEquality {
      get {
        return true;
      }
    }
    public virtual bool MayInvolveReferences {
      get {
        return false;
      }
    }

    /// <summary>
    /// Returns true if it is known how to meaningfully compare the type's inhabitants.
    /// </summary>
    public bool IsOrdered {
      get {
        var ct = NormalizeExpand();
        return !ct.IsTypeParameter && !ct.IsInternalTypeSynonym && !ct.IsCoDatatype && !ct.IsArrowType && !ct.IsIMapType && !ct.IsISetType;
      }
    }

    /// <summary>
    /// Returns "true" iff "sub" is a subtype of "super".
    /// Expects that neither "super" nor "sub" is an unresolved proxy.
    /// </summary>
    public static bool IsSupertype(Type super, Type sub) {
      Contract.Requires(super != null);
      Contract.Requires(sub != null);
      if (!IsHeadSupertypeOf(super, sub)) {
        return false;
      }
      super = super.NormalizeExpand();
      sub = sub.NormalizeExpand();
      var polarities = GetPolarities(super);
      Contract.Assert(super.IsTraitType ? polarities.Count == 0 : polarities.Count == super.TypeArgs.Count && polarities.Count == sub.TypeArgs.Count);
      if (super.IsTraitType) {
        return true;
      }
      var allGood = true;
      for (int i = 0; allGood && i < polarities.Count; i++) {
        switch (polarities[i]) {
          case TypeParameter.TPVariance.Co:
            allGood = IsSupertype(super.TypeArgs[i], sub.TypeArgs[i]);
            break;
          case TypeParameter.TPVariance.Contra:
            allGood = IsSupertype(sub.TypeArgs[i], super.TypeArgs[i]);
            break;
          case TypeParameter.TPVariance.Non:
          default:  // "default" shouldn't ever happen
            allGood = Equal_Improved(super.TypeArgs[i], sub.TypeArgs[i]);
            break;
        }
      }
      return allGood;
    }

    /// <summary>
    /// Expects that "type" has already been normalized.
    /// </summary>
    public static List<TypeParameter.TPVariance> GetPolarities(Type type) {
      Contract.Requires(type != null);
      if (type is BasicType || type is ArtificialType) {
        // there are no type parameters
        return new List<TypeParameter.TPVariance>();
      } else if (type is MapType) {
        return new List<TypeParameter.TPVariance> { TypeParameter.TPVariance.Co, TypeParameter.TPVariance.Co };
      } else if (type is CollectionType) {
        return new List<TypeParameter.TPVariance> { TypeParameter.TPVariance.Co };
      } else {
        var udf = (UserDefinedType)type;
        if (udf.TypeArgs.Count == 0) {
          return new List<TypeParameter.TPVariance>();
        }
        // look up the declaration of the formal type parameters
        var cl = udf.ResolvedClass;
        return cl.TypeArgs.ConvertAll(tp => tp.Variance);
      }
    }

    public static bool FromSameHead_Subtype(Type t, Type u, BuiltIns builtIns, out Type a, out Type b) {
      Contract.Requires(t != null);
      Contract.Requires(u != null);
      Contract.Requires(builtIns != null);
      if (FromSameHead(t, u, out a, out b)) {
        return true;
      }
      t = t.NormalizeExpand();
      u = u.NormalizeExpand();
      if (t.IsRefType && u.IsRefType) {
        if (t.IsObjectQ) {
          a = b = t;
          return true;
        } else if (u.IsObjectQ) {
          a = b = u;
          return true;
        }
        var tt = ((UserDefinedType)t).ResolvedClass as ClassDecl;
        var uu = ((UserDefinedType)u).ResolvedClass as ClassDecl;
        if (uu.DerivesFrom(tt)) {
          a = b = t;
          return true;
        } else if (tt.DerivesFrom(uu)) {
          a = b = u;
          return true;
        }
      }
      return false;
    }

    public static bool FromSameHead(Type t, Type u, out Type a, out Type b) {
      a = t;
      b = u;
      var towerA = GetTowerOfSubsetTypes(a);
      var towerB = GetTowerOfSubsetTypes(b);
      for (var n = Math.Min(towerA.Count, towerB.Count); 0 <= --n;) {
        a = towerA[n];
        b = towerB[n];
        if (SameHead(a, b)) {
          return true;
        }
      }
      return false;
    }

    /// <summary>
    /// Returns true if t and u have the same head type.
    /// It is assumed that t and u have been normalized and expanded by the caller, according
    /// to its purposes.
    /// </summary>
    public static bool SameHead(Type t, Type u) {
      Contract.Requires(t != null);
      Contract.Requires(u != null);
      if (t.TypeArgs.Count == 0) {
        return Equal_Improved(t, u);
      } else if (t is SetType) {
        return u is SetType && t.IsISetType == u.IsISetType;
      } else if (t is SeqType) {
        return u is SeqType;
      } else if (t is MultiSetType) {
        return u is MultiSetType;
      } else if (t is MapType) {
        return u is MapType && t.IsIMapType == u.IsIMapType;
      } else {
        var udtT = (UserDefinedType)t;
        var udtU = u as UserDefinedType;
        return udtU != null && udtT.ResolvedClass == udtU.ResolvedClass;
      }
    }

    /// <summary>
    /// Returns "true" iff the head symbols of "sub" can be a subtype of the head symbol of "super".
    /// Expects that neither "super" nor "sub" is an unresolved proxy type (but their type arguments are
    /// allowed to be, since this method does not inspect the type arguments).
    /// </summary>
    public static bool IsHeadSupertypeOf(Type super, Type sub) {
      Contract.Requires(super != null);
      Contract.Requires(sub != null);
      super = super.NormalizeExpandKeepConstraints();  // expand type synonyms
      var origSub = sub;
      sub = sub.NormalizeExpand();  // expand type synonyms AND constraints
      if (super is BoolType) {
        return sub is BoolType;
      } else if (super is CharType) {
        return sub is CharType;
      } else if (super is IntType) {
        return sub is IntType;
      } else if (super is RealType) {
        return sub is RealType;
      } else if (super is BitvectorType) {
        var bitvectorSuper = (BitvectorType)super;
        var bitvectorSub = sub as BitvectorType;
        return bitvectorSub != null && bitvectorSuper.Width == bitvectorSub.Width;
      } else if (super is IntVarietiesSupertype) {
        while (sub.AsNewtype != null) {
          sub = sub.AsNewtype.BaseType.NormalizeExpand();
        }
        return sub.IsIntegerType || sub is BitvectorType || sub is BigOrdinalType;
      } else if (super is RealVarietiesSupertype) {
        while (sub.AsNewtype != null) {
          sub = sub.AsNewtype.BaseType.NormalizeExpand();
        }
        return sub is RealType;
      } else if (super is BigOrdinalType) {
        return sub is BigOrdinalType;
      } else if (super is SetType) {
        return sub is SetType && (super.IsISetType || !sub.IsISetType);
      } else if (super is SeqType) {
        return sub is SeqType;
      } else if (super is MultiSetType) {
        return sub is MultiSetType;
      } else if (super is MapType) {
        return sub is MapType && (super.IsIMapType || !sub.IsIMapType);
      } else if (super is ArrowType) {
        var asuper = (ArrowType)super;
        var asub = sub as ArrowType;
        return asub != null && asuper.Arity == asub.Arity;
      } else if (super.IsObjectQ) {
        var clSub = sub as UserDefinedType;
        return sub.IsObjectQ || (clSub != null && clSub.ResolvedClass is ClassDecl);
      } else if (super is UserDefinedType) {
        var udtSuper = (UserDefinedType)super;
        if (udtSuper.ResolvedParam != null) {
          return udtSuper.ResolvedParam == sub.AsTypeParameter;
        } else {
          Contract.Assert(udtSuper.ResolvedClass != null);
          sub = origSub;  // get back to the starting point
          while (true) {
            sub = sub.NormalizeExpandKeepConstraints();  // skip past proxies and type synonyms
            var udtSub = sub as UserDefinedType;
            if (udtSub == null) {
              return false;
            } else if (udtSuper.ResolvedClass == udtSub.ResolvedClass) {
              return true;
            } else if (udtSub.ResolvedClass is SubsetTypeDecl) {
              sub = ((SubsetTypeDecl)udtSub.ResolvedClass).RhsWithArgument(udtSub.TypeArgs);
              if (udtSub.ResolvedClass is NonNullTypeDecl && udtSuper.ResolvedClass is NonNullTypeDecl) {
                // move "super" up the base-type chain, as was done with "sub", because non-nullness is essentially a co-variant type constructor
                var possiblyNullSuper = ((SubsetTypeDecl)udtSuper.ResolvedClass).RhsWithArgument(udtSuper.TypeArgs);
                udtSuper = (UserDefinedType)possiblyNullSuper;  // applying .RhsWithArgument to a NonNullTypeDecl should always yield a UserDefinedType
                if (udtSuper.IsObjectQ) {
                  return true;
                }
              }
            } else if (udtSub.ResolvedClass is ClassDecl) {
              var cl = (ClassDecl)udtSub.ResolvedClass;
              return cl.DerivesFrom(udtSuper.ResolvedClass);
            } else {
              return false;
            }
          }
        }
      } else {
        Contract.Assert(false);  // unexpected kind of type
        return true;  // to please the compiler
      }
    }

    /// <summary>
    /// Returns "true" iff "a" and "b" denote the same type, expanding type synonyms (but treating types with
    /// constraints as being separate types).
    /// Expects that neither "a" nor "b" is or contains an unresolved proxy type.
    /// </summary>
    public static bool Equal_Improved(Type a, Type b) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      a = a.NormalizeExpandKeepConstraints();  // expand type synonyms
      b = b.NormalizeExpandKeepConstraints();  // expand type synonyms
      if (a is BoolType) {
        return b is BoolType;
      } else if (a is CharType) {
        return b is CharType;
      } else if (a is IntType) {
        return b is IntType;
      } else if (a is RealType) {
        return b is RealType;
      } else if (a is BitvectorType) {
        var bitvectorSuper = (BitvectorType)a;
        var bitvectorSub = b as BitvectorType;
        return bitvectorSub != null && bitvectorSuper.Width == bitvectorSub.Width;
      } else if (a is BigOrdinalType) {
        return b is BigOrdinalType;
      } else if (a is SetType) {
        return b is SetType && Equal_Improved(a.TypeArgs[0], b.TypeArgs[0]) && (a.IsISetType == b.IsISetType);
      } else if (a is SeqType) {
        return b is SeqType && Equal_Improved(a.TypeArgs[0], b.TypeArgs[0]);
      } else if (a is MultiSetType) {
        return b is MultiSetType && Equal_Improved(a.TypeArgs[0], b.TypeArgs[0]);
      } else if (a is MapType) {
        return b is MapType && Equal_Improved(a.TypeArgs[0], b.TypeArgs[0]) && Equal_Improved(a.TypeArgs[1], b.TypeArgs[1]) && (a.IsIMapType == b.IsIMapType);
      } else if (a is ArrowType) {
        var asuper = (ArrowType)a;
        var asub = b as ArrowType;
        return asub != null && asuper.Arity == asub.Arity;
      } else if (a is UserDefinedType) {
        var udtA = (UserDefinedType)a;
        if (udtA.ResolvedClass != null) {
          while (true) {
            var udtB = b as UserDefinedType;
            if (udtB == null) {
              return false;
            } else if (udtA.ResolvedClass != udtB.ResolvedClass) {
              return false;
            } else {
              Contract.Assert(udtA.TypeArgs.Count == udtB.TypeArgs.Count);
              for (int i = 0; i < udtA.TypeArgs.Count; i++) {
                if (!Equal_Improved(udtA.TypeArgs[i], udtB.TypeArgs[i])) {
                  return false;
                }
              }
              return true;
            }
          }
        } else {
          Contract.Assert(udtA.ResolvedParam != null);
          Contract.Assert(udtA.TypeArgs.Count == 0);
          return udtA.ResolvedParam == b.AsTypeParameter;
        }
      } else if (a is Resolver_IdentifierExpr.ResolverType_Module) {
        return b is Resolver_IdentifierExpr.ResolverType_Module;
      } else if (a is Resolver_IdentifierExpr.ResolverType_Type) {
        return b is Resolver_IdentifierExpr.ResolverType_Type;
      } else {
        Contract.Assert(false);  // unexpected kind of type
        return true;  // to please the compiler
      }
    }

    /// <summary>
    /// Returns a stack of base types leading to "type".  More precisely, of the tower returned,
    ///     tower[0] == type.NormalizeExpand()
    ///     tower.Last == type.NormalizeExpandKeepConstraints()
    /// In between, for consecutive indices i and i+1:
    ///     tower[i] is the base type (that is, .Rhs) of the subset type tower[i+1]
    /// The tower thus has the property that:
    ///     tower[0] is not a UserDefinedType with .ResolvedClass being a SubsetTypeDecl,
    ///     but all other tower[i] (for i > 0) are.
    /// </summary>
    public static List<Type> GetTowerOfSubsetTypes(Type type) {
      Contract.Requires(type != null);
      type = type.NormalizeExpandKeepConstraints();
      List<Type> tower;
      var udt = type as UserDefinedType;
      if (udt != null && udt.ResolvedClass is SubsetTypeDecl) {
        var sst = (SubsetTypeDecl)udt.ResolvedClass;
        var parent = sst.RhsWithArgument(udt.TypeArgs);
        tower = GetTowerOfSubsetTypes(parent);
      } else {
        tower = new List<Type>();
      }
      tower.Add(type);
      return tower;
    }

    /// <summary>
    /// For each i, computes some combination of a[i] and b[i], according to direction[i].
    /// For a negative direction (Contra), computes Meet(a[i], b[i]), provided this meet exists.
    /// For a zero direction (Inv), uses a[i], provided a[i] and b[i] are equal.
    /// For a positive direction (Co), computes Join(a[i], b[i]), provided this join exists.
    /// Returns null if any operation fails.
    /// </summary>
    public static List<Type> ComputeExtrema(List<TypeParameter.TPVariance> directions, List<Type> a, List<Type> b, BuiltIns builtIns) {
      Contract.Requires(directions != null);
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      Contract.Requires(directions.Count == a.Count);
      Contract.Requires(directions.Count == b.Count);
      Contract.Requires(builtIns != null);
      var n = directions.Count;
      var r = new List<Type>(n);
      for (int i = 0; i < n; i++) {
        if (directions[i] == TypeParameter.TPVariance.Non) {
          if (a[i].Equals(b[i])) {
            r.Add(a[i]);
          } else {
            return null;
          }
        } else {
          var t = directions[i] == TypeParameter.TPVariance.Contra ? Meet(a[i], b[i], builtIns) : Join(a[i], b[i], builtIns);
          if (t == null) {
            return null;
          }
          r.Add(t);
        }
      }
      return r;
    }

    /// <summary>
    /// Does a best-effort to compute the meet of "a" and "b", returning "null" if not successful.
    /// </summary>
    public static Type Meet(Type a, Type b, BuiltIns builtIns) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      Contract.Requires(builtIns != null);
      var j = MeetX(a, b, builtIns);
      if (DafnyOptions.O.TypeInferenceDebug) {
        Console.WriteLine("DEBUG: Meet( {0}, {1} ) = {2}", a, b, j);
      }
      return j;
    }
    public static Type MeetX(Type a, Type b, BuiltIns builtIns) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      Contract.Requires(builtIns != null);

      // Before we do anything else, make a note of whether or not both "a" and "b" are non-null types.
      var abNonNullTypes = a.IsNonNullRefType && b.IsNonNullRefType;

      var towerA = GetTowerOfSubsetTypes(a);
      var towerB = GetTowerOfSubsetTypes(b);
      for (var n = Math.Min(towerA.Count, towerB.Count); 1 <= --n; ) {
        a = towerA[n];
        b = towerB[n];
        var udtA = (UserDefinedType)a;
        var udtB = (UserDefinedType)b;
        if (udtA.ResolvedClass == udtB.ResolvedClass) {
          // We have two subset types with equal heads
          if (a.Equals(b)) {  // optimization for a special case, which applies for example when there are no arguments or when the types happen to be the same
            return a;
          }
          Contract.Assert(a.TypeArgs.Count == b.TypeArgs.Count);
          var directions = udtA.ResolvedClass.TypeArgs.ConvertAll(tp => TypeParameter.Negate(tp.Variance));
          var typeArgs = ComputeExtrema(directions, a.TypeArgs, b.TypeArgs, builtIns);
          if (typeArgs == null) {
            return null;
          }
          return new UserDefinedType(udtA.Name, udtA.ResolvedClass, typeArgs);
        }
      }
      // We exhausted all possibilities of subset types being equal, so use the base-most types.
      a = towerA[0];
      b = towerB[0];

      if (a is IntVarietiesSupertype) {
        return b is IntVarietiesSupertype || b.IsNumericBased(NumericPersuation.Int) || b.IsBigOrdinalType || b.IsBitVectorType ? b : null;
      } else if (b is IntVarietiesSupertype) {
        return a.IsNumericBased(NumericPersuation.Int) || a.IsBigOrdinalType || a.IsBitVectorType ? a : null;
      } else if (a.IsBoolType || a.IsCharType || a.IsBitVectorType || a.IsBigOrdinalType || a.IsTypeParameter || a.IsInternalTypeSynonym) {
        return a.Equals(b) ? a : null;
      } else if (a is RealVarietiesSupertype) {
        return b is RealVarietiesSupertype || b.IsNumericBased(NumericPersuation.Real) ? b : null;
      } else if (b is RealVarietiesSupertype) {
        return a.IsNumericBased(NumericPersuation.Real) ? a : null;
      } else if (a.IsNumericBased()) {
        // Note, for meet, we choose not to step down to IntVarietiesSupertype or RealVarietiesSupertype
        return a.Equals(b) ? a : null;
      } else if (a is SetType) {
        var aa = (SetType)a;
        var bb = b as SetType;
        if (bb == null || aa.Finite != bb.Finite) {
          return null;
        }
        // sets are co-variant in their argument type
        var typeArg = Meet(a.TypeArgs[0], b.TypeArgs[0], builtIns);
        return typeArg == null ? null : new SetType(aa.Finite, typeArg);
      } else if (a is MultiSetType) {
        var aa = (MultiSetType)a;
        var bb = b as MultiSetType;
        if (bb == null) {
          return null;
        }
        // multisets are co-variant in their argument type
        var typeArg = Meet(a.TypeArgs[0], b.TypeArgs[0], builtIns);
        return typeArg == null ? null : new MultiSetType(typeArg);
      } else if (a is SeqType) {
        var aa = (SeqType)a;
        var bb = b as SeqType;
        if (bb == null) {
          return null;
        }
        // sequences are co-variant in their argument type
        var typeArg = Meet(a.TypeArgs[0], b.TypeArgs[0], builtIns);
        return typeArg == null ? null : new SeqType(typeArg);
      } else if (a is MapType) {
        var aa = (MapType)a;
        var bb = b as MapType;
        if (bb == null || aa.Finite != bb.Finite) {
          return null;
        }
        // maps are co-variant in both argument types
        var typeArgDomain = Meet(a.TypeArgs[0], b.TypeArgs[0], builtIns);
        var typeArgRange = Meet(a.TypeArgs[1], b.TypeArgs[1], builtIns);
        return typeArgDomain == null || typeArgRange == null ? null : new MapType(aa.Finite, typeArgDomain, typeArgRange);
      } else if (a.IsDatatype) {
        var aa = a.AsDatatype;
        if (aa != b.AsDatatype) {
          return null;
        }
        if (a.Equals(b)) {  // optimization for a special case, which applies for example when there are no arguments or when the types happen to be the same
          return a;
        }
        Contract.Assert(a.TypeArgs.Count == b.TypeArgs.Count);
        var directions = aa.TypeArgs.ConvertAll(tp => TypeParameter.Negate(tp.Variance));
        var typeArgs = ComputeExtrema(directions, a.TypeArgs, b.TypeArgs, builtIns);
        if (typeArgs == null) {
          return null;
        }
        var udt = (UserDefinedType)a;
        return new UserDefinedType(udt.Name, aa, typeArgs);
      } else if (a.AsArrowType != null) {
        var aa = a.AsArrowType;
        var bb = b.AsArrowType;
        if (bb == null || aa.Arity != bb.Arity) {
          return null;
        }
        int arity = aa.Arity;
        Contract.Assert(a.TypeArgs.Count == arity + 1);
        Contract.Assert(b.TypeArgs.Count == arity + 1);
        Contract.Assert(((ArrowType)a).ResolvedClass == ((ArrowType)b).ResolvedClass);
        var directions = new List<TypeParameter.TPVariance>();
        for (int i = 0; i < arity; i++) {
          directions.Add(TypeParameter.Negate(TypeParameter.TPVariance.Contra));  // arrow types are contra-variant in the argument types, so compute joins of these
        }
        directions.Add(TypeParameter.Negate(TypeParameter.TPVariance.Co));  // arrow types are co-variant in the result type, so compute the meet of these
        var typeArgs = ComputeExtrema(directions, a.TypeArgs, b.TypeArgs, builtIns);
        if (typeArgs == null) {
          return null;
        }
        var arr = (ArrowType)aa;
        return new ArrowType((ArrowTypeDecl)arr.ResolvedClass, typeArgs);
      } else if (b.IsObjectQ) {
        var udtB = (UserDefinedType)b;
        return !a.IsRefType ? null : abNonNullTypes ? UserDefinedType.CreateNonNullType(udtB) : udtB;
      } else if (a.IsObjectQ) {
        var udtA = (UserDefinedType)a;
        return !b.IsRefType ? null : abNonNullTypes ? UserDefinedType.CreateNonNullType(udtA) : udtA;
      } else {
        // "a" is a class, trait, or opaque type
        var aa = ((UserDefinedType)a).ResolvedClass;
        Contract.Assert(aa != null);
        if (!(b is UserDefinedType)) {
          return null;
        }
        var bb = ((UserDefinedType)b).ResolvedClass;
        if (a.Equals(b)) {  // optimization for a special case, which applies for example when there are no arguments or when the types happen to be the same
          return a;
        } else if (aa == bb) {
          Contract.Assert(a.TypeArgs.Count == b.TypeArgs.Count);
          var directions = aa.TypeArgs.ConvertAll(tp => TypeParameter.Negate(tp.Variance));
          var typeArgs = ComputeExtrema(directions, a.TypeArgs, b.TypeArgs, builtIns);
          if (typeArgs == null) {
            return null;
          }
          var udt = (UserDefinedType)a;
          var xx = new UserDefinedType(udt.Name, aa, typeArgs);
          return abNonNullTypes ? UserDefinedType.CreateNonNullType(xx) : xx;
        } else if (aa is ClassDecl && bb is ClassDecl) {
          var A = (ClassDecl)aa;
          var B = (ClassDecl)bb;
          // Here are the assumptions about the type system that the rest of this code depends on:
          Contract.Assert(!(A is TraitDecl) || (A.TypeArgs.Count == 0 && ((TraitDecl)A).TraitsTyp.Count == 0));
          Contract.Assert(!(B is TraitDecl) || (B.TypeArgs.Count == 0 && ((TraitDecl)B).TraitsTyp.Count == 0));
          if (A.DerivesFrom(B)) {
            var udtB = (UserDefinedType)b;
            return abNonNullTypes ? UserDefinedType.CreateNonNullType(udtB) : udtB;
          } else if (B.DerivesFrom(A)) {
            var udtA = (UserDefinedType)a;
            return abNonNullTypes ? UserDefinedType.CreateNonNullType(udtA) : udtA;
          } else if (A is TraitDecl || B is TraitDecl) {
            return abNonNullTypes ? UserDefinedType.CreateNonNullType(builtIns.ObjectQ()) : builtIns.ObjectQ();
          }
          // A and B are classes. They always have object as a common supertype, but they may also both be extending some other
          // trait.  If such a trait is unique, pick it. (Unfortunately, this makes the meet operation not associative.)
          var commonTraits = new List<Type>();
          foreach (var at in A.TraitsTyp) {
            if (B.TraitsTyp.Exists(bt => at.Equals(bt))) {
              commonTraits.Add(at);
            }
          }
          if (commonTraits.Count == 1) {
            var udtTrait = (UserDefinedType)commonTraits[0];  // in a successfully resolved program, we expect all .TraitsTyp to be a UserDefinedType
            Contract.Assert(udtTrait.ResolvedClass is NonNullTypeDecl);  // in fact, we expect it to be the non-null version of the trait type
            return abNonNullTypes ? udtTrait : udtTrait.NormalizeExpand();
          } else {
            // the unfortunate part is when commonTraits.Count > 1 here :(
            return abNonNullTypes ? UserDefinedType.CreateNonNullType(builtIns.ObjectQ()) : builtIns.ObjectQ();
          }
        } else {
          return null;
        }
      }
    }

    /// <summary>
    /// Does a best-effort to compute the join of "a" and "b", returning "null" if not successful.
    /// </summary>
    public static Type Join(Type a, Type b, BuiltIns builtIns) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      Contract.Requires(builtIns != null);
      a = a.NormalizeExpandKeepConstraints();
      b = b.NormalizeExpandKeepConstraints();

      var joinNeedsNonNullConstraint = false;
      Type j;
      if (a is UserDefinedType && ((UserDefinedType)a).ResolvedClass is NonNullTypeDecl) {
        joinNeedsNonNullConstraint = true;
        var nnt = (NonNullTypeDecl)((UserDefinedType)a).ResolvedClass;
        j = JoinX(nnt.RhsWithArgument(a.TypeArgs), b, builtIns);
      } else if (b is UserDefinedType && ((UserDefinedType)b).ResolvedClass is NonNullTypeDecl) {
        joinNeedsNonNullConstraint = true;
        var nnt = (NonNullTypeDecl)((UserDefinedType)b).ResolvedClass;
        j = JoinX(a, nnt.RhsWithArgument(b.TypeArgs), builtIns);
      } else {
        j = JoinX(a, b, builtIns);
      }
      if (j != null && joinNeedsNonNullConstraint && !j.IsNonNullRefType) {
        // try to make j into a non-null type; if that's not possible, then there is no join
        var udt = j as UserDefinedType;
        if (udt != null && udt.ResolvedClass is ClassDecl) {
          // add the non-null constraint back in
          j = UserDefinedType.CreateNonNullType(udt);
        } else {
          // the original a and b have no join
          j = null;
        }
      }
      if (DafnyOptions.O.TypeInferenceDebug) {
        Console.WriteLine("DEBUG: Join( {0}, {1} ) = {2}", a, b, j);
      }
      return j;
    }
    public static Type JoinX(Type a, Type b, BuiltIns builtIns) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      Contract.Requires(builtIns != null);

      var towerA = GetTowerOfSubsetTypes(a);
      var towerB = GetTowerOfSubsetTypes(b);
      if (towerB.Count < towerA.Count) {
      // make A be the shorter tower
        var tmp0 = a; a = b; b = tmp0;
        var tmp1 = towerA; towerA = towerB; towerB = tmp1;
      }
      var n = towerA.Count;
      Contract.Assert(1 <= n);  // guaranteed by GetTowerOfSubsetTypes
      if (towerA.Count < towerB.Count) {
        // B is strictly taller. The join exists only if towerA[n-1] is a supertype of towerB[n-1], and
        // then the join is "b".
        return Type.IsSupertype(towerA[n - 1], towerB[n - 1]) ? b : null;
      }
      Contract.Assert(towerA.Count == towerB.Count);
      a = towerA[n - 1];
      b = towerB[n - 1];
      if (2 <= n) {
        var udtA = (UserDefinedType)a;
        var udtB = (UserDefinedType)b;
        if (udtA.ResolvedClass == udtB.ResolvedClass) {
          // We have two subset types with equal heads
          if (a.Equals(b)) {  // optimization for a special case, which applies for example when there are no arguments or when the types happen to be the same
            return a;
          }
          Contract.Assert(a.TypeArgs.Count == b.TypeArgs.Count);
          var directions = udtA.ResolvedClass.TypeArgs.ConvertAll(tp => tp.Variance);
          var typeArgs = ComputeExtrema(directions, a.TypeArgs, b.TypeArgs, builtIns);
          if (typeArgs == null) {
            return null;
          }
          return new UserDefinedType(udtA.Name, udtA.ResolvedClass, typeArgs);
        } else {
          // The two subset types do not have the same head, so there is no join
          return null;
        }
      }
      Contract.Assert(towerA.Count == 1 && towerB.Count == 1);

      if (a is IntVarietiesSupertype) {
        return b is IntVarietiesSupertype || b.IsNumericBased(NumericPersuation.Int) || b.IsBigOrdinalType || b.IsBitVectorType ? b : null;
      } else if (b is IntVarietiesSupertype) {
        return a.IsNumericBased(NumericPersuation.Int) || a.IsBigOrdinalType || a.IsBitVectorType ? a : null;
      } else if (a.IsBoolType || a.IsCharType || a.IsBigOrdinalType || a.IsTypeParameter || a.IsInternalTypeSynonym) {
        return a.Equals(b) ? a : null;
      } else if (a is RealVarietiesSupertype) {
        return b is RealVarietiesSupertype || b.IsNumericBased(NumericPersuation.Real) ? b : null;
      } else if (b is RealVarietiesSupertype) {
        return a.IsNumericBased(NumericPersuation.Real) ? a : null;
      } else if (a.IsNumericBased()) {
        return a.Equals(b) ? a : null;
      } else if (a is SetType) {
        var aa = (SetType)a;
        var bb = b as SetType;
        if (bb == null || aa.Finite != bb.Finite) {
          return null;
        }
        // sets are co-variant in their argument type
        var typeArg = Join(a.TypeArgs[0], b.TypeArgs[0], builtIns);
        return typeArg == null ? null : new SetType(aa.Finite, typeArg);
      } else if (a is MultiSetType) {
        var aa = (MultiSetType)a;
        var bb = b as MultiSetType;
        if (bb == null) {
          return null;
        }
        // multisets are co-variant in their argument type
        var typeArg = Join(a.TypeArgs[0], b.TypeArgs[0], builtIns);
        return typeArg == null ? null : new MultiSetType(typeArg);
      } else if (a is SeqType) {
        var aa = (SeqType)a;
        var bb = b as SeqType;
        if (bb == null) {
          return null;
        }
        // sequences are co-variant in their argument type
        var typeArg = Join(a.TypeArgs[0], b.TypeArgs[0], builtIns);
        return typeArg == null ? null : new SeqType(typeArg);
      } else if (a is MapType) {
        var aa = (MapType)a;
        var bb = b as MapType;
        if (bb == null || aa.Finite != bb.Finite) {
          return null;
        }
        // maps are co-variant in both argument types
        var typeArgDomain = Join(a.TypeArgs[0], b.TypeArgs[0], builtIns);
        var typeArgRange = Join(a.TypeArgs[1], b.TypeArgs[1], builtIns);
        return typeArgDomain == null || typeArgRange == null ? null : new MapType(aa.Finite, typeArgDomain, typeArgRange);
      } else if (a.IsDatatype) {
        var aa = a.AsDatatype;
        if (aa != b.AsDatatype) {
          return null;
        }
        if (a.Equals(b)) {  // optimization for a special case, which applies for example when there are no arguments or when the types happen to be the same
          return a;
        }
        Contract.Assert(a.TypeArgs.Count == b.TypeArgs.Count);
        var directions = aa.TypeArgs.ConvertAll(tp => tp.Variance);
        var typeArgs = ComputeExtrema(directions, a.TypeArgs, b.TypeArgs, builtIns);
        if (typeArgs == null) {
          return null;
        }
        var udt = (UserDefinedType)a;
        return new UserDefinedType(udt.Name, aa, typeArgs);
      } else if (a.AsArrowType != null) {
        var aa = a.AsArrowType;
        var bb = b.AsArrowType;
        if (bb == null || aa.Arity != bb.Arity) {
          return null;
        }
        int arity = aa.Arity;
        Contract.Assert(a.TypeArgs.Count == arity + 1);
        Contract.Assert(b.TypeArgs.Count == arity + 1);
        Contract.Assert(((ArrowType)a).ResolvedClass == ((ArrowType)b).ResolvedClass);
        var directions = new List<TypeParameter.TPVariance>();
        for (int i = 0; i < arity; i++) {
          directions.Add(TypeParameter.TPVariance.Contra);  // arrow types are contra-variant in the argument types, so compute meets of these
        }
        directions.Add(TypeParameter.TPVariance.Co);  // arrow types are co-variant in the result type, so compute the join of these
        var typeArgs = ComputeExtrema(directions, a.TypeArgs, b.TypeArgs, builtIns);
        if (typeArgs == null) {
          return null;
        }
        var arr = (ArrowType)aa;
        return new ArrowType((ArrowTypeDecl)arr.ResolvedClass, typeArgs);
      } else if (b.IsObjectQ) {
        return a.IsRefType ? a : null;
      } else if (a.IsObjectQ) {
        return b.IsRefType ? b : null;
      } else {
        // "a" is a class, trait, or opaque type
        var aa = ((UserDefinedType)a).ResolvedClass;
        Contract.Assert(aa != null);
        if (!(b is UserDefinedType)) {
          return null;
        }
        var bb = ((UserDefinedType)b).ResolvedClass;
        if (a.Equals(b)) {  // optimization for a special case, which applies for example when there are no arguments or when the types happen to be the same
          return a;
        } else if (aa == bb) {
          Contract.Assert(a.TypeArgs.Count == b.TypeArgs.Count);
          var directions = aa.TypeArgs.ConvertAll(tp => tp.Variance);
          var typeArgs = ComputeExtrema(directions, a.TypeArgs, b.TypeArgs, builtIns);
          if (typeArgs == null) {
            return null;
          }
          var udt = (UserDefinedType)a;
          return new UserDefinedType(udt.Name, aa, typeArgs);
        } else if (aa is ClassDecl && bb is ClassDecl) {
          var A = (ClassDecl)aa;
          var B = (ClassDecl)bb;
          if (A.DerivesFrom(B)) {
            Contract.Assert(B is TraitDecl && b.TypeArgs.Count == 0);
            return a;
          } else if (B.DerivesFrom(A)) {
            Contract.Assert(A is TraitDecl && a.TypeArgs.Count == 0);
            return b;
          } else {
            return null;
          }
        } else {
          return null;
        }
      }
    }

    public void ForeachTypeComponent(Action<Type> action) {
      action(this);
      TypeArgs.ForEach(x => x.ForeachTypeComponent(action));
    }

    public Type Subst(Dictionary<TypeParameter, Type> subst) {
      Type type = null;
      Contract.Requires(type != null);
      Contract.Requires(cce.NonNullDictionaryAndValues(subst));
      Contract.Ensures(Contract.Result<Type>() != null);

      if (type is BasicType) {
        return type;
      } else if (type is SelfType) {
        Type t;
        if (subst.TryGetValue(((SelfType)type).TypeArg, out t)) {
          return cce.NonNull(t);
        } else {
          Contract.Assert(false); throw new cce.UnreachableException();  // unresolved SelfType
        }
      } else if (type is MapType) {
        var t = (MapType)type;
        var dom = t.Domain.Subst(subst);
        var ran = t.Range.Subst(subst);
        if (dom == t.Domain && ran == t.Range) {
          return type;
        } else {
          return new MapType(t.Finite, dom, ran);
        }
      } else if (type is CollectionType) {
        var t = (CollectionType)type;
        var arg = t.Arg.Subst(subst);
        if (arg == t.Arg) {
          return type;
        } else if (type is SetType) {
          var st = (SetType)type;
          return new SetType(st.Finite, arg);
        } else if (type is MultiSetType) {
          return new MultiSetType(arg);
        } else if (type is SeqType) {
          return new SeqType(arg);
        } else {
          Contract.Assert(false); throw new cce.UnreachableException();  // unexpected collection type
        }
      } else if (type is ArrowType) {
        var t = (ArrowType)type;
        var at = new ArrowType((ArrowTypeDecl) t.ResolvedClass, t.Args.ConvertAll(u => u.Subst(subst)), t.Result.Subst(subst));
        return at;
      } else if (type is UserDefinedType) {
        var t = (UserDefinedType)type;
        if (t.ResolvedParam != null) {
          Type s;
          if (subst.TryGetValue(t.ResolvedParam, out s)) {
            Contract.Assert(t.TypeArgs.Count == 0); // what to do?
            return cce.NonNull(s);
          } else {
            if (t.TypeArgs.Count == 0) {
              return type;
            } else {
              // a type parameter with type arguments--must be an opaque type
              var otp = (OpaqueType_AsParameter)t.ResolvedParam;
              var ocl = (OpaqueTypeDecl)t.ResolvedClass;
              return new UserDefinedType(otp, ocl, t.TypeArgs.ConvertAll(u => u.Subst(subst)));
            }
          }
        } else if (t.ResolvedClass != null) {
          List<Type> newArgs = null;  // allocate it lazily
          var resolvedClass = t.ResolvedClass;
          var isArrowType = ArrowType.IsPartialArrowTypeName(resolvedClass.Name) || ArrowType.IsTotalArrowTypeName(resolvedClass.Name);
#if TEST_TYPE_SYNONYM_TRANSPARENCY
          if (resolvedClass is TypeSynonymDecl && resolvedClass.Name == "type#synonym#transparency#test") {
            // Usually, all type parameters mentioned in the definition of a type synonym are also type parameters
            // to the type synonym itself, but in this instrumented testing, that is not so, so we also do a substitution
            // in the .Rhs of the synonym.
            var syn = (TypeSynonymDecl)resolvedClass;
            var r = SubstType(syn.Rhs, subst);
            if (r != syn.Rhs) {
              resolvedClass = new TypeSynonymDecl(syn.Name, syn.TypeArgs, syn.Module, r, null);
              newArgs = new List<Type>();
            }
          }
#endif
          for (int i = 0; i < t.TypeArgs.Count; i++) {
            Type p = t.TypeArgs[i];
            Type s = p.Subst(subst);
            if (s != p && newArgs == null) {
              // lazily construct newArgs
              newArgs = new List<Type>();
              for (int j = 0; j < i; j++) {
                newArgs.Add(t.TypeArgs[j]);
              }
            }
            if (newArgs != null) {
              newArgs.Add(s);
            }
          }
          if (newArgs == null) {
            // there were no substitutions
            return type;
          } else {
            // Note, even if t.NamePath is non-null, we don't care to keep that syntactic part of the expression in what we return here
            return new UserDefinedType(t.Name, resolvedClass, newArgs);
          }
        } else {
          // there's neither a resolved param nor a resolved class, which means the UserDefinedType wasn't
          // properly resolved; just return it
          return type;
        }
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected type
      }
    }
  }

  /// <summary>
  /// An ArtificialType is only used during type checking. It should never be assigned as the type of any expression.
  /// </summary>
  public abstract class ArtificialType : Type
  {
  }
  /// <summary>
  /// The type "IntVarietiesSupertype" is used to denote a decimal-less number type, namely an int-based type
  /// or a bitvector type.
  /// </summary>
  public class IntVarietiesSupertype : ArtificialType
  {
    [Pure]
    public override string TypeName(ModuleDefinition context, bool parseAble) {
      return "int";
    }
    public override bool Equals(Type that) {
      return that is IntVarietiesSupertype;
    }
  }
  public class RealVarietiesSupertype : ArtificialType
  {
    [Pure]
    public override string TypeName(ModuleDefinition context, bool parseAble) {
      return "real";
    }
    public override bool Equals(Type that) {
      return that is RealVarietiesSupertype;
    }
  }

  /// <summary>
  /// A NonProxy type is a fully constrained type.  It may contain members.
  /// </summary>
  public abstract class NonProxyType : Type
  {
  }

  public abstract class BasicType : NonProxyType
  {
  }

  public class BoolType : BasicType {
    [Pure]
    public override string TypeName(ModuleDefinition context, bool parseAble) {
      return "bool";
    }
    public override bool Equals(Type that) {
      return that.IsBoolType;
    }
  }

  public class CharType : BasicType
  {
    [Pure]
    public override string TypeName(ModuleDefinition context, bool parseAble) {
      return "char";
    }
    public override bool Equals(Type that) {
      return that.IsCharType;
    }
  }

  public class IntType : BasicType
  {
    [Pure]
    public override string TypeName(ModuleDefinition context, bool parseAble) {
      return "int";
    }
    public override bool Equals(Type that) {
      return that.IsIntegerType;
    }
  }

  public class RealType : BasicType {
    [Pure]
    public override string TypeName(ModuleDefinition context, bool parseAble) {
      return "real";
    }
    public override bool Equals(Type that) {
      return that.IsRealType;
    }
  }

  public class BigOrdinalType : BasicType
  {
    [Pure]
    public override string TypeName(ModuleDefinition context, bool parseAble) {
      return "ORDINAL";
    }
    public override bool Equals(Type that) {
      return that.IsBigOrdinalType;
    }
  }

  public class BitvectorType : BasicType
  {
    public readonly int Width;
    public readonly NativeType NativeType;
    public BitvectorType(int width)
      : base() {
      Contract.Requires(0 <= width);
      Width = width;
      foreach (var nativeType in Resolver.NativeTypes) {
        if ((nativeType.CompilationTargets & DafnyOptions.O.CompileTarget) != 0 && width <= nativeType.Bitwidth) {
          NativeType = nativeType;
          break;
        }
      }
    }

    [Pure]
    public override string TypeName(ModuleDefinition context, bool parseAble) {
      return "bv" + Width;
    }
    public override bool Equals(Type that) {
      var bv = that.NormalizeExpand() as BitvectorType;
      return bv != null && bv.Width == Width;
    }
  }

  public class SelfType : NonProxyType
  {
    public TypeParameter TypeArg;
    public Type ResolvedType;
    public SelfType() : base() {
      TypeArg = new TypeParameter("selfType", TypeParameter.TPVarianceSyntax.NonVariant_Strict);
    }

    [Pure]
    public override string TypeName(ModuleDefinition context, bool parseAble) {
      return "selftype";
    }
    public override bool Equals(Type that) {
      return that.NormalizeExpand() is SelfType;
    }
  }

  public class ArrowType : UserDefinedType
  {
    public List<Type> Args {
      get { return TypeArgs.GetRange(0, Arity); }
    }

    public Type Result {
      get { return TypeArgs[Arity]; }
    }

    public int Arity {
      get { return TypeArgs.Count - 1; }
    }

    /// <summary>
    /// Constructs and returns a resolved arrow type.
    /// </summary>
    public ArrowType(ArrowTypeDecl atd, List<Type> typeArgsAndResult)
      : base(ArrowTypeName(atd.Arity), atd, typeArgsAndResult) {
      Contract.Requires(atd != null);
      Contract.Requires(typeArgsAndResult != null);
      Contract.Requires(typeArgsAndResult.Count == atd.Arity + 1);
    }
    /// <summary>
    /// Constructs and returns a resolved arrow type.
    /// </summary>
    public ArrowType(ArrowTypeDecl atd, List<Type> typeArgs, Type result)
      : this(atd, Util.Snoc(typeArgs, result)) {
      Contract.Requires(atd != null);
      Contract.Requires(typeArgs!= null);
      Contract.Requires(typeArgs.Count == atd.Arity);
      Contract.Requires(result != null);
    }

    public const string Arrow_FullCompileName = "Func";  // this is the same for all arities

    public static string ArrowTypeName(int arity) {
      return "_#Func" + arity;
    }

    [Pure]
    public static bool IsArrowTypeName(string s) {
      return s.StartsWith("_#Func");
    }

    public static string PartialArrowTypeName(int arity) {
      return "_#PartialFunc" + arity;
    }

    [Pure]
    public static bool IsPartialArrowTypeName(string s) {
      return s.StartsWith("_#PartialFunc");
    }

    public static string TotalArrowTypeName(int arity) {
      return "_#TotalFunc" + arity;
    }

    [Pure]
    public static bool IsTotalArrowTypeName(string s) {
      return s.StartsWith("_#TotalFunc");
    }

    public const string ANY_ARROW = "~>";
    public const string PARTIAL_ARROW = "-->";
    public const string TOTAL_ARROW = "->";

    public override string TypeName(ModuleDefinition context, bool parseAble) {
      return PrettyArrowTypeName(ANY_ARROW, Args, Result, context, parseAble);
    }

    /// <summary>
    /// Pretty prints an arrow type.  If "result" is null, then all arguments, including the result type are expected in "typeArgs".
    /// If "result" is non-null, then only the in-arguments are in "typeArgs".
    /// </summary>
    public static string PrettyArrowTypeName(string arrow, List<Type> typeArgs, Type result, ModuleDefinition context, bool parseAble) {
      Contract.Requires(arrow != null);
      Contract.Requires(typeArgs != null);
      Contract.Requires(result != null || 1 <= typeArgs.Count);

      int arity = result == null ? typeArgs.Count - 1 : typeArgs.Count;
      var domainNeedsParens = false;
      if (arity != 1) {
        // 0 or 2-or-more arguments:  need parentheses
        domainNeedsParens = true;
      } else if (typeArgs[0].IsBuiltinArrowType) {
        // arrows are right associative, so we need parentheses around the domain type
        domainNeedsParens = true;
      } else {
        // if the domain type consists of a single tuple type, then an extra set of parentheses is needed
        // Note, we do NOT call .AsDatatype or .AsIndDatatype here, because those calls will do a NormalizeExpand().  Instead, we do the check manually.
        var udt = typeArgs[0] as UserDefinedType;  // note, we do not NormalizeExpand(), since the TypeName will use any synonym
        if (udt != null && udt.ResolvedClass is TupleTypeDecl) {
          domainNeedsParens = true;
        }
      }
      string s = "";
      if (domainNeedsParens) { s += "("; }
      s += Util.Comma(", ", typeArgs.Take(arity), arg => arg.TypeName(context, parseAble));
      if (domainNeedsParens) { s += ")"; }
      s += " " + arrow + " ";
      s += (result ?? typeArgs.Last()).TypeName(context, parseAble);
      return s;
    }

    public override bool SupportsEquality {
      get {
        return false;
      }
    }
  }

  public abstract class CollectionType : NonProxyType
  {
    public abstract string CollectionTypeName { get; }
    public override string TypeName(ModuleDefinition context, bool parseAble) {
      Contract.Ensures(Contract.Result<string>() != null);
      var targs = HasTypeArg() ? this.TypeArgsToString(context, parseAble) : "";
      return CollectionTypeName + targs;
    }
    public Type Arg {
      get {
        Contract.Ensures(Contract.Result<Type>() != null);  // this is true only after "arg" has really been set (i.e., it follows from the precondition)
        Contract.Assume(arg != null);  // This is really a precondition.  Don't call Arg until "arg" has been set.
        return arg;
      }
    }  // denotes the Domain type for a Map
    private Type arg;
    // The following methods, HasTypeArg and SetTypeArg/SetTypeArgs, are to be called during resolution to make sure that "arg" becomes set.
    public bool HasTypeArg() {
      return arg != null;
    }
    public void SetTypeArg(Type arg) {
      Contract.Requires(arg != null);
      Contract.Requires(1 <= this.TypeArgs.Count);  // this is actually an invariant of all collection types
      Contract.Assume(this.arg == null);  // Can only set it once.  This is really a precondition.
      this.arg = arg;
      this.TypeArgs[0] = arg;
    }
    public virtual void SetTypeArgs(Type arg, Type other) {
      Contract.Requires(arg != null);
      Contract.Requires(other != null);
      Contract.Requires(this.TypeArgs.Count == 2);
      Contract.Assume(this.arg == null);  // Can only set it once.  This is really a precondition.
      this.arg = arg;
      this.TypeArgs[0] = arg;
      this.TypeArgs[1] = other;
    }
    [ContractInvariantMethod]
    void ObjectInvariant() {
      // Contract.Invariant(Contract.ForAll(TypeArgs, tp => tp != null));
      // After resolution, the following is invariant:  Contract.Invariant(Arg != null);
      // However, it may not be true until then.
    }
    /// <summary>
    /// This constructor is a collection types with 1 type argument
    /// </summary>
    protected CollectionType(Type arg) {
      this.arg = arg;
      this.TypeArgs = new List<Type> { arg };
    }
    /// <summary>
    /// This constructor is a collection types with 2 type arguments
    /// </summary>
    protected CollectionType(Type arg, Type other) {
      this.arg = arg;
      this.TypeArgs = new List<Type> { arg, other };
    }

    public override bool MayInvolveReferences {
      get {
        return Arg.MayInvolveReferences;
      }
    }
  }

  public class SetType : CollectionType {
    private bool finite;

    public bool Finite {
      get { return finite; }
      set { finite = value; }
    }

    public SetType(bool finite, Type arg) : base(arg) {
      this.finite = finite;
    }
    public override string CollectionTypeName { get { return finite ? "set" : "iset"; } }
    [Pure]
    public override bool Equals(Type that) {
      var t = that.NormalizeExpand() as SetType;
      return t != null && Finite == t.Finite && Arg.Equals(t.Arg);
    }
    public override bool SupportsEquality {
      get {
        // Sets always support equality, because there is a check that the set element type always does.
        return true;
      }
    }
  }

  public class MultiSetType : CollectionType
  {
    public MultiSetType(Type arg) : base(arg) {
    }
    public override string CollectionTypeName { get { return "multiset"; } }
    public override bool Equals(Type that) {
      var t = that.NormalizeExpand() as MultiSetType;
      return t != null && Arg.Equals(t.Arg);
    }
    public override bool SupportsEquality {
      get {
        // Multisets always support equality, because there is a check that the set element type always does.
        return true;
      }
    }
  }

  public class SeqType : CollectionType {
    public SeqType(Type arg) : base(arg) {
    }
    public override string CollectionTypeName { get { return "seq"; } }
    public override bool Equals(Type that) {
      var t = that.NormalizeExpand() as SeqType;
      return t != null && Arg.Equals(t.Arg);
    }
    public override bool SupportsEquality {
      get {
        // The sequence type supports equality if its element type does
        return Arg.SupportsEquality;
      }
    }
  }
  public class MapType : CollectionType
  {
    public bool Finite {
      get { return finite; }
      set { finite = value; }
    }
    private bool finite;
    public Type Range {
      get { return range; }
    }
    private Type range;
    public override void SetTypeArgs(Type domain, Type range) {
      base.SetTypeArgs(domain, range);
      Contract.Assume(this.range == null);  // Can only set once.  This is really a precondition.
      this.range = range;
    }
    public MapType(bool finite, Type domain, Type range) : base(domain, range) {
      Contract.Requires((domain == null && range == null) || (domain != null && range != null));
      this.finite = finite;
      this.range = range;
    }
    public Type Domain {
      get { return Arg; }
    }
    public override string CollectionTypeName { get { return finite ? "map" : "imap"; } }
    [Pure]
    public override string TypeName(ModuleDefinition context, bool parseAble) {
      Contract.Ensures(Contract.Result<string>() != null);
      var targs = HasTypeArg() ? this.TypeArgsToString(context, parseAble) : "";
      return CollectionTypeName + targs;
    }
    public override bool Equals(Type that) {
      var t = that.NormalizeExpand() as MapType;
      return t != null && Finite == t.Finite && Arg.Equals(t.Arg) && Range.Equals(t.Range);
    }
    public override bool SupportsEquality {
      get {
        // A map type supports equality if both its Keys type and Values type does.  It is checked
        // that the Keys type always supports equality, so we only need to check the Values type here.
        return range.SupportsEquality;
      }
    }
    public override bool MayInvolveReferences {
      get {
        return Domain.MayInvolveReferences || Range.MayInvolveReferences;
      }
    }
  }

  public class UserDefinedType : NonProxyType
  {
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Name != null);
      Contract.Invariant(cce.NonNullElements(TypeArgs));
      Contract.Invariant(!ArrowType.IsArrowTypeName(Name) || this is ArrowType);
    }

    public readonly string Name;

    [Rep]

    public string FullName {
      get {
        if (ResolvedClass != null && !ResolvedClass.Module.IsDefaultModule) {
          return ResolvedClass.Module.Name + "." + Name;
        } else {
          return Name;
        }
      }
    }

    string compileName;
    public string CompileName {
      get {
        if (compileName == null) {
          compileName = NonglobalVariable.CompilerizeName(Name);
        }
        return compileName;
      }
    }
    public string FullCompanionCompileName {
      get {
        Contract.Requires(ResolvedClass is TraitDecl);
        var m = ResolvedClass.Module;
        var s = m.IsDefaultModule ? "" : m.CompileName + ".";
        return s + "_Companion_" + ResolvedClass.CompileName;
      }
    }

    public TopLevelDecl ResolvedClass;
    public TypeParameter ResolvedParam;

    /// <summary>
    /// Constructs a Type (in particular, a UserDefinedType) from a TopLevelDecl denoting a type declaration.  If
    /// the given declaration takes type parameters, these are filled as references to the formal type parameters
    /// themselves.  (Usually, this method is called when the type parameters in the result don't matter, other
    /// than that they need to be filled in, so as to make a properly resolved UserDefinedType.)
    /// If "typeArgs" is non-null, then its type parameters are used in constructing the returned type.
    /// If "typeArgs" is null, then the formal type parameters of "cd" are used.
    /// </summary>
    public static UserDefinedType FromTopLevelDecl(TopLevelDecl cd, List<TypeParameter> typeArgs = null) {
      Contract.Requires(cd != null);
      Contract.Assert((cd is ArrowTypeDecl) == ArrowType.IsArrowTypeName(cd.Name));
      var args = (typeArgs ?? cd.TypeArgs).ConvertAll(tp => (Type)new UserDefinedType(tp));
      if (cd is ArrowTypeDecl) {
        return new ArrowType((ArrowTypeDecl)cd, args);
      } else if (cd is ClassDecl && !(cd is DefaultClassDecl)) {
        return new UserDefinedType(cd.Name + "?", cd, args);
      } else {
        return new UserDefinedType(cd.Name, cd, args);
      }
    }

    /// <summary>
    /// This constructor constructs a resolved class/datatype/iterator/subset-type/newtype type
    /// </summary>
    public UserDefinedType(string name, TopLevelDecl cd, [Captured] List<Type> typeArgs) {
      Contract.Requires(name != null);
      Contract.Requires(cd != null);
      Contract.Requires(cce.NonNullElements(typeArgs));
      Contract.Requires(cd.TypeArgs.Count == typeArgs.Count);
      // The following is almost a precondition. In a few places, the source program names a class, not a type,
      // and in then name==cd.Name for a ClassDecl.
      //Contract.Requires(!(cd is ClassDecl) || cd is DefaultClassDecl || cd is ArrowTypeDecl || name == cd.Name + "?");
      Contract.Requires(!(cd is ArrowTypeDecl) || name == cd.Name);
      Contract.Requires(!(cd is DefaultClassDecl) || name == cd.Name);
      this.Name = name;
      this.ResolvedClass = cd;
      this.TypeArgs = typeArgs;
    }

    public static UserDefinedType CreateNonNullType(UserDefinedType udtNullableType) {
      Contract.Requires(udtNullableType != null);
      Contract.Requires(udtNullableType.ResolvedClass is ClassDecl);
      var cl = (ClassDecl)udtNullableType.ResolvedClass;
      return new UserDefinedType(cl.NonNullTypeDecl.Name, cl.NonNullTypeDecl, udtNullableType.TypeArgs);
    }

    public UserDefinedType(TypeParameter tp) {
      Contract.Requires(tp != null);
      Contract.Requires(!(tp is OpaqueType_AsParameter));
      this.Name = tp.Name;
      this.TypeArgs = new List<Type>();
      this.ResolvedParam = tp;
    }

    /// <summary>
    /// Constructs a resolved type for an opaque type.
    /// </summary>
    public UserDefinedType(OpaqueType_AsParameter tp, OpaqueTypeDecl decl, List<Type> typeArgs) {
      Contract.Requires(tp != null);
      Contract.Requires(decl != null && decl.TheType == tp);
      Contract.Requires(typeArgs != null);
      this.Name = tp.Name;
      this.ResolvedParam = tp;
      this.ResolvedClass = decl;
      this.TypeArgs = typeArgs;
    }

    public override bool Equals(Type that) {
      var i = NormalizeExpand();
      if (i is UserDefinedType) {
        var ii = (UserDefinedType)i;
        var t = that.NormalizeExpand() as UserDefinedType;
        if (t == null || ii.ResolvedParam != t.ResolvedParam || ii.ResolvedClass != t.ResolvedClass || ii.TypeArgs.Count != t.TypeArgs.Count) {
          return false;
        } else {
          for (int j = 0; j < ii.TypeArgs.Count; j++) {
            if (!ii.TypeArgs[j].Equals(t.TypeArgs[j])) {
              return false;
            }
          }
          return true;
        }
      } else {
        return i.Equals(that);
      }
    }

    /// <summary>
    /// If type denotes a resolved class type, then return that class type.
    /// Otherwise, return null.
    /// </summary>
    public static UserDefinedType DenotesClass(Type type) {
      Contract.Requires(type != null);
      Contract.Ensures(Contract.Result<UserDefinedType>() == null || Contract.Result<UserDefinedType>().ResolvedClass is ClassDecl);
      type = type.NormalizeExpand();
      UserDefinedType ct = type as UserDefinedType;
      if (ct != null && ct.ResolvedClass is ClassDecl) {
        return ct;
      } else {
        return null;
      }
    }

    public static Type ArrayElementType(Type type) {
      Contract.Requires(type.IsArrayType);

      Contract.Requires(type != null);
      Contract.Ensures(Contract.Result<Type>() != null);

      UserDefinedType udt = DenotesClass(type);
      Contract.Assert(udt != null);
      Contract.Assert(udt.TypeArgs.Count == 1);  // holds true of all array types
      return udt.TypeArgs[0];
    }

    [Pure]
    public override string TypeName(ModuleDefinition context, bool parseAble) {
      Contract.Ensures(Contract.Result<string>() != null);
      if (BuiltIns.IsTupleTypeName(Name)) {
        return "(" + Util.Comma(", ", TypeArgs, ty => ty.TypeName(context, parseAble)) + ")";
      } else if (ArrowType.IsPartialArrowTypeName(Name)) {
        return ArrowType.PrettyArrowTypeName(ArrowType.PARTIAL_ARROW, TypeArgs, null, context, parseAble);
      } else if (ArrowType.IsTotalArrowTypeName(Name)) {
        return ArrowType.PrettyArrowTypeName(ArrowType.TOTAL_ARROW, TypeArgs, null, context, parseAble);
      } else {
#if TEST_TYPE_SYNONYM_TRANSPARENCY
        if (Name == "type#synonym#transparency#test" && ResolvedClass is TypeSynonymDecl) {
          return ((TypeSynonymDecl)ResolvedClass).Rhs.TypeName(context);
        }
#endif
        var s = FullName;
        if (TypeArgs != null && TypeArgs.Count != 0) {
          s += this.TypeArgsToString(context, parseAble);
        }
        return s;
      }
    }

    public override bool SupportsEquality {
      get {
        if (ResolvedClass is ClassDecl || ResolvedClass is NewtypeDecl) {
          return ResolvedClass.IsRevealedInScope(Type.GetScope());
        } else if (ResolvedClass is CoDatatypeDecl) {
          return false;
        } else if (ResolvedClass is IndDatatypeDecl) {
          var dt = (IndDatatypeDecl)ResolvedClass;
          if (!dt.IsRevealedInScope(Type.GetScope())) {
            return false;
          }
          if (dt.EqualitySupport == IndDatatypeDecl.ES.Never) {
            return false;
          }
          Contract.Assert(dt.TypeArgs.Count == TypeArgs.Count);
          var i = 0;
          foreach (var tp in dt.TypeArgs) {
            if (tp.NecessaryForEqualitySupportOfSurroundingInductiveDatatype && !TypeArgs[i].SupportsEquality) {
              return false;
            }
            i++;
          }
          return true;
        } else if (ResolvedClass is TypeSynonymDeclBase) {
          var t = (TypeSynonymDeclBase)ResolvedClass;
          if (t.MustSupportEquality) {
            return true;
          } else if (t.IsRevealedInScope(Type.GetScope())) {
            return t.RhsWithArgument(TypeArgs).SupportsEquality;
          } else {
            return false;
          }
        } else if (ResolvedParam != null) {
          return ResolvedParam.MustSupportEquality;
        }
        Contract.Assume(false);  // the SupportsEquality getter requires the Type to have been successfully resolved
        return true;
      }
    }

    public override bool MayInvolveReferences {
      get {
        if (ResolvedClass is ClassDecl) {
          return true;
        } else if (ResolvedClass is NewtypeDecl) {
          return false;
        } else if (ResolvedClass is DatatypeDecl) {
          var dt = (DatatypeDecl)ResolvedClass;
          if (!dt.IsRevealedInScope(Type.GetScope())) {
            return true;
          }
          Contract.Assert(dt.TypeArgs.Count == TypeArgs.Count);
          return TypeArgs.TrueForAll(ta => ta.MayInvolveReferences);
        } else if (ResolvedClass is TypeSynonymDeclBase) {
          var t = (TypeSynonymDeclBase)ResolvedClass;
          // (Note, if type parameters/opaque types could have a may-involve-references characteristic, then it would be consulted here)
          if (t.IsRevealedInScope(Type.GetScope())) {
            return t.RhsWithArgument(TypeArgs).MayInvolveReferences;
          } else {
            return true;
          }
        } else if (ResolvedParam != null) {
          // (Note, if type parameters/opaque types could have a may-involve-references characteristic, then it would be consulted here)
          return true;
        }
        Contract.Assume(false);  // the MayInvolveReferences getter requires the Type to have been successfully resolved
        return true;
      }
    }

    public static UserDefinedType GetThisType(TopLevelDeclWithMembers cl) {
      Contract.Requires(cl != null);
      Contract.Ensures(Contract.Result<UserDefinedType>() != null);

      if (cl is ClassDecl cls) {
        return UserDefinedType.FromTopLevelDecl(cls.NonNullTypeDecl, cls.TypeArgs);
      } else {
        return UserDefinedType.FromTopLevelDecl(cl, cl.TypeArgs);
      }
    }

    public static UserDefinedType GetReceiverType(MemberDecl member) {
      Contract.Requires(member != null);
      Contract.Ensures(Contract.Result<UserDefinedType>() != null);

      return GetThisType((TopLevelDeclWithMembers)member.EnclosingClass);
    }
  }

  // ------------------------------------------------------------------------------------------------------

  /// <summary>
  /// This interface is used by the Dafny IDE.
  /// </summary>
  public interface INamedRegion
  {
    string Name { get; }
  }

  public abstract class Declaration : INamedRegion, IAttributeBearingDeclaration
  {
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Name != null);
    }

    public static string IdProtect(string name) {
      switch (DafnyOptions.O.CompileTarget) {
        case DafnyOptions.CompilationTarget.Csharp:
          return CsharpCompiler.PublicIdProtect(name);
        case DafnyOptions.CompilationTarget.JavaScript:
          return JavaScriptCompiler.PublicIdProtect(name);
        case DafnyOptions.CompilationTarget.Go:
          return GoCompiler.PublicIdProtect(name);
        case DafnyOptions.CompilationTarget.Java:
          return GoCompiler.PublicIdProtect(name);
        default:
          Contract.Assert(false);  // unexpected compile target
          return name;
      }
    }

    public readonly string Name;
    string INamedRegion.Name { get { return Name; } }
    string compileName;

    private VisibilityScope opaqueScope = new VisibilityScope();
    private VisibilityScope revealScope = new VisibilityScope();

    private bool scopeIsInherited = false;

    public virtual bool CanBeExported() {
      return true;
    }

    public virtual bool CanBeRevealed() {
      return false;
    }

    public bool ScopeIsInherited { get { return scopeIsInherited; } }

    public void AddVisibilityScope(VisibilityScope scope, bool IsOpaque) {
      Contract.Requires(!ScopeIsInherited); //pragmatically we should only augment the visibility of the parent

      if (IsOpaque) {
        opaqueScope.Augment(scope);
      } else {
        revealScope.Augment(scope);
      }
    }


    public void InheritVisibility(Declaration d, bool onlyRevealed = true) {
      Contract.Assert(opaqueScope.IsEmpty());
      Contract.Assert(revealScope.IsEmpty());
      scopeIsInherited = false;

      revealScope = d.revealScope;

      if (!onlyRevealed) {
        opaqueScope = d.opaqueScope;
      }
      scopeIsInherited = true;

    }

    public bool IsRevealedInScope(VisibilityScope scope) {
      return revealScope.VisibleInScope(scope);
    }

    public bool IsVisibleInScope(VisibilityScope scope) {
      return IsRevealedInScope(scope) || opaqueScope.VisibleInScope(scope);
    }

    public virtual string CompileName {
      get {
        if (compileName == null) {
          string qual;
          IsExtern(out qual, out compileName);
          if (compileName == null) {
            // this is the usual name
            compileName = NonglobalVariable.CompilerizeName(Name);
          }
        }
        return compileName;
      }
    }
    public bool IsExtern(out string/*?*/ qualification, out string/*?*/ name) {
      // ensures result==false ==> qualification == null && name == null
      Contract.Ensures(Contract.Result<bool>() || (Contract.ValueAtReturn(out qualification) == null && Contract.ValueAtReturn(out name) == null));
      // ensures result==true ==> qualification != null ==> name != null
      Contract.Ensures(!Contract.Result<bool>() || Contract.ValueAtReturn(out qualification) == null || Contract.ValueAtReturn(out name) != null);

      qualification = null;
      name = null;
      if (!DafnyOptions.O.DisallowExterns) {
        var externArgs = Attributes.FindExpressions(this.Attributes, "extern");
        if (externArgs != null) {
          if (externArgs.Count == 0) {
            return true;
          } else if (externArgs.Count == 1 && externArgs[0] is StringLiteralExpr) {
            name = externArgs[0].AsStringLiteral();
            return true;
          } else if (externArgs.Count == 2 && externArgs[0] is StringLiteralExpr && externArgs[1] is StringLiteralExpr) {
            qualification = externArgs[0].AsStringLiteral();
            name = externArgs[1].AsStringLiteral();
            return true;
          }
        }
      }
      return false;
    }
    public Attributes Attributes;  // readonly, except during class merging in the refinement transformations and when changed by Compiler.MarkCapitalizationConflict

    public Declaration(string name, Attributes attributes) {
      Contract.Requires(name != null);
      this.Name = name;
      this.Attributes = attributes;
    }

    [Pure]
    public override string ToString() {
      Contract.Ensures(Contract.Result<string>() != null);
      return Name;
    }

    internal FreshIdGenerator IdGenerator = new FreshIdGenerator();
  }

  public class OpaqueType_AsParameter : TypeParameter {
    public readonly List<TypeParameter> TypeArgs;
    public OpaqueType_AsParameter(string name, TypeParameterCharacteristics characteristics, List<TypeParameter> typeArgs)
      : base(name, TypeParameter.TPVarianceSyntax.NonVariant_Strict, characteristics) {
      Contract.Requires(name != null);
      Contract.Requires(typeArgs != null);
      TypeArgs = typeArgs;
    }
  }

  public class TypeParameter : Declaration {
    public interface ParentType {
      string FullName {
        get;
      }
    }
    [Peer]
    ParentType parent;
    public ParentType Parent {
      get {
        return parent;
      }
      [param: Captured]
      set {
        Contract.Requires(Parent == null);  // set it only once
        Contract.Requires(value != null);
        parent = value;
      }
    }

    /// <summary>
    /// NonVariant_Strict     (default) - non-variant, no uses left of an arrow
    /// NonVariant_Permissive    !      - non-variant
    /// Covariant_Strict         +      - co-variant, no uses left of an arrow
    /// Covariant_Permissive     *      - co-variant
    /// Contravarianct           -       - contra-variant
    /// </summary>
    public enum TPVarianceSyntax { NonVariant_Strict, NonVariant_Permissive, Covariant_Strict, Covariant_Permissive, Contravariance }
    public enum TPVariance { Co, Non, Contra }
    public static TPVariance Negate(TPVariance v) {
      switch (v) {
        case TPVariance.Co:
          return TPVariance.Contra;
        case TPVariance.Contra:
          return TPVariance.Co;
        default:
          return v;
      }
    }
    public TPVarianceSyntax VarianceSyntax;
    public TPVariance Variance {
      get {
        switch (VarianceSyntax) {
          case TPVarianceSyntax.Covariant_Strict:
          case TPVarianceSyntax.Covariant_Permissive:
            return TPVariance.Co;
          case TPVarianceSyntax.NonVariant_Strict:
          case TPVarianceSyntax.NonVariant_Permissive:
            return TPVariance.Non;
          case TPVarianceSyntax.Contravariance:
            return TPVariance.Contra;
          default:
            Contract.Assert(false);  // unexpected VarianceSyntax
            throw new cce.UnreachableException();
        }
      }
    }
    public bool StrictVariance {
      get {
        switch (VarianceSyntax) {
          case TPVarianceSyntax.Covariant_Strict:
          case TPVarianceSyntax.NonVariant_Strict:
            return true;
          case TPVarianceSyntax.Covariant_Permissive:
          case TPVarianceSyntax.NonVariant_Permissive:
          case TPVarianceSyntax.Contravariance:
            return false;
          default:
            Contract.Assert(false);  // unexpected VarianceSyntax
            throw new cce.UnreachableException();
        }
      }
    }

    public enum EqualitySupportValue { Required, InferredRequired, Unspecified }
    public struct TypeParameterCharacteristics
    {
      public EqualitySupportValue EqualitySupport;  // the resolver may change this value from Unspecified to InferredRequired (for some signatures that may immediately imply that equality support is required)
      public bool MustSupportZeroInitialization;
      public bool DisallowReferenceTypes;
      public TypeParameterCharacteristics(bool dummy) {
        EqualitySupport = EqualitySupportValue.Unspecified;
        MustSupportZeroInitialization = false;
        DisallowReferenceTypes = false;
      }
      public TypeParameterCharacteristics(EqualitySupportValue eqSupport, bool mustSupportZeroInitialization, bool disallowReferenceTypes) {
        EqualitySupport = eqSupport;
        MustSupportZeroInitialization = mustSupportZeroInitialization;
        DisallowReferenceTypes = disallowReferenceTypes;
      }
    }
    public TypeParameterCharacteristics Characteristics;
    public bool MustSupportEquality {
      get { return Characteristics.EqualitySupport != EqualitySupportValue.Unspecified; }
    }

    public bool NecessaryForEqualitySupportOfSurroundingInductiveDatatype = false;  // computed during resolution; relevant only when Parent denotes an IndDatatypeDecl

    public bool IsAbstractTypeDeclaration { // true if this type parameter represents t in type t;
      get { return parent == null; }
    }
    public bool IsToplevelScope { // true if this type parameter is on a toplevel (ie. class C<T>), and false if it is on a member (ie. method m<T>(...))
      get { return parent is TopLevelDecl; }
    }
    public int PositionalIndex; // which type parameter this is (ie. in C<S, T, U>, S is 0, T is 1 and U is 2).

    public TypeParameter(string name, TPVarianceSyntax varianceS, TypeParameterCharacteristics characteristics)
      : base(name, null) {
      Contract.Requires(name != null);
      Characteristics = characteristics;
      VarianceSyntax = varianceS;
    }

    public TypeParameter(string name, TPVarianceSyntax varianceS)
      : this(name, varianceS, new TypeParameterCharacteristics(false)) {
      Contract.Requires(name != null);
    }

    public TypeParameter(string name, int positionalIndex, ParentType parent)
       : this(name, TPVarianceSyntax.NonVariant_Strict)
    {
      PositionalIndex = positionalIndex;
      Parent = parent;
    }

    public string FullName() {
      // when debugging, print it all:
      return /* Parent.FullName + "." + */ Name;
    }

    public static TypeParameterCharacteristics GetExplicitCharacteristics(TopLevelDecl d) {
      Contract.Requires(d != null);
      TypeParameterCharacteristics characteristics = new TypeParameterCharacteristics(false);
      if (d is OpaqueTypeDecl) {
        var dd = (OpaqueTypeDecl)d;
        characteristics = dd.Characteristics;
      } else if (d is TypeSynonymDecl) {
        var dd = (TypeSynonymDecl)d;
        characteristics = dd.Characteristics;
      }
      if (characteristics.EqualitySupport == EqualitySupportValue.InferredRequired) {
        return new TypeParameterCharacteristics(EqualitySupportValue.Unspecified, characteristics.MustSupportZeroInitialization, characteristics.DisallowReferenceTypes);
      } else {
        return characteristics;
      }
    }
  }

  // Represents a submodule declaration at module level scope
  abstract public class ModuleDecl : TopLevelDecl
  {
    public override string WhatKind { get { return "module"; } }
    public ModuleSignature Signature; // filled in by resolution, in topological order.
    public virtual ModuleSignature AccessibleSignature(bool ignoreExports) {
      Contract.Requires(Signature != null);
      return Signature;
    }
    public virtual ModuleSignature AccessibleSignature() {
      Contract.Requires(Signature != null);
      return Signature;
    }
    public int Height;

    public readonly bool Opened;

    public ModuleDecl(string name, ModuleDefinition parent, bool opened)
      : base(name, parent, new List<TypeParameter>(), null) {
        Height = -1;
      Signature = null;
      Opened = opened;
    }
    public abstract object Dereference();

    public int? ResolvedHash { get; set; }
  }
  // Represents module X { ... }
  public class LiteralModuleDecl : ModuleDecl
  {
    public readonly ModuleDefinition ModuleDef;
    public ModuleSignature DefaultExport;  // the default export set of the module. fill in by the resolver.

    private ModuleSignature emptySignature;
    public override ModuleSignature AccessibleSignature(bool ignoreExports) {
      if (ignoreExports) {
        return Signature;
      }
      return this.AccessibleSignature();
    }
    public override ModuleSignature AccessibleSignature() {
      if (DefaultExport == null) {
        if (emptySignature == null) {
          emptySignature = new ModuleSignature();
        }
        return emptySignature;
      }
      return DefaultExport;
    }

    public LiteralModuleDecl(ModuleDefinition module, ModuleDefinition parent)
      : base(module.Name, parent, false) {
      ModuleDef = module;
    }
    public override object Dereference() { return ModuleDef; }
  }
  // Represents "module name = path;", where name is an identifier and path is a possibly qualified name.
  public class AliasModuleDecl : ModuleDecl
  {
    public readonly List<string> Path; // generated by the parser, this is looked up
    public readonly List<string> Exports; // list of exports sets
    public ModuleDecl Root; // the moduleDecl that Path[0] refers to.

    public AliasModuleDecl(List<string> path, string name, ModuleDefinition parent, bool opened, List<string> exports)
      : base(name, parent, opened) {
       Contract.Requires(path != null && path.Count > 0);
       Contract.Requires(exports != null);
       Contract.Requires(exports.Count == 0 || path.Count == 1);
       Path = path;
       Exports = exports;
    }
    public override object Dereference() { return Signature.ModuleDef; }
  }

  // Represents "module name as path [ = compilePath];", where name is a identifier and path is a possibly qualified name.
  public class ModuleFacadeDecl : ModuleDecl
  {
    public ModuleDecl Root;
    public readonly List<string> Path;
    public readonly List<string> Exports; // list of exports sets
    public ModuleDecl CompileRoot;
    public ModuleSignature OriginalSignature;

    public ModuleFacadeDecl(List<string> path, string name, ModuleDefinition parent, bool opened, List<string> exports)
      : base(name, parent, opened) {
      Contract.Requires(path != null && path.Count > 0);
      Contract.Requires(exports != null);
      Contract.Requires(exports.Count == 0 || path.Count == 1);

      Root = null;
    }
    public override object Dereference() { return this; }
  }

  // Represents the exports of a module.
  public class ModuleExportDecl : ModuleDecl
  {
    public readonly bool IsDefault;
    public List<ExportSignature> Exports; // list of TopLevelDecl that are included in the export
    public List<string> Extends; // list of exports that are extended
    public readonly List<ModuleExportDecl> ExtendDecls = new List<ModuleExportDecl>(); // fill in by the resolver
    public readonly HashSet<Tuple<Declaration, bool>> ExportDecls = new HashSet<Tuple<Declaration, bool>>(); // fill in by the resolver
    public bool RevealAll; // only kept for initial rewriting, then discarded
    public bool ProvideAll;

    public readonly VisibilityScope ThisScope;
    public ModuleExportDecl(string name, ModuleDefinition parent,
      List<ExportSignature> exports, List<string> extends, bool provideAll, bool revealAll, bool isDefault)
      : base(isDefault ? parent.Name : name, parent, false) {
      Contract.Requires(exports != null);
      IsDefault = isDefault;
      Exports = exports;
      Extends = extends;
      ProvideAll = provideAll;
      RevealAll = revealAll;
      ThisScope = new VisibilityScope(true, this.FullCompileName);
    }

    public void SetupDefaultSignature() {
      Contract.Requires(this.Signature == null);
      var sig = new ModuleSignature();
      sig.ModuleDef = this.Module;
      sig.IsAbstract = this.Module.IsAbstract;
      sig.VisibilityScope = new VisibilityScope();
      sig.VisibilityScope.Augment(ThisScope);
      this.Signature = sig;
    }

    public override object Dereference() { return this; }
    public override bool CanBeExported() {
      return false;
    }

  }

  public class ExportSignature
  {
    public readonly bool Opaque;
    public readonly string ClassId;
    public readonly string Id;

    public Declaration Decl;  // filled in by the resolver

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Id != null);
    }

    public ExportSignature(string prefix, string id, bool opaque) {
      Contract.Requires(prefix != null);
      Contract.Requires(id != null);
      ClassId = prefix;
      Id = id;
      Opaque = opaque;
    }

    public ExportSignature(string id, bool opaque) {
      Contract.Requires(id != null);
      Id = id;
      Opaque = opaque;
    }

    public override string ToString() {
      if (ClassId != null) {
        return ClassId + "." + Id;
      }
      return Id;
    }
  }

  public class ModuleSignature {
    public  VisibilityScope VisibilityScope = null;
    public readonly Dictionary<string, TopLevelDecl> TopLevels = new Dictionary<string, TopLevelDecl>();
    public readonly Dictionary<string, ModuleExportDecl> ExportSets = new Dictionary<string, ModuleExportDecl>();
    public readonly Dictionary<string, Tuple<DatatypeCtor, bool>> Ctors = new Dictionary<string, Tuple<DatatypeCtor, bool>>();
    public readonly Dictionary<string, MemberDecl> StaticMembers = new Dictionary<string, MemberDecl>();
    public ModuleDefinition ModuleDef = null; // Note: this is null if this signature does not correspond to a specific definition (i.e.
                                              // it is abstract). Otherwise, it points to that definition.
    public ModuleSignature CompileSignature = null; // This is the version of the signature that should be used at compile time.
    public ModuleSignature Refines = null;
    public bool IsAbstract = false;
    public ModuleSignature() {}
    public int? ResolvedHash { get; set; }

    // Qualified accesses follow module imports
    public bool FindImport(string name, out ModuleSignature pp) {
      TopLevelDecl top;
      if (TopLevels.TryGetValue(name, out top) && top is ModuleDecl) {
          pp = ((ModuleDecl)top).AccessibleSignature();
        return true;
      } else {
        pp = null;
        return false;
      }
    }

    public static ModuleSignature Merge(ModuleSignature m, ModuleSignature system) {
      Contract.Requires(m != null);
      Contract.Requires(system != null);
      var info = new ModuleSignature();
      // add the system-declared information, among which we know there are no duplicates
      foreach (var kv in system.TopLevels) {
        info.TopLevels.Add(kv.Key, kv.Value);
      }
      foreach (var kv in system.Ctors) {
        info.Ctors.Add(kv.Key, kv.Value);
      }
      foreach (var kv in system.StaticMembers) {
        info.StaticMembers.Add(kv.Key, kv.Value);
      }
      // add for the module itself
      foreach (var kv in m.TopLevels) {
        Contract.Assert(EquivIfPresent(info.TopLevels, kv.Key, kv.Value));
        info.TopLevels[kv.Key] = kv.Value;
      }
      foreach (var kv in m.Ctors) {
        Contract.Assert(EquivIfPresent(info.Ctors, kv.Key, kv.Value));
        info.Ctors[kv.Key] = kv.Value;
      }
      foreach (var kv in m.StaticMembers) {
        Contract.Assert(EquivIfPresent(info.StaticMembers, kv.Key, kv.Value));
        info.StaticMembers[kv.Key] = kv.Value;
      }
      info.IsAbstract = m.IsAbstract;
      info.VisibilityScope = new VisibilityScope();
      info.VisibilityScope.Augment(m.VisibilityScope);
      info.VisibilityScope.Augment(system.VisibilityScope);
      return info;
    }

    [Pure]
    private static bool EquivIfPresent<T1, T2>(Dictionary<T1, T2> dic, T1 key, T2 val)
    where T2 : class {
      T2 val2;
      if (dic.TryGetValue(key, out val2)) {
        return val.Equals(val2);
      }
      return true;
    }
  }

  public class ModuleDefinition : INamedRegion, IAttributeBearingDeclaration
  {
    public readonly string Name;
    public readonly Program Program;
    public string FullName {
      get {
        if (Module == null || Module.IsDefaultModule) {
          return Name;
        } else {
          return Module.FullName + "." + Name;
        }
      }
    }
    public readonly List<string> PrefixIds;
    string INamedRegion.Name { get { return Name; } }
    public ModuleDefinition Module;  // readonly, except can be changed by resolver for prefix-named modules when the real parent is discovered
    public readonly Attributes Attributes;
    public readonly string RefinementBaseName;  // null if no refinement base
    public ModuleDecl RefinementBaseRoot; // filled in early during resolution, corresponds to RefinementBaseName[0]
    public bool SuccessfullyResolved;  // set to true upon successful resolution; modules that import an unsuccessfully resolved module are not themselves resolved

    public List<Include> Includes;

    public readonly List<TopLevelDecl> TopLevelDecls = new List<TopLevelDecl>();  // filled in by the parser; readonly after that, except for the addition of prefix-named modules, which happens in the resolver
    public readonly List<Tuple<List<string>, LiteralModuleDecl>> PrefixNamedModules = new List<Tuple<List<string>, LiteralModuleDecl>>();  // filled in by the parser; emptied by the resolver
    public readonly Graph<ICallable> CallGraph = new Graph<ICallable>();  // filled in during resolution
    public int Height;  // height in the topological sorting of modules; filled in during resolution
    public readonly bool IsAbstract;
    public readonly bool IsProtected;
    public readonly bool IsFacade; // True iff this module represents a module facade (that is, an abstract interface)
    private readonly bool IsBuiltinName; // true if this is something like _System that shouldn't have it's name mangled.
    public bool IsToBeVerified = true;

    private ModuleSignature refinementBaseSig; // module signature of the refinementBase.
    public ModuleSignature RefinementBaseSig {
      get {
        return refinementBaseSig;
      }

      set {
        // the refinementBase member may only be changed once.
        if (null != refinementBaseSig) {
          throw new InvalidOperationException(string.Format("This module ({0}) already has a refinement base ({1}).", Name, refinementBase.Name));
        }
        refinementBaseSig = value;
      }
    }

    private ModuleDefinition refinementBase; // filled in during resolution via RefinementBase property (null if no refinement base yet or at all).

    public ModuleDefinition RefinementBase {
        get {
           return refinementBase;
        }

        set {
          // the refinementBase member may only be changed once.
          if (null != refinementBase) {
              throw new InvalidOperationException(string.Format("This module ({0}) already has a refinement base ({1}).", Name, refinementBase.Name));
          }
          refinementBase = value;
        }
    }

    public int? ResolvedHash { get; set; }

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(TopLevelDecls));
      Contract.Invariant(CallGraph != null);
    }

    public ModuleDefinition(string name, Program program, List<string> prefixIds, bool isAbstract, bool isProtected, bool isFacade, string refinementBase, ModuleDefinition parent, Attributes attributes, bool isBuiltinName, Parser parser = null)
    {
      Contract.Requires(name != null);
      this.Name = name;
      this.Program = program;
      this.PrefixIds = prefixIds;
      this.Attributes = attributes;
      this.Module = parent;
      RefinementBaseName = refinementBase;
      IsAbstract = isAbstract;
      IsProtected = isProtected;
      IsFacade = isFacade;
      RefinementBaseRoot = null;
      this.refinementBase = null;
      Includes = new List<Include>();
      IsBuiltinName = isBuiltinName;
    }

    VisibilityScope visibilityScope;

    public VisibilityScope VisibilityScope {
      get {
        if (visibilityScope == null) {
          visibilityScope = new VisibilityScope(true, this.CompileName);
        }
        return visibilityScope;
      }
    }

    public virtual bool IsDefaultModule {
      get {
        return false;
      }
    }
    string compileName;
    public string CompileName {
      get {
        if (compileName == null) {
          var externArgs = DafnyOptions.O.DisallowExterns ? null : Attributes.FindExpressions(this.Attributes, "extern");
          if (externArgs != null && 1 <= externArgs.Count && externArgs[0] is StringLiteralExpr) {
            compileName = (string)((StringLiteralExpr)externArgs[0]).Value;
          } else if (IsBuiltinName || externArgs != null) {
            compileName = Name;
          } else {
            compileName = "_" + Height.ToString() + "_" + NonglobalVariable.CompilerizeName(Name);
          }
        }
        return compileName;
      }
    }

    public string RefinementCompileName {
      get {
        return this.CompileName;
      }
    }

    /// <summary>
    /// Determines if "a" and "b" are in the same strongly connected component of the call graph, that is,
    /// if "a" and "b" are mutually recursive.
    /// Assumes that CallGraph has already been filled in for the modules containing "a" and "b".
    /// </summary>
    public static bool InSameSCC(ICallable a, ICallable b) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      if (a is SpecialFunction || b is SpecialFunction) { return false; }
      var module = a.EnclosingModule;
      return module == b.EnclosingModule && module.CallGraph.GetSCCRepresentative(a) == module.CallGraph.GetSCCRepresentative(b);
    }

    /// <summary>
    /// Return the representative elements of the SCCs that contain any member declaration in a
    /// class in "declarations".
    /// Note, the representative element may in some cases be a Method, not necessarily a Function.
    /// </summary>
    public static IEnumerable<ICallable> AllFunctionSCCs(List<TopLevelDecl> declarations) {
      var set = new HashSet<ICallable>();
      foreach (var d in declarations) {
        var cl = d as TopLevelDeclWithMembers;
        if (cl != null) {
          var module = cl.Module;
          foreach (var member in cl.Members) {
            var fn = member as Function;
            if (fn != null) {
              var repr = module.CallGraph.GetSCCRepresentative(fn);
              set.Add(repr);
            }
          }
        }
      }
      return set;
    }

    public static IEnumerable<Function> AllFunctions(List<TopLevelDecl> declarations) {
      foreach (var d in declarations) {
        var cl = d as TopLevelDeclWithMembers;
        if (cl != null) {
          foreach (var member in cl.Members) {
            var fn = member as Function;
            if (fn != null) {
              yield return fn;
            }
          }
        }
      }
    }

    public static IEnumerable<Field> AllFields(List<TopLevelDecl> declarations) {
      foreach (var d in declarations) {
        var cl = d as TopLevelDeclWithMembers;
        if (cl != null) {
          foreach (var member in cl.Members) {
            var fn = member as Field;
            if (fn != null) {
              yield return fn;
            }
          }
        }
      }
    }

    public static IEnumerable<ClassDecl> AllClasses(List<TopLevelDecl> declarations) {
      foreach (var d in declarations) {
        var cl = d as ClassDecl;
        if (cl != null) {
          yield return cl;
        }
      }
    }

    /// <summary>
    /// Yields all functions and methods that are members of some type in the given list of
    /// declarations.
    /// Note, an iterator declaration is a type, in this sense.
    /// Note, if the given list are the top-level declarations of a module, the yield will include
    /// colemmas but not their associated prefix lemmas (which are tucked into the colemma's
    /// .PrefixLemma field).
    /// </summary>
    public static IEnumerable<ICallable> AllCallables(List<TopLevelDecl> declarations) {
      foreach (var d in declarations) {
        var cl = d as TopLevelDeclWithMembers;
        if (cl != null) {
          foreach (var member in cl.Members) {
            var clbl = member as ICallable;
            if (clbl != null && !(member is ConstantField)) {
              yield return clbl;
            }
          }
        }
      }
    }

    /// <summary>
    /// Yields all functions and methods that are members of some non-iterator type in the given
    /// list of declarations, as well as any IteratorDecl's in that list.
    /// </summary>
    public static IEnumerable<ICallable> AllItersAndCallables(List<TopLevelDecl> declarations) {
      foreach (var d in declarations) {
        if (d is IteratorDecl) {
          var iter = (IteratorDecl)d;
          yield return iter;
        } else if (d is TopLevelDeclWithMembers) {
          var cl = (TopLevelDeclWithMembers)d;
          foreach (var member in cl.Members) {
            var clbl = member as ICallable;
            if (clbl != null) {
              yield return clbl;
            }
          }
        }
      }
    }

    public static IEnumerable<IteratorDecl> AllIteratorDecls(List<TopLevelDecl> declarations) {
      foreach (var d in declarations) {
        var iter = d as IteratorDecl;
        if (iter != null) {
          yield return iter;
        }
      }
    }

    /// <summary>
    /// Emits the declarations in "declarations", but for each such declaration that is a class with
    /// a corresponding non-null type, also emits that non-null type *after* the class declaration.
    /// </summary>
    public static IEnumerable<TopLevelDecl> AllDeclarationsAndNonNullTypeDecls(List<TopLevelDecl> declarations) {
      foreach (var d in declarations) {
        yield return d;
        var cl = d as ClassDecl;
        if (cl != null && cl.NonNullTypeDecl != null) {
          yield return cl.NonNullTypeDecl;
        }
      }
    }

    public bool IsEssentiallyEmptyModuleBody() {
      foreach (var d in TopLevelDecls) {
        if (d is ModuleDecl) {
          // modules don't count
          continue;
        } else if (d is ClassDecl) {
          var cl = (ClassDecl)d;
          if (cl.Members.Count == 0) {
            // the class is empty, so it doesn't count
            continue;
          }
        }
        return false;
      }
      return true;
    }
  }

  public class DefaultModuleDecl : ModuleDefinition {
    public DefaultModuleDecl(Program program)
      : base("_module", program, new List<string>(), false, false, false, null, null, null, true) {
    }
    public override bool IsDefaultModule {
      get {
        return true;
      }
    }
  }

  public abstract class TopLevelDecl : Declaration, TypeParameter.ParentType {
    public abstract string WhatKind { get; }
    public readonly ModuleDefinition Module;
    public readonly List<TypeParameter> TypeArgs;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(TypeArgs));
    }

    public TopLevelDecl(string name, ModuleDefinition module, List<TypeParameter> typeArgs, Attributes attributes)
      : base(name, attributes) {
      Contract.Requires(name != null);
      Contract.Requires(cce.NonNullElements(typeArgs));
      Module = module;
      TypeArgs = typeArgs;
    }

    public string FullName {
      get {
        return Module.FullName + "." + Name;
      }
    }
    public string FullSanitizedName {
      get {
        return Module.CompileName + "." + CompileName;
      }
    }

    public string FullSanitizedRefinementName {
      get {
        return Module.RefinementCompileName + "." + CompileName;
      }
    }

    public string FullNameInContext(ModuleDefinition context) {
      if (Module == context) {
        return Name;
      } else {
        return Module.Name + "." + Name;
      }
    }
    public string FullCompileName {
      get {
        var externArgs = Attributes.FindExpressions(this.Attributes, "extern");
        if (!DafnyOptions.O.DisallowExterns && externArgs != null) {
          if (externArgs.Count == 2 && externArgs[0] is StringLiteralExpr && externArgs[1] is StringLiteralExpr) {
            return externArgs[0].AsStringLiteral() + "." + externArgs[1].AsStringLiteral();
          }
        }
        if (Module.IsDefaultModule && DafnyOptions.O.CompileTarget == DafnyOptions.CompilationTarget.Csharp) {
          return Declaration.IdProtect(CompileName);
        } else {
          return Declaration.IdProtect(Module.CompileName) + "." + Declaration.IdProtect(CompileName);
        }
      }
    }

    public TopLevelDecl ViewAsClass {
      get {
        if (this is NonNullTypeDecl) {
          return ((NonNullTypeDecl)this).Class;
        } else {
          return this;
        }
      }
    }
  }

  public abstract class TopLevelDeclWithMembers : TopLevelDecl {
    public readonly List<MemberDecl> Members;
    public TopLevelDeclWithMembers(string name, ModuleDefinition module, List<TypeParameter> typeArgs, List<MemberDecl> members, Attributes attributes)
      : base(name, module, typeArgs, attributes) {
      Contract.Requires(name != null);
      Contract.Requires(cce.NonNullElements(typeArgs));
      Contract.Requires(cce.NonNullElements(members));
      Members = members;
    }
  }

  public class TraitDecl : ClassDecl {
    public override string WhatKind { get { return "trait"; } }
    public bool IsParent { set; get; }
    public TraitDecl(string name, ModuleDefinition module,
      List<TypeParameter> typeArgs, [Captured] List<MemberDecl> members, Attributes attributes)
      : base(name, module, typeArgs, members, attributes, null) { }
  }

  public class ClassDecl : TopLevelDeclWithMembers {
    public override string WhatKind { get { return "class"; } }
    public override bool CanBeRevealed() { return true; }
    public readonly List<MemberDecl> InheritedMembers = new List<MemberDecl>();  // these are instance fields and instance members defined with bodies in traits
    public readonly List<Type> TraitsTyp;  // these are the types that are parsed after the keyword 'extends'
    public readonly List<TraitDecl> TraitsObj = new List<TraitDecl>();  // populated during resolution
    public bool HasConstructor;  // filled in (early) during resolution; true iff there exists a member that is a Constructor
    public readonly NonNullTypeDecl NonNullTypeDecl;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(Members));
      Contract.Invariant(TraitsTyp != null);
      Contract.Invariant(TraitsObj != null);
    }

    public ClassDecl(string name, ModuleDefinition module,
      List<TypeParameter> typeArgs, [Captured] List<MemberDecl> members, Attributes attributes, List<Type> traits)
      : base(name, module, typeArgs, members, attributes) {
      Contract.Requires(name != null);
      Contract.Requires(module != null);
      Contract.Requires(cce.NonNullElements(typeArgs));
      Contract.Requires(cce.NonNullElements(members));
      TraitsTyp = traits ?? new List<Type>();
      if (!IsDefaultClass && !(this is ArrowTypeDecl)) {
        NonNullTypeDecl = new NonNullTypeDecl(this);
      }
    }
    public virtual bool IsDefaultClass {
      get {
        return false;
      }
    }

    internal bool DerivesFrom(TopLevelDecl b) {
      Contract.Requires(b != null);
      return this == b || this.TraitsObj.Exists(tr => tr.DerivesFrom(b));
    }
  }

  public class DefaultClassDecl : ClassDecl {
    public DefaultClassDecl(ModuleDefinition module, [Captured] List<MemberDecl> members)
      : base("_default", module, new List<TypeParameter>(), members, null, null) {
      Contract.Requires(module != null);
      Contract.Requires(cce.NonNullElements(members));
    }
    public override bool IsDefaultClass {
      get {
        return true;
      }
    }
  }

  public class ArrayClassDecl : ClassDecl {
    public override string WhatKind { get { return "array type"; } }
    public readonly int Dims;
    public ArrayClassDecl(int dims, ModuleDefinition module, Attributes attrs)
    : base(BuiltIns.ArrayClassName(dims), module,
      new List<TypeParameter>(new TypeParameter[]{ new TypeParameter("arg", TypeParameter.TPVarianceSyntax.NonVariant_Strict) }),
      new List<MemberDecl>(), attrs, null)
    {
      Contract.Requires(1 <= dims);
      Contract.Requires(module != null);

      Dims = dims;
    }
  }

public class ArrowTypeDecl : ClassDecl
  {
    public override string WhatKind { get { return "function type"; } }
    public readonly int Arity;
    
    public ArrowTypeDecl(List<TypeParameter> tps, ModuleDefinition module, Attributes attributes)
      : base(ArrowType.ArrowTypeName(tps.Count - 1), module, tps, new List<MemberDecl> {}, attributes, null) {
      Contract.Requires(tps != null && 1 <= tps.Count);
      Contract.Requires(module != null);
      Arity = tps.Count - 1;
    }
  }

  public abstract class DatatypeDecl : TopLevelDeclWithMembers, RevealableTypeDecl, ICallable
  {
    public override bool CanBeRevealed() { return true; }
    public readonly List<DatatypeCtor> Ctors;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(Ctors));
      Contract.Invariant(1 <= Ctors.Count);
    }

    public DatatypeDecl(string name, ModuleDefinition module, List<TypeParameter> typeArgs,
      [Captured] List<DatatypeCtor> ctors, List<MemberDecl> members, Attributes attributes)
      : base(name, module, typeArgs, members, attributes) {
      Contract.Requires(name != null);
      Contract.Requires(module != null);
      Contract.Requires(cce.NonNullElements(typeArgs));
      Contract.Requires(cce.NonNullElements(ctors));
      Contract.Requires(cce.NonNullElements(members));
      Contract.Requires(1 <= ctors.Count);
      Ctors = ctors;
      this.NewSelfSynonym();
    }
    public bool HasFinitePossibleValues {
      get {
        return (TypeArgs.Count == 0 && Ctors.TrueForAll(ctr => ctr.Formals.Count == 0));
      }
    }

    public bool IsRecordType {
      get { return this is IndDatatypeDecl && Ctors.Count == 1; }
    }

    TopLevelDecl RevealableTypeDecl.AsTopLevelDecl { get { return this; } }

    List<TypeParameter> ICodeContext.TypeArgs { get { return TypeArgs; } }
    List<Formal> ICodeContext.Ins { get { return new List<Formal>(); } }
    ModuleDefinition ICodeContext.EnclosingModule { get { return Module; } }
    string ICallable.NameRelativeToModule { get { return Name; } }
  }

  public class IndDatatypeDecl : DatatypeDecl, RevealableTypeDecl
  {
    public override string WhatKind { get { return "datatype"; } }
    public DatatypeCtor DefaultCtor;  // set during resolution
    public bool[] TypeParametersUsedInConstructionByDefaultCtor;  // set during resolution; has same length as the number of type arguments

    public enum ES { Never, ConsultTypeArguments }
    public ES EqualitySupport;

    public IndDatatypeDecl(string name, ModuleDefinition module, List<TypeParameter> typeArgs,
      [Captured] List<DatatypeCtor> ctors, List<MemberDecl> members, Attributes attributes)
      : base(name, module, typeArgs, ctors, members, attributes) {
      Contract.Requires(name != null);
      Contract.Requires(module != null);
      Contract.Requires(cce.NonNullElements(typeArgs));
      Contract.Requires(cce.NonNullElements(ctors));
      Contract.Requires(cce.NonNullElements(members));
      Contract.Requires(1 <= ctors.Count);
    }
  }

  public class TupleTypeDecl : IndDatatypeDecl
  {
    public readonly int Dims;
    /// <summary>
    /// Construct a resolved built-in tuple type with "dim" arguments.  "systemModule" is expected to be the _System module.
    /// </summary>
    public TupleTypeDecl(int dims, ModuleDefinition systemModule, Attributes attributes)
      : this(systemModule, CreateCovariantTypeParameters(dims), attributes) {
      Contract.Requires(0 <= dims);
      Contract.Requires(systemModule != null);
    }

    private TupleTypeDecl(ModuleDefinition systemModule, List<TypeParameter> typeArgs, Attributes attributes)
      : base(BuiltIns.TupleTypeName(typeArgs.Count), systemModule, typeArgs, CreateConstructors(typeArgs), new List<MemberDecl>(), attributes) {
      Contract.Requires(systemModule != null);
      Contract.Requires(typeArgs != null);
      Dims = typeArgs.Count;
      foreach (var ctor in Ctors) {
        ctor.EnclosingDatatype = this;  // resolve here
        DefaultCtor = ctor;
        TypeParametersUsedInConstructionByDefaultCtor = new bool[typeArgs.Count];
        for (int i = 0; i < typeArgs.Count; i++) {
          TypeParametersUsedInConstructionByDefaultCtor[i] = true;
        }
      }
      this.EqualitySupport = ES.ConsultTypeArguments;
    }
    private static List<TypeParameter> CreateCovariantTypeParameters(int dims) {
      Contract.Requires(0 <= dims);
      var ts = new List<TypeParameter>();
      for (int i = 0; i < dims; i++) {
        var tp = new TypeParameter("T" + i, TypeParameter.TPVarianceSyntax.Covariant_Strict);
        tp.NecessaryForEqualitySupportOfSurroundingInductiveDatatype = true;
        ts.Add(tp);
      }
      return ts;
    }
    private static List<DatatypeCtor> CreateConstructors(List<TypeParameter> typeArgs) {
      Contract.Requires(typeArgs != null);
      var formals = new List<Formal>();
      for (int i = 0; i < typeArgs.Count; i++) {
        var tp = typeArgs[i];
        var f = new Formal(i.ToString(), new UserDefinedType(tp), true, false);
        formals.Add(f);
      }
      var ctor = new DatatypeCtor(BuiltIns.TupleTypeCtorNamePrefix + typeArgs.Count, formals, null);
      return new List<DatatypeCtor>() { ctor };
    }

    public override string CompileName {
      get {
        return "Tuple" + Dims;
      }
    }
  }

  public class CoDatatypeDecl : DatatypeDecl
  {
    public override string WhatKind { get { return "codatatype"; } }
    public CoDatatypeDecl SscRepr;  // filled in during resolution

    public CoDatatypeDecl(string name, ModuleDefinition module, List<TypeParameter> typeArgs,
      [Captured] List<DatatypeCtor> ctors, List<MemberDecl> members, Attributes attributes)
      : base(name, module, typeArgs, ctors, members, attributes) {
      Contract.Requires(name != null);
      Contract.Requires(module != null);
      Contract.Requires(cce.NonNullElements(typeArgs));
      Contract.Requires(cce.NonNullElements(ctors));
      Contract.Requires(cce.NonNullElements(members));
      Contract.Requires(1 <= ctors.Count);
    }
  }

  /// <summary>
  /// The "ValuetypeDecl" class models the built-in value types (like bool, int, set, and seq.
  /// Its primary function is to hold the formal type parameters and built-in members of these types.
  /// </summary>
  public class ValuetypeDecl : TopLevelDecl
  {
    public override string WhatKind { get { return Name; } }
    public readonly Dictionary<string, MemberDecl> Members = new Dictionary<string, MemberDecl>();
    readonly Func<Type, bool> typeTester;
    readonly Func<List<Type>, Type>/*?*/ typeCreator;

    public ValuetypeDecl(string name, ModuleDefinition module, int typeParameterCount, Func<Type, bool> typeTester, Func<List<Type>, Type>/*?*/ typeCreator)
      : base(name, module, new List<TypeParameter>(), null) {
      Contract.Requires(name != null);
      Contract.Requires(module != null);
      Contract.Requires(0 <= typeParameterCount);
      Contract.Requires(typeTester != null);
      // fill in the type parameters
      for (int i = 0; i < typeParameterCount; i++) {
        TypeArgs.Add(new TypeParameter(((char)('T' + i)).ToString(), i, this));
      }
      this.typeTester = typeTester;
      this.typeCreator = typeCreator;
    }

    public bool IsThisType(Type t) {
      Contract.Assert(t != null);
      return typeTester(t);
    }

    public Type CreateType(List<Type> typeArgs) {
      Contract.Requires(typeArgs != null);
      Contract.Requires(typeArgs.Count == TypeArgs.Count);
      Contract.Assume(typeCreator != null);  // can only call CreateType for a ValuetypeDecl with a type creator (this is up to the caller to ensure)
      return typeCreator(typeArgs);
    }
  }

  public class DatatypeCtor : Declaration, TypeParameter.ParentType
  {
    public readonly List<Formal> Formals;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(Formals));
      Contract.Invariant(Destructors != null);
      Contract.Invariant(
        Destructors.Count == 0 || // this is until resolution
        Destructors.Count == Formals.Count);  // after resolution
    }

    // TODO: One could imagine having a precondition on datatype constructors
    public DatatypeDecl EnclosingDatatype;  // filled in during resolution
    public SpecialField QueryField;  // filled in during resolution
    public List<DatatypeDestructor> Destructors = new List<DatatypeDestructor>();  // contents filled in during resolution; includes both implicit (not mentionable in source) and explicit destructors

    public DatatypeCtor(string name, [Captured] List<Formal> formals, Attributes attributes)
      : base(name, attributes) {
      Contract.Requires(name != null);
      Contract.Requires(cce.NonNullElements(formals));
      this.Formals = formals;
    }

    public string FullName {
      get {
        Contract.Ensures(Contract.Result<string>() != null);
        Contract.Assume(EnclosingDatatype != null);

        return "#" + EnclosingDatatype.FullName + "." + Name;
      }
    }
  }

  /// <summary>
  /// An ICodeContext is an ICallable or a NoContext.
  /// </summary>
  public interface ICodeContext
  {
    List<TypeParameter> TypeArgs { get; }
    List<Formal> Ins { get; }
    ModuleDefinition EnclosingModule { get; }  // to be called only after signature-resolution is complete
    string FullSanitizedName { get; }
  }
  /// <summary>
  /// An ICallable is a Function, Method, IteratorDecl, or (less fitting for the name ICallable) RedirectingTypeDecl or DatatypeDecl.
  /// </summary>
  public interface ICallable : ICodeContext
  {
    string WhatKind { get; }
    string NameRelativeToModule { get; }
  }

  public class DontUseICallable : ICallable
  {
    public string WhatKind { get { throw new cce.UnreachableException(); } }
    public List<TypeParameter> TypeArgs { get { throw new cce.UnreachableException(); } }
    public List<Formal> Ins { get { throw new cce.UnreachableException(); } }
    public ModuleDefinition EnclosingModule { get { throw new cce.UnreachableException(); } }
    public string FullSanitizedName { get { throw new cce.UnreachableException(); } }
    public string NameRelativeToModule { get { throw new cce.UnreachableException(); } }
  }
  /// <summary>
  /// An IMethodCodeContext is a Method or IteratorDecl.
  /// </summary>
  public interface IMethodCodeContext : ICallable
  {
    List<Formal> Outs { get; }
  }

  /// <summary>
  /// Applies when we are not inside an ICallable.  In particular, a NoContext is used to resolve the attributes of declarations with no other context.
  /// </summary>
  public class NoContext : ICodeContext
  {
    public readonly ModuleDefinition Module;
    public NoContext(ModuleDefinition module)
    {
      this.Module = module;
    }
    List<TypeParameter> ICodeContext.TypeArgs { get { return new List<TypeParameter>(); } }
    List<Formal> ICodeContext.Ins { get { return new List<Formal>(); } }
    ModuleDefinition ICodeContext.EnclosingModule { get { return Module; } }
    public string FullSanitizedName { get { Contract.Assume(false, "should not be called on NoContext"); throw new cce.UnreachableException(); } }
  }

  public class IteratorDecl : ClassDecl, IMethodCodeContext
  {
    public override string WhatKind { get { return "iterator"; } }
    public readonly List<Formal> Ins;
    public readonly List<Formal> Outs;
    public readonly BlockStmt Body;
    public readonly bool SignatureIsOmitted;
    public readonly List<Field> OutsFields;
    public readonly List<Field> OutsHistoryFields;  // these are the 'xs' variables
    public SpecialField Member_New;  // filled in during resolution
    public Constructor Member_Init;  // created during registration phase of resolution; its specification is filled in during resolution
    public Predicate Member_Valid;  // created during registration phase of resolution; its specification is filled in during resolution
    public Method Member_MoveNext;  // created during registration phase of resolution; its specification is filled in during resolution
    public readonly LocalVariable YieldCountVariable;

    public IteratorDecl(string name, ModuleDefinition module, List<TypeParameter> typeArgs,
                        List<Formal> ins, List<Formal> outs,
                        BlockStmt body, Attributes attributes, bool signatureIsOmitted)
      : base(name, module, MutateIntoRequiringZeroInitBit(typeArgs), new List<MemberDecl>(), attributes, null)
    {
      Contract.Requires(name != null);
      Contract.Requires(module != null);
      Contract.Requires(typeArgs != null);
      Contract.Requires(ins != null);
      Contract.Requires(outs != null);
      Ins = ins;
      Outs = outs;
      Body = body;
      SignatureIsOmitted = signatureIsOmitted;

      OutsFields = new List<Field>();
      OutsHistoryFields = new List<Field>();
    }

    private static List<TypeParameter> MutateIntoRequiringZeroInitBit(List<TypeParameter> typeArgs) {
      Contract.Requires(typeArgs != null);
      Contract.Ensures(Contract.Result<List<TypeParameter>>() == typeArgs);
      // Note! This is not the only place where IteratorDecl type parameters come through.  Some may
      // be created by "FillInTypeArguments".
      foreach (var tp in typeArgs) {
        tp.Characteristics.MustSupportZeroInitialization = true;
      }
      return typeArgs;
    }

    /// <summary>
    /// Returns the non-null expressions of this declaration proper (that is, do not include the expressions of substatements).
    /// Does not include the generated class members.
    /// </summary>
    public virtual IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in Attributes.SubExpressions(Attributes)) {
          yield return e;
        }
      }
    }

    /// <summary>
    /// This Dafny type exists only for the purpose of giving the yield-count variable a type, so
    /// that the type can be recognized during translation of Dafny into Boogie.  It represents
    /// an integer component in a "decreases" clause whose order is (\lambda x,y :: x GREATER y),
    /// not the usual (\lambda x,y :: x LESS y AND 0 ATMOST y).
    /// </summary>
    public class EverIncreasingType : BasicType
    {
      [Pure]
      public override string TypeName(ModuleDefinition context, bool parseAble) {
        Contract.Assert(parseAble == false);

        return "_increasingInt";
      }
      public override bool Equals(Type that) {
        return that.NormalizeExpand() is EverIncreasingType;
      }
    }

    List<TypeParameter> ICodeContext.TypeArgs { get { return this.TypeArgs; } }
    List<Formal> ICodeContext.Ins { get { return this.Ins; } }
    List<Formal> IMethodCodeContext.Outs { get { return this.Outs; } }
    string ICallable.NameRelativeToModule { get { return this.Name; } }

    ModuleDefinition ICodeContext.EnclosingModule { get { return this.Module; } }
  }

  public abstract class MemberDecl : Declaration {
    public abstract string WhatKind { get; }
    public readonly bool HasStaticKeyword;
    public virtual bool IsStatic {
      get {
        return HasStaticKeyword || (EnclosingClass is ClassDecl && ((ClassDecl)EnclosingClass).IsDefaultClass);
      }
    }
    public bool IsInstanceIndependentConstant {
      get {
        var cf = this as ConstantField;
        return cf != null && cf.Rhs != null;
      }
    }

    public TopLevelDecl EnclosingClass;  // filled in during resolution
    public MemberDecl RefinementBase;  // filled in during the pre-resolution refinement transformation; null if the member is new here
    public MemberDecl(string name, bool hasStaticKeyword, Attributes attributes)
      : base(name, attributes) {
      Contract.Requires(name != null);
      HasStaticKeyword = hasStaticKeyword;
    }
    /// <summary>
    /// Returns className+"."+memberName.  Available only after resolution.
    /// </summary>
    public virtual string FullName {
      get {
        Contract.Requires(EnclosingClass != null);
        Contract.Ensures(Contract.Result<string>() != null);

        return EnclosingClass.FullName + "." + Name;
      }
    }
    public virtual string FullSanitizedName {
      get {
        Contract.Requires(EnclosingClass != null);
        Contract.Ensures(Contract.Result<string>() != null);

        if (Name == "requires") {
          return Translator.Requires(((ArrowTypeDecl)EnclosingClass).Arity);
        } else if (Name == "reads") {
          return Translator.Reads(((ArrowTypeDecl)EnclosingClass).Arity);
        } else {
          return EnclosingClass.FullSanitizedName + "." + CompileName;
        }
      }
    }
    public virtual string FullSanitizedRefinementName {
      get {
        Contract.Requires(EnclosingClass != null);
        Contract.Ensures(Contract.Result<string>() != null);

        if (Name == "requires") {
          return Translator.Requires(((ArrowTypeDecl)EnclosingClass).Arity);
        } else if (Name == "reads") {
          return Translator.Reads(((ArrowTypeDecl)EnclosingClass).Arity);
        } else {
          return EnclosingClass.FullSanitizedRefinementName + "." + CompileName;
        }
      }
    }
    public virtual string FullNameInContext(ModuleDefinition context) {
      Contract.Requires(EnclosingClass != null);
      Contract.Ensures(Contract.Result<string>() != null);

      return EnclosingClass.FullNameInContext(context) + "." + Name;
    }
    public override string CompileName {
      get {
        var nm = base.CompileName;
        if (this.Name == EnclosingClass.Name) {
          nm = "_" + nm;
        }
        return nm;
      }
    }
    public virtual string FullCompileName {
      get {
        Contract.Requires(EnclosingClass != null);
        Contract.Ensures(Contract.Result<string>() != null);

        return EnclosingClass.FullCompileName + "." + Declaration.IdProtect(CompileName);
      }
    }
    public virtual IEnumerable<Expression> SubExpressions {
      get {
        yield break;
      }
    }
  }

  public class Field : MemberDecl {
    public override string WhatKind { get { return "field"; } }
    public readonly bool IsMutable;  // says whether or not the field can ever change values
    public readonly bool IsUserMutable;  // says whether or not code is allowed to assign to the field (IsUserMutable implies IsMutable)
    public readonly Type Type;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Type != null);
      Contract.Invariant(!IsUserMutable || IsMutable);  // IsUserMutable ==> IsMutable
    }

    public Field(string name, Type type, Attributes attributes)
      : this(name, false, true, true, type, attributes) {
      Contract.Requires(name != null);
      Contract.Requires(type != null);
    }

    public Field(string name, bool hasStaticKeyword, bool isMutable, bool isUserMutable, Type type, Attributes attributes)
      : base(name, hasStaticKeyword, attributes) {
      Contract.Requires(name != null);
      Contract.Requires(type != null);
      Contract.Requires(!isUserMutable || isMutable);
      IsMutable = isMutable;
      IsUserMutable = isUserMutable;
      Type = type;
    }
  }

  public class SpecialFunction : Function, ICodeContext, ICallable
  {
    readonly ModuleDefinition Module;
    public SpecialFunction(string name, ModuleDefinition module, bool hasStaticKeyword, bool isProtected,
                    List<TypeParameter> typeArgs, List<Formal> formals, Type resultType,
                    Expression body, Attributes attributes)
      : base(name, hasStaticKeyword, isProtected, typeArgs, formals, null, resultType, body, attributes)
    {
      Module = module;
    }
    ModuleDefinition ICodeContext.EnclosingModule { get { return this.Module; } }
    string ICallable.NameRelativeToModule { get { return Name; } }
  }

  public class SpecialField : Field
  {
    public enum ID {
      UseIdParam,  // IdParam is a string
      ArrayLength,  // IdParam is null for .Length; IdParam is an int "x" for GetLength(x)
      ArrayLengthInt,  // same as ArrayLength, but produces int instead of BigInteger
      Floor,
      IsLimit,
      IsSucc,
      Offset,
      IsNat,
      Keys,
      Values,
      Items,
      Reads,
      Modifies,
      New,
    }
    public readonly ID SpecialId;
    public readonly object IdParam;
    public SpecialField(string name, ID specialId, object idParam, bool isMutable, bool isUserMutable, Type type, Attributes attributes)
      : this(name, specialId, idParam, false, isMutable, isUserMutable, type, attributes) {
      Contract.Requires(name != null);
      Contract.Requires(!isUserMutable || isMutable);
      Contract.Requires(type != null);
    }

    public SpecialField(string name, ID specialId, object idParam, bool hasStaticKeyword, bool isMutable, bool isUserMutable, Type type, Attributes attributes)
      : base(name, hasStaticKeyword, isMutable, isUserMutable, type, attributes) {
      Contract.Requires(name != null);
      Contract.Requires(!isUserMutable || isMutable);
      Contract.Requires(type != null);

      SpecialId = specialId;
      IdParam = idParam;
    }

    public override string FullName {
      get {
        Contract.Ensures(Contract.Result<string>() != null);
        return EnclosingClass != null ? EnclosingClass.FullName + "." + Name : Name;
      }
    }

    public override string FullSanitizedName {
      get {
        Contract.Ensures(Contract.Result<string>() != null);
        return EnclosingClass != null ? EnclosingClass.FullSanitizedName + "." + CompileName : CompileName;
      }
    }

    public override string FullSanitizedRefinementName {
      get{
        Contract.Ensures(Contract.Result<string>() != null);
        return EnclosingClass != null ? EnclosingClass.FullSanitizedRefinementName + "." + CompileName : CompileName;
      }
    }

    public override string FullNameInContext(ModuleDefinition context) {
      Contract.Ensures(Contract.Result<string>() != null);
      return EnclosingClass != null ? EnclosingClass.FullNameInContext(context) + "." + Name : Name;
    }

    public override string CompileName {
      get {
        Contract.Ensures(Contract.Result<string>() != null);
        return EnclosingClass != null ? base.CompileName : Name;
      }
    }

    public override string FullCompileName {
      get {
        Contract.Ensures(Contract.Result<string>() != null);
        var cn = Declaration.IdProtect(CompileName);
        return EnclosingClass != null ? EnclosingClass.FullCompileName + "." + cn : cn;
      }
    }
  }

  public class DatatypeDestructor : SpecialField
  {
    public readonly List<DatatypeCtor> EnclosingCtors = new List<DatatypeCtor>();  // is always a nonempty list
    public readonly List<Formal> CorrespondingFormals = new List<Formal>();  // is always a nonempty list
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(EnclosingCtors != null);
      Contract.Invariant(CorrespondingFormals != null);
      Contract.Invariant(EnclosingCtors.Count > 0);
      Contract.Invariant(EnclosingCtors.Count == CorrespondingFormals.Count);
    }

    public DatatypeDestructor(DatatypeCtor enclosingCtor, Formal correspondingFormal, string name, string compiledName, bool isGhost, Type type, Attributes attributes)
      : base(name, SpecialField.ID.UseIdParam, compiledName, isGhost, false, false, type, attributes)
    {
      Contract.Requires(enclosingCtor != null);
      Contract.Requires(correspondingFormal != null);
      Contract.Requires(name != null);
      Contract.Requires(type != null);
      EnclosingCtors.Add(enclosingCtor);  // more enclosing constructors may be added later during resolution
      CorrespondingFormals.Add(correspondingFormal);  // more corresponding formals may be added later during resolution
    }

    /// <summary>
    /// To be called only by the resolver. Called to share this datatype destructor between multiple constructors
    /// of the same datatype.
    /// </summary>
    internal void AddAnotherEnclosingCtor(DatatypeCtor ctor, Formal formal) {
      Contract.Requires(ctor != null);
      Contract.Requires(formal != null);
      EnclosingCtors.Add(ctor);  // more enclosing constructors may be added later during resolution
      CorrespondingFormals.Add(formal);  // more corresponding formals may be added later during resolution
    }

    internal string EnclosingCtorNames(string grammaticalConjunction) {
      Contract.Requires(grammaticalConjunction != null);
      return PrintableCtorNameList(EnclosingCtors, grammaticalConjunction);
    }

    static internal string PrintableCtorNameList(List<DatatypeCtor> ctors, string grammaticalConjunction) {
      Contract.Requires(ctors != null);
      Contract.Requires(grammaticalConjunction != null);
      var n = ctors.Count;
      if (n == 1) {
        return string.Format("'{0}'", ctors[0].Name);
      } else if (n == 2) {
        return string.Format("'{0}' {1} '{2}'", ctors[0].Name, grammaticalConjunction, ctors[1].Name);
      } else {
        var s = "";
        for (int i = 0; i < n - 1; i++) {
          s += string.Format("'{0}', ", ctors[i].Name);
        }
        return s + string.Format("{0} '{1}'", grammaticalConjunction, ctors[n - 1].Name);
      }
    }
  }

  public class ConstantField : SpecialField, ICallable
  {
    public override string WhatKind { get { return "const field"; } }
    public readonly Expression Rhs;
    public ConstantField(string name, Expression/*?*/ rhs, bool hasStaticKeyword, Type type, Attributes attributes)
      : base(name, SpecialField.ID.UseIdParam, NonglobalVariable.CompilerizeName(name), hasStaticKeyword, false, false, type, attributes)
    {
      Contract.Requires(name != null);
      Contract.Requires(type != null);
      this.Rhs = rhs;
    }

    public override bool CanBeRevealed() {
      return true;
    }

    //
    public List<TypeParameter> TypeArgs { get { return new List<TypeParameter>(); } }
    public List<Formal> Ins { get { return new List<Formal>(); } }
    public ModuleDefinition EnclosingModule { get { return this.EnclosingClass.Module; } }
    public bool MustReverify { get { return false; } }
    public bool AllowsNontermination { get { throw new cce.UnreachableException(); } }
    public string NameRelativeToModule {
      get {
        if (EnclosingClass is DefaultClassDecl) {
          return Name;
        } else {
          return EnclosingClass.Name + "." + Name;
        }
      }
    }
    public Specification<Expression> Decreases { get { throw new cce.UnreachableException(); } }
    public bool InferredDecreases
    {
      get { throw new cce.UnreachableException(); }
      set { throw new cce.UnreachableException(); }
    }
  }

  public class OpaqueTypeDecl : TopLevelDecl, TypeParameter.ParentType, RevealableTypeDecl
  {
    public override string WhatKind { get { return "opaque type"; } }
    public override bool CanBeRevealed() { return true; }
    public readonly TypeParameter TheType;
    public TypeParameter.TypeParameterCharacteristics Characteristics {
      get { return TheType.Characteristics; }
    }
    public bool MustSupportEquality {
      get { return TheType.MustSupportEquality; }
    }
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(TheType != null && Name == TheType.Name);
    }

    public OpaqueTypeDecl(string name, ModuleDefinition module, TypeParameter.TypeParameterCharacteristics characteristics, List<TypeParameter> typeArgs, Attributes attributes)
      : base(name, module, typeArgs, attributes) {
      Contract.Requires(name != null);
      Contract.Requires(module != null);
      Contract.Requires(typeArgs != null);
      TheType = new OpaqueType_AsParameter(name, characteristics, TypeArgs);
      this.NewSelfSynonym();
    }

    public TopLevelDecl AsTopLevelDecl {
      get { return this; }
    }

    public bool SupportsEquality {
      get { return this.MustSupportEquality; }
    }
  }

  public interface RedirectingTypeDecl : ICallable
  {
    string Name { get; }

    Attributes Attributes { get; }
    ModuleDefinition Module { get; }
    Type Rhs { get; }
    SubsetTypeDecl.WKind WitnessKind { get; }
    Expression/*?*/ Witness { get; }  // non-null iff WitnessKind is Compiled
    FreshIdGenerator IdGenerator { get; }
  }

  public static class RevealableTypeDeclHelper {
    private static Dictionary<TopLevelDecl, InternalTypeSynonymDecl> tsdMap = new Dictionary<TopLevelDecl, InternalTypeSynonymDecl>();

    public static void NewSelfSynonym(this RevealableTypeDecl rtd) {
      var d = rtd.AsTopLevelDecl;
      Contract.Assert(!tsdMap.ContainsKey(d));

      var thisType = UserDefinedType.FromTopLevelDecl(d);
      if (d is OpaqueTypeDecl) {
        thisType.ResolvedParam = ((OpaqueTypeDecl)d).TheType;
      }

      var tsd = new InternalTypeSynonymDecl(d.Name, TypeParameter.GetExplicitCharacteristics(d), d.TypeArgs, d.Module, thisType, d.Attributes);
      tsd.InheritVisibility(d, false);

      tsdMap.Add(d, tsd);
    }

    public static UserDefinedType SelfSynonym(this RevealableTypeDecl rtd, List<Type> args) {
      Contract.Requires(args != null);
      var d = rtd.AsTopLevelDecl;
      Contract.Assert(tsdMap.ContainsKey(d));
      var typeSynonym = tsdMap[d];
      Contract.Assert(typeSynonym.TypeArgs.Count == args.Count);
      return new UserDefinedType(typeSynonym.Name, typeSynonym, args);
    }

    public static InternalTypeSynonymDecl SelfSynonymDecl(this RevealableTypeDecl rtd) {
      var d = rtd.AsTopLevelDecl;
      Contract.Assert(tsdMap.ContainsKey(d));
      return tsdMap[d];
    }

    public static TopLevelDecl AccessibleDecl(this RevealableTypeDecl rtd, VisibilityScope scope) {
      var d = rtd.AsTopLevelDecl;
      if (d.IsRevealedInScope(scope)) {
        return d;
      } else {
        return rtd.SelfSynonymDecl();
      }
    }

    //Internal implementations are called before extensions, so this is safe
    public static bool IsRevealedInScope(this RevealableTypeDecl rtd, VisibilityScope scope) {
      var d = rtd.AsTopLevelDecl;
      return d.IsRevealedInScope(scope);
    }
  }

  public interface RevealableTypeDecl {
    TopLevelDecl AsTopLevelDecl {get; }
  }

  public class NewtypeDecl : TopLevelDeclWithMembers, RevealableTypeDecl, RedirectingTypeDecl
  {
    public override string WhatKind { get { return "newtype"; } }
    public override bool CanBeRevealed() { return true; }
    public readonly Type BaseType;
    public readonly SubsetTypeDecl.WKind WitnessKind = SubsetTypeDecl.WKind.None;
    public readonly Expression/*?*/ Witness;  // non-null iff WitnessKind is Compiled or Ghost
    public NativeType NativeType; // non-null for fixed-size representations (otherwise, use BigIntegers for integers)
    public NewtypeDecl(string name, ModuleDefinition module, Type baseType, SubsetTypeDecl.WKind witnessKind, Expression witness, List<MemberDecl> members, Attributes attributes)
      : base(name, module, new List<TypeParameter>(), members, attributes) {
      Contract.Requires(name != null);
      Contract.Requires(module != null);
      Contract.Requires(baseType != null);
      Contract.Requires((witnessKind == SubsetTypeDecl.WKind.Compiled || witnessKind == SubsetTypeDecl.WKind.Ghost) == (witness != null));
      Contract.Requires(members != null);
      BaseType = baseType;
      Witness = witness;
      WitnessKind = witnessKind;
      this.NewSelfSynonym();
    }

    TopLevelDecl RevealableTypeDecl.AsTopLevelDecl { get { return this; } }
    public TypeParameter.EqualitySupportValue EqualitySupport {
      get {
        if (this.BaseType.SupportsEquality) {
          return TypeParameter.EqualitySupportValue.Required;
        } else {
          return TypeParameter.EqualitySupportValue.Unspecified;
        }
      }
    }

    string RedirectingTypeDecl.Name { get { return Name; } }
    Attributes RedirectingTypeDecl.Attributes { get { return Attributes; } }
    ModuleDefinition RedirectingTypeDecl.Module { get { return Module; } }
    Type RedirectingTypeDecl.Rhs { get { return BaseType; } }
    SubsetTypeDecl.WKind RedirectingTypeDecl.WitnessKind { get { return WitnessKind; } }
    Expression RedirectingTypeDecl.Witness { get { return Witness; } }
    FreshIdGenerator RedirectingTypeDecl.IdGenerator { get { return IdGenerator; } }

    List<TypeParameter> ICodeContext.TypeArgs { get { return new List<TypeParameter>(); } }
    List<Formal> ICodeContext.Ins { get { return new List<Formal>(); } }
    ModuleDefinition ICodeContext.EnclosingModule { get { return Module; } }
    string ICallable.NameRelativeToModule { get { return Name; } }
  }


  public abstract class TypeSynonymDeclBase : TopLevelDecl, RedirectingTypeDecl
  {
    public override string WhatKind { get { return "type synonym"; } }
    public TypeParameter.TypeParameterCharacteristics Characteristics;  // the resolver may change the .EqualitySupport component of this value from Unspecified to InferredRequired (for some signatures that may immediately imply that equality support is required)
    public bool MustSupportEquality {
      get { return Characteristics.EqualitySupport != TypeParameter.EqualitySupportValue.Unspecified; }
    }
    public readonly Type Rhs;
    public TypeSynonymDeclBase(string name, TypeParameter.TypeParameterCharacteristics characteristics, List<TypeParameter> typeArgs, ModuleDefinition module, Type rhs, Attributes attributes)
      : base(name, module, typeArgs, attributes) {
      Contract.Requires(name != null);
      Contract.Requires(typeArgs != null);
      Contract.Requires(module != null);
      Contract.Requires(rhs != null);
      Characteristics = characteristics;
      Rhs = rhs;
    }
    /// <summary>
    /// Return .Rhs instantiated with "typeArgs", but only look at the part of .Rhs that is in scope.
    /// </summary>
    public Type RhsWithArgument(List<Type> typeArgs) {
      Contract.Requires(typeArgs != null);
      Contract.Requires(typeArgs.Count == TypeArgs.Count);
      var scope = Type.GetScope();
      var rtd = Rhs.AsRevealableType;
      if (rtd != null) {
        Contract.Assume(rtd.AsTopLevelDecl.IsVisibleInScope(scope));
        if (!rtd.IsRevealedInScope(scope)) {
          // type is actually hidden in this scope
          return rtd.SelfSynonym(typeArgs);
        }
      }
      return RhsWithArgumentIgnoringScope(typeArgs);
    }
    /// <summary>
    /// Returns the declared .Rhs but with formal type arguments replaced by the given actuals.
    /// </summary>
    public Type RhsWithArgumentIgnoringScope(List<Type> typeArgs) {
      Contract.Requires(typeArgs != null);
      Contract.Requires(typeArgs.Count == TypeArgs.Count);
      // Instantiate with the actual type arguments
      if (typeArgs.Count == 0) {
        // this optimization seems worthwhile
        return Rhs;
      } else {
        var subst = Util.Dict(TypeArgs, typeArgs);
        return Rhs.Subst(subst);
      }
    }

    string RedirectingTypeDecl.Name { get { return Name; } }
    Attributes RedirectingTypeDecl.Attributes { get { return Attributes; } }
    ModuleDefinition RedirectingTypeDecl.Module { get { return Module; } }
    Type RedirectingTypeDecl.Rhs { get { return Rhs; } }
    SubsetTypeDecl.WKind RedirectingTypeDecl.WitnessKind { get { return SubsetTypeDecl.WKind.None; } }
    Expression RedirectingTypeDecl.Witness { get { return null; } }
    FreshIdGenerator RedirectingTypeDecl.IdGenerator { get { return IdGenerator; } }

    List<TypeParameter> ICodeContext.TypeArgs { get { return TypeArgs; } }
    List<Formal> ICodeContext.Ins { get { return new List<Formal>(); } }
    ModuleDefinition ICodeContext.EnclosingModule { get { return Module; } }
    string ICallable.NameRelativeToModule { get { return Name; } }
    public override bool CanBeRevealed() {
      return true;
    }
  }

  public class TypeSynonymDecl : TypeSynonymDeclBase, RedirectingTypeDecl, RevealableTypeDecl {
    public TypeSynonymDecl(string name, TypeParameter.TypeParameterCharacteristics characteristics, List<TypeParameter> typeArgs, ModuleDefinition module, Type rhs, Attributes attributes)
      : base(name, characteristics, typeArgs, module, rhs, attributes) {
        this.NewSelfSynonym();
    }
    TopLevelDecl RevealableTypeDecl.AsTopLevelDecl { get { return this; } }
  }

  public class InternalTypeSynonymDecl : TypeSynonymDeclBase, RedirectingTypeDecl {
    public InternalTypeSynonymDecl(string name, TypeParameter.TypeParameterCharacteristics characteristics, List<TypeParameter> typeArgs, ModuleDefinition module, Type rhs, Attributes attributes)
      : base(name, characteristics, typeArgs, module, rhs, attributes) {
    }
  }



  public class SubsetTypeDecl : TypeSynonymDecl, RedirectingTypeDecl
  {
    public override string WhatKind { get { return "subset type"; } }
    public enum WKind { None, Compiled, Ghost, Special }
    public readonly SubsetTypeDecl.WKind WitnessKind;
    public readonly Expression/*?*/ Witness;  // non-null iff WitnessKind is Compiled or Ghost
    public SubsetTypeDecl(string name, TypeParameter.TypeParameterCharacteristics characteristics, List<TypeParameter> typeArgs, ModuleDefinition module,
      Type rhs, WKind witnessKind, Expression witness,
      Attributes attributes)
      : base(name, characteristics, typeArgs, module, rhs, attributes) {
      Contract.Requires(name != null);
      Contract.Requires(typeArgs != null);
      Contract.Requires(module != null);
      Contract.Requires(rhs != null);
      Contract.Requires((witnessKind == WKind.Compiled || witnessKind == WKind.Ghost) == (witness != null));
      Witness = witness;
      WitnessKind = witnessKind;
    }
    Type RedirectingTypeDecl.Rhs { get { return Rhs; } }
    WKind RedirectingTypeDecl.WitnessKind { get { return WitnessKind; } }
    Expression RedirectingTypeDecl.Witness { get { return Witness; } }
  }

  public class NonNullTypeDecl : SubsetTypeDecl
  {
    public readonly ClassDecl Class;
    /// <summary>
    /// The public constructor is NonNullTypeDecl(ClassDecl cl). The rest is pretty crazy: There are stages of "this"-constructor calls
    /// in order to build values that depend on previously computed parameters.
    /// </summary>
    public NonNullTypeDecl(ClassDecl cl)
      : this(cl, cl.TypeArgs.ConvertAll(tp => new TypeParameter(tp.Name, tp.VarianceSyntax, tp.Characteristics)))
 {
      Contract.Requires(cl != null);
    }

    private NonNullTypeDecl(ClassDecl cl, List<TypeParameter> tps)
      : this(cl, tps,
      new UserDefinedType(cl.Name + "?", cl, tps.Count == 0 ? null : tps.ConvertAll(tp => (Type)new UserDefinedType(tp))))
    {
      Contract.Requires(cl != null);
      Contract.Requires(tps != null);
    }

    private NonNullTypeDecl(ClassDecl cl, List<TypeParameter> tps, Type baseType)
      : base(cl.Name, new TypeParameter.TypeParameterCharacteristics(), tps, cl.Module, baseType,
      SubsetTypeDecl.WKind.Special, null, BuiltIns.AxiomAttribute())
    {
      Contract.Requires(cl != null);
      Contract.Requires(tps != null);
      Contract.Requires(baseType != null);
      Class = cl;
    }
  }

  [ContractClass(typeof(IVariableContracts))]
  public interface IVariable {
    string Name {
      get;
    }
    string DisplayName {  // what the user thinks he wrote
      get;
    }
    string UniqueName {
      get;
    }
    bool HasBeenAssignedUniqueName {  // unique names are not assigned until the Translator; if you don't already know if that stage has run, this boolean method will tell you
      get;
    }
    string AssignUniqueName(FreshIdGenerator generator);
    string CompileName {
      get;
    }
    Type Type {
      get;
    }
    bool IsMutable {
      get;
    }
  }
  [ContractClassFor(typeof(IVariable))]
  public abstract class IVariableContracts : IVariable {
    public string Name {
      get {
        Contract.Ensures(Contract.Result<string>() != null);
        throw new NotImplementedException();  // this getter implementation is here only so that the Ensures contract can be given here
      }
    }
    public string DisplayName {
      get {
        Contract.Ensures(Contract.Result<string>() != null);
        throw new NotImplementedException();  // this getter implementation is here only so that the Ensures contract can be given here
      }
    }
    public string UniqueName {
      get {
        Contract.Ensures(Contract.Result<string>() != null);
        throw new NotImplementedException();  // this getter implementation is here only so that the Ensures contract can be given here
      }
    }
    public bool HasBeenAssignedUniqueName {
      get {
        throw new NotImplementedException();  // this getter implementation is here only so that the Ensures contract can be given here
      }
    }
    public string CompileName {
      get {
        Contract.Ensures(Contract.Result<string>() != null);
        throw new NotImplementedException();  // this getter implementation is here only so that the Ensures contract can be given here
      }
    }
    public Type Type {
      get {
        Contract.Ensures(Contract.Result<Type>() != null);
        throw new NotImplementedException();  // this getter implementation is here only so that the Ensures contract can be given here
      }
    }
    public Type OptionalType {
      get {
        Contract.Ensures(Contract.Result<Type>() != null);
        throw new NotImplementedException();  // this getter implementation is here only so that the Ensures contract can be given here
      }
    }
    public bool IsMutable {
      get {
        throw new NotImplementedException();
      }
    }
    public string AssignUniqueName(FreshIdGenerator generator)
    {
      Contract.Ensures(Contract.Result<string>() != null);
      throw new NotImplementedException();
    }
  }

  public abstract class NonglobalVariable : IVariable {
    readonly string name;

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(name != null);
      Contract.Invariant(Type != null);
    }

    public string Name {
      get {
        Contract.Ensures(Contract.Result<string>() != null);
        return name;
      }
    }
    public string DisplayName {
      get { return LocalVariable.DisplayNameHelper(this); }
    }
    private string uniqueName;
    public string UniqueName {
      get {
        return uniqueName;
      }
    }
    public bool HasBeenAssignedUniqueName {
      get {
        return uniqueName != null;
      }
    }
    public string AssignUniqueName(FreshIdGenerator generator)
    {
      if (uniqueName == null)
      {
        uniqueName = generator.FreshId(Name + "#");
        compileName = string.Format("_{0}_{1}", Compiler.FreshId(), CompilerizeName(name));
      }
      return UniqueName;
    }
    static char[] specialChars = new char[] { '\'', '_', '?', '\\', '#' };
    public static string CompilerizeName(string nm) {
      if ('0' <= nm[0] && nm[0] <= '9') {
        // the identifier is one that consists of just digits
        return "_" + nm;
      }
      string name = null;
      int i = 0;
      while (true) {
        int j = nm.IndexOfAny(specialChars, i);
        if (j == -1) {
          if (i == 0) {
            return nm;  // this is the common case
          } else {
            return name + nm.Substring(i);
          }
        } else {
          string nxt = nm.Substring(i, j - i);
          name = name == null ? nxt : name + nxt;
          switch (nm[j]) {
            case '\'': name += "_k"; break;
            case '_': name += "__"; break;
            case '?': name += "_q"; break;
            case '\\': name += "_b"; break;
            case '#': name += "_h"; break;
            default:
              Contract.Assume(false);  // unexpected character
              break;
          }
          i = j + 1;
          if (i == nm.Length) {
            return name;
          }
        }
      }
    }
    protected string compileName;
    public virtual string CompileName {
      get {
        if (compileName == null)
        {
          compileName = string.Format("_{0}_{1}", Compiler.FreshId(), CompilerizeName(name));
        }
        return compileName;
      }
    }
    public Type Type;
    Type IVariable.Type => Type;
    public abstract bool IsMutable {
      get;
    }

    public NonglobalVariable(string name, Type type, bool isGhost) {
      Contract.Requires(name != null);
      Contract.Requires(type != null);
      this.name = name;
      this.Type = type;
    }
  }

  public class Formal : NonglobalVariable {
    public readonly bool InParam;  // true to in-parameter, false for out-parameter
    public override bool IsMutable {
      get {
        return !InParam;
      }
    }
    public readonly bool IsOld;

    public Formal(string name, Type type, bool inParam, bool isGhost, bool isOld = false)
      : base(name, type, isGhost) {
      Contract.Requires(name != null);
      Contract.Requires(type != null);
      InParam = inParam;
      IsOld = isOld;
    }

    public bool HasName {
      get {
        return !Name.StartsWith("#");
      }
    }
    public override string CompileName {
      get {
        if (compileName == null) {
          compileName = CompilerizeName(Name);
        }
        return compileName;
      }
    }
  }

  /// <summary>
  /// An ImplicitFormal is a parameter that is declared implicitly, in particular the "_k" depth parameter
  /// of each colemma (for use in the comethod body only, not the specification).
  /// </summary>
  public class ImplicitFormal : Formal {
    public ImplicitFormal(string name, Type type, bool inParam, bool isGhost)
      : base(name, type, inParam, isGhost) {
      Contract.Requires(name != null);
      Contract.Requires(type != null);
    }
  }

  /// <summary>
  /// ThisSurrogate represents the implicit parameter "this". It is used to allow more uniform handling of
  /// parameters. A pointer value of a ThisSurrogate object is not important, only the fact that it is
  /// a ThisSurrogate is. ThisSurrogate objects are only used in specially marked places in the Dafny
  /// implementation.
  /// </summary>
  public class ThisSurrogate : ImplicitFormal {
    public ThisSurrogate(Type type)
      : base("this", type, true, false) {
      Contract.Requires(type != null);
    }
  }

  [DebuggerDisplay("Bound<{name}>")]
  public class BoundVar : NonglobalVariable {
    public override bool IsMutable {
      get {
        return false;
      }
    }

    public BoundVar(string name, Type type)
      : base(name, type, false) {
      Contract.Requires(name != null);
      Contract.Requires(type != null);
    }
  }

  public class Function : MemberDecl, TypeParameter.ParentType, ICallable {
    public override string WhatKind { get { return "function"; } }
    public override bool CanBeRevealed() { return true; }
    public readonly bool IsProtected;
    public bool IsRecursive;  // filled in during resolution
    public bool IsFueled;  // filled in during resolution if anyone tries to adjust this function's fuel
    public readonly List<TypeParameter> TypeArgs;
    public readonly List<Formal> Formals;
    public readonly Formal Result;
    public readonly Type ResultType;
    public readonly List<MaybeFreeExpression> Req;
    public readonly List<FrameExpression> Reads;
    public readonly List<MaybeFreeExpression> Ens;
    public readonly Specification<Expression> Decreases;
    public Expression Body;  // an extended expression; Body is readonly after construction, except for any kind of rewrite that may take place around the time of resolution
    public bool IsBuiltin;
    public Function OverriddenFunction;
    public bool containsQuantifier;
    public bool ContainsQuantifier {
      set { containsQuantifier = value; }
      get { return containsQuantifier;  }
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in Req) {
          yield return e.E;
        }
        foreach (var e in Reads) {
          yield return e.E;
        }
        foreach (var e in Ens) {
          yield return e.E;
        }
        foreach (var e in Decreases.Expressions) {
          yield return e;
        }
        if (Body != null) {
          yield return Body;
        }
      }
    }

    public Type Type {
      get {
        // Note, the following returned type can contain type parameters from the function and its enclosing class
        return new ArrowType(Formals.ConvertAll(f => f.Type), ResultType);
      }
    }

    public bool AllowsNontermination {
      get {
        return Contract.Exists(Decreases.Expressions, e => e is WildcardExpr);
      }
    }

    /// <summary>
    /// The "AllCalls" field is used for non-FixpointPredicate, non-PrefixPredicate functions only (so its value should not be relied upon for FixpointPredicate and PrefixPredicate functions).
    /// It records all function calls made by the Function, including calls made in the body as well as in the specification.
    /// The field is filled in during resolution (and used toward the end of resolution, to attach a helpful "decreases" prefix to functions in clusters
    /// with co-recursive calls.
    /// </summary>
    public readonly List<FunctionCallExpr> AllCalls = new List<FunctionCallExpr>();
    public enum CoCallClusterInvolvement {
      None,  // the SCC containing the function does not involve any co-recursive calls
      IsMutuallyRecursiveTarget,  // the SCC contains co-recursive calls, and this function is the target of some non-self recursive call
      CoRecursiveTargetAllTheWay,  // the SCC contains co-recursive calls, and this function is the target only of self-recursive calls and co-recursive calls
    }
    public CoCallClusterInvolvement CoClusterTarget = CoCallClusterInvolvement.None;

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(TypeArgs));
      Contract.Invariant(cce.NonNullElements(Formals));
      Contract.Invariant(ResultType != null);
      Contract.Invariant(cce.NonNullElements(Req));
      Contract.Invariant(cce.NonNullElements(Reads));
      Contract.Invariant(cce.NonNullElements(Ens));
      Contract.Invariant(Decreases != null);
    }

    /// <summary>
    /// Note, functions are "ghost" by default; a non-ghost function is called a "function method".
    /// </summary>
    public Function(string name, bool hasStaticKeyword, bool isProtected,
                    List<TypeParameter> typeArgs, List<Formal> formals, Formal result, Type resultType,
                    Expression body, Attributes attributes)
      : base(name, hasStaticKeyword, attributes) {
      Contract.Requires(name != null);
      Contract.Requires(cce.NonNullElements(typeArgs));
      Contract.Requires(cce.NonNullElements(formals));
      Contract.Requires(resultType != null);
      this.IsProtected = isProtected;
      this.IsFueled = false;  // Defaults to false.  Only set to true if someone mentions this function in a fuel annotation
      this.TypeArgs = typeArgs;
      this.Formals = formals;
      this.Result = result;
      this.ResultType = result != null ? result.Type : resultType;
      this.Body = body;

      if (attributes != null) {
        List<Expression> args = Attributes.FindExpressions(attributes, "fuel");
        if (args != null) {
          if (args.Count == 1) {
            LiteralExpr literal = args[0] as LiteralExpr;
            if (literal != null && literal.Value is BigInteger) {
              this.IsFueled = true;
            }
          } else if (args.Count == 2) {
            LiteralExpr literalLow = args[0] as LiteralExpr;
            LiteralExpr literalHigh = args[1] as LiteralExpr;

            if (literalLow != null && literalLow.Value is BigInteger && literalHigh != null && literalHigh.Value is BigInteger) {
              this.IsFueled = true;
            }
          }
        }
      }
    }


    List<TypeParameter> ICodeContext.TypeArgs { get { return this.TypeArgs; } }
    List<Formal> ICodeContext.Ins { get { return this.Formals; } }
    string ICallable.NameRelativeToModule {
      get {
        if (EnclosingClass is DefaultClassDecl) {
          return Name;
        } else {
          return EnclosingClass.Name + "." + Name;
        }
      }
    }
    bool _inferredDecr;
    ModuleDefinition ICodeContext.EnclosingModule { get { return this.EnclosingClass.Module; } }

    [Pure]
    public bool IsFuelAware() { return IsRecursive || IsFueled; }
    public virtual bool ReadsHeap { get { return Reads.Count != 0; } }
  }

  public class Predicate : Function
  {
    public override string WhatKind { get { return "predicate"; } }
    public enum BodyOriginKind
    {
      OriginalOrInherited,  // this predicate definition is new (and the predicate may or may not have a body), or the predicate's body (whether or not it exists) is being inherited unmodified (from the previous refinement--it may be that the inherited body was itself an extension, for example)
      DelayedDefinition,  // this predicate declaration provides, for the first time, a body--the declaration refines a previously declared predicate, but the previous one had no body
      Extension  // this predicate extends the definition of a predicate with a body in a module being refined
    }
    public readonly BodyOriginKind BodyOrigin;
    public Predicate(string name, bool hasStaticKeyword, bool isProtected,
                     List<TypeParameter> typeArgs, List<Formal> formals,
                     Expression body, BodyOriginKind bodyOrigin, Attributes attributes)
      : base(name, hasStaticKeyword, isProtected, typeArgs, formals, null, Type.Bool, body, attributes) {
      Contract.Requires(bodyOrigin == Predicate.BodyOriginKind.OriginalOrInherited || body != null);
      BodyOrigin = bodyOrigin;
    }
  }

  public class Method : MemberDecl, TypeParameter.ParentType, IMethodCodeContext
  {
    public override string WhatKind { get { return "method"; } }
    public readonly bool SignatureIsOmitted;
    public bool MustReverify;
    public readonly List<TypeParameter> TypeArgs;
    public readonly List<Formal> Ins;
    public readonly List<Formal> Outs;
    public BlockStmt Body;  // Body is readonly after construction, except for any kind of rewrite that may take place around the time of resolution (note that "methodBody" is a "DividedBlockStmt" for any "Method" that is a "Constructor")
    public bool IsRecursive;  // filled in during resolution
    public bool IsTailRecursive;  // filled in during resolution
    public readonly ISet<IVariable> AssignedAssumptionVariables = new HashSet<IVariable>();
    public Method OverriddenMethod;


    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(TypeArgs));
      Contract.Invariant(cce.NonNullElements(Ins));
      Contract.Invariant(cce.NonNullElements(Outs));
    }

    public Method(string name,
                  bool hasStaticKeyword,
                  [Captured] List<TypeParameter> typeArgs,
                  [Captured] List<Formal> ins, [Captured] List<Formal> outs,
                  [Captured] BlockStmt body,
                  Attributes attributes, bool signatureIsOmitted)
      : base(name, hasStaticKeyword, attributes) {
      Contract.Requires(name != null);
      Contract.Requires(cce.NonNullElements(typeArgs));
      Contract.Requires(cce.NonNullElements(ins));
      Contract.Requires(cce.NonNullElements(outs));
      this.TypeArgs = typeArgs;
      this.Ins = ins;
      this.Outs = outs;
      this.Body = body;
      this.SignatureIsOmitted = signatureIsOmitted;
      MustReverify = false;
    }

    List<TypeParameter> ICodeContext.TypeArgs { get { return this.TypeArgs; } }
    List<Formal> ICodeContext.Ins { get { return this.Ins; } }
    List<Formal> IMethodCodeContext.Outs { get { return this.Outs; } }
    string ICallable.NameRelativeToModule {
      get {
        if (EnclosingClass is DefaultClassDecl) {
          return Name;
        } else {
          return EnclosingClass.Name + "." + Name;
        }
      }
    }

    ModuleDefinition ICodeContext.EnclosingModule {
      get {
        Contract.Assert(this.EnclosingClass != null);  // this getter is supposed to be called only after signature-resolution is complete
        return this.EnclosingClass.Module;
      }
    }

    public override string CompileName {
      get {
        var nm = base.CompileName;
        if (IsStatic && nm == "Main" && !IsMain) {
          // for a static method that is named "Main" but is not a legal "Main" method,
          // change its name.
          nm = EnclosingClass.Name + "_" + nm;
        }
        return nm;
      }
    }

    public bool IsMain {
      get {
        Contract.Requires(EnclosingClass is Core.TopLevelDeclWithMembers);
        // In order to be a legal Main() method, the following must be true:
        //    The method is not a ghost method
        //    The method takes no non-ghost parameters and no type parameters
        //    The enclosing type does not take any type parameters
        //    If the method is an instance (that is, non-static) method in a class, then the enclosing class must not declare any constructor
        // In addition, either:
        //    The method is called "Main"
        //    The method has no requires clause
        //    The method has no modifies clause
        // or:
        //    The method is annotated with {:main}
        // Note, in the case where the method is annotated with {:main}, the method is allowed to have preconditions and modifies clauses.
        // This lets the programmer add some explicit assumptions about the outside world, modeled, for example, via ghost parameters.
        var cl = (TopLevelDeclWithMembers) EnclosingClass;
        if (TypeArgs.Count == 0 && cl.TypeArgs.Count == 0) {
          if (Ins.Count == 0 && Outs.Count == 0) {
            if (IsStatic || (cl is Core.ClassDecl klass && !(klass is Core.TraitDecl) && !klass.HasConstructor)) {
              if (Name == "Main") {
                return true;
              } else if (Core.Attributes.Contains(Attributes, "main")) {
                return true;
              }
            }
          }
        }
        return false;
      }
    }
  }

  public class Constructor : Method
  {
    public override string WhatKind { get { return "constructor"; } }
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Body == null || Body is DividedBlockStmt);
    }
    public List<Statement> BodyInit {  // first part of Body's statements
      get {
        if (Body == null) {
          return null;
        } else {
          return ((DividedBlockStmt)Body).BodyInit;
        }
      }
    }
    public List<Statement> BodyProper {  // second part of Body's statements
      get {
        if (Body == null) {
          return null;
        } else {
          return ((DividedBlockStmt)Body).BodyProper;
        }
      }
    }
    public Constructor(string name,
                  List<TypeParameter> typeArgs,
                  List<Formal> ins,
                  DividedBlockStmt body,
                  Attributes attributes, bool signatureIsOmitted)
      : base(name, false, typeArgs, ins, new List<Formal>(), body, attributes, signatureIsOmitted) {
      Contract.Requires(name != null);
      Contract.Requires(cce.NonNullElements(typeArgs));
      Contract.Requires(cce.NonNullElements(ins));
    }

    public bool HasName {
      get {
        return Name != "_ctor";
      }
    }
  }

  // ------------------------------------------------------------------------------------------------------

  public abstract class Statement : IAttributeBearingDeclaration
  {
    public LList<Label> Labels;  // mutable during resolution

    private Attributes attributes;
    public Attributes Attributes {
      get {
        return attributes;
      }
      set {
        attributes = value;
      }
    }

    public Statement(Attributes attrs) {
      this.attributes = attrs;
    }

    public Statement()
      : this(null) {
    }

    /// <summary>
    /// Returns the non-null substatements of the Statements.
    /// </summary>
    public virtual IEnumerable<Statement> SubStatements {
      get { yield break; }
    }

    /// <summary>
    /// Returns the non-null expressions of this statement proper (that is, do not include the expressions of substatements).
    /// </summary>
    public virtual IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in Attributes.SubExpressions(Attributes)) {
          yield return e;
        }
      }
    }
  }

  public class LList<T>
  {
    public readonly T Data;
    public readonly LList<T> Next;
    const LList<T> Empty = null;

    public LList(T d, LList<T> next) {
      Data = d;
      Next = next;
    }

    public static LList<T> Append(LList<T> a, LList<T> b) {
      if (a == null) return b;
      return new LList<T>(a.Data, Append(a.Next, b));
      // pretend this is ML
    }
    public static int Count(LList<T> n) {
      int count = 0;
      while (n != null) {
        count++;
        n = n.Next;
      }
      return count;
    }
  }

  public class Label
  {
    public readonly string Name;
    string uniqueId = null;
    public string AssignUniqueId(FreshIdGenerator idGen)
    {
      if (uniqueId == null)
      {
        uniqueId = idGen.FreshNumericId("label");
      }
      return uniqueId;
    }
    public Label(string/*?*/ label) {
      Name = label;
    }
  }

  public class AssertLabel : Label
  {
    public Boogie.Expr E;  // filled in during translation
    public AssertLabel(string label)
      : base(label) {
      Contract.Requires(label != null);
    }
  }

  public abstract class PredicateStmt : Statement
  {
    public readonly Expression Expr;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Expr != null);
    }

    public PredicateStmt(Expression expr, Attributes attrs)
      : base(attrs) {
      Contract.Requires(expr != null);
      this.Expr = expr;
    }

    public PredicateStmt(Expression expr)
      : this(expr, null) {
    }
    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in base.SubExpressions) { yield return e; }
        yield return Expr;
      }
    }
  }

  public class AssertStmt : PredicateStmt {
    public readonly BlockStmt Proof;
    public readonly AssertLabel Label;
    public AssertStmt(Expression expr, BlockStmt/*?*/ proof, AssertLabel/*?*/ label, Attributes attrs)
      : base(expr, attrs) {
      Contract.Requires(expr != null);
      Proof = proof;
      Label = label;
    }
    public override IEnumerable<Statement> SubStatements {
      get {
        if (Proof != null) {
          yield return Proof;
        }
      }
    }
    public void AddCustomizedErrorMessage(string name, string s) {
      var args = new List<Expression>() { new StringLiteralExpr(s, true) };
      this.Attributes = new UserSuppliedAttributes(name, args, this.Attributes);
    }
  }

  public class AssumeStmt : PredicateStmt {
    public AssumeStmt(Expression expr, Attributes attrs)
      : base(expr, attrs) {
      Contract.Requires(expr != null);
    }
  }

  public class PrintStmt : Statement {
    public readonly List<Expression> Args;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(Args));
    }

    public PrintStmt(List<Expression> args) {
      Contract.Requires(cce.NonNullElements(args));

      Args = args;
    }
    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in base.SubExpressions) { yield return e; }
        foreach (var arg in Args) {
          yield return arg;
        }
      }
    }
  }

  public class RevealStmt : Statement
  {
    public readonly List<Expression> Exprs;
    public readonly List<AssertLabel> LabeledAsserts = new List<AssertLabel>();  // contents filled in during resolution to indicate that "Expr" denotes a labeled assertion
    public readonly List<Statement> ResolvedStatements = new List<Statement>(); // contents filled in during resolution

    public override IEnumerable<Statement> SubStatements {
      get { return ResolvedStatements; }
    }

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Exprs != null);
      Contract.Invariant(LabeledAsserts.Count <= Exprs.Count);
    }

    public RevealStmt(List<Expression> exprs) {
      Contract.Requires(exprs != null);
      this.Exprs = exprs;
    }

    public static string SingleName(Expression e) {
      Contract.Requires(e != null);
      if (e is NameSegment ns) {
        return ns.Name;
      } else if (e is LiteralExpr lit) {
        return (string) lit.Value;
      } else {
        return null;
      }
    }
  }

  public class BreakStmt : Statement {
    public readonly string TargetLabel;
    public readonly int BreakCount;
    public Statement TargetStmt;  // filled in during resolution
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(TargetLabel != null || 1 <= BreakCount);
    }

    public BreakStmt(string targetLabel) {
      Contract.Requires(targetLabel != null);
      this.TargetLabel = targetLabel;
    }
    public BreakStmt(int breakCount) {
      Contract.Requires(1 <= breakCount);
      this.BreakCount = breakCount;
    }
  }

  public abstract class ProduceStmt : Statement
  {
    public List<AssignmentRhs> rhss;
    public UpdateStmt hiddenUpdate;
    public ProduceStmt(List<AssignmentRhs> rhss) {
      this.rhss = rhss;
      hiddenUpdate = null;
    }
    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in base.SubExpressions) { yield return e; }
        if (rhss != null) {
          foreach (var rhs in rhss) {
            foreach (var ee in rhs.SubExpressions) {
              yield return ee;
            }
          }
        }
      }
    }
    public override IEnumerable<Statement> SubStatements {
      get {
        if (rhss != null) {
          foreach (var rhs in rhss) {
            foreach (var s in rhs.SubStatements) {
              yield return s;
            }
          }
        }
      }
    }
  }

  public class ReturnStmt : ProduceStmt
  {
    public bool ReverifyPost;  // set during pre-resolution refinement transformation
    public ReturnStmt(List<AssignmentRhs> rhss) : base(rhss) {
    }
  }

  public class YieldStmt : ProduceStmt
  {
    public YieldStmt(List<AssignmentRhs> rhss) : base(rhss) {
    }
  }

  public abstract class AssignmentRhs
  {
    private Attributes attributes;
    public Attributes Attributes
    {
      get
      {
        return attributes;
      }
      set
      {
        attributes = value;
      }
    }

    public bool HasAttributes()
    {
      return Attributes != null;
    }

    internal AssignmentRhs(Attributes attrs = null) {
      Attributes = attrs;
    }
    /// <summary>
    /// Returns the non-null subexpressions of the AssignmentRhs.
    /// </summary>
    public virtual IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in Attributes.SubExpressions(Attributes)) {
          yield return e;
        }
      }
    }
    /// <summary>
    /// Returns the non-null sub-statements of the AssignmentRhs.
    /// </summary>
    public virtual IEnumerable<Statement> SubStatements{
      get { yield break; }
    }
  }

  public class ExprRhs : AssignmentRhs
  {
    public readonly Expression Expr;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Expr != null);
    }

    public ExprRhs(Expression expr, Attributes attrs = null)  // TODO: these 'attrs' apparently aren't handled correctly in the Cloner, and perhaps not in various visitors either (for example, CheckIsCompilable should not go into attributes)
      : base()
    {
      Contract.Requires(expr != null);
      Expr = expr;
    }
    public override IEnumerable<Expression> SubExpressions {
      get {
        yield return Expr;
      }
    }
  }

  /// <summary>
  /// A TypeRhs represents one of five things, each having to do with allocating something in the heap:
  ///  * new T[EE]
  ///    This allocates an array of objects of type T (where EE is a list of expression)
  ///  * new T[EE] (elementInit)
  ///    This is like the previous, but uses "elementInit" to initialize the elements of the new array.
  ///  * new T[E] [EE]
  ///    This is like the first one, but uses the elements displayed in the list EE as the initial
  ///    elements of the array.  Only a 1-dimensional array may be used in this case.  The size denoted
  ///    by E must equal the length of EE.
  ///  * new C
  ///    This allocates an object of type C
  ///  * new C.Init(EE)
  ///    This allocates an object of type C and then invokes the method/constructor Init on it
  /// There are three ways to construct a TypeRhs syntactically:
  ///  * TypeRhs(T, EE, initExpr)
  ///      -- represents "new T[EE]" (with "elementInit" being "null") and "new T[EE] (elementInit)"
  ///  * TypeRhs(T, E, EE)
  ///      -- represents "new T[E] [EE]"
  ///  * TypeRhs(C)
  ///      -- represents new C
  ///  * TypeRhs(Path, EE)
  ///    Here, Path may either be of the form C.Init
  ///      -- represents new C.Init(EE)
  ///    or all of Path denotes a type
  ///      -- represents new C._ctor(EE), where _ctor is the anonymous constructor for class C
  /// </summary>
  public class TypeRhs : AssignmentRhs
  {
    /// <summary>
    /// If ArrayDimensions != null, then the TypeRhs represents "new EType[ArrayDimensions]",
    ///     ElementInit is non-null to represent "new EType[ArrayDimensions] (elementInit)",
    ///     InitDisplay is non-null to represent "new EType[ArrayDimensions] [InitDisplay]",
    ///     and Arguments, Path, and InitCall are all null.
    /// If ArrayDimentions == null && Arguments == null, then the TypeRhs represents "new EType"
    ///     and ElementInit, Path, and InitCall are all null.
    /// If Arguments != null, then the TypeRhs represents "new Path(Arguments)"
    ///     and EType and InitCall is filled in by resolution, and ArrayDimensions == null and ElementInit == null.
    /// If OptionalNameComponent == null and Arguments != null, then the TypeRHS has not been resolved yet;
    ///   resolution will either produce an error or will chop off the last part of "EType" and move it to
    ///   OptionalNameComponent, after which the case above applies.
    /// </summary>
    public Type EType;  // in the case of Arguments != null, EType is filled in during resolution
    public readonly List<Expression> ArrayDimensions;
    public readonly Expression ElementInit;
    public readonly List<Expression> InitDisplay;
    public readonly List<Expression> Arguments;
    public Type Path;
    public CallStmt InitCall;  // may be null (and is definitely null for arrays), may be filled in during resolution
    public Type Type;  // filled in during resolution
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(EType != null || Arguments != null);
      Contract.Invariant(ElementInit == null || InitDisplay == null);
      Contract.Invariant(InitDisplay == null || ArrayDimensions.Count == 1);
      Contract.Invariant(ArrayDimensions == null || (Arguments == null && Path == null && InitCall == null && 1 <= ArrayDimensions.Count));
      Contract.Invariant(Arguments == null || (Path != null && ArrayDimensions == null && ElementInit == null && InitDisplay == null));
      Contract.Invariant(!(ArrayDimensions == null && Arguments == null) || (Path == null && InitCall == null && ElementInit == null && InitDisplay == null));
    }

    public TypeRhs(Type type, List<Expression> arrayDimensions, Expression elementInit) {
      Contract.Requires(type != null);
      Contract.Requires(arrayDimensions != null && 1 <= arrayDimensions.Count);
      EType = type;
      ArrayDimensions = arrayDimensions;
      ElementInit = elementInit;
    }
    public TypeRhs(Type type, Expression dim, List<Expression> initDisplay) {
      Contract.Requires(type != null);
      Contract.Requires(dim != null);
      Contract.Requires(initDisplay != null);
      EType = type;
      ArrayDimensions = new List<Expression> { dim };
      InitDisplay = initDisplay;
    }
    public TypeRhs(Type type)
    {
      Contract.Requires(type != null);
      EType = type;
    }
    public TypeRhs(Type path, List<Expression> arguments, bool disambiguatingDummy)
    {
      Contract.Requires(path != null);
      Contract.Requires(arguments != null);
      Path = path;
      Arguments = arguments;
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        if (ArrayDimensions != null) {
          foreach (var e in ArrayDimensions) {
            yield return e;
          }
          if (ElementInit != null) {
            yield return ElementInit;
          }
          if (InitDisplay != null) {
            foreach (var e in InitDisplay) {
              yield return e;
            }
          }
        }
      }
    }
    public override IEnumerable<Statement> SubStatements {
      get {
        if (InitCall != null) {
          yield return InitCall;
        }
      }
    }
  }

  public class HavocRhs : AssignmentRhs {
    public HavocRhs()
    {
    }
  }

  public class VarDeclStmt : Statement
  {
    public readonly List<LocalVariable> Locals;
    public readonly ConcreteUpdateStatement Update;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(Locals));
      Contract.Invariant(Locals.Count != 0);
    }

    public VarDeclStmt(List<LocalVariable> locals, ConcreteUpdateStatement update)
      : base()
    {
      Contract.Requires(locals != null);
      Contract.Requires(locals.Count != 0);

      Locals = locals;
      Update = update;
    }

    public override IEnumerable<Statement> SubStatements {
      get { if (Update != null) { yield return Update; } }
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in base.SubExpressions) { yield return e; }
        foreach (var v in Locals) {
          foreach (var e in Attributes.SubExpressions(v.Attributes)) {
            yield return e;
          }
        }
      }
    }
  }

  public class LetStmt : Statement
  {
    public readonly CasePattern<LocalVariable> LHS;
    public readonly Expression RHS;

    public LetStmt(CasePattern<LocalVariable> lhs, Expression rhs)
      : base() {
      LHS = lhs;
      RHS = rhs;
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in Attributes.SubExpressions(Attributes)) {
          yield return e;
        }
        yield return RHS;
      }
    }

    public IEnumerable<LocalVariable> LocalVars {
      get {
        foreach (var bv in LHS.Vars) {
          yield return bv;
        }
      }
    }
  }

  /// <summary>
  /// Common superclass of UpdateStmt, AssignSuchThatStmt and AssignOrReturnStmt
  /// </summary>
  public abstract class ConcreteUpdateStatement : Statement
  {
    public readonly List<Expression> Lhss;
    public ConcreteUpdateStatement(List<Expression> lhss, Attributes attrs = null)
      : base(attrs) {
      Contract.Requires(cce.NonNullElements(lhss));
      Lhss = lhss;
    }
  }

  public class AssignSuchThatStmt : ConcreteUpdateStatement
  {
    public readonly Expression Expr;
    public readonly bool HasAssume;

    public List<ComprehensionExpr.BoundedPool> Bounds;  // initialized and filled in by resolver; null for a ghost statement
    // invariant Bounds == null || Bounds.Count == BoundVars.Count;
    public List<IVariable> MissingBounds;  // filled in during resolution; remains "null" if bounds can be found
    // invariant Bounds == null || MissingBounds == null;
    public class WiggleWaggleBound : ComprehensionExpr.BoundedPool
    {
      public override PoolVirtues Virtues => PoolVirtues.Enumerable | PoolVirtues.IndependentOfAlloc | PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
      public override int Preference() => 1;
    }

    public AssignSuchThatStmt(List<Expression> lhss, Expression expr, bool hasAssume, Attributes attrs)
      : base(lhss, attrs) {
      Contract.Requires(cce.NonNullElements(lhss));
      Contract.Requires(lhss.Count != 0);
      Contract.Requires(expr != null);
      Expr = expr;
      HasAssume = hasAssume;
    }
    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in base.SubExpressions) { yield return e; }
        yield return Expr;
        foreach (var lhs in Lhss) {
          yield return lhs;
        }
      }
    }
  }

  public class UpdateStmt : ConcreteUpdateStatement
  {
    public readonly List<AssignmentRhs> Rhss;
    public readonly bool CanMutateKnownState;

    public readonly List<Statement> ResolvedStatements = new List<Statement>();  // contents filled in during resolution
    public override IEnumerable<Statement> SubStatements {
      get { return ResolvedStatements; }
    }

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(Lhss));
      Contract.Invariant(cce.NonNullElements(Rhss));
    }
    public UpdateStmt(List<Expression> lhss, List<AssignmentRhs> rhss)
      : base(lhss)
    {
      Contract.Requires(cce.NonNullElements(lhss));
      Contract.Requires(cce.NonNullElements(rhss));
      Contract.Requires(lhss.Count != 0 || rhss.Count == 1);
      Rhss = rhss;
      CanMutateKnownState = false;
    }
    public UpdateStmt(List<Expression> lhss, List<AssignmentRhs> rhss, bool mutate)
      : base(lhss)
    {
      Contract.Requires(cce.NonNullElements(lhss));
      Contract.Requires(cce.NonNullElements(rhss));
      Contract.Requires(lhss.Count != 0 || rhss.Count == 1);
      Rhss = rhss;
      CanMutateKnownState = mutate;
    }
  }

  public class AssignStmt : Statement {
    public readonly Expression Lhs;
    public readonly AssignmentRhs Rhs;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Lhs != null);
      Contract.Invariant(Rhs != null);
    }

    public AssignStmt(Expression lhs, AssignmentRhs rhs)
      : base() {
      Contract.Requires(lhs != null);
      Contract.Requires(rhs != null);
      this.Lhs = lhs;
      this.Rhs = rhs;
    }

    public override IEnumerable<Statement> SubStatements {
      get {
        foreach (var s in Rhs.SubStatements) {
          yield return s;
        }
      }
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in base.SubExpressions) { yield return e; }
        yield return Lhs;
        foreach (var ee in Rhs.SubExpressions) {
          yield return ee;
        }
      }
    }

    public enum LhsKind { Variable, Field, ArrayElement }
    public static string LhsKind_To_String(LhsKind gk) {
      switch (gk) {
        case LhsKind.Variable: return "non-ghost variable";
        case LhsKind.Field: return "non-ghost field";
        case LhsKind.ArrayElement: return "array element";
        default:
          Contract.Assume(false);  // unexpected NonGhostKind
          throw new cce.UnreachableException();  // please compiler
      }
    }
    /// <summary>
    /// This method assumes "lhs" has been successfully resolved.
    /// </summary>
    public static LhsKind LhsIsToGhost_Which(Expression lhs) {
      Contract.Requires(lhs != null);
      if (lhs is IdentifierExpr) {
        return LhsKind.Variable;
      } else if (lhs is MemberSelectExpr) {
        return LhsKind.Field;
      } else {
        return LhsKind.ArrayElement;
      }
    }
  }

  public class LocalVariable : IVariable, IAttributeBearingDeclaration {
    readonly string name;
    public Type Type;
    public Attributes Attributes;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(name != null);
      Contract.Invariant(Type != null);
    }

    public LocalVariable(string name, Type type) {
      Contract.Requires(name != null);
      Contract.Requires(type != null);  // can be a proxy, though

      this.name = name;
      this.Type = type;
    }

    public string Name {
      get {
        Contract.Ensures(Contract.Result<string>() != null);
        return name;
      }
    }
    public static bool HasWildcardName(IVariable v) {
      Contract.Requires(v != null);
      return v.Name.StartsWith("_v");
    }
    public static string DisplayNameHelper(IVariable v) {
      Contract.Requires(v != null);
      return HasWildcardName(v) ? "_" : v.Name;
    }
    public string DisplayName {
      get { return DisplayNameHelper(this); }
    }
    private string uniqueName;
    public string UniqueName {
      get {
        return uniqueName;
      }
    }
    public bool HasBeenAssignedUniqueName {
      get {
        return uniqueName != null;
      }
    }
    public string AssignUniqueName(FreshIdGenerator generator)
    {
      if (uniqueName == null)
      {
        uniqueName = generator.FreshId(Name + "#");
        compileName = string.Format("_{0}_{1}", Compiler.FreshId(), NonglobalVariable.CompilerizeName(name));
      }
      return UniqueName;
    }
    string compileName;
    public string CompileName {
      get {
        if (compileName == null)
        {
          compileName = string.Format("_{0}_{1}", Compiler.FreshId(), NonglobalVariable.CompilerizeName(name));
        }
        return compileName;
      }
    }
    Type IVariable.Type => Type;
    public bool IsMutable {
      get {
        return true;
      }
    }
  }

  /// <summary>
  /// A CallStmt is always resolved.  It is typically produced as a resolved counterpart of the syntactic AST note ApplySuffix.
  /// </summary>
  public class CallStmt : Statement {
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(MethodSelect.Member is Method);
      Contract.Invariant(cce.NonNullElements(Lhs));
      Contract.Invariant(cce.NonNullElements(Args));
    }

    public readonly List<Expression> Lhs;
    public readonly MemberSelectExpr MethodSelect;
    public readonly List<Expression> Args;

    public Expression Receiver { get { return MethodSelect.Obj; } }
    public Method Method { get { return (Method)MethodSelect.Member; } }

    public CallStmt(List<Expression> lhs, MemberSelectExpr memSel, List<Expression> args) {
      Contract.Requires(cce.NonNullElements(lhs));
      Contract.Requires(memSel != null);
      Contract.Requires(memSel.Member is Method);
      Contract.Requires(cce.NonNullElements(args));

      this.Lhs = lhs;
      this.MethodSelect = memSel;
      this.Args = args;
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in base.SubExpressions) { yield return e; }
        foreach (var ee in Lhs) {
          yield return ee;
        }
        yield return MethodSelect;
        foreach (var ee in Args) {
          yield return ee;
        }
      }
    }
  }

  public class BlockStmt : Statement {
    public readonly List<Statement> Body;
    public BlockStmt([Captured] List<Statement> body) {
      Contract.Requires(cce.NonNullElements(body));
      this.Body = body;
    }

    public override IEnumerable<Statement> SubStatements {
      get { return Body; }
    }

    public virtual void AppendStmt(Statement s) {
      Contract.Requires(s != null);
      Body.Add(s);
    }
  }

  public class DividedBlockStmt : BlockStmt
  {
    public readonly List<Statement> BodyInit;  // first part of Body's statements
    public readonly List<Statement> BodyProper;  // second part of Body's statements
    public DividedBlockStmt(List<Statement> bodyInit, List<Statement> bodyProper)
      : base(Util.Concat(bodyInit, bodyProper)) {
      Contract.Requires(cce.NonNullElements(bodyInit));
      Contract.Requires(cce.NonNullElements(bodyProper));
      this.BodyInit = bodyInit;
      this.BodyProper = bodyProper;
    }
    public override void AppendStmt(Statement s) {
      BodyProper.Add(s);
      base.AppendStmt(s);
    }
  }

  public class IfStmt : Statement {
    public readonly bool IsBindingGuard;
    public readonly Expression Guard;
    public readonly BlockStmt Thn;
    public readonly Statement Els;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(!IsBindingGuard || (Guard is ExistsExpr && ((ExistsExpr)Guard).Range == null));
      Contract.Invariant(Thn != null);
      Contract.Invariant(Els == null || Els is BlockStmt || Els is IfStmt || Els is SkeletonStatement);
    }
    public IfStmt(bool isBindingGuard, Expression guard, BlockStmt thn, Statement els) {
      Contract.Requires(!isBindingGuard || (guard is ExistsExpr && ((ExistsExpr)guard).Range == null));
      Contract.Requires(thn != null);
      Contract.Requires(els == null || els is BlockStmt || els is IfStmt || els is SkeletonStatement);
      this.IsBindingGuard = isBindingGuard;
      this.Guard = guard;
      this.Thn = thn;
      this.Els = els;
    }
    public override IEnumerable<Statement> SubStatements {
      get {
        yield return Thn;
        if (Els != null) {
          yield return Els;
        }
      }
    }
    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in base.SubExpressions) { yield return e; }
        if (Guard != null) {
          yield return Guard;
        }
      }
    }
  }

  public class GuardedAlternative
  {
    public readonly bool IsBindingGuard;
    public readonly Expression Guard;
    public readonly List<Statement> Body;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Guard != null);
      Contract.Invariant(!IsBindingGuard || (Guard is ExistsExpr && ((ExistsExpr)Guard).Range == null));
      Contract.Invariant(Body != null);
    }
    public GuardedAlternative(bool isBindingGuard, Expression guard, List<Statement> body)
    {
      Contract.Requires(guard != null);
      Contract.Requires(!isBindingGuard || (guard is ExistsExpr && ((ExistsExpr)guard).Range == null));
      Contract.Requires(body != null);
      this.IsBindingGuard = isBindingGuard;
      this.Guard = guard;
      this.Body = body;
    }
  }

  public class AlternativeStmt : Statement
  {
    public readonly bool UsesOptionalBraces;
    public readonly List<GuardedAlternative> Alternatives;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Alternatives != null);
    }
    public AlternativeStmt(List<GuardedAlternative> alternatives, bool usesOptionalBraces) {
      Contract.Requires(alternatives != null);
      this.Alternatives = alternatives;
      this.UsesOptionalBraces = usesOptionalBraces;
    }
    public override IEnumerable<Statement> SubStatements {
      get {
        foreach (var alt in Alternatives) {
          foreach (var s in alt.Body) {
            yield return s;
          }
        }
      }
    }
    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in base.SubExpressions) { yield return e; }
        foreach (var alt in Alternatives) {
          yield return alt.Guard;
        }
      }
    }
  }

  public abstract class LoopStmt : Statement
  {
    public readonly List<MaybeFreeExpression> Invariants;
    public readonly Specification<Expression> Decreases;
    public bool InferredDecreases;  // filled in by resolution
    public readonly Specification<FrameExpression> Mod;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(Invariants));
      Contract.Invariant(Decreases != null);
      Contract.Invariant(Mod != null);
    }
    public LoopStmt(List<MaybeFreeExpression> invariants, Specification<Expression> decreases, Specification<FrameExpression> mod)
    {
      Contract.Requires(cce.NonNullElements(invariants));
      Contract.Requires(decreases != null);
      Contract.Requires(mod != null);

      this.Invariants = invariants;
      this.Decreases = decreases;
      this.Mod = mod;
      if (DafnyOptions.O.Dafnycc) {
        Decreases = new Specification<Expression>(
          new List<Expression>() { new WildcardExpr() }, null);
      }
    }
    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in base.SubExpressions) { yield return e; }
        foreach (var mfe in Invariants) {
          foreach (var e in Attributes.SubExpressions(mfe.Attributes)) { yield return e; }
          yield return mfe.E;
        }
        foreach (var e in Attributes.SubExpressions(Decreases.Attributes)) { yield return e; }
        if (Decreases.Expressions != null) {
          foreach (var e in Decreases.Expressions) {
            yield return e;
          }
        }
        foreach (var e in Attributes.SubExpressions(Mod.Attributes)) { yield return e; }
        if (Mod.Expressions != null) {
          foreach (var fe in Mod.Expressions) {
            yield return fe.E;
          }
        }
      }
    }
  }

  public class WhileStmt : LoopStmt
  {
    public readonly Expression Guard;
    public readonly BlockStmt Body;

    public WhileStmt(Expression guard,
                     List<MaybeFreeExpression> invariants, Specification<Expression> decreases, Specification<FrameExpression> mod,
                     BlockStmt body)
      : base(invariants, decreases, mod) {
      this.Guard = guard;
      this.Body = body;
    }

    public override IEnumerable<Statement> SubStatements {
      get {
        if (Body != null) {
          yield return Body;
        }
      }
    }
    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in base.SubExpressions) { yield return e; }
        if (Guard != null) {
          yield return Guard;
        }
      }
    }
  }

  /// <summary>
  /// This class is really just a WhileStmt, except that it serves the purpose of remembering if the object was created as the result of a refinement
  /// merge.
  /// </summary>
  public class RefinedWhileStmt : WhileStmt
  {
    public RefinedWhileStmt(Expression guard,
                            List<MaybeFreeExpression> invariants, Specification<Expression> decreases, Specification<FrameExpression> mod,
                            BlockStmt body)
      : base(guard, invariants, decreases, mod, body) {
      Contract.Requires(body != null);
    }
  }

  public class AlternativeLoopStmt : LoopStmt
  {
    public readonly bool UsesOptionalBraces;
    public readonly List<GuardedAlternative> Alternatives;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Alternatives != null);
    }
    public AlternativeLoopStmt(List<MaybeFreeExpression> invariants, Specification<Expression> decreases, Specification<FrameExpression> mod,
                               List<GuardedAlternative> alternatives, bool usesOptionalBraces)
      : base(invariants, decreases, mod) {
      Contract.Requires(alternatives != null);
      this.Alternatives = alternatives;
      this.UsesOptionalBraces = usesOptionalBraces;
    }
    public override IEnumerable<Statement> SubStatements {
      get {
        foreach (var alt in Alternatives) {
          foreach (var s in alt.Body) {
            yield return s;
          }
        }
      }
    }
    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in base.SubExpressions) { yield return e; }
        foreach (var alt in Alternatives) {
          yield return alt.Guard;
        }
      }
    }
  }

  public class ForallStmt : Statement
  {
    public readonly List<BoundVar> BoundVars;  // note, can be the empty list, in which case Range denotes "true"
    public Expression Range;  // mostly readonly, except that it may in some cases be updated during resolution to conjoin the precondition of the call in the body
    public readonly List<MaybeFreeExpression> Ens;
    public readonly Statement Body;
    public List<Expression> ForallExpressions;   // fill in by rewriter.
    public bool CanConvert = true; //  can convert to ForallExpressions

    public List<ComprehensionExpr.BoundedPool> Bounds;  // initialized and filled in by resolver
    // invariant: if successfully resolved, Bounds.Count == BoundVars.Count;

    /// <summary>
    /// Assign means there are no ensures clauses and the body consists of one update statement,
    ///   either to an object field or to an array.
    /// Call means there are no ensures clauses and the body consists of a single call to a (presumably
    ///   ghost, but non-ghost is also allowed) method with no out-parameters and an empty modifies
    ///   clause.
    /// Proof means there is at least one ensures clause, and the body consists of any (presumably ghost,
    ///   but non-ghost is also allowed) code without side effects on variables (including fields and array
    ///   elements) declared outside the body itself.
    /// Notes:
    /// * More kinds may be allowed in the future.
    /// * One could also allow Call to call non-ghost methods without side effects.  However, that
    ///   would seem pointless in the program, so they are disallowed (to avoid any confusion that
    ///   such use of the forall statement might actually have a point).
    /// * One could allow Proof even without ensures clauses that "export" what was learned.
    ///   However, that might give the false impression that the body is nevertheless exported.
    /// </summary>
    public enum BodyKind { Assign, Call, Proof }
    public BodyKind Kind;  // filled in during resolution

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(BoundVars != null);
      Contract.Invariant(Range != null);
      Contract.Invariant(BoundVars.Count != 0 || LiteralExpr.IsTrue(Range));
      Contract.Invariant(Ens != null);
    }

    public ForallStmt(List<BoundVar> boundVars, Attributes attrs, Expression range, List<MaybeFreeExpression> ens, Statement body) {
      Contract.Requires(cce.NonNullElements(boundVars));
      Contract.Requires(range != null);
      Contract.Requires(boundVars.Count != 0 || LiteralExpr.IsTrue(range));
      Contract.Requires(cce.NonNullElements(ens));
      this.BoundVars = boundVars;
      this.Attributes = attrs;
      this.Range = range;
      this.Ens = ens;
      this.Body = body;
    }

    public Statement S0 {
      get {
        // dig into Body to find a single statement
        Statement s = this.Body;
        while (true) {
          var block = s as BlockStmt;
          if (block != null && block.Body.Count == 1) {
            s = block.Body[0];
            // dig further into s
          } else if (s is UpdateStmt) {
            var update = (UpdateStmt)s;
            if (update.ResolvedStatements.Count == 1) {
              s = update.ResolvedStatements[0];
              // dig further into s
            } else {
              return s;
            }
          } else {
            return s;
          }
        }
      }
    }

    public override IEnumerable<Statement> SubStatements {
      get {
        if (Body != null) {
          yield return Body;
        }
      }
    }
    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in base.SubExpressions) { yield return e; }
        yield return Range;
        foreach (var ee in Ens) {
          foreach (var e in Attributes.SubExpressions(ee.Attributes)) { yield return e; }
          yield return ee.E;
        }
      }
    }

    public List<BoundVar> UncompilableBoundVars() {
      Contract.Ensures(Contract.Result<List<BoundVar>>() != null);
      var v = ComprehensionExpr.BoundedPool.PoolVirtues.Finite | ComprehensionExpr.BoundedPool.PoolVirtues.Enumerable;
      return ComprehensionExpr.BoundedPool.MissingBounds(BoundVars, Bounds, v);
    }
  }

  public class ModifyStmt : Statement
  {
    public readonly Specification<FrameExpression> Mod;
    public readonly BlockStmt Body;

    public ModifyStmt(List<FrameExpression> mod, Attributes attrs, BlockStmt body) {
      Contract.Requires(mod != null);
      Mod = new Specification<FrameExpression>(mod, attrs);
      Body = body;
    }

    public override IEnumerable<Statement> SubStatements {
      get {
        if (Body != null) {
          yield return Body;
        }
      }
    }
    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in base.SubExpressions) { yield return e; }
        foreach (var e in Attributes.SubExpressions(Mod.Attributes)) { yield return e; }
        foreach (var fe in Mod.Expressions) {
          yield return fe.E;
        }
      }
    }
  }

  public class CalcStmt : Statement
  {
    public abstract class CalcOp {
      /// <summary>
      /// Resulting operator "x op z" if "x this y" and "y other z".
      /// Returns null if this and other are incompatible.
      /// </summary>
      [Pure]
      public abstract CalcOp ResultOp(CalcOp other);

      /// <summary>
      /// Returns an expression "line0 this line1".
      /// </summary>
      [Pure]
      public abstract Expression StepExpr(Expression line0, Expression line1);
    }

    public class BinaryCalcOp : CalcOp {
      public readonly BinaryExpr.Opcode Op;

      [ContractInvariantMethod]
      void ObjectInvariant()
      {
        Contract.Invariant(ValidOp(Op));
      }

      /// <summary>
      /// Is op a valid calculation operator?
      /// </summary>
      [Pure]
      public static bool ValidOp(BinaryExpr.Opcode op) {
        return
             op == BinaryExpr.Opcode.Eq || op == BinaryExpr.Opcode.Neq
          || op == BinaryExpr.Opcode.Lt || op == BinaryExpr.Opcode.Le
          || op == BinaryExpr.Opcode.Gt || op == BinaryExpr.Opcode.Ge
          || LogicOp(op);
      }

      /// <summary>
      /// Is op a valid operator only for Boolean lines?
      /// </summary>
      [Pure]
      public static bool LogicOp(BinaryExpr.Opcode op) {
        return op == BinaryExpr.Opcode.Iff || op == BinaryExpr.Opcode.Imp || op == BinaryExpr.Opcode.Exp;
      }

      public BinaryCalcOp(BinaryExpr.Opcode op) {
        Contract.Requires(ValidOp(op));
        Op = op;
      }

      /// <summary>
      /// Does this subsume other (this . other == other . this == this)?
      /// </summary>
      private bool Subsumes(BinaryCalcOp other) {
        Contract.Requires(other != null);
        var op1 = Op;
        var op2 = other.Op;
        if (op1 == BinaryExpr.Opcode.Neq || op2 == BinaryExpr.Opcode.Neq)
          return op2 == BinaryExpr.Opcode.Eq;
        if (op1 == op2)
          return true;
        if (LogicOp(op1) || LogicOp(op2))
          return op2 == BinaryExpr.Opcode.Eq ||
            (op1 == BinaryExpr.Opcode.Imp && op2 == BinaryExpr.Opcode.Iff) ||
            (op1 == BinaryExpr.Opcode.Exp && op2 == BinaryExpr.Opcode.Iff) ||
            (op1 == BinaryExpr.Opcode.Eq && op2 == BinaryExpr.Opcode.Iff);
        return op2 == BinaryExpr.Opcode.Eq ||
          (op1 == BinaryExpr.Opcode.Lt && op2 == BinaryExpr.Opcode.Le) ||
          (op1 == BinaryExpr.Opcode.Gt && op2 == BinaryExpr.Opcode.Ge);
      }

      public override CalcOp ResultOp(CalcOp other) {
        if (other is BinaryCalcOp) {
          var o = (BinaryCalcOp) other;
          if (this.Subsumes(o)) {
            return this;
          } else if (o.Subsumes(this)) {
            return other;
          }
          return null;
        } else if (other is TernaryCalcOp) {
          return other.ResultOp(this);
        } else {
          Contract.Assert(false);
          throw new cce.UnreachableException();
        }
      }

      public override Expression StepExpr(Expression line0, Expression line1)
      {
        if (Op == BinaryExpr.Opcode.Exp) {
          // The order of operands is reversed so that it can be turned into implication during resolution
          return new BinaryExpr(Op, line1, line0);
        } else {
          return new BinaryExpr(Op, line0, line1);
        }
      }

      public override string ToString()
      {
        return BinaryExpr.OpcodeString(Op);
      }

    }

    public class TernaryCalcOp : CalcOp {
      public readonly Expression Index; // the only allowed ternary operator is ==#, so we only store the index

      [ContractInvariantMethod]
      void ObjectInvariant()
      {
        Contract.Invariant(Index != null);
      }

      public TernaryCalcOp(Expression idx) {
        Contract.Requires(idx != null);
        Index = idx;
      }

      public override CalcOp ResultOp(CalcOp other) {
        if (other is BinaryCalcOp) {
          if (((BinaryCalcOp) other).Op == BinaryExpr.Opcode.Eq) {
            return this;
          }
          return null;
        } else if (other is TernaryCalcOp) {
          var a = Index;
          var b = ((TernaryCalcOp) other).Index;
          var minIndex = new ITEExpr(false, new BinaryExpr(BinaryExpr.Opcode.Le, a, b), a, b);
          return new TernaryCalcOp(minIndex); // ToDo: if we could compare expressions for syntactic equalty, we could use this here to optimize
        } else {
          Contract.Assert(false);
          throw new cce.UnreachableException();
        }
      }

      public override Expression StepExpr(Expression line0, Expression line1)
      {
        return new TernaryExpr(TernaryExpr.Opcode.PrefixEqOp, Index, line0, line1);
      }

      public override string ToString()
      {
        return "==#";
      }

    }

    public readonly List<Expression> Lines;    // Last line is dummy, in order to form a proper step with the dangling hint
    public readonly List<BlockStmt> Hints;     // Hints[i] comes after line i; block statement is used as a container for multiple sub-hints
    public readonly CalcOp UserSuppliedOp;     // may be null, if omitted by the user
    public CalcOp Op;                          // main operator of the calculation (either UserSuppliedOp or (after resolution) an inferred CalcOp)
    public readonly List<CalcOp/*?*/> StepOps; // StepOps[i] comes after line i
    public readonly List<Expression> Steps;    // expressions li op l<i + 1>, filled in during resolution (last step is dummy)
    public Expression Result;                  // expression l0 ResultOp ln, filled in during resolution

    public static readonly CalcOp DefaultOp = new BinaryCalcOp(BinaryExpr.Opcode.Eq);

    [ContractInvariantMethod]
    void ObjectInvariant()
    {
      Contract.Invariant(Lines != null);
      Contract.Invariant(cce.NonNullElements(Lines));
      Contract.Invariant(Hints != null);
      Contract.Invariant(cce.NonNullElements(Hints));
      Contract.Invariant(StepOps != null);
      Contract.Invariant(Steps != null);
      Contract.Invariant(cce.NonNullElements(Steps));
      Contract.Invariant(Hints.Count == Math.Max(Lines.Count - 1, 0));
      Contract.Invariant(StepOps.Count == Hints.Count);
    }

    public CalcStmt(CalcOp userSuppliedOp, List<Expression> lines, List<BlockStmt> hints, List<CalcOp/*?*/> stepOps, Attributes attrs) : base()
    {
      Contract.Requires(lines != null);
      Contract.Requires(hints != null);
      Contract.Requires(stepOps != null);
      Contract.Requires(cce.NonNullElements(lines));
      Contract.Requires(cce.NonNullElements(hints));
      Contract.Requires(hints.Count == Math.Max(lines.Count - 1, 0));
      Contract.Requires(stepOps.Count == hints.Count);
      this.UserSuppliedOp = userSuppliedOp;
      this.Lines = lines;
      this.Hints = hints;
      this.StepOps = stepOps;
      this.Steps = new List<Expression>();
      this.Result = null;
      this.Attributes = attrs;
    }

    public override IEnumerable<Statement> SubStatements
    {
      get {
        foreach (var h in Hints) {
          yield return h;
        }
      }
    }
    public override IEnumerable<Expression> SubExpressions
    {
      get {
        foreach (var e in base.SubExpressions) { yield return e; }
        foreach (var e in Attributes.SubExpressions(Attributes)) { yield return e; }

        for (int i = 0; i < Lines.Count - 1; i++) {  // note, we skip the duplicated line at the end
          yield return Lines[i];
        }
        foreach (var calcop in AllCalcOps) {
          var o3 = calcop as TernaryCalcOp;
          if (o3 != null) {
            yield return o3.Index;
          }
        }
      }
    }

    IEnumerable<CalcOp> AllCalcOps {
      get {
        if (UserSuppliedOp != null) {
          yield return UserSuppliedOp;
        }
        foreach (var stepop in StepOps) {
          if (stepop != null) {
            yield return stepop;
          }
        }
      }
    }

    /// <summary>
    /// Left-hand side of a step expression.
    /// Note that Lhs(op.StepExpr(line0, line1)) != line0 when op is <==.
    /// </summary>
    public static Expression Lhs(Expression step)
    {
      Contract.Requires(step is BinaryExpr || step is TernaryExpr);
      if (step is BinaryExpr) {
        return ((BinaryExpr) step).E0;
      } else {
        return ((TernaryExpr) step).E1;
      }
    }

    /// <summary>
    /// Right-hand side of a step expression.
    /// Note that Rhs(op.StepExpr(line0, line1)) != line1 when op is REVERSE-IMPLICATION.
    /// </summary>
    public static Expression Rhs(Expression step)
    {
      Contract.Requires(step is BinaryExpr || step is TernaryExpr);
      if (step is BinaryExpr) {
        return ((BinaryExpr) step).E1;
      } else {
        return ((TernaryExpr) step).E2;
      }
    }
  }

  public class MatchStmt : Statement
  {
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Source != null);
      Contract.Invariant(cce.NonNullElements(Cases));
      Contract.Invariant(cce.NonNullElements(MissingCases));
    }

    private Expression source;
    private List<MatchCaseStmt> cases;
    public readonly List<DatatypeCtor> MissingCases = new List<DatatypeCtor>();  // filled in during resolution
    public readonly bool UsesOptionalBraces;
    public MatchStmt OrigUnresolved;  // the resolver makes this clone of the MatchStmt before it starts desugaring it

    public MatchStmt(Expression source, [Captured] List<MatchCaseStmt> cases, bool usesOptionalBraces) {
      Contract.Requires(source != null);
      Contract.Requires(cce.NonNullElements(cases));
      this.source = source;
      this.cases = cases;
      this.UsesOptionalBraces = usesOptionalBraces;
    }

    public Expression Source {
      get { return source; }
    }

    public List<MatchCaseStmt> Cases {
      get { return cases; }
    }

    // should only be used in desugar in resolve to change the cases of the matchexpr
    public void UpdateSource(Expression source) {
      this.source = source;
    }

    public void UpdateCases(List<MatchCaseStmt> cases) {
      this.cases = cases;
    }

    public override IEnumerable<Statement> SubStatements {
      get {
        foreach (var kase in cases) {
          foreach (var s in kase.Body) {
            yield return s;
          }
        }
      }
    }
    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in base.SubExpressions) { yield return e; }
        yield return Source;
      }
    }
  }

  public class MatchCaseStmt : MatchCase
  {
    private List<Statement> body;

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(Body));
    }

    public MatchCaseStmt(string id, [Captured] List<BoundVar> arguments, [Captured] List<Statement> body)
      : base(id, arguments)
    {
      Contract.Requires(id != null);
      Contract.Requires(cce.NonNullElements(arguments));
      Contract.Requires(cce.NonNullElements(body));
      this.body = body;
    }

    public MatchCaseStmt(string id, [Captured] List<CasePattern<BoundVar>> cps, [Captured] List<Statement> body)
      : base(id, cps) {
      Contract.Requires(id != null);
      Contract.Requires(cce.NonNullElements(cps));
      Contract.Requires(cce.NonNullElements(body));
      this.body = body;
    }

    public List<Statement> Body {
      get { return body; }
    }

    // should only be called by resolve to reset the body of the MatchCaseExpr
    public void UpdateBody(List<Statement> body) {
      this.body = body;
    }
  }

  /// <summary>
  /// The class represents several possible scenarios:
  /// * ...;
  ///   S == null
  /// * assert ...
  ///   ConditionOmitted == true
  /// * assume ...
  ///   ConditionOmitted == true
  /// * if ... { Stmt }
  ///   if ... { Stmt } else ElseStmt
  ///   ConditionOmitted == true
  /// * while ... invariant J;
  ///   ConditionOmitted == true && BodyOmitted == true
  /// * while ... invariant J; { Stmt }
  ///   ConditionOmitted == true && BodyOmitted == false
  /// * modify ...;
  ///   ConditionOmitted == true && BodyOmitted == false
  /// * modify ... { Stmt }
  ///   ConditionOmitted == true && BodyOmitted == false
  /// </summary>
  public class SkeletonStatement : Statement
  {
    public readonly Statement S;
    public readonly bool ConditionOmitted;
    public readonly bool BodyOmitted;
    public readonly List<string> NameReplacements;
    public readonly List<Expression> ExprReplacements;
    public SkeletonStatement()
      : base()
    {
      S = null;
    }
    public SkeletonStatement(Statement s, bool conditionOmitted, bool bodyOmitted)
      : base()
    {
      S = s;
      ConditionOmitted = conditionOmitted;
      BodyOmitted = bodyOmitted;
    }
    public SkeletonStatement(List<string> nameReplacements, List<Expression> exprReplacements)
      : base() {
      NameReplacements = nameReplacements;
      ExprReplacements = exprReplacements;

    }
    public override IEnumerable<Statement> SubStatements {
      get {
        // The SkeletonStatement is really a modification of its inner statement S.  Therefore,
        // we don't consider S to be a substatement.  Instead, the substatements of S are the
        // substatements of the SkeletonStatement.  In the case the SkeletonStatement modifies
        // S by omitting its body (which is true only for loops), there are no substatements.
        if (!BodyOmitted) {
          foreach (var s in S.SubStatements) {
            yield return s;
          }
        }
      }
    }
  }

  // ------------------------------------------------------------------------------------------------------
  public abstract class Expression
  {
    protected Type type;
    public Type Type {  // filled in during resolution
      get {
        Contract.Ensures(type != null || Contract.Result<Type>() == null);  // useful in conjunction with postcondition of constructor
        return type;
      }
      set {
        Contract.Requires(type == null);  // set it only once
        Contract.Requires(value != null);

        //modifies type;
        type = value;
      }
    }

    public Expression() {
      Contract.Ensures(type == null);  // we would have liked to have written Type==null, but that's not admissible or provable
    }
    public Expression(Type type) {
      Contract.Requires(type != null);
      Contract.Ensures(this.type != null);

      this.type = type;
    }

    /// <summary>
    /// Returns the non-null subexpressions of the Expression.  To be called after the expression has been resolved; this
    /// means, for example, that any concrete syntax that resolves to some other expression will return the subexpressions
    /// of the resolved expression.
    /// </summary>
    public virtual IEnumerable<Expression> SubExpressions {
      get { yield break; }
    }

    public virtual bool IsImplicit {
      get { return false; }
    }

    public static IEnumerable<Expression> Conjuncts(Expression expr) {
      Contract.Requires(expr != null);
      Contract.Requires(expr.Type.IsBoolType);
      Contract.Ensures(cce.NonNullElements(Contract.Result<IEnumerable<Expression>>()));

      var bin = expr as BinaryExpr;
      if (bin != null && bin.ResolvedOp == BinaryExpr.ResolvedOpcode.And) {
        foreach (Expression e in Conjuncts(bin.E0)) {
          yield return e;
        }
        foreach (Expression e in Conjuncts(bin.E1)) {
          yield return e;
        }
        yield break;
      }
      yield return expr;
    }

    /// <summary>
    /// Create a resolved expression of the form "e0 + e1"
    /// </summary>
    public static Expression CreateAdd(Expression e0, Expression e1) {
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);
      Contract.Requires(
        (e0.Type.IsNumericBased(Type.NumericPersuation.Int) && e1.Type.IsNumericBased(Type.NumericPersuation.Int)) ||
        (e0.Type.IsNumericBased(Type.NumericPersuation.Real) && e1.Type.IsNumericBased(Type.NumericPersuation.Real)));
      Contract.Ensures(Contract.Result<Expression>() != null);
      var s = new BinaryExpr(BinaryExpr.Opcode.Add, e0, e1);
      s.ResolvedOp = BinaryExpr.ResolvedOpcode.Add;  // resolve here
      s.Type = e0.Type.NormalizeExpand();  // resolve here
      return s;
    }

    /// <summary>
    /// Create a resolved expression of the form "e0 * e1"
    /// </summary>
    public static Expression CreateMul(Expression e0, Expression e1) {
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);
      Contract.Requires(
        (e0.Type.IsNumericBased(Type.NumericPersuation.Int) && e1.Type.IsNumericBased(Type.NumericPersuation.Int)) ||
        (e0.Type.IsNumericBased(Type.NumericPersuation.Real) && e1.Type.IsNumericBased(Type.NumericPersuation.Real)));
      Contract.Ensures(Contract.Result<Expression>() != null);
      var s = new BinaryExpr(BinaryExpr.Opcode.Mul, e0, e1);
      s.ResolvedOp = BinaryExpr.ResolvedOpcode.Mul;  // resolve here
      s.Type = e0.Type.NormalizeExpand();  // resolve here
      return s;
    }

    /// <summary>
    /// Create a resolved expression of the form "CVT(e0) - CVT(e1)", where "CVT" is either "int" (if
    /// e0.Type is an integer-based numeric type) or "real" (if e0.Type is a real-based numeric type).
    /// </summary>
    public static Expression CreateSubtract_TypeConvert(Expression e0, Expression e1) {
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);
      Contract.Requires(
        (e0.Type.IsNumericBased(Type.NumericPersuation.Int) && e1.Type.IsNumericBased(Type.NumericPersuation.Int)) ||
        (e0.Type.IsNumericBased(Type.NumericPersuation.Real) && e1.Type.IsNumericBased(Type.NumericPersuation.Real)));
      Contract.Ensures(Contract.Result<Expression>() != null);

      Type toType = e0.Type.IsNumericBased(Type.NumericPersuation.Int) ? (Type)Type.Int : Type.Real;
      e0 = CastIfNeeded(e0, toType);
      e1 = CastIfNeeded(e1, toType);
      return CreateSubtract(e0, e1);
    }

    private static Expression CastIfNeeded(Expression expr, Type toType) {
      if (!expr.Type.Equals(toType)) {
        var cast = new ConversionExpr(expr, toType);
        cast.Type = toType;
        return cast;
      } else {
        return expr;
      }
    }

    /// <summary>
    /// Create a resolved expression of the form "e0 - e1"
    /// </summary>
    public static Expression CreateSubtract(Expression e0, Expression e1) {
      Contract.Requires(e0 != null);
      Contract.Requires(e0.Type != null);
      Contract.Requires(e1 != null);
      Contract.Requires(e1.Type != null);
      Contract.Requires(
        (e0.Type.IsNumericBased(Type.NumericPersuation.Int) && e1.Type.IsNumericBased(Type.NumericPersuation.Int)) ||
        (e0.Type.IsNumericBased(Type.NumericPersuation.Real) && e1.Type.IsNumericBased(Type.NumericPersuation.Real)) ||
        (e0.Type.IsBigOrdinalType && e1.Type.IsBigOrdinalType));
      Contract.Ensures(Contract.Result<Expression>() != null);
      var s = new BinaryExpr(BinaryExpr.Opcode.Sub, e0, e1);
      s.ResolvedOp = BinaryExpr.ResolvedOpcode.Sub;  // resolve here
      s.Type = e0.Type.NormalizeExpand();  // resolve here
      return s;
    }

    /// <summary>
    /// Create a resolved expression of the form "e + n"
    /// </summary>
    public static Expression CreateIncrement(Expression e, int n) {
      Contract.Requires(e != null);
      Contract.Requires(e.Type != null);
      Contract.Requires(e.Type.IsNumericBased(Type.NumericPersuation.Int));
      Contract.Requires(0 <= n);
      Contract.Ensures(Contract.Result<Expression>() != null);
      if (n == 0) {
        return e;
      }
      var nn = CreateIntLiteral(n);
      return CreateAdd(e, nn);
    }

    /// <summary>
    /// Create a resolved expression of the form "e - n"
    /// </summary>
    public static Expression CreateDecrement(Expression e, int n) {
      Contract.Requires(e != null);
      Contract.Requires(e.Type.IsNumericBased(Type.NumericPersuation.Int));
      Contract.Requires(0 <= n);
      Contract.Ensures(Contract.Result<Expression>() != null);
      if (n == 0) {
        return e;
      }
      var nn = CreateIntLiteral(n);
      return CreateSubtract(e, nn);
    }

    /// <summary>
    /// Create a resolved expression of the form "n"
    /// </summary>
    public static Expression CreateIntLiteral(int n) {
      Contract.Requires(n != int.MinValue);
      if (0 <= n) {
        var nn = new LiteralExpr(n);
        nn.Type = Type.Int;
        return nn;
      } else {
        return CreateDecrement(CreateIntLiteral(0), -n);
      }
    }

    /// <summary>
    /// Create a resolved expression of the form "x"
    /// </summary>
    public static Expression CreateRealLiteral(Basetypes.BigDec x) {
      var nn = new LiteralExpr(x);
      nn.Type = Type.Real;
      return nn;
    }

    /// <summary>
    /// Create a resolved expression of the form "n", for either type "int" or type "ORDINAL".
    /// </summary>
    public static Expression CreateNatLiteral(int n, Type ty) {
      Contract.Requires(0 <= n);
      Contract.Requires(ty.IsNumericBased(Type.NumericPersuation.Int) || ty is BigOrdinalType);
      var nn = new LiteralExpr(n);
      nn.Type = ty;
      return nn;
    }

    /// <summary>
    /// Create a resolved expression for a bool b
    /// </summary>
    public static Expression CreateBoolLiteral(bool b) {
      var lit = new LiteralExpr(b);
      lit.Type = Type.Bool;  // resolve here
      return lit;
    }

    public static ThisExpr AsThis(Expression expr) {
      Contract.Requires(expr != null);
      return expr as ThisExpr;
    }

    /// <summary>
    /// If "expr" denotes a boolean literal "b", then return "true" and set "value" to "b".
    /// Otherwise, return "false" (and the value of "value" should not be used by the caller).
    /// This method can be called before resolution.
    /// </summary>
    public static bool IsBoolLiteral(Expression expr, out bool value) {
      Contract.Requires(expr != null);
      var e = expr as LiteralExpr;
      if (e != null && e.Value is bool) {
        value = (bool)e.Value;
        return true;
      } else {
        value = false;  // to please compiler
        return false;
      }
    }

    /// <summary>
    /// Returns "true" if "expr" denotes the empty set (for "iset", "set", or "multiset").
    /// This method can be called before resolution.
    /// </summary>
    public static bool IsEmptySetOrMultiset(Expression expr) {
      Contract.Requires(expr != null);
      return (expr is SetDisplayExpr && ((SetDisplayExpr)expr).Elements.Count == 0) ||
        (expr is MultiSetDisplayExpr && ((MultiSetDisplayExpr)expr).Elements.Count == 0);
    }

    public static Expression CreateNot(Expression e) {
      Contract.Requires(e.Type.IsBoolType);
      var un = new UnaryOpExpr(UnaryOpExpr.Opcode.Not, e);
      un.Type = Type.Bool;  // resolve here
      return un;
    }

    /// <summary>
    /// Create a resolved expression of the form "e0 LESS e1"
    /// </summary>
    public static Expression CreateLess(Expression e0, Expression e1) {
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);
      Contract.Requires(
        (e0.Type.IsNumericBased(Type.NumericPersuation.Int) && e1.Type.IsNumericBased(Type.NumericPersuation.Int)) ||
        (e0.Type.IsBigOrdinalType && e1.Type.IsBigOrdinalType));
      Contract.Ensures(Contract.Result<Expression>() != null);
      var s = new BinaryExpr(BinaryExpr.Opcode.Lt, e0, e1);
      s.ResolvedOp = BinaryExpr.ResolvedOpcode.Lt;  // resolve here
      s.Type = Type.Bool;  // resolve here
      return s;
    }

    /// <summary>
    /// Create a resolved expression of the form "e0 ATMOST e1"
    /// </summary>
    public static Expression CreateAtMost(Expression e0, Expression e1) {
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);
      Contract.Requires(
        (e0.Type.IsNumericBased(Type.NumericPersuation.Int) && e1.Type.IsNumericBased(Type.NumericPersuation.Int)) ||
        (e0.Type.IsNumericBased(Type.NumericPersuation.Real) && e1.Type.IsNumericBased(Type.NumericPersuation.Real)));
      Contract.Ensures(Contract.Result<Expression>() != null);
      var s = new BinaryExpr(BinaryExpr.Opcode.Le, e0, e1);
      s.ResolvedOp = BinaryExpr.ResolvedOpcode.Le;  // resolve here
      s.Type = Type.Bool;  // resolve here
      return s;
    }

    public static Expression CreateEq(Expression e0, Expression e1, Type ty) {
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);
      Contract.Requires(ty != null);
      var eq = new BinaryExpr(BinaryExpr.Opcode.Eq, e0, e1);
      if (ty is SetType) {
        eq.ResolvedOp = BinaryExpr.ResolvedOpcode.SetEq;
      } else if (ty is SeqType) {
        eq.ResolvedOp = BinaryExpr.ResolvedOpcode.SeqEq;
      } else if (ty is MultiSetType) {
        eq.ResolvedOp = BinaryExpr.ResolvedOpcode.MultiSetEq;
      } else if (ty is MapType) {
        eq.ResolvedOp = BinaryExpr.ResolvedOpcode.MapEq;
      } else {
        eq.ResolvedOp = BinaryExpr.ResolvedOpcode.EqCommon;
      }
      eq.type = Type.Bool;
      return eq;
    }

    /// <summary>
    /// Create a resolved expression of the form "e0 && e1"
    /// </summary>
    public static Expression CreateAnd(Expression a, Expression b) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      Contract.Requires(a.Type.IsBoolType && b.Type.IsBoolType);
      Contract.Ensures(Contract.Result<Expression>() != null);
      if (LiteralExpr.IsTrue(a)) {
        return b;
      } else if (LiteralExpr.IsTrue(b)) {
        return a;
      } else {
        var and = new BinaryExpr(BinaryExpr.Opcode.And, a, b);
        and.ResolvedOp = BinaryExpr.ResolvedOpcode.And;  // resolve here
        and.Type = Type.Bool;  // resolve here
        return and;
      }
    }

    /// <summary>
    /// Create a resolved expression of the form "e0 ==> e1"
    /// </summary>
    public static Expression CreateImplies(Expression a, Expression b) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      Contract.Requires(a.Type.IsBoolType && b.Type.IsBoolType);
      Contract.Ensures(Contract.Result<Expression>() != null);
      if (LiteralExpr.IsTrue(a) || LiteralExpr.IsTrue(b)) {
        return b;
      } else {
        var imp = new BinaryExpr(BinaryExpr.Opcode.Imp, a, b);
        imp.ResolvedOp = BinaryExpr.ResolvedOpcode.Imp;  // resolve here
        imp.Type = Type.Bool;  // resolve here
        return imp;
      }
    }

    /// <summary>
    /// Create a resolved expression of the form "if test then e0 else e1"
    /// </summary>
    public static Expression CreateITE(Expression test, Expression e0, Expression e1) {
      Contract.Requires(test != null);
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);
      Contract.Requires(test.Type.IsBoolType && e0.Type.Equals(e1.Type));
      Contract.Ensures(Contract.Result<Expression>() != null);
      var ite = new ITEExpr(false, test, e0, e1);
      ite.Type = e0.type;  // resolve here
      return ite;
    }

    /// <summary>
    /// Create a resolved case expression for a match expression
    /// </summary>
    public static MatchCaseExpr CreateMatchCase(MatchCaseExpr old_case, Expression new_body) {
      Contract.Requires(old_case != null);
      Contract.Requires(new_body != null);
      Contract.Ensures(Contract.Result<MatchCaseExpr>() != null);

      Cloner cloner = new Cloner();
      var newVars = old_case.Arguments.ConvertAll(cloner.CloneBoundVar);
      new_body = VarSubstituter(old_case.Arguments.ConvertAll<NonglobalVariable>(x=>(NonglobalVariable)x), newVars, new_body);

      var new_case = new MatchCaseExpr(old_case.Id, newVars, new_body);

      new_case.Ctor = old_case.Ctor; // resolve here
      return new_case;
    }

    /// <summary>
    /// Create a match expression with a resolved type
    /// </summary>
    public static Expression CreateMatch(Expression src, List<MatchCaseExpr> cases, Type type) {
      MatchExpr e = new MatchExpr(src, cases, false);
      e.Type = type;  // resolve here

      return e;
    }

    /// <summary>
    /// Create a let expression with a resolved type and fresh variables
    /// </summary>
    public static Expression CreateLet(List<CasePattern<BoundVar>> LHSs, List<Expression> RHSs, Expression body, bool exact) {
      Contract.Requires(LHSs != null && RHSs != null);
      Contract.Requires(LHSs.Count == RHSs.Count);
      Contract.Requires(body != null);

      Cloner cloner = new Cloner();
      var newLHSs = LHSs.ConvertAll<CasePattern<BoundVar>>(cloner.CloneCasePattern<BoundVar>);

      var oldVars = new List<BoundVar>();
      LHSs.Iter(p => oldVars.AddRange(p.Vars));
      var newVars = new List<BoundVar>();
      newLHSs.Iter(p => newVars.AddRange(p.Vars));
      body = VarSubstituter(oldVars.ConvertAll<NonglobalVariable>(x => (NonglobalVariable)x), newVars, body);

      var let = new LetExpr(newLHSs, RHSs, body, exact);
      let.Type = body.Type;  // resolve here
      return let;
    }

    /// <summary>
    /// Create a quantifier expression with a resolved type and fresh variables
    /// Optionally replace the old body with the supplied argument
    /// </summary>
    public static Expression CreateQuantifier(QuantifierExpr expr, bool forall,  Expression body = null) {
      //(List<BoundVar> vars, Expression range, Expression body, Attributes attribs, Qu) {
      Contract.Requires(expr != null);

      ResolvedCloner cloner = new ResolvedCloner();
      var newVars = expr.BoundVars.ConvertAll(cloner.CloneBoundVar);

      if (body == null) {
        body = expr.Term;
      }

      body = VarSubstituter(expr.BoundVars.ConvertAll<NonglobalVariable>(x=>(NonglobalVariable)x), newVars, body);

      QuantifierExpr q;
      if (forall) {
        q = new ForallExpr(new List<TypeParameter>(), newVars, expr.Range, body, expr.Attributes);
      } else {
        q = new ExistsExpr(new List<TypeParameter>(), newVars, expr.Range, body, expr.Attributes);
      }
      q.Type = Type.Bool;

      return q;
    }

    /// <summary>
    /// Create a resolved IdentifierExpr (whose token is that of the variable)
    /// </summary>
    public static Expression CreateIdentExpr(IVariable v) {
      Contract.Requires(v != null);
      return new IdentifierExpr(v);
    }

    public static Expression VarSubstituter(List<NonglobalVariable> oldVars, List<BoundVar> newVars, Expression e, Dictionary<TypeParameter, Type> typeMap=null) {
      Contract.Requires(oldVars != null && newVars != null);
      Contract.Requires(oldVars.Count == newVars.Count);

      Dictionary<IVariable, Expression/*!*/> substMap = new Dictionary<IVariable, Expression>();
      if (typeMap == null) {
        typeMap = new Dictionary<TypeParameter, Type>();
      }

      for (int i = 0; i < oldVars.Count; i++) {
        substMap.Add(oldVars[i], new IdentifierExpr(newVars[i]));
      }

      Substituter sub = new Substituter(null, substMap, typeMap);
      return sub.Substitute(e);
    }

    /// <summary>
    /// Returns the string literal underlying an actual string literal (not as a sequence display of characters)
    /// </summary>
    /// <returns></returns>
    public string AsStringLiteral() {
      var le = this as StringLiteralExpr;
      return le == null ? null : le.Value as string;
    }
  }

  /// <summary>
  /// Instances of this class are introduced during resolution to indicate that a static method or function has
  /// been invoked without specifying a receiver (that is, by just giving the name of the enclosing class).
  /// </summary>
  public class StaticReceiverExpr : LiteralExpr
  {
    public readonly Type UnresolvedType;
    private bool Implicit;

    public StaticReceiverExpr(Type t, bool isImplicit) {
      Contract.Requires(t != null);
      UnresolvedType = t;
      Implicit = isImplicit;
    }

    /// <summary>
    /// Constructs a resolved LiteralExpr representing the fictitious static-receiver literal whose type is
    /// "cl" parameterized by the type arguments of "cl" itself.
    /// </summary>
    public StaticReceiverExpr(TopLevelDeclWithMembers cl, bool isImplicit)
    {
      Contract.Requires(cl != null);
      var typeArgs = cl.TypeArgs.ConvertAll(tp => (Type)new UserDefinedType(tp));
      Type = new UserDefinedType(cl is ClassDecl klass && klass.IsDefaultClass ? cl.Name : cl.Name + "?", cl, typeArgs);
      UnresolvedType = Type;
      Implicit = isImplicit;
    }

    /// <summary>
    /// Constructs a resolved LiteralExpr representing the fictitious literal whose type is
    /// "cl" parameterized according to the type arguments to "t".  It is assumed that "t" denotes
    /// a class or trait that (possibly reflexively or transitively) extends "cl".
    /// Examples:
    /// * If "t" denotes "C(G)" and "cl" denotes "C", then the type of the StaticReceiverExpr
    ///   will be "C(G)".
    /// * Suppose "C" is a class that extends a trait "T"; then, if "t" denotes "C" and "cl" denotes
    ///   "T", then the type of the StaticReceiverExpr will be "T".
    /// * In the future, Dafny will support type parameters for traits and for classes that implement
    ///   traits.  Then, suppose "C(X)" is a class that extends "T(f(X))", and that "T(Y)" is
    ///   a trait that in turn extends trait "W(g(Y))".  If "t" denotes type "C(G)" and "cl" denotes "W",
    ///   then type of the StaticReceiverExpr will be "T(g(f(G)))".
    /// </summary>
    public StaticReceiverExpr(UserDefinedType t, TopLevelDeclWithMembers cl, bool isImplicit) {
      Contract.Requires(t.ResolvedClass != null);
      Contract.Requires(cl != null);
      if (t.ResolvedClass != cl) {
        if (t.ResolvedClass is ClassDecl) {
          var orig = (ClassDecl)t.ResolvedClass;
          Contract.Assert(orig.TraitsObj.Contains(cl));  // Dafny currently supports only one level of inheritance from traits
          Contract.Assert(orig.TypeArgs.Count == 0);  // Dafny currently only allows type-parameter-less classes to extend traits
          Contract.Assert(cl.TypeArgs.Count == 0);  // Dafny currently does not support type parameters for traits
        }
        t = new UserDefinedType(cl.Name, cl, new List<Type>());
      }
      Type = t;
      UnresolvedType = Type;
      Implicit = isImplicit;
    }

    public override bool IsImplicit {
      get { return Implicit; }
    }
  }

  public class LiteralExpr : Expression {
    /// <summary>
    /// One of the following:
    ///   * 'null' for the 'null' literal (a special case of which is the subclass StaticReceiverExpr)
    ///   * a bool for a bool literal
    ///   * a BigInteger for int literal
    ///   * a Basetypes.BigDec for a (rational) real literal
    ///   * a string for a char literal
    ///     This case always uses the subclass CharLiteralExpr.
    ///     Note, a string is stored to keep any escape sequence, since this simplifies printing of the character
    ///     literal, both when pretty printed as a Dafny expression and when being compiled into C# code.  The
    ///     parser checks the validity of any escape sequence and the verifier deals with turning such into a
    ///     single character value.
    ///   * a string for a string literal
    ///     This case always uses the subclass StringLiteralExpr.
    ///     Note, the string is stored with all escapes as characters.  For example, the input string "hello\n" is
    ///     stored in a LiteralExpr has being 7 characters long, whereas the Dafny (and C#) length of this string is 6.
    ///     This simplifies printing of the string, both when pretty printed as a Dafny expression and when being
    ///     compiled into C# code.  The parser checks the validity of the escape sequences and the verifier deals
    ///     with turning them into single characters.
    /// </summary>
    public readonly object Value;

    [Pure]
    public static bool IsTrue(Expression e) {
      Contract.Requires(e != null);
      if (e is LiteralExpr) {
        LiteralExpr le = (LiteralExpr)e;
        return le.Value is bool && (bool)le.Value;
      } else {
        return false;
      }
    }

    public LiteralExpr() {
      this.Value = null;
    }

    public LiteralExpr(BigInteger n) {
      Contract.Requires(0 <= n.Sign);
      this.Value = n;
    }

    public LiteralExpr(Basetypes.BigDec n) {
      Contract.Requires(0 <= n.Mantissa.Sign);
      this.Value = n;
    }

    public LiteralExpr(int n) {
      Contract.Requires(0 <= n);
      this.Value = new BigInteger(n);
    }

    public LiteralExpr(bool b) {
      this.Value = b;
    }

    /// <summary>
    /// This constructor is to be used only with the StringLiteralExpr and CharLiteralExpr subclasses, for
    /// two reasons:  both of these literals store a string in .Value, and string literals also carry an
    /// additional field.
    /// </summary>
    protected LiteralExpr(string s) {
      Contract.Requires(s != null);
      this.Value = s;
    }
  }

  public class CharLiteralExpr : LiteralExpr
  {
    public CharLiteralExpr(string s)
      : base(s) {
      Contract.Requires(s != null);
    }
  }

  public class StringLiteralExpr : LiteralExpr
  {
    public readonly bool IsVerbatim;
    public StringLiteralExpr(string s, bool isVerbatim)
      : base(s) {
      Contract.Requires(s != null);
      IsVerbatim = isVerbatim;
    }
  }

  public class DatatypeValue : Expression {
    public readonly string DatatypeName;
    public readonly string MemberName;
    public readonly List<Expression> Arguments;
    public DatatypeCtor Ctor;  // filled in by resolution
    public List<Type> InferredTypeArgs = new List<Type>();  // filled in by resolution
    public bool IsCoCall;  // filled in by resolution
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(DatatypeName != null);
      Contract.Invariant(MemberName != null);
      Contract.Invariant(cce.NonNullElements(Arguments));
      Contract.Invariant(cce.NonNullElements(InferredTypeArgs));
      Contract.Invariant(Ctor == null || InferredTypeArgs.Count == Ctor.EnclosingDatatype.TypeArgs.Count);
    }

    public DatatypeValue(string datatypeName, string memberName, [Captured] List<Expression> arguments) {
      Contract.Requires(cce.NonNullElements(arguments));
      Contract.Requires(datatypeName != null);
      Contract.Requires(memberName != null);
      this.DatatypeName = datatypeName;
      this.MemberName = memberName;
      this.Arguments = arguments;
    }

    public override IEnumerable<Expression> SubExpressions {
      get { return Arguments; }
    }
  }

  public class ThisExpr : Expression {
    public ThisExpr() {
    }

    /// <summary>
    /// This constructor creates a ThisExpr and sets its Type field to denote the receiver type
    /// of member "m". This constructor is intended to be used by post-resolution code that needs
    /// to obtain a Dafny "this" expression.
    /// </summary>
    public ThisExpr(MemberDecl m)
      : base(UserDefinedType.GetReceiverType(m)) {
      Contract.Requires(m != null);
      Contract.Requires(m.EnclosingClass != null);
      Contract.Requires(!m.IsStatic);
    }

    /// <summary>
    /// This constructor creates a ThisExpr and sets its Type field to denote the receiver type
    /// of member "m". This constructor is intended to be used by post-resolution code that needs
    /// to obtain a Dafny "this" expression.
    /// </summary>
    public ThisExpr(TopLevelDeclWithMembers cl)
      : base(UserDefinedType.GetThisType(cl)) {
      Contract.Requires(cl != null);
    }
  }
  public class ExpressionPair {
    public Expression A, B;
    public ExpressionPair(Expression a, Expression b) {
      Contract.Requires(a != null);
      Contract.Requires(b != null);
      A = a;
      B = b;
    }
  }

  public class ImplicitThisExpr : ThisExpr {
    public ImplicitThisExpr() {
    }

    /// This constructor creates a ThisExpr and sets its Type field to denote the receiver type
    /// of member "m". This constructor is intended to be used by post-resolution code that needs
    /// to obtain a Dafny "this" expression.
    /// </summary>
    public ImplicitThisExpr(MemberDecl m)
      : base(m) {
      Contract.Requires(m != null);
      Contract.Requires(m.EnclosingClass != null);
      Contract.Requires(!m.IsStatic);
    }

    /// <summary>
    /// This constructor creates a ThisExpr and sets its Type field to denote the receiver type
    /// of member "m". This constructor is intended to be used by post-resolution code that needs
    /// to obtain a Dafny "this" expression.
    /// </summary>
    public ImplicitThisExpr(TopLevelDeclWithMembers cl)
      : base(cl) {
      Contract.Requires(cl != null);
    }

    public override bool IsImplicit {
      get { return true; }
    }
  }

  /// <summary>
  /// An ImplicitThisExpr_ConstructorCall is used in the .InitCall of a TypeRhs,
  /// which has a need for a "throw-away receiver".  Using a different type
  /// gives a way to distinguish this receiver from other receivers, which
  /// plays a role in checking the restrictions on divided block statements.
  /// </summary>
  public class ImplicitThisExpr_ConstructorCall : ImplicitThisExpr
  {
    public ImplicitThisExpr_ConstructorCall() {
    }
  }

  public class IdentifierExpr : Expression
  {
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Name != null);
    }

    public readonly string Name;
    public IVariable Var;  // filled in by resolution

    /// <summary>
    /// Constructs a resolved IdentifierExpr.
    /// </summary>
    public IdentifierExpr(IVariable v) {
      Contract.Requires(v != null);
      Name = v.Name;
      Var = v;
      Type = v.Type;
    }
  }

  /// <summary>
  /// This class is used only inside the resolver itself. It gets hung in the AST in uncompleted name segments.
  /// </summary>
  class Resolver_IdentifierExpr : Expression
  {
    // The Resolver_IdentifierExpr either uses Decl and TypeArgs:
    public readonly TopLevelDecl Decl;
    public readonly List<Type> TypeArgs;
    // ... or it uses TypeParamDecl:
    public readonly TypeParameter TypeParamDecl;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant((Decl != null) != (TypeParamDecl != null));  // The Decl / TypeParamDecl fields are exclusive
      Contract.Invariant((Decl != null) == (TypeArgs != null));  // The Decl / TypeArgs fields are used together
      Contract.Invariant(TypeArgs == null || TypeArgs.Count == Decl.TypeArgs.Count);
      Contract.Invariant(Type == null || (Type is ResolverType_Module && TypeParamDecl == null) || Type is ResolverType_Type);
    }

    public abstract class ResolverType : Type
    {
    }
    public class ResolverType_Module : ResolverType
    {
      [Pure]
      public override string TypeName(ModuleDefinition context, bool parseAble) {
        Contract.Assert(parseAble == false);
        return "#module";
      }
      public override bool Equals(Type that) {
        return that.NormalizeExpand() is ResolverType_Module;
      }
    }
    public class ResolverType_Type : ResolverType {
      [Pure]
      public override string TypeName(ModuleDefinition context, bool parseAble) {
        Contract.Assert(parseAble == false);
        return "#type";
      }
      public override bool Equals(Type that) {
        return that.NormalizeExpand() is ResolverType_Type;
      }
    }

    public Resolver_IdentifierExpr(TopLevelDecl decl, List<Type> typeArgs) {
      Contract.Requires(decl != null);
      Contract.Requires(typeArgs != null && typeArgs.Count == decl.TypeArgs.Count);
      Decl = decl;
      TypeArgs = typeArgs;
      Type = decl is ModuleDecl ? (Type)new ResolverType_Module() : new ResolverType_Type();
    }
    public Resolver_IdentifierExpr(TypeParameter tp) {
      Contract.Requires(tp != null);
      TypeParamDecl = tp;
      Type = new ResolverType_Type();
    }
  }

  public abstract class DisplayExpression : Expression {
    public readonly List<Expression> Elements;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(cce.NonNullElements(Elements));
    }

    public DisplayExpression(List<Expression> elements) {
      Contract.Requires(cce.NonNullElements(elements));
      Elements = elements;
    }

    public override IEnumerable<Expression> SubExpressions {
      get { return Elements; }
    }
  }

  public class SetDisplayExpr : DisplayExpression {
    public bool Finite;
    public SetDisplayExpr(bool finite, List<Expression> elements)
      : base(elements) {
      Contract.Requires(cce.NonNullElements(elements));
      Finite = finite;
    }
  }

  public class MultiSetDisplayExpr : DisplayExpression {
    public MultiSetDisplayExpr(List<Expression> elements) : base(elements) {
      Contract.Requires(cce.NonNullElements(elements));
    }
  }

  public class MapDisplayExpr : Expression {
    public bool Finite;
    public List<ExpressionPair> Elements;
    public MapDisplayExpr(bool finite, List<ExpressionPair> elements) {
      Contract.Requires(cce.NonNullElements(elements));
      Finite = finite;
      Elements = elements;
    }
    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var ep in Elements) {
          yield return ep.A;
          yield return ep.B;
        }
      }
    }
  }
  public class SeqDisplayExpr : DisplayExpression {
    public SeqDisplayExpr(List<Expression> elements)
      : base(elements) {
      Contract.Requires(cce.NonNullElements(elements));
    }
  }

  public class MemberSelectExpr : Expression {
    public readonly Expression Obj;
    public readonly string MemberName;
    public MemberDecl Member;          // filled in by resolution, will be a Field or Function
    public List<Type> TypeApplication; // If Member is a Function or Method, then TypeApplication is the list of type arguments used with the enclosing class and the function/method itself; if it is a Field, then TypeApplication is the list of type arguments used with the enclosing class

    public Dictionary<TypeParameter, Type> TypeArgumentSubstitutions() {
      Contract.Ensures(Contract.Result<Dictionary<TypeParameter, Type>>() != null);
      Contract.Ensures(Contract.Result<Dictionary<TypeParameter, Type>>().Count == TypeApplication.Count);

      var icallable = Member as ICallable;
      Contract.Assert(Member.EnclosingClass.TypeArgs.Count + (icallable == null ? 0 : icallable.TypeArgs.Count) == TypeApplication.Count);  // a consequence of proper resolution
      var subst = new Dictionary<TypeParameter, Type>();
      var i = 0;
      foreach (var tp in Member.EnclosingClass.TypeArgs) {
        subst.Add(tp, TypeApplication[i]);
        i++;
      }
      if (icallable != null) {
        foreach (var tp in icallable.TypeArgs) {
          subst.Add(tp, TypeApplication[i]);
          i++;
        }
      }
      return subst;
    }

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Obj != null);
      Contract.Invariant(MemberName != null);
      Contract.Invariant((Member != null) == (TypeApplication != null));  // TypeApplication is set whenever Member is set
    }

    public MemberSelectExpr(Expression obj, string memberName) {
      Contract.Requires(obj != null);
      Contract.Requires(memberName != null);
      this.Obj = obj;
      this.MemberName = memberName;
    }

    /// <summary>
    /// Returns a resolved MemberSelectExpr for a field.
    /// </summary>
    public MemberSelectExpr(Expression obj, Field field)
      : this(obj, field.Name)
    {
      Contract.Requires(obj != null);
      Contract.Requires(field != null);
      Contract.Requires(obj.Type != null);  // "obj" is required to be resolved
      this.Member = field;  // resolve here
      if (field.EnclosingClass is TraitDecl) {
        // It could be that the type of "obj" is a class that implements the trait.  If so,
        // it would be necessary to map the class type instantiation to a type instantiation
        // of the trait.  However, at present in Dafny, traits take no type arguments, so
        // our job is easy.
        Contract.Assert(field.EnclosingClass.TypeArgs.Count == 0);
        this.TypeApplication = new List<Type>();
      } else {
        var receiverType = obj.Type.NormalizeExpand();
        this.TypeApplication = receiverType.TypeArgs;  // resolve here
      }
      Contract.Assert(field.EnclosingClass == null || this.TypeApplication.Count == field.EnclosingClass.TypeArgs.Count);
      var subst = new Dictionary<TypeParameter, Type>();
      for (int i = 0; i < this.TypeApplication.Count; i++) {
        subst.Add(field.EnclosingClass.TypeArgs[i], this.TypeApplication[i]);
      }
      this.Type = field.Type.Subst(subst);  // resolve here
    }

    public void MemberSelectCase(Action<Field> fieldK, Action<Function> functionK) {
      MemberSelectCase<bool>(
        f => {
          fieldK(f);
          return true;
        },
        f => {
          functionK(f);
          return true;
        });
    }

    public A MemberSelectCase<A>(Func<Field,A> fieldK, Func<Function,A> functionK) {
      var field = Member as Field;
      var function = Member as Function;
      if (field != null) {
        return fieldK(field);
      } else {
        Contract.Assert(function != null);
        return functionK(function);
      }
    }

    public override IEnumerable<Expression> SubExpressions {
      get { yield return Obj; }
    }
  }

  public class SeqSelectExpr : Expression {
    public readonly bool SelectOne;  // false means select a range
    public readonly Expression Seq;
    public readonly Expression E0;
    public readonly Expression E1;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Seq != null);
      Contract.Invariant(!SelectOne || E1 == null);
    }

    public SeqSelectExpr(bool selectOne, Expression seq, Expression e0, Expression e1) {
      Contract.Requires(seq != null);
      Contract.Requires(!selectOne || e1 == null);

      SelectOne = selectOne;
      Seq = seq;
      E0 = e0;
      E1 = e1;
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        yield return Seq;
        if (E0 != null) yield return E0;
        if (E1 != null) yield return E1;
      }
    }
  }

  public class MultiSelectExpr : Expression {
    public readonly Expression Array;
    public readonly List<Expression> Indices;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Array != null);
      Contract.Invariant(cce.NonNullElements(Indices));
      Contract.Invariant(1 <= Indices.Count);
    }

    public MultiSelectExpr(Expression array, List<Expression> indices) {
      Contract.Requires(array != null);
      Contract.Requires(cce.NonNullElements(indices) && 1 <= indices.Count);

      Array = array;
      Indices = indices;
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        yield return Array;
        foreach (var e in Indices) {
          yield return e;
        }
      }
    }
  }

  /// <summary>
  /// Represents an expression of the form A[B := C], where, syntactically, A, B, and C are expressions.
  /// Successfully resolved, the expression stands for one of the following:
  /// * if A is a sequence, then B is an integer-based index into the sequence and C's type is the sequence element type
  /// * if A is a map(T,U), then B is a key of type T and C is a value of type U
  /// * if A is a multiset, then B's type is the multiset element type and C is an integer-based numeric
  /// * if A is a datatype, then B is the name of a destructor of A's type and C's type is the type of that destructor -- in
  ///   this case, the resolver will set the ResolvedUpdateExpr to an expression that constructs an appropriate datatype value
  /// </summary>
  public class SeqUpdateExpr : Expression {
    public readonly Expression Seq;
    public readonly Expression Index;
    public readonly Expression Value;
    public Expression ResolvedUpdateExpr;       // filled in during resolution, if the SeqUpdateExpr corresponds to a datatype update
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Seq != null);
      Contract.Invariant(Index != null);
      Contract.Invariant(Value != null);
    }

    public SeqUpdateExpr(Expression seq, Expression index, Expression val) {
      Contract.Requires(seq != null);
      Contract.Requires(index != null);
      Contract.Requires(val != null);
      Seq = seq;
      Index = index;
      Value = val;
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        if (ResolvedUpdateExpr == null)
        {
          yield return Seq;
          yield return Index;
          yield return Value;
        }
        else
        {
          foreach (var e in ResolvedUpdateExpr.SubExpressions)
          {
            yield return e;
          }
        }
      }
    }
  }

  public class ApplyExpr : Expression {
    // The idea is that this apply expression does not need a type argument substitution,
    // since lambda functions and anonymous functions are never polymorphic.
    // Make a FunctionCallExpr otherwise, to call a resolvable anonymous function.
    public readonly Expression Function;
    public readonly List<Expression> Args;

    public override IEnumerable<Expression> SubExpressions {
      get {
        yield return Function;
        foreach (var e in Args) {
          yield return e;
        }
      }
    }

    public ApplyExpr(Expression fn, List<Expression> args)
      : base()
    {
      Function = fn;
      Args = args;
    }
  }

  public class RevealExpr : Expression
  {
    public readonly Expression Expr;
    public Expression ResolvedExpression;

    public override IEnumerable<Expression> SubExpressions {
      get {
        if (ResolvedExpression != null) {
          yield return ResolvedExpression;
        }
      }
    }

    public RevealExpr(Expression expr) {
      this.Expr = expr;
    }
  }

  public class FunctionCallExpr : Expression {
    public readonly string Name;
    public readonly Expression Receiver;
    public readonly List<Expression> Args;
    public Dictionary<TypeParameter, Type> TypeArgumentSubstitutions;  // created, initialized, and used by resolution (and also used by translation)
    public enum CoCallResolution {
      No,
      Yes,
      NoBecauseFunctionHasSideEffects,
      NoBecauseFunctionHasPostcondition,
      NoBecauseRecursiveCallsAreNotAllowedInThisContext,
      NoBecauseIsNotGuarded,
      NoBecauseRecursiveCallsInDestructiveContext
    }
    public CoCallResolution CoCall = CoCallResolution.No;  // indicates whether or not the call is a co-recursive call; filled in by resolution
    public string CoCallHint = null;  // possible additional hint that can be used in verifier error message, filled in by resolver

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Name != null);
      Contract.Invariant(Receiver != null);
      Contract.Invariant(cce.NonNullElements(Args));
      Contract.Invariant(
        Function == null || TypeArgumentSubstitutions == null ||
        Contract.ForAll(
          Function.TypeArgs,
            a => TypeArgumentSubstitutions.ContainsKey(a)) &&
        Contract.ForAll(
          TypeArgumentSubstitutions.Keys,
            a => Function.TypeArgs.Contains(a) || Function.EnclosingClass.TypeArgs.Contains(a)));
    }

    public Function Function;  // filled in by resolution

    [Captured]
    public FunctionCallExpr(string fn, Expression receiver, [Captured] List<Expression> args) {
      Contract.Requires(fn != null);
      Contract.Requires(receiver != null);
      Contract.Requires(cce.NonNullElements(args));
      Contract.Ensures(type == null);
      Contract.Ensures(cce.Owner.Same(this, receiver));

      this.Name = fn;
      cce.Owner.AssignSame(this, receiver);
      this.Receiver = receiver;
      this.Args = args;
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        yield return Receiver;
        foreach (var e in Args) {
          yield return e;
        }
      }
    }
  }

  public class SeqConstructionExpr : Expression
  {
    public Expression N;
    public Expression Initializer;
    public SeqConstructionExpr(Expression length, Expression initializer)
      : base() {
      Contract.Requires(length != null);
      Contract.Requires(initializer != null);
      N = length;
      Initializer = initializer;
    }
    public override IEnumerable<Expression> SubExpressions {
      get {
        yield return N;
        yield return Initializer;
      }
    }
  }

  public class MultiSetFormingExpr : Expression
  {
    [Peer]
    public readonly Expression E;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(E != null);
    }

    [Captured]
    public MultiSetFormingExpr(Expression expr) {
      Contract.Requires(expr != null);
      cce.Owner.AssignSame(this, expr);
      E = expr;
    }

    public override IEnumerable<Expression> SubExpressions {
      get { yield return E; }
    }
  }

  public class OldExpr : Expression
  {
    [Peer]
    public readonly Expression E;
    public readonly string/*?*/ At;
    public Label AtLabel;  // filled in during resolution; after that, At==null iff AtLabel==null
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(E != null);
    }

    [Captured]
    public OldExpr(Expression expr, string at = null) {
      Contract.Requires(expr != null);
      cce.Owner.AssignSame(this, expr);
      E = expr;
      At = at;
    }

    public override IEnumerable<Expression> SubExpressions {
      get { yield return E; }
    }
  }

  public class UnchangedExpr : Expression
  {
    public readonly List<FrameExpression> Frame;
    public readonly string/*?*/ At;
    public Label AtLabel;  // filled in during resolution; after that, At==null iff AtLabel==null
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Frame != null);
    }

    public UnchangedExpr(List<FrameExpression> frame, string/*?*/ at) {
      Contract.Requires(frame != null);
      this.Frame = frame;
      this.At = at;
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var fe in Frame) {
          yield return fe.E;
        }
      }
    }
  }

  public abstract class UnaryExpr : Expression
  {
    public readonly Expression E;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(E != null);
    }

    public UnaryExpr(Expression e) {
      Contract.Requires(e != null);
      this.E = e;
    }

    public override IEnumerable<Expression> SubExpressions {
      get { yield return E; }
    }
  }

  public class UnaryOpExpr : UnaryExpr
  {
    public enum Opcode {
      Not,  // boolean negation or bitwise negation
      Cardinality,
      Fresh,
      Allocated,
      Lit,  // there is no syntax for this operator, but it is sometimes introduced during translation
    }
    public readonly Opcode Op;

    public UnaryOpExpr(Opcode op, Expression e)
      : base(e) {
      Contract.Requires(e != null);
      this.Op = op;
    }
  }

  public class ConversionExpr : UnaryExpr
  {
    public readonly Type ToType;
    public ConversionExpr(Expression expr, Type toType)
      : base(expr) {
      Contract.Requires(expr != null);
      Contract.Requires(toType != null);
      ToType = toType;
    }
  }

  public class BinaryExpr : Expression
  {
    public enum Opcode {
      Iff,
      Imp,
      Exp, // turned into Imp during resolution
      And,
      Or,
      Eq,
      Neq,
      Lt,
      Le,
      Ge,
      Gt,
      Disjoint,
      In,
      NotIn,
      LeftShift,
      RightShift,
      Add,
      Sub,
      Mul,
      Div,
      Mod,
      BitwiseAnd,
      BitwiseOr,
      BitwiseXor
    }
    public readonly Opcode Op;
    public enum ResolvedOpcode {
      YetUndetermined,  // the value before resolution has determined the value; .ResolvedOp should never be read in this state

      // logical operators
      Iff,
      Imp,
      And,
      Or,
      // non-collection types
      EqCommon,
      NeqCommon,
      // integers, reals, bitvectors
      Lt,
      LessThanLimit,  // a synonym for Lt for ORDINAL, used only during translation
      Le,
      Ge,
      Gt,
      Add,
      Sub,
      Mul,
      Div,
      Mod,
      // bitvectors
      LeftShift,
      RightShift,
      BitwiseAnd,
      BitwiseOr,
      BitwiseXor,
      // char
      LtChar,
      LeChar,
      GeChar,
      GtChar,
      // sets
      SetEq,
      SetNeq,
      ProperSubset,
      Subset,
      Superset,
      ProperSuperset,
      Disjoint,
      InSet,
      NotInSet,
      Union,
      Intersection,
      SetDifference,
      // multi-sets
      MultiSetEq,
      MultiSetNeq,
      MultiSubset,
      MultiSuperset,
      ProperMultiSubset,
      ProperMultiSuperset,
      MultiSetDisjoint,
      InMultiSet,
      NotInMultiSet,
      MultiSetUnion,
      MultiSetIntersection,
      MultiSetDifference,
      // Sequences
      SeqEq,
      SeqNeq,
      ProperPrefix,
      Prefix,
      Concat,
      InSeq,
      NotInSeq,
      // Maps
      MapEq,
      MapNeq,
      InMap,
      NotInMap,
      MapDisjoint,
      MapUnion,
      // datatypes
      RankLt,
      RankGt
    }
    private ResolvedOpcode _theResolvedOp = ResolvedOpcode.YetUndetermined;
    public ResolvedOpcode ResolvedOp {
      set {
        Contract.Assume(_theResolvedOp == ResolvedOpcode.YetUndetermined || _theResolvedOp == value);  // there's never a reason for resolution to change its mind, is there?
        _theResolvedOp = value;
      }
      get {
        Contract.Assume(_theResolvedOp != ResolvedOpcode.YetUndetermined);  // shouldn't read it until it has been properly initialized
        return _theResolvedOp;
      }
    }
    public ResolvedOpcode ResolvedOp_PossiblyStillUndetermined {  // offer a way to return _theResolveOp -- for experts only!
      get { return _theResolvedOp; }
    }
    public static bool IsEqualityOp(ResolvedOpcode op) {
      switch (op) {
        case ResolvedOpcode.EqCommon:
        case ResolvedOpcode.SetEq:
        case ResolvedOpcode.SeqEq:
        case ResolvedOpcode.MultiSetEq:
        case ResolvedOpcode.MapEq:
          return true;
        default:
          return false;
      }
    }

    public static Opcode ResolvedOp2SyntacticOp(ResolvedOpcode rop) {
      switch (rop) {
        case ResolvedOpcode.Iff: return Opcode.Iff;
        case ResolvedOpcode.Imp: return Opcode.Imp;
        case ResolvedOpcode.And: return Opcode.And;
        case ResolvedOpcode.Or: return Opcode.Or;

        case ResolvedOpcode.EqCommon:
        case ResolvedOpcode.SetEq:
        case ResolvedOpcode.MultiSetEq:
        case ResolvedOpcode.SeqEq:
        case ResolvedOpcode.MapEq:
          return Opcode.Eq;

        case ResolvedOpcode.NeqCommon:
        case ResolvedOpcode.SetNeq:
        case ResolvedOpcode.MultiSetNeq:
        case ResolvedOpcode.SeqNeq:
        case ResolvedOpcode.MapNeq:
          return Opcode.Neq;

        case ResolvedOpcode.Lt:
        case ResolvedOpcode.LtChar:
        case ResolvedOpcode.ProperSubset:
        case ResolvedOpcode.ProperMultiSuperset:
        case ResolvedOpcode.ProperPrefix:
        case ResolvedOpcode.RankLt:
          return Opcode.Lt;

        case ResolvedOpcode.Le:
        case ResolvedOpcode.LeChar:
        case ResolvedOpcode.Subset:
        case ResolvedOpcode.MultiSubset:
        case ResolvedOpcode.Prefix:
          return Opcode.Le;

        case ResolvedOpcode.Ge:
        case ResolvedOpcode.GeChar:
        case ResolvedOpcode.Superset:
        case ResolvedOpcode.MultiSuperset:
          return Opcode.Ge;

        case ResolvedOpcode.Gt:
        case ResolvedOpcode.GtChar:
        case ResolvedOpcode.ProperSuperset:
        case ResolvedOpcode.ProperMultiSubset:
        case ResolvedOpcode.RankGt:
          return Opcode.Gt;

        case ResolvedOpcode.LeftShift:
          return Opcode.LeftShift;

        case ResolvedOpcode.RightShift:
          return Opcode.RightShift;

        case ResolvedOpcode.Add:
        case ResolvedOpcode.Union:
        case ResolvedOpcode.MultiSetUnion:
        case ResolvedOpcode.MapUnion:
        case ResolvedOpcode.Concat:
          return Opcode.Add;

        case ResolvedOpcode.Sub:
        case ResolvedOpcode.SetDifference:
        case ResolvedOpcode.MultiSetDifference:
          return Opcode.Sub;

        case ResolvedOpcode.Mul:
        case ResolvedOpcode.Intersection:
        case ResolvedOpcode.MultiSetIntersection:
          return Opcode.Mul;

        case ResolvedOpcode.Div: return Opcode.Div;
        case ResolvedOpcode.Mod: return Opcode.Mod;

        case ResolvedOpcode.BitwiseAnd: return Opcode.BitwiseAnd;
        case ResolvedOpcode.BitwiseOr: return Opcode.BitwiseOr;
        case ResolvedOpcode.BitwiseXor: return Opcode.BitwiseXor;

        case ResolvedOpcode.Disjoint:
        case ResolvedOpcode.MultiSetDisjoint:
        case ResolvedOpcode.MapDisjoint:
          return Opcode.Disjoint;

        case ResolvedOpcode.InSet:
        case ResolvedOpcode.InMultiSet:
        case ResolvedOpcode.InSeq:
        case ResolvedOpcode.InMap:
          return Opcode.In;

        case ResolvedOpcode.NotInSet:
        case ResolvedOpcode.NotInMultiSet:
        case ResolvedOpcode.NotInSeq:
        case ResolvedOpcode.NotInMap:
          return Opcode.NotIn;

        case ResolvedOpcode.LessThanLimit:  // not expected here (but if it were, the same case as Lt could perhaps be used)
        default:
          Contract.Assert(false);  // unexpected ResolvedOpcode
          return Opcode.Add;  // please compiler
      }
    }

    public static string OpcodeString(Opcode op) {
      Contract.Ensures(Contract.Result<string>() != null);

      switch (op) {
        case Opcode.Iff:
          return "<==>";
        case Opcode.Imp:
          return "==>";
        case Opcode.Exp:
          return "<==";
        case Opcode.And:
          return "&&";
        case Opcode.Or:
          return "||";
        case Opcode.Eq:
          return "==";
        case Opcode.Lt:
          return "<";
        case Opcode.Gt:
          return ">";
        case Opcode.Le:
          return "<=";
        case Opcode.Ge:
          return ">=";
        case Opcode.Neq:
          return "!=";
        case Opcode.Disjoint:
          return "!!";
        case Opcode.In:
          return "in";
        case Opcode.NotIn:
          return "!in";
        case Opcode.LeftShift:
          return "<<";
        case Opcode.RightShift:
          return ">>";
        case Opcode.Add:
          return "+";
        case Opcode.Sub:
          return "-";
        case Opcode.Mul:
          return "*";
        case Opcode.Div:
          return "/";
        case Opcode.Mod:
          return "%";
        case Opcode.BitwiseAnd:
          return "&";
        case Opcode.BitwiseOr:
          return "|";
        case Opcode.BitwiseXor:
          return "^";
        default:
          Contract.Assert(false);
          throw new cce.UnreachableException();  // unexpected operator
      }
    }
    public readonly Expression E0;
    public readonly Expression E1;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(E0 != null);
      Contract.Invariant(E1 != null);
    }


    public BinaryExpr(Opcode op, Expression e0, Expression e1) {
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);
      this.Op = op;
      this.E0 = e0;
      this.E1 = e1;
    }

    /// <summary>
    /// Returns a resolved binary expression
    /// </summary>
    public BinaryExpr(BinaryExpr.ResolvedOpcode rop, Expression e0, Expression e1)
    : this(BinaryExpr.ResolvedOp2SyntacticOp(rop), e0, e1) {
      ResolvedOp = rop;
      Type = Type.Bool;
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        yield return E0;
        yield return E1;
      }
    }
  }

  public class TernaryExpr : Expression
  {
    public readonly Opcode Op;
    public readonly Expression E0;
    public readonly Expression E1;
    public readonly Expression E2;
    public enum Opcode { /*SOON: IfOp,*/ PrefixEqOp, PrefixNeqOp }
    public static readonly bool PrefixEqUsesNat = false;  // "k" is either a "nat" or an "ORDINAL"
    public TernaryExpr(Opcode op, Expression e0, Expression e1, Expression e2) {
      Contract.Requires(e0 != null);
      Contract.Requires(e1 != null);
      Contract.Requires(e2 != null);
      Op = op;
      E0 = e0;
      E1 = e1;
      E2 = e2;
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        yield return E0;
        yield return E1;
        yield return E2;
      }
    }
  }

  public class LetExpr : Expression, IAttributeBearingDeclaration
  {
    public readonly List<CasePattern<BoundVar>> LHSs;
    public readonly List<Expression> RHSs;
    public readonly Expression Body;
    public readonly bool Exact;  // Exact==true means a regular let expression; Exact==false means an assign-such-that expression
    public readonly Attributes Attributes;
    public List<ComprehensionExpr.BoundedPool> Constraint_Bounds;  // initialized and filled in by resolver; null for Exact=true and for when expression is in a ghost context
    // invariant Constraint_Bounds == null || Constraint_Bounds.Count == BoundVars.Count;
    private Expression translationDesugaring;  // filled in during translation, lazily; to be accessed only via Translation.LetDesugaring; always null when Exact==true
    private Translator lastTranslatorUsed; // avoid clashing desugaring between translators

    public void setTranslationDesugaring(Translator trans, Expression expr){
      lastTranslatorUsed = trans;
      translationDesugaring = expr;
    }

    public Expression getTranslationDesugaring(Translator trans) {
      if (lastTranslatorUsed == trans) {
        return translationDesugaring;
      } else {
        return null;
      }
    }

    public LetExpr(List<CasePattern<BoundVar>> lhss, List<Expression> rhss, Expression body, bool exact, Attributes attrs = null) {
      LHSs = lhss;
      RHSs = rhss;
      Body = body;
      Exact = exact;
      Attributes = attrs;
    }
    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in Attributes.SubExpressions(Attributes)) {
          yield return e;
        }
        foreach (var rhs in RHSs) {
          yield return rhs;
        }
        yield return Body;
      }
    }
    public IEnumerable<BoundVar> BoundVars {
      get {
        foreach (var lhs in LHSs) {
          foreach (var bv in lhs.Vars) {
            yield return bv;
          }
        }
      }
    }
  }

  // Represents expr Name: Body
  //         or expr Name: (assert Body == Contract; Body)
  public class NamedExpr : Expression
  {
    public readonly string Name;
    public readonly Expression Body;
    public readonly Expression Contract;

    public NamedExpr(string p, Expression body) {
      Name = p;
      Body = body;
    }
    public NamedExpr(string p, Expression body, Expression contract) {
      Name = p;
      Body = body;
      Contract = contract;
    }
    public override IEnumerable<Expression> SubExpressions {
      get {
        yield return Body;
        if (Contract != null) yield return Contract;
      }
    }
  }

  /// <summary>
  /// A ComprehensionExpr has the form:
  ///   BINDER x Attributes | Range(x) :: Term(x)
  /// When BINDER is "forall" or "exists", the range may be "null" (which stands for the logical value "true").
  /// For other BINDERs (currently, "set"), the range is non-null.
  /// where "Attributes" is optional, and "| Range(x)" is optional and defaults to "true".
  /// Currently, BINDER is one of the logical quantifiers "exists" or "forall".
  /// </summary>
  public abstract class ComprehensionExpr : Expression, IAttributeBearingDeclaration
  {
    public readonly List<BoundVar> BoundVars;
    public readonly Expression Range;
    private Expression term;
    public Expression Term { get { return term; } }

    public void UpdateTerm(Expression newTerm) {
      term = newTerm;
    }

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(BoundVars != null);
      Contract.Invariant(Term != null);
    }

    public Attributes Attributes;

    public abstract class BoundedPool {
      [Flags]
      public enum PoolVirtues { None = 0, Finite = 1, Enumerable = 2, IndependentOfAlloc = 4, IndependentOfAlloc_or_ExplicitAlloc = 8 }
      public abstract PoolVirtues Virtues { get; }
      /// <summary>
      /// A higher preference is better.
      /// A preference below 2 is a last-resort bounded pool. Bounds discovery will not consider
      /// such a pool to be final until there are no other choices.
      ///
      /// For easy reference, here is the BoundedPool hierarchy and their preference levels:
      ///
      /// 0: AllocFreeBoundedPool
      /// 0: ExplicitAllocatedBoundedPool
      /// 0: SpecialAllocIndependenceAllocatedBoundedPool
      ///
      /// 1: WiggleWaggleBound
      ///
      /// 2: SuperSetBoundedPool
      /// 2: DatatypeInclusionBoundedPool
      ///
      /// 3: SubSetBoundedPool
      ///
      /// 4: IntBoundedPool with one bound
      /// 5: IntBoundedPool with both bounds
      /// 5: CharBoundedPool
      ///
      /// 8: DatatypeBoundedPool
      ///
      /// 10: CollectionBoundedPool
      ///     - SetBoundedPool
      ///     - MapBoundedPool
      ///     - SeqBoundedPool
      ///
      /// 14: BoolBoundedPool
      ///
      /// 15: ExactBoundedPool
      /// </summary>
      public abstract int Preference(); // higher is better

      public static BoundedPool GetBest(List<BoundedPool> bounds, PoolVirtues requiredVirtues) {
        Contract.Requires(bounds != null);
        bounds = CombineIntegerBounds(bounds);
        BoundedPool best = null;
        foreach (var bound in bounds) {
          if ((bound.Virtues & requiredVirtues) == requiredVirtues) {
            if (best == null || bound.Preference() > best.Preference()) {
              best = bound;
            }
          }
        }
        return best;
      }
      public static List<VT> MissingBounds<VT>(List<VT> vars, List<BoundedPool> bounds, PoolVirtues requiredVirtues = PoolVirtues.None) where VT : IVariable {
        Contract.Requires(vars != null);
        Contract.Requires(bounds != null);
        Contract.Requires(vars.Count == bounds.Count);
        Contract.Ensures(Contract.Result<List<VT>>() != null);
        var missing = new List<VT>();
        for (var i = 0; i < vars.Count; i++) {
          if (bounds[i] == null || (bounds[i].Virtues & requiredVirtues) != requiredVirtues) {
            missing.Add(vars[i]);
          }
        }
        return missing;
      }
      public static List<bool> HasBounds(List<BoundedPool> bounds, PoolVirtues requiredVirtues = PoolVirtues.None) {
        Contract.Requires(bounds != null);
        Contract.Ensures(Contract.Result<List<bool>>() != null);
        Contract.Ensures(Contract.Result<List<bool>>().Count == bounds.Count);
        return bounds.ConvertAll(bound => bound != null && (bound.Virtues & requiredVirtues) == requiredVirtues);
      }
      static List<BoundedPool> CombineIntegerBounds(List<BoundedPool> bounds) {
        var lowerBounds = new List<IntBoundedPool>();
        var upperBounds = new List<IntBoundedPool>();
        var others = new List<BoundedPool>();
        foreach (var b in bounds) {
          var ib = b as IntBoundedPool;
          if (ib != null && ib.UpperBound == null) {
            lowerBounds.Add(ib);
          } else if (ib != null && ib.LowerBound == null) {
            upperBounds.Add(ib);
          } else {
            others.Add(b);
          }
        }
        // pair up the bounds
        var n = Math.Min(lowerBounds.Count, upperBounds.Count);
        for (var i = 0; i < n; i++) {
          others.Add(new IntBoundedPool(lowerBounds[i].LowerBound, upperBounds[i].UpperBound));
        }
        for (var i = n; i < lowerBounds.Count; i++) {
          others.Add(lowerBounds[i]);
        }
        for (var i = n; i < upperBounds.Count; i++) {
          others.Add(upperBounds[i]);
        }
        return others;
      }
    }
    public class ExactBoundedPool : BoundedPool
    {
      public readonly Expression E;
      public ExactBoundedPool(Expression e) {
        Contract.Requires(e != null);
        E = e;
      }
      public override PoolVirtues Virtues => PoolVirtues.Finite | PoolVirtues.Enumerable | PoolVirtues.IndependentOfAlloc | PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
      public override int Preference() => 15;  // the best of all bounds
    }
    public class BoolBoundedPool : BoundedPool
    {
      public override PoolVirtues Virtues => PoolVirtues.Finite | PoolVirtues.Enumerable | PoolVirtues.IndependentOfAlloc | PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
      public override int Preference() => 14;
    }
    public class CharBoundedPool : BoundedPool
    {
      public override PoolVirtues Virtues => PoolVirtues.Finite | PoolVirtues.Enumerable | PoolVirtues.IndependentOfAlloc | PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
      public override int Preference() => 5;
    }
    public class AllocFreeBoundedPool : BoundedPool
    {
      public Type Type;
      public AllocFreeBoundedPool(Type t) {
        Type = t;
      }
      public override PoolVirtues Virtues {
        get {
          if (Type.IsRefType) {
            return PoolVirtues.Finite | PoolVirtues.IndependentOfAlloc | PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
          } else {
            return PoolVirtues.IndependentOfAlloc | PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
          }
        }
      }
      public override int Preference() => 0;
    }
    public class ExplicitAllocatedBoundedPool : BoundedPool
    {
      public ExplicitAllocatedBoundedPool() {
      }
      public override PoolVirtues Virtues => PoolVirtues.Finite | PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
      public override int Preference() => 0;
    }
    public class SpecialAllocIndependenceAllocatedBoundedPool : BoundedPool
    {
      public SpecialAllocIndependenceAllocatedBoundedPool() {
      }
      public override PoolVirtues Virtues => PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
      public override int Preference() => 0;
    }
    public class IntBoundedPool : BoundedPool
    {
      public readonly Expression LowerBound;
      public readonly Expression UpperBound;
      public IntBoundedPool(Expression lowerBound, Expression upperBound) {
        Contract.Requires(lowerBound != null || upperBound != null);
        LowerBound = lowerBound;
        UpperBound = upperBound;
      }
      public override PoolVirtues Virtues {
        get {
          if (LowerBound != null && UpperBound != null) {
            return PoolVirtues.Finite | PoolVirtues.Enumerable | PoolVirtues.IndependentOfAlloc | PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
          } else {
            return PoolVirtues.Enumerable | PoolVirtues.IndependentOfAlloc | PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
          }
        }
      }
      public override int Preference() => LowerBound != null && UpperBound != null ? 5 : 4;
    }
    public abstract class CollectionBoundedPool : BoundedPool
    {
      public readonly bool ExactTypes;
      public readonly bool IsFiniteCollection;
      public CollectionBoundedPool(bool exactTypes, bool isFiniteCollection) {
        ExactTypes = exactTypes;
        IsFiniteCollection = isFiniteCollection;
      }
      public override PoolVirtues Virtues {
        get {
          var v = PoolVirtues.IndependentOfAlloc;
          if (IsFiniteCollection) {
            v |= PoolVirtues.Finite;
            if (ExactTypes) {
              v |= PoolVirtues.Enumerable | PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
            }
          }
          return v;
        }
      }
      public override int Preference() => 10;
    }
    public class SetBoundedPool : CollectionBoundedPool
    {
      public readonly Expression Set;
      public SetBoundedPool(Expression set, bool exactTypes, bool isFiniteCollection) : base(exactTypes, isFiniteCollection) { Set = set; }
    }
    public class SubSetBoundedPool : BoundedPool
    {
      public readonly Expression UpperBound;
      public readonly bool IsFiniteCollection;
      public SubSetBoundedPool(Expression set, bool isFiniteCollection) {
        UpperBound = set;
        IsFiniteCollection = isFiniteCollection;
      }
      public override PoolVirtues Virtues {
        get {
          if (IsFiniteCollection) {
            return PoolVirtues.Finite | PoolVirtues.Enumerable | PoolVirtues.IndependentOfAlloc | PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
          } else {
            // it's still enumerable, because at run time, all sets are finite after all
            return PoolVirtues.Enumerable | PoolVirtues.IndependentOfAlloc | PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
          }
        }
      }
      public override int Preference() => 3;
    }
    public class SuperSetBoundedPool : BoundedPool
    {
      public readonly Expression LowerBound;
      public SuperSetBoundedPool(Expression set) { LowerBound = set; }
      public override int Preference() => 2;
      public override PoolVirtues Virtues {
        get {
          if (LowerBound.Type.IsAllocFree) {
            return PoolVirtues.IndependentOfAlloc | PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
          } else {
            return PoolVirtues.None;
          }
        }
      }
    }
    public class MultiSetBoundedPool : CollectionBoundedPool
    {
      public readonly Expression MultiSet;
      public MultiSetBoundedPool(Expression multiset, bool exactTypes) : base(exactTypes, true) { MultiSet = multiset; }
    }
    public class MapBoundedPool : CollectionBoundedPool
    {
      public readonly Expression Map;
      public MapBoundedPool(Expression map, bool exactTypes, bool isFiniteCollection) : base(exactTypes, isFiniteCollection) { Map = map; }
    }
    public class SeqBoundedPool : CollectionBoundedPool
    {
      public readonly Expression Seq;
      public SeqBoundedPool(Expression seq, bool exactTypes) : base(exactTypes, true) { Seq = seq; }
    }
    public class DatatypeBoundedPool : BoundedPool
    {
      public readonly DatatypeDecl Decl;
      public DatatypeBoundedPool(DatatypeDecl d) { Decl = d; }
      public override PoolVirtues Virtues => PoolVirtues.Finite | PoolVirtues.Enumerable | PoolVirtues.IndependentOfAlloc | PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
      public override int Preference() => 8;
    }
    public class DatatypeInclusionBoundedPool : BoundedPool
    {
      public readonly bool IsIndDatatype;
      public DatatypeInclusionBoundedPool(bool isIndDatatype) : base() { IsIndDatatype = isIndDatatype; }
      public override PoolVirtues Virtues => (IsIndDatatype ? PoolVirtues.Finite : PoolVirtues.None) | PoolVirtues.IndependentOfAlloc | PoolVirtues.IndependentOfAlloc_or_ExplicitAlloc;
      public override int Preference() => 2;
    }

    public List<BoundedPool> Bounds;  // initialized and filled in by resolver
    // invariant Bounds == null || Bounds.Count == BoundVars.Count;

    public List<BoundVar> UncompilableBoundVars() {
      Contract.Ensures(Contract.Result<List<BoundVar>>() != null);
      var v = BoundedPool.PoolVirtues.Finite | BoundedPool.PoolVirtues.Enumerable;
      return ComprehensionExpr.BoundedPool.MissingBounds(BoundVars, Bounds, v);
    }

    public ComprehensionExpr(List<BoundVar> bvars, Expression range, Expression term, Attributes attrs) {
      Contract.Requires(cce.NonNullElements(bvars));
      Contract.Requires(term != null);

      this.BoundVars = bvars;
      this.Range = range;
      this.UpdateTerm(term);
      this.Attributes = attrs;
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in Attributes.SubExpressions(Attributes)) {
          yield return e;
        }
        if (Range != null) { yield return Range; }
        yield return Term;
      }
    }
  }

  public abstract class QuantifierExpr : ComprehensionExpr, TypeParameter.ParentType {
    private readonly int UniqueId;
    public List<TypeParameter> TypeArgs;
    private static int currentQuantId = -1;

    protected virtual BinaryExpr.ResolvedOpcode SplitResolvedOp { get { return BinaryExpr.ResolvedOpcode.Or; } }

    private Expression SplitQuantifierToExpression() {
      Contract.Requires(SplitQuantifier != null && SplitQuantifier.Any());
      Expression accumulator = SplitQuantifier[0];
      for (int tid = 1; tid < SplitQuantifier.Count; tid++) {
        accumulator = new BinaryExpr(SplitResolvedOp, accumulator, SplitQuantifier[tid]);
      }
      return accumulator;
    }

    private List<Expression> _SplitQuantifier;
    public List<Expression> SplitQuantifier {
      get {
        return _SplitQuantifier;
      }
      set {
        Contract.Assert(!value.Contains(this)); // don't let it put into its own split quantifiers.
        _SplitQuantifier = value;
        SplitQuantifierExpression = SplitQuantifierToExpression();
      }
    }

    internal Expression SplitQuantifierExpression { get; private set; }

    static int FreshQuantId() {
      return System.Threading.Interlocked.Increment(ref currentQuantId);
    }

    public string FullName {
      get {
        return "q$" + UniqueId;
      }
    }

    public String Refresh(string prefix, FreshIdGenerator idGen) {
      return idGen.FreshId(prefix);
    }

    public TypeParameter Refresh(TypeParameter p, FreshIdGenerator idGen) {
      var cp = new TypeParameter(idGen.FreshId(p.Name + "#"), p.VarianceSyntax, p.Characteristics);
      cp.Parent = this;
      return cp;
    }
    [ContractInvariantMethod]
    void ObjectInvariant() {
      var _scratch = true;
      Contract.Invariant(Attributes.ContainsBool(Attributes, "typeQuantifier", ref _scratch) || TypeArgs.Count == 0);
    }
    public QuantifierExpr(List<TypeParameter> tvars, List<BoundVar> bvars, Expression range, Expression term, Attributes attrs)
      : base(bvars, range, term, attrs) {
      Contract.Requires(cce.NonNullElements(bvars));
      Contract.Requires(term != null);
      this.TypeArgs = tvars;
      this.UniqueId = FreshQuantId();
    }

    public virtual Expression LogicalBody(bool bypassSplitQuantifier = false) {
      // Don't call this on a quantifier with a Split clause: it's not a real quantifier. The only exception is the Compiler.
      Contract.Requires(bypassSplitQuantifier || SplitQuantifier == null);
      throw new cce.UnreachableException(); // This body is just here for the "Requires" clause
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        if (SplitQuantifier == null) {
          foreach (var e in base.SubExpressions) {
            yield return e;
          }
        } else {
          foreach (var e in Attributes.SubExpressions(Attributes)) {
            yield return e;
          }
          foreach (var e in SplitQuantifier) {
            yield return e;
          }
        }
      }
    }
  }

  public class ForallExpr : QuantifierExpr {
    protected override BinaryExpr.ResolvedOpcode SplitResolvedOp { get { return BinaryExpr.ResolvedOpcode.And; } }

    public ForallExpr(List<BoundVar> bvars, Expression range, Expression term, Attributes attrs)
      : this(new List<TypeParameter>(), bvars, range, term, attrs) {
      Contract.Requires(cce.NonNullElements(bvars));
      Contract.Requires(term != null);
    }
    public ForallExpr(List<TypeParameter> tvars, List<BoundVar> bvars, Expression range, Expression term, Attributes attrs)
      : base(tvars, bvars, range, term, attrs) {
      Contract.Requires(cce.NonNullElements(bvars));
      Contract.Requires(term != null);
    }
    public override Expression LogicalBody(bool bypassSplitQuantifier = false) {
      if (Range == null) {
        return Term;
      }
      var body = new BinaryExpr(BinaryExpr.Opcode.Imp, Range, Term);
      body.ResolvedOp = BinaryExpr.ResolvedOpcode.Imp;
      body.Type = Term.Type;
      return body;
    }
  }

  public class ExistsExpr : QuantifierExpr {
    protected override BinaryExpr.ResolvedOpcode SplitResolvedOp { get { return BinaryExpr.ResolvedOpcode.Or; } }

    public ExistsExpr(List<BoundVar> bvars, Expression range, Expression term, Attributes attrs)
      : this(new List<TypeParameter>(), bvars, range, term, attrs) {
      Contract.Requires(cce.NonNullElements(bvars));
      Contract.Requires(term != null);
    }
    public ExistsExpr(List<TypeParameter> tvars, List<BoundVar> bvars, Expression range, Expression term, Attributes attrs)
      : base(tvars, bvars, range, term, attrs) {
      Contract.Requires(cce.NonNullElements(bvars));
      Contract.Requires(term != null);
    }
    public override Expression LogicalBody(bool bypassSplitQuantifier = false) {
      if (Range == null) {
        return Term;
      }
      var body = new BinaryExpr(BinaryExpr.Opcode.And, Range, Term);
      body.ResolvedOp = BinaryExpr.ResolvedOpcode.And;
      body.Type = Term.Type;
      return body;
    }
  }

  public class SetComprehension : ComprehensionExpr
  {
    public readonly bool Finite;
    public readonly bool TermIsImplicit;  // records the given syntactic form
    public bool TermIsSimple {
      get {
        var term = Term as IdentifierExpr;
        var r = term != null && BoundVars.Count == 1 && BoundVars[0].Name == term.Name;
        Contract.Assert(!TermIsImplicit || r);  // TermIsImplicit ==> r
        Contract.Assert(!r || term.Var == null || term.Var == BoundVars[0]);  // if the term is simple and it has been resolved, then it should have resolved to BoundVars[0]
        return r;
      }
    }

    public SetComprehension(bool finite, List<BoundVar> bvars, Expression range, Expression/*?*/ term, Attributes attrs)
      : base(bvars, range, term ?? new IdentifierExpr(bvars[0]), attrs) {
      Contract.Requires(cce.NonNullElements(bvars));
      Contract.Requires(1 <= bvars.Count);
      Contract.Requires(range != null);
      Contract.Requires(term != null || bvars.Count == 1);

      TermIsImplicit = term == null;
      Finite = finite;
    }
  }
  public class MapComprehension : ComprehensionExpr
  {
    public readonly bool Finite;
    public readonly Expression TermLeft;

    public List<Boogie.Function> ProjectionFunctions;  // filled in during translation (and only for general map comprehensions where "TermLeft != null")

    public MapComprehension(bool finite, List<BoundVar> bvars, Expression range, Expression/*?*/ termLeft, Expression termRight, Attributes attrs)
      : base(bvars, range, termRight, attrs) {
      Contract.Requires(cce.NonNullElements(bvars));
      Contract.Requires(1 <= bvars.Count);
      Contract.Requires(range != null);
      Contract.Requires(termRight != null);
      Contract.Requires(termLeft != null || bvars.Count == 1);

      Finite = finite;
      TermLeft = termLeft;
    }

    /// <summary>
    /// IsGeneralMapComprehension returns true for general map comprehensions.
    /// In other words, it returns false if either no TermLeft was given or if
    /// the given TermLeft is the sole bound variable.
    /// This property getter requires that the expression has been successfully
    /// resolved.
    /// </summary>
    public bool IsGeneralMapComprehension {
      get {
        if (TermLeft == null) {
          return false;
        } else if (BoundVars.Count != 1) {
          return true;
        }
        if (TermLeft is IdentifierExpr ide && ide.Var == BoundVars[0]) {
          // TermLeft is the sole bound variable, so this is the same as
          // if TermLeft wasn't given at all
          return false;
        }
        return true;
      }
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        foreach (var e in Attributes.SubExpressions(Attributes)) {
          yield return e;
        }
        if (Range != null) { yield return Range; }
        if (TermLeft != null) { yield return TermLeft; }
        yield return Term;
      }
    }
  }

  public class LambdaExpr : ComprehensionExpr
  {
    public readonly List<FrameExpression> Reads;

    public LambdaExpr(List<BoundVar> bvars, Expression requires, List<FrameExpression> reads, Expression body)
      : base(bvars, requires, body, null)
    {
      Contract.Requires(reads != null);
      Reads = reads;
    }

    // Synonym
    public Expression Body {
      get {
        return Term;
      }
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        yield return Term;
        if (Range != null) {
          yield return Range;
        }
        foreach (var read in Reads) {
          yield return read.E;
        }
      }
    }

  }


  public class WildcardExpr : Expression
  {  // a WildcardExpr can occur only in reads clauses and a loop's decreases clauses (with different meanings)
    public WildcardExpr() {
    }
  }

  /// <summary>
  /// A StmtExpr has the form S;E where S is a statement (from a restricted set) and E is an expression.
  /// The expression S;E evaluates to whatever E evaluates to, but its well-formedness comes down to
  /// executing S (which itself must be well-formed) and then checking the well-formedness of E.
  /// </summary>
  public class StmtExpr : Expression
  {
    public readonly Statement S;
    public readonly Expression E;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(S != null);
      Contract.Invariant(E != null);
    }

    public StmtExpr(Statement stmt, Expression expr)
    {
      Contract.Requires(stmt != null);
      Contract.Requires(expr != null);
      S = stmt;
      E = expr;
    }
    public override IEnumerable<Expression> SubExpressions {
      get {
        // Note:  A StmtExpr is unusual in that it contains a statement.  For now, callers
        // of SubExpressions need to be aware of this and handle it specially.
        yield return E;
      }
    }

    /// <summary>
    /// Returns a conclusion that S gives rise to, that is, something that is known after
    /// S is executed.
    /// This method should be called only after successful resolution of the expression.
    /// </summary>
    public Expression GetSConclusion() {
      // this is one place where we actually investigate what kind of statement .S is
      if (S is PredicateStmt) {
        var s = (PredicateStmt)S;
        return s.Expr;
      } else if (S is CalcStmt) {
        var s = (CalcStmt)S;
        return s.Result;
      } else if (S is UpdateStmt) {
        return new LiteralExpr(true);  // one could use the postcondition of the method, suitably instantiated, but "true" is conservative and much simpler :)
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected statement
      }
    }
  }

  public class ITEExpr : Expression
  {
    public readonly bool IsBindingGuard;
    public readonly Expression Test;
    public readonly Expression Thn;
    public readonly Expression Els;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Test != null);
      Contract.Invariant(Thn != null);
      Contract.Invariant(Els != null);
    }

    public ITEExpr(bool isBindingGuard, Expression test, Expression thn, Expression els) {
      Contract.Requires(test != null);
      Contract.Requires(thn != null);
      Contract.Requires(els != null);
      this.IsBindingGuard = isBindingGuard;
      this.Test = test;
      this.Thn = thn;
      this.Els = els;
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        yield return Test;
        yield return Thn;
        yield return Els;
      }
    }
  }

  public class MatchExpr : Expression {  // a MatchExpr is an "extended expression" and is only allowed in certain places
    private Expression source;
    private List<MatchCaseExpr> cases;
    public readonly List<DatatypeCtor> MissingCases = new List<DatatypeCtor>();  // filled in during resolution
    public readonly bool UsesOptionalBraces;
    public MatchExpr OrigUnresolved;  // the resolver makes this clone of the MatchExpr before it starts desugaring it

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Source != null);
      Contract.Invariant(cce.NonNullElements(Cases));
      Contract.Invariant(cce.NonNullElements(MissingCases));
    }

    public MatchExpr(Expression source, [Captured] List<MatchCaseExpr> cases, bool usesOptionalBraces) {
      Contract.Requires(source != null);
      Contract.Requires(cce.NonNullElements(cases));
      this.source = source;
      this.cases = cases;
      this.UsesOptionalBraces = usesOptionalBraces;
    }

    public Expression Source {
      get { return source; }
    }

    public List<MatchCaseExpr> Cases {
      get { return cases; }
    }

    // should only be used in desugar in resolve to change the source and cases of the matchexpr
    public void UpdateSource(Expression source) {
      this.source = source;
    }

    public void UpdateCases(List<MatchCaseExpr> cases) {
      this.cases = cases;
    }

    public override IEnumerable<Expression> SubExpressions {
      get {
        yield return Source;
        foreach (var mc in cases) {
          yield return mc.Body;
        }
      }
    }
  }

  /// <summary>
  /// A CasePattern is either a BoundVar or a datatype constructor with optional arguments.
  /// Lexically, the CasePattern starts with an identifier.  If it continues with an open paren (as
  /// indicated by Arguments being non-null), then the CasePattern is a datatype constructor.  If
  /// it continues with a colon (which is indicated by Var.Type not being a proxy type), then it is
  /// a BoundVar.  But if it ends with just the identifier, then resolution is required to figure out
  /// which it is; in this case, Var is non-null, because this is the only place where Var.IsGhost
  /// is recorded by the parser.
  /// </summary>
  public class CasePattern<VT> where VT : IVariable
  {
    public readonly string Id;
    // After successful resolution, exactly one of the following two fields is non-null.
    public DatatypeCtor Ctor;  // finalized by resolution (null if the pattern is a bound variable)
    public VT Var;  // finalized by resolution (null if the pattern is a constructor)  Invariant:  Var != null ==> Arguments == null
    public readonly List<CasePattern<VT>> Arguments;

    public Expression Expr;  // an r-value version of the CasePattern; filled in by resolution

    public CasePattern(string id, [Captured] List<CasePattern<VT>> arguments) {
      Contract.Requires(id != null);
      Id = id;
      Arguments = arguments;
    }

    public CasePattern(VT bv) {
      Contract.Requires(bv != null);
      Id = bv.Name;
      Var = bv;
    }

    /// <summary>
    /// Sets the Expr field.  Assumes the CasePattern and its arguments to have been successfully resolved, except for assigning
    /// to Expr.
    /// </summary>
    public void AssembleExpr(List<Type> dtvTypeArgs) {
      Contract.Requires(Var != null || dtvTypeArgs != null);
      if (Var != null) {
        Contract.Assert(this.Id == this.Var.Name);
        this.Expr = new IdentifierExpr(this.Var);
      } else {
        var dtValue = new DatatypeValue(this.Ctor.EnclosingDatatype.Name, this.Id, this.Arguments == null ? new List<Expression>() : this.Arguments.ConvertAll(arg => arg.Expr));
        dtValue.Ctor = this.Ctor;  // resolve here
        dtValue.InferredTypeArgs.AddRange(dtvTypeArgs);  // resolve here
        dtValue.Type = new UserDefinedType(this.Ctor.EnclosingDatatype.Name, this.Ctor.EnclosingDatatype, dtvTypeArgs);
        this.Expr = dtValue;
      }
    }

    public IEnumerable<VT> Vars {
      get {
        if (Var != null) {
          yield return Var;
        } else {
          if (Arguments != null) {
            foreach (var arg in Arguments) {
              foreach (var bv in arg.Vars) {
                yield return bv;
              }
            }
          }
        }
      }
    }
  }

  public abstract class MatchCase
  {
    public readonly string Id;
    public DatatypeCtor Ctor;  // filled in by resolution
    public List<BoundVar> Arguments; // created by the resolver.
    public List<CasePattern<BoundVar>> CasePatterns; // generated from parsers. It should be converted to List<BoundVar> during resolver. Invariant:  CasePatterns != null ==> Arguments == null
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(Id != null);
      Contract.Invariant(cce.NonNullElements(Arguments) || cce.NonNullElements(CasePatterns));
    }

    public MatchCase(string id, [Captured] List<BoundVar> arguments) {
      Contract.Requires(id != null);
      Contract.Requires(cce.NonNullElements(arguments));
      this.Id = id;
      this.Arguments = arguments;
    }

    public MatchCase(string id, [Captured] List<CasePattern<BoundVar>> cps) {
      Contract.Requires(id != null);
      Contract.Requires(cce.NonNullElements(cps));
      this.Id = id;
      this.CasePatterns = cps;
    }
  }

  public class MatchCaseExpr : MatchCase
  {
    private Expression body;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(body != null);
    }

    public MatchCaseExpr(string id, [Captured] List<BoundVar> arguments, Expression body)
      : base(id, arguments) {
      Contract.Requires(id != null);
      Contract.Requires(cce.NonNullElements(arguments));
      Contract.Requires(body != null);
      this.body = body;
    }

    public MatchCaseExpr(string id, [Captured] List<CasePattern<BoundVar>> cps, Expression body)
      : base(id, cps)
    {
      Contract.Requires(id != null);
      Contract.Requires(cce.NonNullElements(cps));
      Contract.Requires(body != null);
      this.body = body;
    }

    public Expression Body {
      get { return body; }
    }

    // should only be called by resolve to reset the body of the MatchCaseExpr
    public void UpdateBody(Expression body) {
      this.body = body;
    }
  }

  public class BoxingCastExpr : Expression {  // a BoxingCastExpr is used only as a temporary placeholding during translation
    public readonly Expression E;
    public readonly Type FromType;
    public readonly Type ToType;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(E != null);
      Contract.Invariant(FromType != null);
      Contract.Invariant(ToType != null);
    }

    public BoxingCastExpr(Expression e, Type fromType, Type toType) {
      Contract.Requires(e != null);
      Contract.Requires(fromType != null);
      Contract.Requires(toType != null);

      E = e;
      FromType = fromType;
      ToType = toType;
    }

    public override IEnumerable<Expression> SubExpressions {
      get { yield return E; }
    }
  }

  public class UnboxingCastExpr : Expression {  // an UnboxingCastExpr is used only as a temporary placeholding during translation
    public readonly Expression E;
    public readonly Type FromType;
    public readonly Type ToType;
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(E != null);
      Contract.Invariant(FromType != null);
      Contract.Invariant(ToType != null);
    }

    public UnboxingCastExpr(Expression e, Type fromType, Type toType) {
      Contract.Requires(e != null);
      Contract.Requires(fromType != null);
      Contract.Requires(toType != null);

      E = e;
      FromType = fromType;
      ToType = toType;
    }

    public override IEnumerable<Expression> SubExpressions {
      get { yield return E; }
    }
  }


  public class MaybeFreeExpression {
    public readonly Expression E;
    public readonly bool IsFree;
    public readonly AssertLabel/*?*/ Label;

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(E != null);
    }

    private Attributes attributes;
    public Attributes Attributes {
      get {
        return attributes;
      }
      set {
        attributes = value;
      }
    }

    public bool HasAttributes() {
      return Attributes != null;
    }

    public MaybeFreeExpression(Expression e)
      : this(e, false, null)
    {
      Contract.Requires(e != null);
    }

    public MaybeFreeExpression(Expression e, bool isFree)
      : this(e, isFree, null)
    {
      Contract.Requires(e != null);
    }

    public MaybeFreeExpression(Expression e, bool isFree, Attributes attrs) {
      Contract.Requires(e != null);
      E = e;
      IsFree = isFree;
      Attributes = attrs;
    }

    public MaybeFreeExpression(Expression e, bool isFree, AssertLabel/*?*/ label, Attributes attrs) {
      Contract.Requires(e != null);
      E = e;
      IsFree = isFree;
      Label = label;
      Attributes = attrs;
    }

    public void AddCustomizedErrorMessage(string name, string s) {
      var args = new List<Expression>() { new StringLiteralExpr(s, true) };
      this.Attributes = new UserSuppliedAttributes(name, args, this.Attributes);
    }
  }


  public class FrameExpression {
    public readonly Expression E;  // may be a WildcardExpr
    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(E != null);
      Contract.Invariant(!(E is WildcardExpr) || FieldName == null && Field == null);
    }

    public readonly string FieldName;
    public Field Field;  // filled in during resolution (but is null if FieldName is)

    /// <summary>
    /// If a "fieldName" is given, then "tok" denotes its source location.  Otherwise, "tok"
    /// denotes the source location of "e".
    /// </summary>
    public FrameExpression(Expression e, string fieldName) {
      Contract.Requires(e != null);
      Contract.Requires(!(e is WildcardExpr) || fieldName == null);
      E = e;
      FieldName = fieldName;
    }
  }

  /// <summary>
  /// The parsing and resolution/type checking of expressions of the forms
  ///   0. ident &lt; Types &gt;
  ///   1. Expr . ident &lt; Types &gt;
  ///   2. Expr ( Exprs )
  ///   3. Expr [ Exprs ]
  ///   4. Expr [ Expr .. Expr ]
  /// is done as follows.  These forms are parsed into the following AST classes:
  ///   0. NameSegment
  ///   1. ExprDotName
  ///   2. ApplySuffix
  ///   3. SeqSelectExpr or MultiSelectExpr
  ///   4. SeqSelectExpr
  ///
  /// The first three of these inherit from ConcreteSyntaxExpression.  The resolver will resolve
  /// these into:
  ///   0. IdentifierExpr or MemberSelectExpr (with .Lhs set to ImplicitThisExpr or StaticReceiverExpr)
  ///   1. IdentifierExpr or MemberSelectExpr
  ///   2. FuncionCallExpr or ApplyExpr
  ///
  /// The IdentifierExpr's that forms 0 and 1 can turn into sometimes denote the name of a module or
  /// type.  The .Type field of the corresponding resolved expressions are then the special Type subclasses
  /// ResolutionType_Module and ResolutionType_Type, respectively.  These will not be seen by the
  /// verifier or compiler, since, in a well-formed program, the verifier and compiler will use the
  /// .ResolvedExpr field of whatever form-1 expression contains these.
  ///
  /// Notes:
  ///   * IdentifierExpr and FunctionCallExpr are resolved-only expressions (that is, they don't contain
  ///     all the syntactic components that were used to parse them).
  ///   * Rather than the current SeqSelectExpr/MultiSelectExpr split of forms 3 and 4, it would
  ///     seem more natural to refactor these into 3: IndexSuffixExpr and 4: RangeSuffixExpr.
  /// </summary>
  abstract public class SuffixExpr : Expression {
    public readonly Expression Lhs;
    public SuffixExpr(Expression lhs) {
      Contract.Requires(lhs != null);
      Lhs = lhs;
    }
  }

  public class NameSegment : Expression
  {
    public readonly string Name;
    public readonly List<Type> OptTypeArguments;
    public NameSegment(string name, List<Type> optTypeArguments) {
      Contract.Requires(name != null);
      Contract.Requires(optTypeArguments == null || optTypeArguments.Count > 0);
      Name = name;
      OptTypeArguments = optTypeArguments;
    }
  }

  /// <summary>
  /// An ExprDotName desugars into either an IdentifierExpr (if the Lhs is a static name) or a MemberSelectExpr (if the Lhs is a computed expression).
  /// </summary>
  public class ExprDotName : SuffixExpr
  {
    public readonly string SuffixName;
    public readonly List<Type> OptTypeArguments;

    [ContractInvariantMethod]
    void ObjectInvariant() {
      Contract.Invariant(SuffixName != null);
    }

    public ExprDotName(Expression obj, string suffixName, List<Type> optTypeArguments)
      : base(obj) {
      Contract.Requires(obj != null);
      Contract.Requires(suffixName != null);
      this.SuffixName = suffixName;
      OptTypeArguments = optTypeArguments;
    }
  }

  public class Specification<T> where T : class
  {
    public readonly List<T> Expressions;

    [ContractInvariantMethod]
    private void ObjectInvariant()
    {
      Contract.Invariant(Expressions == null || cce.NonNullElements<T>(Expressions));
    }


    public Specification(List<T> exprs, Attributes attrs)
    {
      Contract.Requires(exprs == null || cce.NonNullElements<T>(exprs));
      Expressions = exprs;
      Attributes = attrs;
    }

    private Attributes attributes;
    public Attributes Attributes
    {
      get
      {
        return attributes;
      }
      set
      {
        attributes = value;
      }
    }

    public bool HasAttributes()
    {
      return Attributes != null;
    }
  }

  public class BottomUpVisitor
  {
    public void Visit(IEnumerable<Expression> exprs) {
      exprs.Iter(Visit);
    }
    public void Visit(IEnumerable<Statement> stmts) {
      stmts.Iter(Visit);
    }
    public void Visit(MaybeFreeExpression expr) {
      Visit(expr.E);
    }
    public void Visit(FrameExpression expr) {
      Visit(expr.E);
    }
    public void Visit(IEnumerable<MaybeFreeExpression> exprs) {
      exprs.Iter(Visit);
    }
    public void Visit(IEnumerable<FrameExpression> exprs) {
      exprs.Iter(Visit);
    }
    public void Visit(ICallable decl) {
      if (decl is Function) {
        Visit((Function)decl);
      } else if (decl is Method) {
        Visit((Method)decl);
      }
      //TODO More?
    }
    public void Visit(Method method) {
      Visit(method.Ens);
      Visit(method.Req);
      Visit(method.Mod.Expressions);
      Visit(method.Decreases.Expressions);
      if (method.Body != null) { Visit(method.Body); }
      //TODO More?
    }
    public void Visit(Function function) {
      Visit(function.Ens);
      Visit(function.Req);
      Visit(function.Reads);
      Visit(function.Decreases.Expressions);
      if (function.Body != null) { Visit(function.Body); }
      //TODO More?
    }
    public void Visit(Expression expr) {
      Contract.Requires(expr != null);
      // recursively visit all subexpressions and all substatements
      expr.SubExpressions.Iter(Visit);
      if (expr is StmtExpr) {
        // a StmtExpr also has a sub-statement
        var e = (StmtExpr)expr;
        Visit(e.S);
      }
      VisitOneExpr(expr);
    }
    public void Visit(Statement stmt) {
      Contract.Requires(stmt != null);
      // recursively visit all subexpressions and all substatements
      stmt.SubExpressions.Iter(Visit);
      stmt.SubStatements.Iter(Visit);
      VisitOneStmt(stmt);
    }
    protected virtual void VisitOneExpr(Expression expr) {
      Contract.Requires(expr != null);
      // by default, do nothing
    }
    protected virtual void VisitOneStmt(Statement stmt) {
      Contract.Requires(stmt != null);
      // by default, do nothing
    }
  }
  public class TopDownVisitor<State>
  {
    public void Visit(Expression expr, State st) {
      Contract.Requires(expr != null);
      if (VisitOneExpr(expr, ref st)) {
        // recursively visit all subexpressions and all substatements
        expr.SubExpressions.Iter(e => Visit(e, st));
        if (expr is StmtExpr) {
          // a StmtExpr also has a sub-statement
          var e = (StmtExpr)expr;
          Visit(e.S, st);
        }
      }
    }
    public void Visit(Statement stmt, State st) {
      Contract.Requires(stmt != null);
      if (VisitOneStmt(stmt, ref st)) {
        // recursively visit all subexpressions and all substatements
        stmt.SubExpressions.Iter(e => Visit(e, st));
        stmt.SubStatements.Iter(s => Visit(s, st));
      }
    }
    public void Visit(IEnumerable<Expression> exprs, State st) {
      exprs.Iter(e => Visit(e, st));
    }
    public void Visit(IEnumerable<Statement> stmts, State st) {
      stmts.Iter(e => Visit(e, st));
    }
    public void Visit(MaybeFreeExpression expr, State st) {
      Visit(expr.E, st);
    }
    public void Visit(FrameExpression expr, State st) {
      Visit(expr.E, st);
    }
    public void Visit(IEnumerable<MaybeFreeExpression> exprs, State st) {
      exprs.Iter(e => Visit(e, st));
    }
    public void Visit(IEnumerable<FrameExpression> exprs, State st) {
      exprs.Iter(e => Visit(e, st));
    }
    public void Visit(ICallable decl, State st) {
      if (decl is Function) {
        Visit((Function)decl, st);
      } else if (decl is Method) {
        Visit((Method)decl, st);
      }
      //TODO More?
    }
    public void Visit(Method method, State st) {
      Visit(method.Ens, st);
      Visit(method.Req, st);
      Visit(method.Mod.Expressions, st);
      Visit(method.Decreases.Expressions, st);
      if (method.Body != null) { Visit(method.Body, st); }
      //TODO More?
    }
    public void Visit(Function function, State st) {
      Visit(function.Ens, st);
      Visit(function.Req, st);
      Visit(function.Reads, st);
      Visit(function.Decreases.Expressions, st);
      if (function.Body != null) { Visit(function.Body, st); }
      //TODO More?
    }
    /// <summary>
    /// Visit one expression proper.  This method is invoked before it is invoked on the
    /// sub-parts (sub-expressions and sub-statements).  A return value of "true" says to
    /// continue invoking the method on sub-parts, whereas "false" says not to do so.
    /// The on-return value of "st" is the value that is passed to sub-parts.
    /// </summary>
    protected virtual bool VisitOneExpr(Expression expr, ref State st) {
      Contract.Requires(expr != null);
      return true;  // by default, visit the sub-parts with the same "st"
    }
    /// <summary>
    /// Visit one statement proper.  For the rest of the description of what this method
    /// does, see VisitOneExpr.
    /// </summary>
    protected virtual bool VisitOneStmt(Statement stmt, ref State st) {
      Contract.Requires(stmt != null);
      return true;  // by default, visit the sub-parts with the same "st"
    }
  }

  /// <summary>
  /// The substituter has methods to create an expression from an existing one, where the new one has the indicated
  /// substitutions for "this" (receiverReplacement), variables (substMap), and types (typeMap).
  /// CAUTION:  The result of the substitution is intended for use by TrExpr, not for well-formedness checks.  In
  /// particular, the substituter does not copy parts of an expression that are used only for well-formedness checks.
  /// </summary>
  public class Substituter
  {
    public readonly Expression receiverReplacement;
    public readonly Dictionary<IVariable, Expression/*!*/>/*!*/ substMap;
    public readonly Dictionary<TypeParameter, Type/*!*/>/*!*/ typeMap;

    public Substituter(Expression receiverReplacement, Dictionary<IVariable, Expression/*!*/>/*!*/ substMap, Dictionary<TypeParameter, Type> typeMap) {
      Contract.Requires(substMap != null);
      Contract.Requires(typeMap != null);
      this.receiverReplacement = receiverReplacement;
      this.substMap = substMap;
      this.typeMap = typeMap;
    }
    public virtual Expression Substitute(Expression expr) {
      Contract.Requires(expr != null);
      Contract.Ensures(Contract.Result<Expression>() != null);

      Expression newExpr = null;  // set to non-null value only if substitution has any effect; if non-null, the .Type of newExpr will be filled in at end

      if (expr is LiteralExpr || expr is WildcardExpr) {
        // nothing to substitute
      } else if (expr is ThisExpr) {
        return receiverReplacement == null ? expr : receiverReplacement;
      } else if (expr is IdentifierExpr) {
        IdentifierExpr e = (IdentifierExpr)expr;
        Expression substExpr;
        if (substMap.TryGetValue(e.Var, out substExpr)) {
          var substIdExpr = substExpr as IdentifierExpr;
          if (substIdExpr != null) {
            substExpr = new IdentifierExpr(substIdExpr.Var);
          }
          return cce.NonNull(substExpr);
        }
      } else if (expr is DisplayExpression) {
        DisplayExpression e = (DisplayExpression)expr;
        List<Expression> newElements = SubstituteExprList(e.Elements);
        if (newElements != e.Elements) {
          if (expr is SetDisplayExpr) {
            newExpr = new SetDisplayExpr(((SetDisplayExpr)expr).Finite, newElements);
          } else if (expr is MultiSetDisplayExpr) {
            newExpr = new MultiSetDisplayExpr(newElements);
          } else {
            newExpr = new SeqDisplayExpr(newElements);
          }
        }
      } else if (expr is MapDisplayExpr) {
        var e = (MapDisplayExpr)expr;
        var elmts = new List<ExpressionPair>();
        var anyChanges = false;
        foreach (var ep in e.Elements) {
          var a = Substitute(ep.A);
          var b = Substitute(ep.B);
          elmts.Add(new ExpressionPair(a, b));
          if (a != ep.A || b != ep.B) {
            anyChanges = true;
          }
        }
        if (anyChanges) {
          newExpr = new MapDisplayExpr(e.Finite, elmts);
        }
      } else if (expr is MemberSelectExpr) {
        MemberSelectExpr fse = (MemberSelectExpr)expr;
        Expression substE = Substitute(fse.Obj);
        MemberSelectExpr fseNew = new MemberSelectExpr(substE, fse.MemberName);
        fseNew.Member = fse.Member;
        fseNew.TypeApplication = fse.TypeApplication.ConvertAll(t => t.Subst(typeMap));
        newExpr = fseNew;
      } else if (expr is SeqSelectExpr) {
        SeqSelectExpr sse = (SeqSelectExpr)expr;
        Expression seq = Substitute(sse.Seq);
        Expression e0 = sse.E0 == null ? null : Substitute(sse.E0);
        Expression e1 = sse.E1 == null ? null : Substitute(sse.E1);
        if (seq != sse.Seq || e0 != sse.E0 || e1 != sse.E1) {
          newExpr = new SeqSelectExpr(sse.SelectOne, seq, e0, e1);
        }

      } else if (expr is SeqUpdateExpr) {
        var sse = (SeqUpdateExpr)expr;
        if (sse.ResolvedUpdateExpr != null) {
          return Substitute(sse.ResolvedUpdateExpr);
        } else {
          Expression seq = Substitute(sse.Seq);
          Expression index = Substitute(sse.Index);
          Expression val = Substitute(sse.Value);
          if (seq != sse.Seq || index != sse.Index || val != sse.Value) {
            newExpr = new SeqUpdateExpr(seq, index, val);
          }
        }

      } else if (expr is MultiSelectExpr) {
        MultiSelectExpr mse = (MultiSelectExpr)expr;
        Expression array = Substitute(mse.Array);
        List<Expression> newArgs = SubstituteExprList(mse.Indices);
        if (array != mse.Array || newArgs != mse.Indices) {
          newExpr = new MultiSelectExpr(array, newArgs);
        }

      } else if (expr is FunctionCallExpr) {
        FunctionCallExpr e = (FunctionCallExpr)expr;
        Expression receiver = Substitute(e.Receiver);
        List<Expression> newArgs = SubstituteExprList(e.Args);
        var newTypeInstantiation = SubstituteTypeMap(e.TypeArgumentSubstitutions);
        if (receiver != e.Receiver || newArgs != e.Args || newTypeInstantiation != e.TypeArgumentSubstitutions) {
          FunctionCallExpr newFce = new FunctionCallExpr(e.Name, receiver, newArgs);
          newFce.Function = e.Function;  // resolve on the fly (and set newFce.Type below, at end)
          newFce.CoCall = e.CoCall;  // also copy the co-call status
          newFce.CoCallHint = e.CoCallHint;  // and any co-call hint
          newFce.TypeArgumentSubstitutions = newTypeInstantiation;
          newExpr = newFce;
        }

      } else if (expr is ApplyExpr) {
        ApplyExpr e = (ApplyExpr)expr;
        Expression fn = Substitute(e.Function);
        List<Expression> args = SubstituteExprList(e.Args);
        newExpr = new ApplyExpr(fn, args);

      } else if (expr is DatatypeValue) {
        DatatypeValue dtv = (DatatypeValue)expr;
        List<Expression> newArgs = SubstituteExprList(dtv.Arguments);
        if (newArgs != dtv.Arguments) {
          DatatypeValue newDtv = new DatatypeValue(dtv.DatatypeName, dtv.MemberName, newArgs);
          newDtv.Ctor = dtv.Ctor;  // resolve on the fly (and set newDtv.Type below, at end)
          newDtv.InferredTypeArgs = Util.Map(dtv.InferredTypeArgs, tt => tt.Subst(typeMap));
                                    // ^ Set the correct type arguments to the constructor
          newExpr = newDtv;
        }

      } else if (expr is OldExpr) {
        var e = (OldExpr)expr;
        // Note, it is up to the caller to avoid variable capture.  In most cases, this is not a
        // problem, since variables have unique declarations.  However, it is an issue if the substitution
        // takes place inside an OldExpr.  In those cases (see LetExpr), the caller can use a
        // BoogieWrapper before calling Substitute.
        Expression se = Substitute(e.E);
        if (se != e.E) {
          newExpr = new OldExpr(se, e.At) { AtLabel = e.AtLabel };
        }
      } else if (expr is UnchangedExpr) {
        var e = (UnchangedExpr)expr;
        var fr = new List<FrameExpression>();
        var anythingChanged = false;
        foreach (var fe in e.Frame) {
          var fefe = SubstFrameExpr(fe);
          if (fefe != fe) {
            anythingChanged = true;
          }
          fr.Add(fefe);
        }
        if (anythingChanged) {
          newExpr = new UnchangedExpr(fr, e.At) { AtLabel = e.AtLabel };
        }
      } else if (expr is SeqConstructionExpr) {
        var e = (SeqConstructionExpr)expr;
        var sn = Substitute(e.N);
        var sinit = Substitute(e.Initializer);
        if (sn != e.N || sinit != e.Initializer) {
          newExpr = new SeqConstructionExpr(sn, sinit);
        }
      } else if (expr is MultiSetFormingExpr) {
        var e = (MultiSetFormingExpr)expr;
        var se = Substitute(e.E);
        if (se != e.E) {
          newExpr = new MultiSetFormingExpr(se);
        }
      } else if (expr is BoxingCastExpr) {
        var e = (BoxingCastExpr)expr;
        var se = Substitute(e.E);
        if (se != e.E) {
          newExpr = new BoxingCastExpr(se, e.FromType, e.ToType);
        }
      } else if (expr is UnaryExpr) {
        var e = (UnaryExpr)expr;
        Expression se = Substitute(e.E);
        if (se != e.E) {
          if (e is UnaryOpExpr) {
            var ee = (UnaryOpExpr)e;
            newExpr = new UnaryOpExpr(ee.Op, se);
          } else if (e is ConversionExpr) {
            var ee = (ConversionExpr)e;
            newExpr = new ConversionExpr(se, ee.ToType);
          } else {
            Contract.Assert(false);  // unexpected UnaryExpr subtype
          }
        }
      } else if (expr is BinaryExpr) {
        BinaryExpr e = (BinaryExpr)expr;
        Expression e0 = Substitute(e.E0);
        Expression e1 = Substitute(e.E1);
        if (e0 != e.E0 || e1 != e.E1) {
          BinaryExpr newBin = new BinaryExpr(e.Op, e0, e1);
          newBin.ResolvedOp = e.ResolvedOp;  // part of what needs to be done to resolve on the fly (newBin.Type is set below, at end)
          newExpr = newBin;
        }

      } else if (expr is TernaryExpr) {
        var e = (TernaryExpr)expr;
        var e0 = Substitute(e.E0);
        var e1 = Substitute(e.E1);
        var e2 = Substitute(e.E2);
        if (e0 != e.E0 || e1 != e.E1 || e2 != e.E2) {
          newExpr = new TernaryExpr(e.Op, e0, e1, e2);
        }

      } else if (expr is LetExpr) {
        var e = (LetExpr)expr;
        if (e.Exact) {
          var rhss = new List<Expression>();
          bool anythingChanged = false;
          foreach (var rhs in e.RHSs) {
            var r = Substitute(rhs);
            if (r != rhs) {
              anythingChanged = true;
            }
            rhss.Add(r);
          }
          // Note, CreateBoundVarSubstitutions has the side effect of updating the substitution map.
          // For an Exact let expression, this is something that needs to be done after substituting
          // in the RHSs.
          var newCasePatterns = CreateCasePatternSubstitutions(e.LHSs, true);
          if (newCasePatterns != e.LHSs) {
            anythingChanged = true;
          }

          var body = Substitute(e.Body);
          // undo any changes to substMap (could be optimized to do this only if newBoundVars != e.Vars)
          foreach (var bv in e.BoundVars) {
            substMap.Remove(bv);
          }
          // Put things together
          if (anythingChanged || body != e.Body) {
            newExpr = new LetExpr(newCasePatterns, rhss, body, e.Exact);
          }
        } else {
          var rhs = Substitute(e.RHSs[0]);
          var body = Substitute(e.Body);
          if (rhs == e.RHSs[0] && body == e.Body) {
            return e;
          }
          var newLet = new LetExpr(e.LHSs, new List<Expression>{ rhs }, body, e.Exact);
          newExpr = newLet;
        }

      } else if (expr is MatchExpr) {
        var e = (MatchExpr)expr;
        var src = Substitute(e.Source);
        bool anythingChanged = src != e.Source;
        var cases = new List<MatchCaseExpr>();
        foreach (var mc in e.Cases) {
          var newBoundVars = CreateBoundVarSubstitutions(mc.Arguments, false);
          var body = Substitute(mc.Body);
          // undo any changes to substMap (could be optimized to do this only if newBoundVars != mc.Arguments)
          foreach (var bv in mc.Arguments) {
            substMap.Remove(bv);
          }
          // Put things together
          if (newBoundVars != mc.Arguments || body != mc.Body) {
            anythingChanged = true;
          }
          var newCaseExpr = new MatchCaseExpr(mc.Id, newBoundVars, body);
          newCaseExpr.Ctor = mc.Ctor;  // resolve here
          cases.Add(newCaseExpr);
        }
        if (anythingChanged) {
          var newME = new MatchExpr(src, cases, e.UsesOptionalBraces);
          newME.MissingCases.AddRange(e.MissingCases);
          newExpr = newME;
        }

      } else if (expr is NamedExpr) {
        var e = (NamedExpr)expr;
        var body = Substitute(e.Body);
        var contract = e.Contract == null ? null : Substitute(e.Contract);
        newExpr = new NamedExpr(e.Name, body, contract);
      } else if (expr is ComprehensionExpr) {
        var e = (ComprehensionExpr)expr;
        // For quantifiers and setComprehesion we want to make sure that we don't introduce name clashes with
        // the enclosing scopes.

        var q = e as QuantifierExpr;
        if (q != null && q.SplitQuantifier != null) {
          return Substitute(q.SplitQuantifierExpression);
        }

        var newBoundVars = CreateBoundVarSubstitutions(e.BoundVars, expr is ForallExpr || expr is ExistsExpr || expr is SetComprehension);
        var newRange = e.Range == null ? null : Substitute(e.Range);
        var newTerm = Substitute(e.Term);
        var newAttrs = SubstAttributes(e.Attributes);
        if (newBoundVars != e.BoundVars || newRange != e.Range || newTerm != e.Term || newAttrs != e.Attributes) {
          if (e is SetComprehension) {
            newExpr = new SetComprehension(((SetComprehension)e).Finite, newBoundVars, newRange, newTerm, newAttrs);
          } else if (e is MapComprehension) {
            var mc = (MapComprehension)e;
            var newTermLeft = mc.IsGeneralMapComprehension ? Substitute(mc.TermLeft) : null;
            newExpr = new MapComprehension(mc.Finite, newBoundVars, newRange, newTermLeft, newTerm, newAttrs);
          } else if (expr is ForallExpr) {
            newExpr = new ForallExpr(((QuantifierExpr)expr).TypeArgs, newBoundVars, newRange, newTerm, newAttrs);
          } else if (expr is ExistsExpr) {
            newExpr = new ExistsExpr(((QuantifierExpr)expr).TypeArgs, newBoundVars, newRange, newTerm, newAttrs);
          } else if (expr is LambdaExpr) {
            var l = (LambdaExpr)expr;
            newExpr = new LambdaExpr(newBoundVars, newRange, l.Reads.ConvertAll(SubstFrameExpr), newTerm);
          } else {
            Contract.Assert(false);  // unexpected ComprehensionExpr
          }
          if (e.Bounds != null) {
            ((ComprehensionExpr)newExpr).Bounds = e.Bounds.ConvertAll(bound => SubstituteBoundedPool(bound));
          }
        }
        // undo any changes to substMap (could be optimized to do this only if newBoundVars != e.BoundVars)
        foreach (var bv in e.BoundVars) {
          substMap.Remove(bv);
        }

      } else if (expr is StmtExpr) {
        var e = (StmtExpr)expr;
        newExpr = new StmtExpr(SubstStmt(e.S), Substitute(e.E));

      } else if (expr is ITEExpr) {
        ITEExpr e = (ITEExpr)expr;
        Expression test = Substitute(e.Test);
        Expression thn = Substitute(e.Thn);
        Expression els = Substitute(e.Els);
        if (test != e.Test || thn != e.Thn || els != e.Els) {
          newExpr = new ITEExpr(e.IsBindingGuard, test, thn, els);
        }

      } else if (expr is RevealExpr) {
        var e = (RevealExpr)expr;
        return Substitute(e.ResolvedExpression);

      } else {
        Contract.Assume(false); // unexpected Expression
      }

      if (newExpr == null) {
        return expr;
      } else {
        newExpr.Type = expr.Type.Subst(typeMap);  // resolve on the fly (any additional resolution must be done above)
        return newExpr;
      }
    }

    public ComprehensionExpr.BoundedPool SubstituteBoundedPool(ComprehensionExpr.BoundedPool bound) {
      if (bound == null) {
        return null;
      } else if (bound is ComprehensionExpr.ExactBoundedPool) {
        var b = (ComprehensionExpr.ExactBoundedPool)bound;
        return new ComprehensionExpr.ExactBoundedPool(Substitute(b.E));
      } else if (bound is ComprehensionExpr.BoolBoundedPool) {
        return bound;  // nothing to substitute
      } else if (bound is ComprehensionExpr.CharBoundedPool) {
        return bound;  // nothing to substitute
      } else if (bound is ComprehensionExpr.IntBoundedPool) {
        var b = (ComprehensionExpr.IntBoundedPool)bound;
        return new ComprehensionExpr.IntBoundedPool(b.LowerBound == null ? null : Substitute(b.LowerBound), b.UpperBound == null ? null : Substitute(b.UpperBound));
      } else if (bound is ComprehensionExpr.SetBoundedPool) {
        var b = (ComprehensionExpr.SetBoundedPool)bound;
        return new ComprehensionExpr.SetBoundedPool(Substitute(b.Set), b.ExactTypes, b.IsFiniteCollection);
      } else if (bound is ComprehensionExpr.MultiSetBoundedPool) {
        var b = (ComprehensionExpr.MultiSetBoundedPool)bound;
        return new ComprehensionExpr.MultiSetBoundedPool(Substitute(b.MultiSet), b.ExactTypes);
      } else if (bound is ComprehensionExpr.SubSetBoundedPool) {
        var b = (ComprehensionExpr.SubSetBoundedPool)bound;
        return new ComprehensionExpr.SubSetBoundedPool(Substitute(b.UpperBound), b.IsFiniteCollection);
      } else if (bound is ComprehensionExpr.SuperSetBoundedPool) {
        var b = (ComprehensionExpr.SuperSetBoundedPool)bound;
        return new ComprehensionExpr.SuperSetBoundedPool(Substitute(b.LowerBound));
      } else if (bound is ComprehensionExpr.MapBoundedPool) {
        var b = (ComprehensionExpr.MapBoundedPool)bound;
        return new ComprehensionExpr.MapBoundedPool(Substitute(b.Map), b.ExactTypes, b.IsFiniteCollection);
      } else if (bound is ComprehensionExpr.SeqBoundedPool) {
        var b = (ComprehensionExpr.SeqBoundedPool)bound;
        return new ComprehensionExpr.SeqBoundedPool(Substitute(b.Seq), b.ExactTypes);
      } else if (bound is ComprehensionExpr.DatatypeBoundedPool) {
        return bound;  // nothing to substitute
      } else if (bound is ComprehensionExpr.DatatypeInclusionBoundedPool) {
        return bound;  // nothing to substitute
      } else if (bound is ComprehensionExpr.AllocFreeBoundedPool) {
        return bound;  // nothing to substitute
      } else if (bound is ComprehensionExpr.ExplicitAllocatedBoundedPool) {
        return bound;  // nothing to substitute
      } else if (bound is AssignSuchThatStmt.WiggleWaggleBound) {
        return bound;  // nothing to substitute
      } else if (bound is ComprehensionExpr.SpecialAllocIndependenceAllocatedBoundedPool) {
        return bound;  // nothing to substitute
      } else {
        Contract.Assume(false);  // unexpected ComprehensionExpr.BoundedPool
        throw new cce.UnreachableException();  // to please compiler
      }
    }

    /// <summary>
    /// Return a list of bound variables, of the same length as 'vars' but with possible substitutions.
    /// For any change necessary, update 'substMap' to reflect the new substitution; the caller is responsible for
    /// undoing these changes once the updated 'substMap' has been used.
    /// If no changes are necessary, the list returned is exactly 'vars' and 'substMap' is unchanged.
    /// </summary>
    protected virtual List<BoundVar> CreateBoundVarSubstitutions(List<BoundVar> vars, bool forceSubstitutionOfBoundVars) {
      bool anythingChanged = false;
      var newBoundVars = new List<BoundVar>();
      foreach (var bv in vars) {
        var tt = bv.Type.Subst(typeMap);
        if (!forceSubstitutionOfBoundVars && tt == bv.Type) {
          newBoundVars.Add(bv);
        } else {
          anythingChanged = true;
          var newBv = new BoundVar(bv.Name, tt);
          newBoundVars.Add(newBv);
          // update substMap to reflect the new BoundVar substitutions
          var ie = new IdentifierExpr(newBv);
          substMap.Add(bv, ie);
        }
      }
      return anythingChanged ? newBoundVars : vars;
    }

    /// <summary>
    /// Return a list of local variables, of the same length as 'vars' but with possible substitutions.
    /// For any change necessary, update 'substMap' to reflect the new substitution; the caller is responsible for
    /// undoing these changes once the updated 'substMap' has been used.
    /// If no changes are necessary, the list returned is exactly 'vars' and 'substMap' is unchanged.
    /// </summary>
    protected virtual List<LocalVariable> CreateLocalVarSubstitutions(List<LocalVariable> vars, bool forceSubstitutionOfVars) {
      bool anythingChanged = false;
      var newVars = new List<LocalVariable>();
      foreach (var v in vars) {
        var tt = v.Type.Subst(typeMap);
        if (!forceSubstitutionOfVars && tt == v.Type) {
          newVars.Add(v);
        } else {
          anythingChanged = true;
          var newVar = new LocalVariable(v.Name, tt);
          newVars.Add(newVar);
          // update substMap to reflect the new LocalVariable substitutions
          var ie = new IdentifierExpr(newVar);
          substMap.Add(v, ie);
        }
      }
      return anythingChanged ? newVars : vars;
    }

    /// <summary>
    /// Return a list of case patterns, of the same length as 'patterns' but with possible substitutions.
    /// For any change necessary, update 'substMap' to reflect the new substitution; the caller is responsible for
    /// undoing these changes once the updated 'substMap' has been used.
    /// If no changes are necessary, the list returned is exactly 'patterns' and 'substMap' is unchanged.
    /// </summary>
    protected virtual List<CasePattern<BoundVar>> CreateCasePatternSubstitutions(List<CasePattern<BoundVar>> patterns, bool forceSubstitutionOfBoundVars) {
      bool anythingChanged = false;
      var newPatterns = new List<CasePattern<BoundVar>>();
      foreach (var pat in patterns) {
        var newPat = SubstituteCasePattern(pat, forceSubstitutionOfBoundVars);
        newPatterns.Add(newPat);
        if (newPat != pat) {
          anythingChanged = true;
        }
      }
      return anythingChanged ? newPatterns : patterns;
    }
    CasePattern<BoundVar> SubstituteCasePattern(CasePattern<BoundVar> pat, bool forceSubstitutionOfBoundVars) {
      Contract.Requires(pat != null);
      if (pat.Var != null) {
        var bv = pat.Var;
        var tt = bv.Type.Subst(typeMap);
        if (forceSubstitutionOfBoundVars || tt != bv.Type) {
          var newBv = new BoundVar(pat.Id, tt);
          // update substMap to reflect the new BoundVar substitutions
          var ie = new IdentifierExpr(newBv);
          ie.Var = newBv;  // resolve here
          ie.Type = newBv.Type;  // resolve here
          substMap.Add(bv, ie);
          var newPat = new CasePattern<BoundVar>(newBv);
          newPat.AssembleExpr(null);
          return newPat;
        }
      } else if (pat.Arguments != null) {
        bool anythingChanged = false;
        var newArgs = new List<CasePattern<BoundVar>>();
        foreach (var arg in pat.Arguments) {
          var newArg = SubstituteCasePattern(arg, forceSubstitutionOfBoundVars);
          newArgs.Add(newArg);
          if (newArg != arg) {
            anythingChanged = true;
          }
        }
        if (anythingChanged) {
          var patE = (DatatypeValue)pat.Expr;
          var newPat = new CasePattern<BoundVar>(pat.Id, newArgs);
          newPat.Ctor = pat.Ctor;
          newPat.AssembleExpr(patE.InferredTypeArgs.ConvertAll(tp => tp.Subst(typeMap)));
          return newPat;
        }
      }
      return pat;
    }

    protected List<Expression/*!*/>/*!*/ SubstituteExprList(List<Expression/*!*/>/*!*/ elist) {
      Contract.Requires(cce.NonNullElements(elist));
      Contract.Ensures(cce.NonNullElements(Contract.Result<List<Expression>>()));

      List<Expression> newElist = null;  // initialized lazily
      for (int i = 0; i < elist.Count; i++) {
        cce.LoopInvariant(newElist == null || newElist.Count == i);

        Expression substE = Substitute(elist[i]);
        if (substE != elist[i] && newElist == null) {
          newElist = new List<Expression>();
          for (int j = 0; j < i; j++) {
            newElist.Add(elist[j]);
          }
        }
        if (newElist != null) {
          newElist.Add(substE);
        }
      }
      if (newElist == null) {
        return elist;
      } else {
        return newElist;
      }
    }

    protected Dictionary<TypeParameter, Type> SubstituteTypeMap(Dictionary<TypeParameter, Type> tmap) {
      Contract.Requires(tmap != null);
      Contract.Ensures(Contract.Result<Dictionary<TypeParameter, Type>>() != null);
      if (typeMap.Count == 0) {  // optimization
        return tmap;
      }
      bool anythingChanged = false;
      var newTmap = new Dictionary<TypeParameter, Type>();
      var i = 0;
      foreach (var maplet in tmap) {
        cce.LoopInvariant(newTmap == null || newTmap.Count == i);
        var tt = maplet.Value.Subst(typeMap);
        if (tt != maplet.Value) {
          anythingChanged = true;
        }
        newTmap.Add(maplet.Key, tt);
        i++;
      }
      if (anythingChanged) {
        return newTmap;
      } else {
        return tmap;
      }
    }

    /// <summary>
    /// This method (which currently is used only internally to class Substituter) performs substitutions in
    /// statements that can occur in a StmtExpr.  (For example, it does not bother to do anything with a
    /// PrintStmt, ReturnStmt, or YieldStmt.)
    /// </summary>
    protected virtual Statement SubstStmt(Statement stmt) {
      Statement r;
      if (stmt == null) {
        return null;
      } else if (stmt is AssertStmt) {
        var s = (AssertStmt)stmt;
        r = new AssertStmt(Substitute(s.Expr), SubstBlockStmt(s.Proof), s.Label, SubstAttributes(s.Attributes));
      } else if (stmt is AssumeStmt) {
        var s = (AssumeStmt)stmt;
        r = new AssumeStmt(Substitute(s.Expr), SubstAttributes(s.Attributes));
      } else if (stmt is BreakStmt) {
        var s = (BreakStmt)stmt;
        BreakStmt rr;
        if (s.TargetLabel != null) {
          rr = new BreakStmt(s.TargetLabel);
        } else {
          rr = new BreakStmt(s.BreakCount);
        }
        // r.TargetStmt will be filled in as later
        List<BreakStmt> breaks;
        if (!BreaksToBeResolved.TryGetValue(s, out breaks)) {
          breaks = new List<BreakStmt>();
          BreaksToBeResolved.Add(s, breaks);
        }
        breaks.Add(rr);
        r = rr;
      } else if (stmt is AssignStmt) {
        var s = (AssignStmt)stmt;
        r = new AssignStmt(Substitute(s.Lhs), SubstRHS(s.Rhs));
      } else if (stmt is CallStmt) {
        var s = (CallStmt)stmt;
        var rr = new CallStmt(s.Lhs.ConvertAll(Substitute), (MemberSelectExpr)Substitute(s.MethodSelect), s.Args.ConvertAll(Substitute));
        r = rr;
      } else if (stmt is DividedBlockStmt) {
        r = SubstDividedBlockStmt((DividedBlockStmt)stmt);
      } else if (stmt is BlockStmt) {
        r = SubstBlockStmt((BlockStmt)stmt);
      } else if (stmt is IfStmt) {
        var s = (IfStmt)stmt;
        r = new IfStmt(s.IsBindingGuard, Substitute(s.Guard), SubstBlockStmt(s.Thn), SubstStmt(s.Els));
      } else if (stmt is AlternativeStmt) {
        var s = (AlternativeStmt)stmt;
        r = new AlternativeStmt(s.Alternatives.ConvertAll(SubstGuardedAlternative), s.UsesOptionalBraces);
      } else if (stmt is WhileStmt) {
        var s = (WhileStmt)stmt;
        r = new WhileStmt(Substitute(s.Guard), s.Invariants.ConvertAll(SubstMayBeFreeExpr), SubstSpecExpr(s.Decreases), SubstSpecFrameExpr(s.Mod), SubstBlockStmt(s.Body));
      } else if (stmt is AlternativeLoopStmt) {
        var s = (AlternativeLoopStmt)stmt;
        r = new AlternativeLoopStmt(s.Invariants.ConvertAll(SubstMayBeFreeExpr), SubstSpecExpr(s.Decreases), SubstSpecFrameExpr(s.Mod), s.Alternatives.ConvertAll(SubstGuardedAlternative), s.UsesOptionalBraces);
      } else if (stmt is ForallStmt) {
        var s = (ForallStmt)stmt;
        var newBoundVars = CreateBoundVarSubstitutions(s.BoundVars, false);
        var body = SubstStmt(s.Body);
        // undo any changes to substMap (could be optimized to do this only if newBoundVars != e.Vars)
        foreach (var bv in s.BoundVars) {
          substMap.Remove(bv);
        }
        // Put things together
        var rr = new ForallStmt(newBoundVars, SubstAttributes(s.Attributes), Substitute(s.Range), s.Ens.ConvertAll(SubstMayBeFreeExpr), body);
        rr.Kind = s.Kind;
        r = rr;
      } else if (stmt is CalcStmt) {
        var s = (CalcStmt)stmt;
        var rr = new CalcStmt(SubstCalcOp(s.UserSuppliedOp), s.Lines.ConvertAll(Substitute), s.Hints.ConvertAll(SubstBlockStmt), s.StepOps.ConvertAll(SubstCalcOp), SubstAttributes(s.Attributes));
        rr.Op = SubstCalcOp(s.Op);
        rr.Steps.AddRange(s.Steps.ConvertAll(Substitute));
        rr.Result = Substitute(s.Result);
        r = rr;
      } else if (stmt is MatchStmt) {
        var s = (MatchStmt)stmt;
        var rr = new MatchStmt(Substitute(s.Source), s.Cases.ConvertAll(SubstMatchCaseStmt), s.UsesOptionalBraces);
        rr.MissingCases.AddRange(s.MissingCases);
        r = rr;
      } else if (stmt is AssignSuchThatStmt) {
        var s = (AssignSuchThatStmt)stmt;
        r = new AssignSuchThatStmt(s.Lhss.ConvertAll(Substitute), Substitute(s.Expr), s.HasAssume, null);
      } else if (stmt is UpdateStmt) {
        var s = (UpdateStmt)stmt;
        var resolved = s.ResolvedStatements;
        UpdateStmt rr;
        if (resolved.Count == 1) {
          // when later translating this UpdateStmt, the s.Lhss and s.Rhss components won't be used, only s.ResolvedStatements
          rr = new UpdateStmt(s.Lhss, s.Rhss, s.CanMutateKnownState);
        } else {
          rr = new UpdateStmt(s.Lhss.ConvertAll(Substitute), s.Rhss.ConvertAll(SubstRHS), s.CanMutateKnownState);
        }
        rr.ResolvedStatements.AddRange(s.ResolvedStatements.ConvertAll(SubstStmt));
        r = rr;
      } else if (stmt is VarDeclStmt) {
        var s = (VarDeclStmt)stmt;
        var lhss = CreateLocalVarSubstitutions(s.Locals, false);
        var rr = new VarDeclStmt(lhss, (ConcreteUpdateStatement)SubstStmt(s.Update));
        r = rr;
      } else if (stmt is RevealStmt) {
        var s = (RevealStmt)stmt;
        // don't need to substitute s.Expr since it won't be used, only the s.ResolvedStatements are used.
        var rr = new RevealStmt(s.Exprs);
        rr.LabeledAsserts.AddRange(s.LabeledAsserts);
        rr.ResolvedStatements.AddRange(s.ResolvedStatements.ConvertAll(SubstStmt));
        r = rr;
      } else {
        Contract.Assert(false); throw new cce.UnreachableException();  // unexpected statement
      }

      // add labels to the cloned statement
      AddStmtLabels(r, stmt.Labels);
      r.Attributes = SubstAttributes(stmt.Attributes);
      if (stmt.Labels != null || stmt is WhileStmt) {
        List<BreakStmt> breaks;
        if (BreaksToBeResolved.TryGetValue(stmt, out breaks)) {
          foreach (var b in breaks) {
            b.TargetStmt = r;
          }
          BreaksToBeResolved.Remove(stmt);
        }
      }

      return r;
    }

    Dictionary<Statement, List<BreakStmt>> BreaksToBeResolved = new Dictionary<Statement, List<BreakStmt>>();  // old-target -> new-breaks

    protected void AddStmtLabels(Statement s, LList<Label> node) {
      if (node != null) {
        AddStmtLabels(s, node.Next);
        s.Labels = new LList<Label>(node.Data, s.Labels);
      }
    }

    protected virtual DividedBlockStmt SubstDividedBlockStmt(DividedBlockStmt stmt) {
      return stmt == null ? null : new DividedBlockStmt(stmt.BodyInit.ConvertAll(SubstStmt), stmt.BodyProper.ConvertAll(SubstStmt));
    }

    protected virtual BlockStmt SubstBlockStmt(BlockStmt stmt) {
      if (stmt == null) {
        return null;
      }
      var prevSubstMap = new Dictionary<IVariable, Expression>(substMap);
      var b = new BlockStmt(stmt.Body.ConvertAll(SubstStmt));
      if (substMap.Count != prevSubstMap.Count) {
        // reset substMap to what it was (note that substMap is a readonly field, so we can't just change it back to prevSubstMap)
        substMap.Clear();
        foreach (var item in prevSubstMap) {
          substMap.Add(item.Key, item.Value);
        }
      }
      return b;
    }

    protected GuardedAlternative SubstGuardedAlternative(GuardedAlternative alt) {
      Contract.Requires(alt != null);
      return new GuardedAlternative(alt.IsBindingGuard, Substitute(alt.Guard), alt.Body.ConvertAll(SubstStmt));
    }

    protected MaybeFreeExpression SubstMayBeFreeExpr(MaybeFreeExpression expr) {
      Contract.Requires(expr != null);
      var mfe = new MaybeFreeExpression(Substitute(expr.E), expr.IsFree);
      mfe.Attributes = SubstAttributes(expr.Attributes);
      return mfe;
    }

    protected Specification<Expression> SubstSpecExpr(Specification<Expression> spec) {
      var ee = spec.Expressions == null ? null : spec.Expressions.ConvertAll(Substitute);
      return new Specification<Expression>(ee, SubstAttributes(spec.Attributes));
    }

    protected Specification<FrameExpression> SubstSpecFrameExpr(Specification<FrameExpression> frame) {
      var ee = frame.Expressions == null ? null : frame.Expressions.ConvertAll(SubstFrameExpr);
      return new Specification<FrameExpression>(ee, SubstAttributes(frame.Attributes));
    }

    public FrameExpression SubstFrameExpr(FrameExpression frame) {
      Contract.Requires(frame != null);
      var fe = new FrameExpression(Substitute(frame.E), frame.FieldName);
      fe.Field = frame.Field;  // resolve here
      return fe;
    }

    protected AssignmentRhs SubstRHS(AssignmentRhs rhs) {
      AssignmentRhs c;
      if (rhs is ExprRhs) {
        var r = (ExprRhs)rhs;
        c = new ExprRhs(Substitute(r.Expr));
      } else if (rhs is HavocRhs) {
        c = new HavocRhs();
      } else {
        // since the Substituter is assumed to operate on statements only if they are part of a StatementExpression, then the TypeRhs case cannot occur
        Contract.Assume(false); throw new cce.UnreachableException();
      }
      c.Attributes = SubstAttributes(rhs.Attributes);
      return c;
    }

    protected MatchCaseStmt SubstMatchCaseStmt(MatchCaseStmt c) {
      Contract.Requires(c != null);
      var newBoundVars = CreateBoundVarSubstitutions(c.Arguments, false);
      var r = new MatchCaseStmt(c.Id, newBoundVars, c.Body.ConvertAll(SubstStmt));
      r.Ctor = c.Ctor;
      // undo any changes to substMap (could be optimized to do this only if newBoundVars != e.Vars)
      foreach (var bv in c.Arguments) {
        substMap.Remove(bv);
      }
      return r;
    }

    protected CalcStmt.CalcOp SubstCalcOp(CalcStmt.CalcOp op) {
      if (op == null) {
        return null;
      } else if (op is CalcStmt.BinaryCalcOp) {
        return new CalcStmt.BinaryCalcOp(((CalcStmt.BinaryCalcOp)op).Op);
      } else if (op is CalcStmt.TernaryCalcOp) {
        return new CalcStmt.TernaryCalcOp(Substitute(((CalcStmt.TernaryCalcOp)op).Index));
      } else {
        Contract.Assert(false);
        throw new cce.UnreachableException();
      }
    }

    public Attributes SubstAttributes(Attributes attrs) {
      Contract.Requires(cce.NonNullDictionaryAndValues(substMap));
      if (attrs != null) {
        var newArgs = new List<Expression>();  // allocate it eagerly, what the heck, it doesn't seem worth the extra complexity in the code to do it lazily for the infrequently occurring attributes
        bool anyArgSubst = false;
        foreach (var arg in attrs.Args) {
          var argToBeAdded = arg;
          var substArg = Substitute(arg);
          if (substArg != arg) {
            argToBeAdded = substArg;
            anyArgSubst = true;
          }
          newArgs.Add(argToBeAdded);
        }
        if (!anyArgSubst) {
          newArgs = attrs.Args;
        }

        Attributes prev = SubstAttributes(attrs.Prev);
        if (newArgs != attrs.Args || prev != attrs.Prev) {
          if (attrs is UserSuppliedAttributes) {
            var usa = (UserSuppliedAttributes)attrs;
            return new UserSuppliedAttributes(usa.Name, newArgs, prev);
          } else {
            return new Attributes(attrs.Name, newArgs, prev);
          }
        }
      }
      return attrs;
    }
  }
}
