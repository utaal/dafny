namespace Microsoft.Dafny {
  /// An API between Compiler and PreCompiler by which each backend specifies
  /// the requirements of the target language so that the pre-compiler can
  /// produce code that corresponds as closely as possible to target-language
  /// code.  For example, functions/methods in Java and JavaScript can only
  /// return one value, so they set MultipleReturnStyle to Tuple, prompting
  /// the pre-compiler to rewrite methods to return tuples where necessary.
  public class TargetLanguage {
    public string Name;

    /// How the language handles methods that return multiple values.  (A method
    /// with a single non-ghost out parameter is always translated into a method
    /// that simply returns one value.)
    public MultipleReturnStyleEnum MultipleReturnStyle;

    public enum MultipleReturnStyleEnum {
      /// Methods can return multiple values.  This is exactly the situation in
      /// Dafny, so nothing needs to be done by the pre-compiler.  (Go)
      MultipleReturns,
      /// Methods can have output parameters.  This is currently handled the
      /// same as MultipleReturns by the pre-compiler; the backend handles the
      /// straightforward reinterpretation of <tt>a, b := f();</tt> as
      /// <tt>f(out a, out b);</tt>.  (C#)
      OutParameters,
      /// No support for returning multiple values.  The pre-compiler must
      /// rewrite methods to return tuples instead where necessary.  (Java,
      /// JavaScript)
      Tuple,
    }
  }
}