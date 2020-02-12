// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:cs "%s" > "%t"
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

function method F(x: int, y: bool): int {
  x + if y then 2 else 3
}

method A0(x: int, y: bool) {
  return;
}

method A1(x: int, y: bool) returns (a: int) {
  return a;
}

method A2(x: int, y: bool) returns (a: int, b: bool) {
  return a, b;
}

method A3(x: int, y: bool) returns (a: int, b: bool, c: int) {
  var u;
  if x == 3 {
    u := c;
  } else if x == 4 {
    u := c + 0;
  } else {
    u := c + 0 + 0;
  }
  u := 1 * u;
  {
    var y := 65;
    u := 0 + u;
  }
  return a, b, u;
}

// HACK: The pre-compiler needs access to the n-tuple type whenever there's
// a method with n non-ghost outs (if compiling to a language with
// MultipleReturnStyle set to Tuple).  Currently there's no way to add
// tuple types except through the parser, so we make sure the needed tuples
// appear in the program as a temporary workaround.
method SillyMethod() {
  var a : (int, int) := (2, 3);
  var b : (int, int, int) := (4, 8, 15);
}

method Main()
{
  var w, a, b, c, d, e, f;
  w := F(2, false);
  A0(2, false);
  a := A1(2, false);
  b, c := A2(2, false);
  d, e, f := A3(2, false);
  print w, " ", a, " ", b, " ", c, " ", d, " ", e, " ", f, "\n";
}
