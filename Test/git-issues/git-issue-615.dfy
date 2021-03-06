// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class MyClass {
  ghost const repr: object
}

datatype D1 = D1(o: MyClass)
{
  ghost const objs: set<object> := getObjs()

  function getObjs(): set<object>
    reads o
    { {o, o.repr} }
}

class MyClass2 {
  var x: int
  const c := F()

  function method F(): int
    reads this
  {
    x
  }
}
