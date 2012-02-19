datatype List<T> = Nil | Cons(hd: T, tl: List);

method M0() {
  var l: List;
  l := Cons(5, Nil);
  assert l.hd == 5;

  var k: MyClass<bool>;
  k := new MyClass;
  k.data := false;

  var h := new MyClass;
  h.data := false;

  var y := new MyClass.Init(120);
  var z: int := y.data;
}

method M1() {  // same thing as above, but with types filled in explicitly
  var l: List<int>;
  l := Cons(5, Nil);
  assert l.hd == 5;

  var k: MyClass<bool>;
  k := new MyClass<bool>;
  k.data := false;

  var h := new MyClass<bool>;
  h.data := false;

  var y := new MyClass<int>.Init(120);
  var z: int := y.data;
}

class MyClass<G> {
  var data: G;
  method Init(g: G)
    modifies this;
  {
    data := g;
  }
}

// ---------------------------------------------------

// The followinng functions and methods are oblivious of the fact that
// List takes a type parameter.

function concat(xs: List, ys: List): List
{
  match xs
  case Nil => ys
  case Cons(x, tail) => Cons(x, concat(tail, ys))
}

function reverse(xs: List): List
{
  match xs
  case Nil => Nil
  case Cons(t, rest) => concat(reverse(rest), Cons(t, Nil))
}

ghost method Theorem(xs: List)
  ensures reverse(reverse(xs)) == xs;
{
  match (xs) {
    case Nil =>
    case Cons(t, rest) =>
      Lemma(reverse(rest), Cons(t, Nil));
  }
}

ghost method Lemma(xs: List, ys: List)
  ensures reverse(concat(xs, ys)) == concat(reverse(ys), reverse(xs));
{
  match (xs) {
    case Nil =>
      assert forall ws :: concat(ws, Nil) == ws;
    case Cons(t, rest) =>
      assert forall a, b, c :: concat(a, concat(b, c)) == concat(concat(a, b), c);
  }
}