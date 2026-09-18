package com.raccoonlang

class ImplicitParamTests extends munit.FunSuite {
  private def checked(src: String): Value = TestSupport.check(src)._2.map(_.value).getOrElse(fail("Expected result"))
  private val nat =
    """
      |inductive Nat : Type
      | | zero : Nat
      | | succ (n: Nat) : Nat
      |""".stripMargin

  test("implicit binders reconstruct from later explicit argument types") {
    val src = nat + "\n" + """
                             |def id {A: Type}(x: A): A := x
                             |{ id(Nat.succ(Nat.zero)) }
                             |""".stripMargin
    assertEquals(PrettyPrinter.print(checked(src)), "1")
  }

  test("supplying a forced implicit positionally is an arity error") {
    val src = nat + "\n" + """
                             |def id {A: Type}(x: A): A := x
                             |{ id(Nat, Nat.zero) }
                             |""".stripMargin
    intercept[ArityMismatch](checked(src))
  }

  test("unforced implicit binders are rejected") {
    val src = nat + "\naxiom bad : Nat -> {A: Type} -> A\n"
    intercept[NonForcedImplicitParam](TestSupport.check(src))
  }

  test("implicit binders can occur in the middle of a telescope") {
    val src = nat + "\n" + """
                             |def choose (n: Nat){A: Type}(x: A)(y: A): A := x
                             |{ choose(Nat.zero, Nat.zero, Nat.succ(Nat.zero)) }
                             |""".stripMargin
    assertEquals(PrettyPrinter.print(checked(src)), "0")
  }

  test("a polymorphic function adapts to an expected monomorphic Pi") {
    val src = nat + "\n" + """
                             |def id {A: Type}(x: A): A := x
                             |{
                             |  let f : Nat -> Nat := id
                             |  f(Nat.succ(Nat.zero))
                             |}
                             |""".stripMargin
    assertEquals(PrettyPrinter.print(checked(src)), "1")
  }

  test("runtime evaluation reconstructs the same implicit") {
    val src = nat + "\n" + """
                             |def id {A: Type}(x: A): A := x
                             |{ id(Nat.zero) }
                             |""".stripMargin
    assertEquals(PrettyPrinter.print(TestSupport.eval(src)), "0")
  }

  test("dependent constructor indices reconstruct from a later field") {
    val src = nat + "\n" + """
                             |inductive Vec (A: Type) indices (n: Nat) : Type
                             | | nil : Vec(A, Nat.zero)
                             | | cons {n: Nat} (tail: Vec(A, n)) (head: A) : Vec(A, Nat.succ(n))
                             |
                             |def len {n: Nat} (v: Vec(Nat, n)): Nat := n
                             |{
                             |  len(Vec.cons(Vec.nil(Nat), Nat.zero))
                             |}
                             |""".stripMargin
    assertEquals(PrettyPrinter.print(checked(src)), "1")
  }

  test("implicit family arguments can be used in codomains and bodies") {
    val src = nat + "\n" +
      "inductive Box {u: Level}(A: Sort(u)) : Sort(u)\n" +
      " | mk (a: A) : Box(A)\n\n" +
      "def unbox {u: Level}{A: Sort(u)} (b: Box(A)): A := {\n match b returning A with\n | Box.mk a => a\n}\n" +
      "{ unbox(Box.mk(Nat.zero)) }\n"
    assertEquals(PrettyPrinter.print(checked(src)), "0")
  }

  test("implicit indices remain available as ordinary terms") {
    val src = nat + "\n" +
      "inductive Vec (A: Type) indices (n: Nat) : Type\n" +
      " | nil : Vec(A, Nat.zero)\n" +
      " | cons {n: Nat} (tail: Vec(A, n)) (head: A) : Vec(A, Nat.succ(n))\n\n" +
      "def len {n: Nat} (v: Vec(Nat, n)): Nat := n\n" +
      "{ len(Vec.cons(Vec.nil(Nat), Nat.zero)) }\n"
    assertEquals(PrettyPrinter.print(checked(src)), "1")
  }

  test("ordinary hidden constructor binders are not family-parameter inference") {
    val src = "inductive Bad (A: Type) : Type\n | mk {B: Type} : Bad(B)\n"
    intercept[NonForcedImplicitParam](TestSupport.check(src))
  }

  test("match patterns bind implicit constructor fields") {
    val src =
      "inductive Nat : Type\n | zero : Nat\n\n" +
        "inductive Pack : Sort(Level.succ(Level.one))\n | mk {A: Type} (x: A) : Pack\n\n" +
        "def carrier (p: Pack): Type := {\n match p returning Type with\n | Pack.mk A x => A\n}\n" +
        "{ carrier(Pack.mk(Nat.zero)) }\n"
    checked(src)
  }

  test("explicit arguments are still checked against their binder types") {
    val src = nat + "\ndef id {A: Type}(x: A): A := x\n{ id(Type) }\n"
    intercept[TypeMismatch](TestSupport.check(src))
  }

  test("dependent Pi codomains do not force an implicit, while nondependent ones do") {
    val ok = nat +
      "\ndef ok {C: Type} (f: (n: Nat) -> C): Nat := Nat.zero\n"
    TestSupport.check(ok)
    val bad = nat +
      "\ndef bad {C: Nat -> Type} (f: (n: Nat) -> C(n)): Nat := Nat.zero\n"
    intercept[NonForcedImplicitParam](TestSupport.check(bad))
  }

  test("unused implicit level binders are rejected") {
    intercept[NonForcedImplicitParam](TestSupport.check("axiom bad : {u: Level} -> Type\n"))
  }

  test("implicit-only axioms are rejected") {
    intercept[NonForcedImplicitParam](TestSupport.check("axiom arbitrary : {A: Type} -> A\n"))
  }

  test("positional constructor and level implicits are rejected") {
    val ctor = nat +
      "\ninductive Box (A: Type) : Type\n | mk (x: A) : Box(A)\n\n{ Box.mk(Nat, Nat.zero) }\n"
    intercept[ArityMismatch](TestSupport.check(ctor))
    val level = nat +
      "\ndef idUp {u: Level}(A: Sort(Level.succ(u)))(x: A): A := x\n{ idUp(Level.one, Type, Nat) }\n"
    intercept[ArityMismatch](TestSupport.check(level))
  }
}
