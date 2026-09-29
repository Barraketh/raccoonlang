package com.raccoonlang

/**
 * Declared family kinds and scopes (spec §5.1): a family's classifier is declared, never derived; its kind and scope
 * contain each constructor field's, its scope the scope of each parameter's and index's type, and a family at a kind
 * other than `Kind.unr` names each lifetime parameter. An instance is at exactly the declared sort under its arguments
 * (§2.4). Each rule has an admitted program and the smallest mutation that reaches its diagnostic.
 */
class FamilyKindScopeTests extends munit.FunSuite with TestSupport {

  /** A family scoped by its lifetime, and a linear one. */
  private val families =
    """
      |inductive V (l: Lifetime) : Type { scope = l }
      | | mk : V(l)
      |
      |inductive Tok (l: Lifetime) : Type { kind = lin, scope = l }
      | | mk : Tok(l)
      |""".stripMargin

  private def withFamilies(decls: String): String = families + "\n" + decls

  test("the declared kind contains each field's kind") {
    def program(sort: String): String =
      s"inductive Holder {k: Kind}{S: Lifetime}(A: Type { kind = k, scope = S }) : $sort\n | mk (held: A) : Holder(A)\n"

    typecheckDecls(program("Type { kind = k, scope = S }"))
    typecheckDecls(program("Type { kind = lin, scope = S }"))
    val error = expectOnly[KindExceeded](typecheckDecls(program("Type { scope = S }")))
    assert(error.part.contains("Holder.mk.held"), error.part)
    expectOnly[KindExceeded](
      typecheckDecls(withFamilies("inductive Held (l: Lifetime) : Type { scope = l }\n | mk (t: Tok(l)) : Held(l)\n"))
    )
    expectOnly[KindExceeded](
      typecheckDecls(
        "struct Box {k: Kind}{S: Lifetime}(A: Type { kind = k, scope = S }) : Type { scope = S }\n" +
          " | mk (value: A) : Box(A)\n"
      )
    )
  }

  test("the declared scope contains each field's scope") {
    def program(sort: String): String =
      withFamilies(s"inductive Holds (l: Lifetime) : $sort\n | mk (h: V(l)) : Holds(l)\n")

    typecheckDecls(program("Type { scope = l }"))
    val error = expectOnly[ScopeExceeded](typecheckDecls(program("Type")))
    assert(error.part.contains("Holds.mk.h"), error.part)
  }

  // spec §5.1: a field in which the parameter holds no value is at its own kind, Kind.unr for an arrow. Its scope is
  // still the arrow's (§2.4), which counts its domains' scopes, so it is not "nothing" for the scope.
  test("a function-typed field is at Kind.unr but counts its domains' scopes") {
    typecheckDecls(
      "inductive Fn {k: Kind}{S: Lifetime}(A: Type { kind = k, scope = S }) : Type { scope = S }\n" +
        " | mk (f: A -> Nat) : Fn(A)\n"
    )
    def program(sort: String): String =
      withFamilies(s"inductive Reader (l: Lifetime) : $sort\n | mk (f: V(l) -> Nat) : Reader(l)\n")

    typecheckDecls(program("Type { scope = l }"))
    val error = expectOnly[ScopeExceeded](typecheckDecls(program("Type")))
    assert(error.part.contains("Reader.mk.f"), error.part)
  }

  test("the declared scope contains each parameter's and index's type's scope") {
    def phantom(sort: String): String =
      s"inductive Phantom {S: Lifetime}(A: Type { scope = S }) : $sort\n | mk : Phantom(A)\n"
    def leased(sort: String): String = withFamilies(s"inductive P {l: Lifetime}(h: V(l)) : $sort\n | mk : P(h)\n")
    def indexed(sort: String): String =
      withFamilies(s"inductive I (l: Lifetime) indices (h: V(l)) : $sort\n | mk : I(l, V.mk(l))\n")

    typecheckDecls(phantom("Type { scope = S }"))
    typecheckDecls(leased("Type { scope = l }"))
    typecheckDecls(indexed("Type { scope = l }"))
    assert(expectOnly[ScopeExceeded](typecheckDecls(phantom("Type"))).part.startsWith("parameter A"))
    assert(expectOnly[ScopeExceeded](typecheckDecls(leased("Type"))).part.startsWith("parameter h"))
    assert(expectOnly[ScopeExceeded](typecheckDecls(indexed("Type"))).part.startsWith("index h"))
  }

  test("a sort parameter's type contributes nothing to the scope") {
    typecheckDecls(
      "inductive S (u: Level)(k: Kind)(l: Lifetime) : Type\n | mk : S(u, k, l)\n\n" +
        "inductive F {k: Kind}(A: Type { kind = k }) : Type { kind = k }\n | mk (a: A) : F(A)\n"
    )
  }

  test("a family holding two scopes declares their union") {
    def program(scope: String): String =
      s"""
         |inductive Pair {S: Lifetime}{T: Lifetime}(A: Type { scope = S })(B: Type { scope = T }) : Type { scope = $scope }
         | | mk (a: A)(b: B) : Pair(A, B)
         |""".stripMargin

    typecheckDecls(program("union(S, T)"))
    assert(expectOnly[ScopeExceeded](typecheckDecls(program("S"))).part.startsWith("parameter B"))
  }

  test("a family at a kind other than Kind.unr names each lifetime parameter") {
    def tok(sort: String): String = s"inductive Tok (l: Lifetime) : $sort\n | mk : Tok(l)\n"
    def cell(sort: String): String = s"inductive Cell (k: Kind)(l: Lifetime) : $sort\n | mk : Cell(k, l)\n"

    typecheckDecls(tok("Type { kind = lin, scope = l }"))
    typecheckDecls(tok("Type"))
    typecheckDecls(cell("Type { kind = k, scope = l }"))
    assert(
      expectOnly[ScopeExceeded](typecheckDecls(tok("Type { kind = lin }"))).part.startsWith("lifetime parameter l")
    )
    expectOnly[ScopeExceeded](typecheckDecls(cell("Type { kind = k }")))
  }

  // spec §2.7: a proposition obeys §5.1 like any family, so an Eq holding an A is at A's scope, and it holds no token.
  test("a proposition's declared kind and scope obey the same rules") {
    def same(sort: String): String =
      s"""
         |inductive Same {S: Lifetime}(A: Type { scope = S }) indices (x: A)(y: A) : $sort
         | | refl (x: A) : Same(A, x, x)
         |""".stripMargin

    typecheckDecls(same("Prop { scope = S }"))
    expectOnly[ScopeExceeded](typecheckDecls(same("Prop")))
    expectOnly[KindExceeded](
      typecheckDecls(withFamilies("inductive Holds (l: Lifetime) : Prop { scope = l }\n | mk (t: Tok(l)) : Holds(l)\n"))
    )
  }

  // A sibling's field is read by its declared sort: were it derived, First would inherit Second's token.
  test("a mutual sibling is read by its declared classifier") {
    def program(sort: String): String =
      withFamilies(
        s"""
           |mutual {
           |  inductive First (l: Lifetime) : $sort
           |   | mk (second: Second(l)) : First(l)
           |
           |  inductive Second (l: Lifetime) : $sort
           |   | stop (t: Tok(l)) : Second(l)
           |}
           |""".stripMargin
      )

    typecheckDecls(program("Type { kind = lin, scope = l }"))
    val error = expectOnly[KindExceeded](typecheckDecls(program("Type { scope = l }")))
    assert(error.part.contains("Second.stop.t"), error.part)
  }

  // spec §3.1: a family at a kind variable is linear exactly at the instances whose argument is.
  test("an instance is at exactly the declared sort under its arguments") {
    def program(linear: String, plain: String): String =
      withFamilies(
        s"""
           |inductive Holder {k: Kind}{S: Lifetime}(A: Type { kind = k, scope = S }) : Type { kind = k, scope = S }
           | | mk (held: A) : Holder(A)
           |
           |inductive Lst {S: Lifetime}(A: Type { scope = S }) : Type { scope = S }
           | | nil : Lst(A)
           | | cons (head: A)(tail: Lst(A)) : Lst(A)
           |
           |def linear (l: Lifetime) : $linear := Holder(Tok(l))
           |def plain : $plain := Holder(Nat)
           |def leases (l: Lifetime) : Type { scope = l } := Lst(V(l))
           |def empty (l: Lifetime) : Lst(V(l)) := Lst.nil(V(l))
           |""".stripMargin
      )

    typecheckDecls(program("Type { kind = lin, scope = l }", "Type"))
    expectOnly[TypeMismatch](typecheckDecls(program("Type { scope = l }", "Type")))
    expectOnly[TypeMismatch](typecheckDecls(program("Type { kind = lin, scope = l }", "Type { kind = lin }")))
  }
}
