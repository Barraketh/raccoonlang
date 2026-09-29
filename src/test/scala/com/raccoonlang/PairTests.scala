package com.raccoonlang

/**
 * The bundled prelude's `Pair` (docs/PAIRS_AND_PRELUDE.md §2): a pair of types at any level above `Prop`, at the kind
 * and scope its components give it. Every implicit is forced by the constructor's fields, and it has no selectors, so a
 * value is taken apart by `match`. Each rule has an admitted program and the smallest mutation that reaches its
 * diagnostic.
 */
class PairTests extends munit.FunSuite with TestSupport {

  /** A linear token, a scoped lease, and a consumer of a token. */
  private val families =
    """
      |inductive Tok (l: Lifetime) : Type { kind = lin, scope = l }
      | | mk : Tok(l)
      |
      |inductive Lease (l: Lifetime) : Type { scope = l }
      | | mk : Lease(l)
      |
      |def burn {l: Lifetime}(t: Tok(l)): Nat := match t returning Nat with
      | | Tok.mk => 1
      |""".stripMargin

  private def withFamilies(decls: String): String = families + "\n" + decls

  test("an instance is at the level, kind and scope its components give it") {
    def program(sort: String, instance: String): String = withFamilies(s"def at (l: Lifetime): $sort := $instance\n")

    typecheckDecls(program("Type { kind = lin, scope = l }", "Pair(Tok(l), Nat)"))
    typecheckDecls(program("Type { kind = lin, scope = l }", "Pair(Nat, Tok(l))"))
    typecheckDecls(program("Type { scope = l }", "Pair(Lease(l), Nat)"))
    typecheckDecls(program("Type", "Pair(Nat, Bool)"))
    typecheckDecls(program("Sort { level = succ(one) }", "Pair(Type, Type)"))
    typecheckDecls(program("Sort { level = succ(one) }", "Pair(Nat, Type)"))
    expectOnly[TypeMismatch](typecheckDecls(program("Type { scope = l }", "Pair(Tok(l), Nat)")))
    expectOnly[TypeMismatch](typecheckDecls(program("Type { kind = lin, scope = l }", "Pair(Lease(l), Nat)")))
    expectOnly[TypeMismatch](typecheckDecls(program("Type", "Pair(Lease(l), Nat)")))
    expectOnly[TypeMismatch](typecheckDecls(program("Type", "Pair(Type, Type)")))
  }

  // spec §2.3: a component's level is a successor, so a proof is paired with a value by Prod, Sigma or Subtype. A
  // proposition's level `zero` solves no successor `succ(u)`, whichever position it takes.
  test("a component is a type, never a proposition") {
    typecheckDecls("def at : Type := Pair(Nat, Nat)\n")
    assertEquals(
      expectOnly[ImplicitReconstructionFailed](typecheckDecls("def at : Type := Pair(True, Nat)\n")).param,
      "u"
    )
    assertEquals(
      expectOnly[ImplicitReconstructionFailed](typecheckDecls("def at : Type := Pair(Nat, True)\n")).param,
      "v"
    )
    typecheckDecls("def at : Nat := Prod.snd(Prod.mk(True.intro, 0))\n")
    expectOnly[ImplicitReconstructionFailed](
      typecheckDecls("def at : Nat := match Pair.mk(True.intro, 0) returning Nat with\n | Pair.mk _ n => n\n")
    )
  }

  test("Pair.mk forces every implicit from its fields") {
    // No expected type reaches either construction: the types, levels, kinds and scopes all come from the fields.
    val nested =
      """
        |{
        |  let p := Pair.mk(3, Pair.mk(Nat, Bool.true))
        |  match p returning Nat with
        |  | Pair.mk n _ => n
        |}
        |""".stripMargin
    assert(ValueEquivalence.defEq(runProgram(nested), runProgram("{ 3 }")))
    typecheckDecls(
      withFamilies(
        """
          |def spend {l: Lifetime}(t: Tok(l)): Nat := {
          |  let p := Pair.mk(t, Lease.mk(l))
          |  match p returning Nat with
          |  | Pair.mk t2 _ => burn(t2)
          |}
          |""".stripMargin
      )
    )
  }

  test("a linear instance is used exactly once, and an unrestricted one freely") {
    def program(body: String): String =
      withFamilies(s"def spend {l: Lifetime}(p: Pair(Tok(l), Nat)): Nat :=\n  $body\n")

    typecheckDecls(program("match p returning Nat with\n  | Pair.mk t n => Nat.add(burn(t), n)"))
    assertEquals(expectOnly[LinearUnused](typecheckDecls(program("0"))), LinearUnused("p"))
    assertEquals(
      expectOnly[LinearUnused](typecheckDecls(program("match p returning Nat with\n  | Pair.mk t n => n"))),
      LinearUnused("t")
    )
    def twice(component: String): String =
      withFamilies(
        s"def twice (l: Lifetime)(p: Pair($component, Bool)): Pair(Pair($component, Bool), Pair($component, Bool)) := " +
          "Pair.mk(p, p)\n"
      )
    typecheckDecls(twice("Nat"))
    typecheckDecls(twice("Lease(l)"))
    assertEquals(expectOnly[LinearReused](typecheckDecls(twice("Tok(l)"))), LinearReused("p"))
  }

  test("a scoped component keeps the pair in its scope") {
    def program(body: String): String = withFamilies(s"def at : Nat := $body\n")

    typecheckDecls(program("scope l => match Pair.mk(Lease.mk(l), 1) returning Nat with\n | Pair.mk _ n => n"))
    assertEquals(
      expectOnly[LifetimeEscapes](
        typecheckDecls(program("match (scope l => Pair.mk(Lease.mk(l), 1)) returning Nat with\n | Pair.mk _ n => n"))
      ).lifetime,
      "l"
    )
  }

  // spec §2.2: `Pair` is an inductive, since a selector binds both fields and drops one.
  test("a pair has no selectors") {
    def program(body: String): String = s"def first (p: Pair(Nat, Bool)): Nat := $body\n"

    typecheckDecls(program("match p returning Nat with\n | Pair.mk n _ => n"))
    assertEquals(expectOnly[NotFound](typecheckDecls(program("p.fst"))), NotFound("Pair.fst"))
  }
}
