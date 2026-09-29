package com.raccoonlang

/**
 * Axioms (spec §7.3): only the trusted prelude declares them. A program that needs an assumption declares it in a
 * custom prelude, whose axioms keep the trusted bootstrap's obligations (docs/kernel.md), so every value of a sealed
 * family comes from its constructors (§7.1).
 */
class AxiomTests extends munit.FunSuite with TestSupport {
  private val peano =
    """
      |inductive Peano : Type
      | | zero : Peano
      | | succ (_: Peano) : Peano
      |""".stripMargin

  /** The test prelude with Peano and two assumptions about it. */
  private lazy val assumptions =
    TestSupport.preludeAssuming(
      TestSupport.testPreludeSource,
      peano + "\naxiom magicNat : Peano\n\naxiom choose (A: Type)(x: A): A\n"
    )

  test("an axiom in the trusted prelude declares an opaque constant") {
    val res = runProgram("{ magicNat }", assumptions)
    assertEquals(PrettyPrinter.print(res), "magicNat")
    assertEquals(PrettyPrinter.print(res.tpe), "Peano")
  }

  test("a parameterized axiom in the trusted prelude can be applied") {
    val res = runProgram("{ choose(Peano, Peano.zero) }", assumptions)
    assertEquals(PrettyPrinter.print(res), "choose(Peano, Peano.zero)")
    assertEquals(PrettyPrinter.print(res.tpe), "Peano")
  }

  test("an axiom's result must be a type") {
    val bad = TestSupport.preludeAssuming(TestSupport.testPreludeSource, peano + "\naxiom bad : Peano.zero\n")
    interceptError[NotAType](bad.checkedEnv)
  }

  test("an axiom outside the trusted prelude is UntrustedAxiom, in the entry file and in an imported module") {
    // The same declaration the prelude above admits.
    assertEquals(
      expectOnly[UntrustedAxiom](typecheckDecls(peano + "\naxiom magicNat : Peano\n", Prelude.test)),
      UntrustedAxiom("magicNat")
    )
    assertEquals(expectOnly[UntrustedAxiom](outside("axiom n : Nat\n", "{ 0 }")), UntrustedAxiom("n"))
  }

  test("an axiom outside the prelude is UntrustedAxiom whatever its type, spec §7.3's examples and harmless ones") {
    val pair = "inductive Pair (l: Lifetime)(m: Lifetime) : Type { scope = union(l, m) }\n | mk : Pair(l, m)\n\n"
    Vector(
      "axiom excludedMiddle (P: Prop): Or(P, Not(P))\n" -> "excludedMiddle",
      "axiom eat {A: Type { kind = lin }}(x: A): Unit\n" -> "eat",
      pair + "axiom pairEq (a: Lifetime)(b: Lifetime): Eq(Type { scope = union(a, b) }, Pair(a, b), Pair(b, a))\n" ->
        "pairEq",
      "axiom a : List(Nat)\n" -> "a"
    ).foreach { case (program, axiom) =>
      assertEquals(expectOnly[UntrustedAxiom](typecheckDecls(program)), UntrustedAxiom(axiom))
    }
  }

  test("the prelude's Quot binds lifetimes, and the same declaration in a program is UntrustedAxiom") {
    val quot =
      "axiom Quot2 {u: Level}{S: Lifetime}{Sr: Lifetime}{Sq: Lifetime}(A: Sort { level = u, scope = S })" +
        "(r: { scope = Sr } A -> A -> Prop { scope = Sq }): Sort { level = u, scope = union(S, union(Sr, Sq)) }\n"
    TestSupport.preludeAssuming(TestSupport.bundledPreludeSource, quot).checkedEnv
    assertEquals(expectOnly[UntrustedAxiom](typecheckDecls(quot)), UntrustedAxiom("Quot2"))
  }

  /** A sealed permit its module redeems for a token, and a module function returning one (spec §7.1). */
  private val permitModule =
    """
      |sealed inductive Permit (l: Lifetime) : Prop { scope = l }
      | | mk : Permit(l)
      |
      |sealed inductive Tok (l: Lifetime) : Type { kind = lin, scope = l }
      | | mk : Tok(l)
      |
      |def redeem {l: Lifetime}(p: Permit(l)): Tok(l) := match p returning Tok(l) with
      | | .mk => Tok.mk(l)
      |
      |def burn {l: Lifetime}(t: Tok(l)): Nat := match t returning Nat with
      | | .mk => 1
      |
      |def grant (n: Nat): Permit(Lifetime.empty) := Permit.mk(Lifetime.empty)
      |""".stripMargin

  test("a proof of a sealed proposition is reconstructed like any other, so the module's match redeems it") {
    // A proof function's body never runs: grant(0) is reconstructed as Permit.mk from its proposition.
    assertEquals(inside(permitModule, "{ burn(redeem(grant(0))) }").map(PrettyPrinter.print), Some("1"))
    assertEquals(outside(permitModule, "{ burn(redeem(grant(0))) }").map(PrettyPrinter.print), Some("1"))
    // So is a proof pulled out of another family's field, and one whose proposition computes to Permit.
    val wrapped =
      "struct Wrapper : Prop\n | mk (p: Permit(Lifetime.empty)) : Wrapper\n\n" +
        "def unwrap (w: Wrapper): Nat := match w returning Nat with\n | .mk p => burn(redeem(p))\n\n" +
        "{ unwrap(Wrapper.mk(grant(1))) }\n"
    assertEquals(outside(permitModule, wrapped).map(PrettyPrinter.print), Some("1"))
    val computed =
      "def P (n: Nat) : Prop := match n returning Prop with\n | .zero => Permit(Lifetime.empty)\n | .succ _ => True\n\n" +
        "def at (p: Permit(Lifetime.empty)): P(0) := p\n\n{ burn(redeem(at(grant(2)))) }\n"
    assertEquals(outside(permitModule, computed).map(PrettyPrinter.print), Some("1"))
  }
}
