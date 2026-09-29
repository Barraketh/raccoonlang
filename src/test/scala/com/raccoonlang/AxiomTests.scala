package com.raccoonlang

import com.raccoonlang.AxiomMintsToken.Part

class AxiomTests extends munit.FunSuite with TestSupport {
  private val natPrelude =
    """
      |inductive Peano : Type
      | | zero : Peano
      | | succ (_: Peano) : Peano
      |
      |""".stripMargin

  test("axiom declares an opaque constant") {
    val res = runProgram(
      natPrelude +
        """
          |axiom magicNat : Peano
          |
          |{
          |  magicNat
          |}
          |""".stripMargin,
      Prelude.test
    )

    assertEquals(PrettyPrinter.print(res), "magicNat")
    assertEquals(PrettyPrinter.print(res.tpe), "Peano")
  }

  test("parameterized axiom can be applied") {
    val res = runProgram(
      natPrelude +
        """
          |axiom choose (A: Type)(x: A): A
          |
          |{
          |  choose(Peano, Peano.zero)
          |}
          |""".stripMargin,
      Prelude.test
    )

    assertEquals(PrettyPrinter.print(res), "choose(Peano, Peano.zero)")
    assertEquals(PrettyPrinter.print(res.tpe), "Peano")
  }

  test("axiom result must be a type") {
    val p =
      natPrelude +
        """
          |axiom bad : Peano.zero
          |""".stripMargin

    interceptError[NotAType] {
      typecheckDecls(p, Prelude.test)
    }
  }

  // What an axiom may state (spec §7.3): each rule is an admitted axiom and the smallest mutation that is
  // AxiomMintsToken.

  private val families =
    """
      |inductive Tok (l: Lifetime) : Type { kind = lin, scope = l }
      | | mk : Tok(l)
      |
      |inductive W (l: Lifetime) : Type { kind = lin, scope = l }
      | | mk (t: Tok(l)) : W(l)
      |
      |inductive V (l: Lifetime) : Type
      | | mk (n: Nat) : V(l)
      |
      |inductive Wrap (l: Lifetime) : Type
      | | mk : Wrap(l)
      |
      |""".stripMargin

  private def admits(axiom: String): Unit = typecheckDecls(families + axiom)

  private def mints(axiom: String)(implicit loc: munit.Location): AxiomMintsToken =
    expectOnly[AxiomMintsToken](typecheckDecls(families + axiom))

  test("an axiom that binds a kind or a lifetime is AxiomMintsToken, and one that binds a level is admitted") {
    admits("axiom choose {u: Level}(A: Sort { level = u })(x: A): A\n")
    // A fieldless Wrap: no two lifetimes are apart, so no program could refute this equation.
    admits("axiom wrapEq : Eq(Type, Wrap(Lifetime.empty), Wrap(Lifetime.empty))\n")
    assertEquals(
      mints("axiom wrapEq (a: Lifetime)(b: Lifetime): Eq(Type, Wrap(a), Wrap(b))\n"),
      AxiomMintsToken("wrapEq", Part.Binder("a", Value.LifetimeTpe))
    )
    admits("axiom drop (A: Type): Unit\n")
    assertEquals(
      mints("axiom drop {k: Kind}(A: Type { kind = k }): Unit\n"),
      AxiomMintsToken("drop", Part.Binder("k", Value.KindTpe))
    )
    // A function type inside the axiom's type binds too.
    admits("axiom call (f: Nat -> Nat): Nat\n")
    assertEquals(
      mints("axiom call (f: (l: Lifetime) -> Nat): Nat\n"),
      AxiomMintsToken("call", Part.Binder("l", Value.LifetimeTpe))
    )
  }

  test("an axiom whose type holds a kind or lifetime but Kind.unr and Lifetime.empty is AxiomMintsToken") {
    admits("axiom eat {A: Type { kind = unr, scope = empty }}(x: A): Unit\n")
    assertEquals(
      mints("axiom eat {A: Type { kind = lin }}(x: A): Unit\n"),
      AxiomMintsToken("eat", Part.Parameter(Value.Kind.lin))
    )
    // A closure field counts, as a sort field does.
    admits("axiom run (f: Unit -> Nat): Nat\n")
    assertEquals(
      mints("axiom run (f: { kind = lin } Unit -> Nat): Nat\n"),
      AxiomMintsToken("run", Part.Parameter(Value.Kind.lin))
    )
    // The type is read as a value, where an atom may stand inside a neutral a definition computed.
    val tag = "opaque def tag (l: Lifetime): Nat := 0\n"
    admits(tag + "def z : Nat := tag(Lifetime.empty)\naxiom atZero : Eq(Nat, z, 0)\n")
    mints(tag + "def z : Nat := scope l => tag(l)\naxiom atZero : Eq(Nat, z, 0)\n") match {
      case AxiomMintsToken("atZero", Part.Parameter(atom: Value.Lifetime)) => assertEquals(atom.toString, "l")
      case other                                                           => fail(s"expected the atom, got $other")
    }
  }

  test("an axiom whose type contains a linear type is AxiomMintsToken, a family holding a token included") {
    admits("axiom peek (v: V(Lifetime.empty)): Unit\n")
    assertEquals(
      mints("axiom peek (w: W(Lifetime.empty)): Unit\n").toString,
      "AxiomMintsToken(peek,LinearType(W(Lifetime.empty)))"
    )
    assertEquals(
      mints("axiom tok : Tok(Lifetime.empty)\n").toString,
      "AxiomMintsToken(tok,LinearType(Tok(Lifetime.empty)))"
    )
    // A neutral type is linear when the sort it states is.
    assertEquals(
      mints("opaque def T : Type { kind = lin } := Tok(Lifetime.empty)\naxiom t : T\n").toString,
      "AxiomMintsToken(t,LinearType(T))"
    )
  }

  test("an axiom whose type mentions only unrestricted, unscoped instances is admitted") {
    // List binds a lifetime, but its own type is not the axiom's: the instance's arguments are Lifetime.empty and Nat.
    runProgram("axiom a : List(Nat)\n{ a }")
    runProgram("axiom n (A: Type)(xs: List(A)): Nat\n{ n(Nat, List.nil(Nat)) }")
  }

  test("the trusted prelude's Quot binds lifetimes, and the same declaration in a program is AxiomMintsToken") {
    // The rule would refuse the prelude's own declarations; only the prelude's trust admits them.
    val env = Prelude.default.checkedEnv
    Vector("Quot" -> "S", "Quot.sound" -> "S").foreach { case (axiom, binder) =>
      assertEquals(
        interceptError[AxiomMintsToken](Axioms.requireMintsNoToken(axiom, env(axiom).tpe, Span.synthetic())),
        AxiomMintsToken(axiom, Part.Binder(binder, Value.LifetimeTpe))
      )
    }
    val quot =
      "axiom Quot2 {u: Level}{S: Lifetime}{Sr: Lifetime}{Sq: Lifetime}(A: Sort { level = u, scope = S })" +
        "(r: { scope = Sr } A -> A -> Prop { scope = Sq }): Sort { level = u, scope = union(S, union(Sr, Sq)) }\n"
    assertEquals(mints(quot), AxiomMintsToken("Quot2", Part.Binder("S", Value.LifetimeTpe)))
  }

  /** A sealed permit its module redeems for a token (spec §7.3). */
  private val permitModule =
    """
      |sealed inductive Permit (l: Lifetime) : Prop
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
      |""".stripMargin

  test("an axiom at a family sealed to another module is AxiomMintsToken, so it cannot forge a permit") {
    // Proof irrelevance reconstructs forge as Permit.mk, so the module's own match redeems it for a token. Inside the
    // module that is the module's own choice.
    val attack = "axiom forge : Permit(Lifetime.empty)\n{ burn(redeem(forge)) }\n"
    assertEquals(inside(permitModule, attack).map(PrettyPrinter.print), Some("1"))
    assertEquals(
      expectOnly[AxiomMintsToken](outside(permitModule, attack)),
      AxiomMintsToken("forge", Part.SealedFamily("Permit"))
    )
    // The mutation is the seal alone.
    assertEquals(
      outside(permitModule.replace("sealed inductive Permit", "inductive Permit"), attack).map(PrettyPrinter.print),
      Some("1")
    )
  }
}
