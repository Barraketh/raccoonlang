package com.raccoonlang

/** The bundled Pair is level- and kind-polymorphic, forces its fields, and has no selectors. */
class PairTests extends munit.FunSuite with TestSupport {
  private val token =
    """
      |inductive Tok : Type { kind = lin }
      | | mk : Tok
      |
      |def burn (t: Tok): Nat := match t returning Nat with
      | | Tok.mk => 1
      |""".stripMargin

  private def withToken(decls: String): String = token + "\n" + decls

  test("an instance has the level and kind its components give it") {
    def program(sort: String, instance: String): String = s"def at : $sort := $instance\n"

    typecheckDecls(withToken(program("Type { kind = lin }", "Pair(Tok, Nat)")))
    typecheckDecls(withToken(program("Type { kind = lin }", "Pair(Nat, Tok)")))
    typecheckDecls(withToken(program("Type", "Pair(Nat, Bool)")))
    typecheckDecls(withToken(program("Type { level = one }", "Pair(Type, Type)")))
    typecheckDecls(withToken(program("Type { level = one }", "Pair(Nat, Type)")))
    expectOnly[TypeMismatch](typecheckDecls(withToken(program("Type", "Pair(Tok, Nat)"))))
    expectOnly[TypeMismatch](typecheckDecls(withToken(program("Type { kind = lin }", "Pair(Nat, Nat)"))))
    expectOnly[TypeMismatch](typecheckDecls(withToken(program("Type", "Pair(Type, Type)"))))
  }

  test("a generic kind parameter admits a linear pair, while an unrestricted binder rejects it") {
    val source = withToken(
      """
        |def count {A: Type}(x: A): Nat := 1
        |def countAt {k: Kind}{A: Type { kind = k }}(x: A): Pair(A, Nat) := Pair.mk(x, 0)
        |def linear (t: Tok): Pair(Pair(Tok, Nat), Nat) := countAt(Pair.mk(t, 0))
        |def plain : Nat := count(Pair.mk(0, Bool.true))
        |""".stripMargin
    )
    typecheckDecls(source)
    expectOnly[TypeMismatch](
      typecheckDecls(withToken("def count {A: Type}(x: A): Nat := 1\ndef f (t: Tok): Nat := count(Pair.mk(t, 0))\n"))
    )
  }

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
    assertEquals(
      expectOnly[ImplicitReconstructionFailed](typecheckDecls("def at : Type := Pair(True.intro, 0)\n")).param,
      "u"
    )
    typecheckDecls(
      "struct WithProof : Type\n | mk (proof: True)(value: Nat) : WithProof\n" +
        "def at : Nat := WithProof.value(WithProof.mk(True.intro, 0))\n"
    )
  }

  test("Pair.mk infers all parameters from its fields and can carry linear data") {
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
      withToken(
        """
          |def spend (t: Tok): Nat := {
          |  let p := Pair.mk(t, 0)
          |  match p returning Nat with
          |  | Pair.mk t2 n => Nat.add(burn(t2), n)
          |}
          |""".stripMargin
      )
    )
  }

  test("a linear pair is used exactly once, while unrestricted pairs may be copied") {
    def program(body: String): String = withToken(s"def spend (p: Pair(Tok, Nat)): Nat :=\n  $body\n")

    typecheckDecls(program("match p returning Nat with\n  | Pair.mk t n => Nat.add(burn(t), n)"))
    assertEquals(expectOnly[LinearUnused](typecheckDecls(program("0"))), LinearUnused("p"))
    assertEquals(
      expectOnly[LinearUnused](typecheckDecls(program("match p returning Nat with\n  | Pair.mk t n => n"))),
      LinearUnused("t")
    )
    typecheckDecls("def twice (p: Pair(Nat, Bool)): Pair(Pair(Nat, Bool), Pair(Nat, Bool)) := Pair.mk(p, p)\n")
    assertEquals(
      expectOnly[LinearReused](
        typecheckDecls(
          withToken(
            "def twice (p: Pair(Tok, Nat)): Pair(Pair(Tok, Nat), Pair(Tok, Nat)) := Pair.mk(p, p)\n"
          )
        )
      ),
      LinearReused("p")
    )
  }

  test("a pair has no selectors") {
    def program(body: String): String = s"def first (p: Pair(Nat, Bool)): Nat := $body\n"

    typecheckDecls(program("match p returning Nat with\n | Pair.mk n _ => n"))
    assertEquals(expectOnly[NotFound](typecheckDecls(program("p.fst"))), NotFound("Pair.fst"))
  }
}
