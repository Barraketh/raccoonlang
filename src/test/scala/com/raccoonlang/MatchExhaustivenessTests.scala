package com.raccoonlang

class MatchExhaustivenessTests extends munit.FunSuite {
  private def typecheckDecls(src: String): Unit = {
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        Interpreter.run(core, Prelude.test)
      case err: Failure => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }
  }

  test("non-exhaustive: missing succ case on Nat") {
    val p =
      """
        |def onlyZero (n: Nat): Nat := {
        |  match n with
        |  | Nat.zero => Nat.zero
        |}
        |
        |""".stripMargin

    intercept[MissingCase] { typecheckDecls(p) }
  }

  test("duplicate case: two Nat.zero branches") {
    val p =
      """
        |def dup (n: Nat): Nat := {
        |  match n with
        |  | Nat.zero => Nat.zero
        |  | Nat.zero => Nat.zero
        |  | Nat.succ x => x
        |}
        |
        |""".stripMargin

    intercept[DuplicateCase] { typecheckDecls(p) }
  }

  test("unreachable case: Vec.cons on Vec A Nat.zero") {
    val p =
      """
        |inductive Vec (A: Type) indices (n: Nat) : Sort(Level.one)
        | | nil {A: Type} : Vec(A, Nat.zero)
        | | cons {A: Type} (n: Nat) (xs: Vec(A, n)) (x: A): Vec(A, Nat.succ(n))
        |
        |def f (A: Type)(v: Vec(A, Nat.zero)): Nat := {
        |  match v returning Nat with
        |  | Vec.nil => Nat.zero
        |  | Vec.cons n xs x => Nat.zero
        |}
        |
        |""".stripMargin

    intercept[UnreachableCase] { typecheckDecls(p) }
  }

  test("non-exhaustive: opaque scrutinee application should still require succ case") {
    val p =
      """
        |// Opaque on purpose: evaluator will keep this as a Symbol head
        |axiom g (n: Nat): Nat
        |
        |def bad (n: Nat): Nat := {
        |  // scrutinee is neutral/opaque application: g n
        |  match g(n) with
        |  | Nat.zero => Nat.zero
        |}
        |
        |""".stripMargin

    intercept[MissingCase] { typecheckDecls(p) }
  }

  test("exhaustive: opaque scrutinee application should typecheck") {
    val p =
      """
        |axiom g (n: Nat): Nat
        |
        |def ok (n: Nat): Nat := {
        |  match g(n) with
        |  | Nat.zero => Nat.zero
        |  | Nat.succ x => x
        |}
        |
        |""".stripMargin

    // Should typecheck (even if it evaluates to a stuck match at runtime for opaque g).
    typecheckDecls(p)
  }

  test("omitted returning: inferred when all reachable constructor result types are equal") {
    val p =
      """
        |inductive Wrap (A: Type) : Type
        | | left {A: Type} (x: A) : Wrap(A)
        | | right {A: Type} (x: A) : Wrap(A)
        |
        |def keepWrap (A: Type)(w: Wrap(A)): Wrap(A) := {
        |  match w with
        |  | Wrap.left x => Wrap.left(A, x)
        |  | Wrap.right x => Wrap.right(A, x)
        |}
        |
        |""".stripMargin

    typecheckDecls(p)
  }

  test("omitted returning: contextual result supports matches with no reachable constructors") {
    val p =
      """
        |inductive IsZero indices (n: Nat) : Type
        | | intro : IsZero(Nat.zero)
        |
        |def absurdSucc (n: Nat)(h: IsZero(Nat.succ(n))): Nat := {
        |  match h with
        |}
        |
        |""".stripMargin

    typecheckDecls(p)
  }

  test("omitted returning: contextual result supports differing constructor result types") {
    val p =
      """
        |inductive Shape indices (n: Nat) : Type
        | | zeroCase : Shape(Nat.zero)
        | | succCase (m: Nat) : Shape(Nat.succ(m))
        |
        |def keepShape (n: Nat)(s: Shape(n)): Shape(n) := {
        |  match s with
        |  | Shape.zeroCase => s
        |  | Shape.succCase m => s
        |}
        |
        |""".stripMargin

    typecheckDecls(p)
  }
}
