package com.raccoonlang

class InductiveCheckTest extends munit.FunSuite {

  private def elabAndTypecheck(src: String): Unit = {
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value)
        Interpreter.run(core)
      case err: Failure => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }
  }

  test("Inductive type must be a Sort (no Pi): inductive Bad : Nat") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive Bad : Nat
        | | mk : Bad
        |
        |""".stripMargin

    intercept[InductiveTypeNotASort] { elabAndTypecheck(p) }
  }

  test("Inductive type must be a Sort (Pi case): inductive Bad(A: Type) : A") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive Bad(A: Type) : A
        | | mk(A: Type): Bad(A)
        |
        |""".stripMargin

    intercept[InductiveTypeNotASort] { elabAndTypecheck(p) }
  }

  test("Constructor result must be inductive head: ctor returns Nat, not Bad") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive Bad : Type
        | | mk : Nat
        |
        |""".stripMargin

    intercept[InvalidConstructorResult] { elabAndTypecheck(p) }
  }

  test("Field universe too large: (A: Sort Level.one) in Type inductive") {
    val p =
      """
        |inductive Small : Type
        | | mk (A: Sort(Level::one)): Small
        |
        |""".stripMargin

    intercept[InductiveUniverseTooSmall] { elabAndTypecheck(p) }
  }

  test("Non-strict positivity: function-typed field with Bad in domain (f: Bad -> Bad)") {
    val p =
      """
        |inductive Bad : Type
        | | con (f: Bad -> Bad): Bad
        |
        |""".stripMargin

    intercept[NonStrictlyPositive] { elabAndTypecheck(p) }
  }

  test("Non-strict positivity: aligned universes under other constructor F args (Wrap u (Bad u))") {
    val p =
      """
        |def Wrap(A: Sort(Level::zero)): Sort(Level::zero) := A
        |
        |inductive Bad : Sort(Level::zero)
        | | con(x: Wrap(Bad)): Bad
        |
        |""".stripMargin

    intercept[NonStrictlyPositive] { elabAndTypecheck(p) }
  }

  test("Constructor result parameter prefix must match repeated params") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive Vec (A: Type) indices (n: Nat) : Sort(Level::one)
        | | bad : (A: Type) -> (n: Nat) -> Vec(Nat, Nat::zero)
        |
        |""".stripMargin

    intercept[InvalidConstructorResult] { elabAndTypecheck(p) }
  }

  test("Constructor result must have full family arity (params + indices)") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive Vec (A: Type) indices (n: Nat) : Sort(Level::one)
        | | bad : (A: Type) -> (n: Nat) -> Vec(A)
        |
        |""".stripMargin

    intercept[ArityMismatch] { elabAndTypecheck(p) }
  }

  test("Inductive params must be uniform") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive Vec (A: Type) indices (n: Nat) : Sort(Level::one)
        | | bad (B: Type)(n: Nat): Vec(B, n)
        |
        |""".stripMargin

    intercept[InvalidConstructorResult] { elabAndTypecheck(p) }
  }
}
