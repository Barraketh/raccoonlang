package com.raccoonlang

import com.raccoonlang.ErrorReporter.Source

class EqualityWithNormalizerTests extends munit.FunSuite {
  private def typecheckDecls(src: String): Unit = {
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        try {
          Interpreter.run(core, Prelude.test)
        } catch {
          case t: TypeError =>
            val source = Source(src)
            fail(ErrorReporter.pretty(t, source))
        }
      case err: Failure => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }
  }

  test("Eq proofs via normalizer: comm, zero, assoc") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |stable def add (a: Nat)(b: Nat): Nat decreases structural(b) := {
        |  match b with
        |  | Nat.zero => a
        |  | Nat.succ x => add(Nat.succ(a), x)
        |}
        |
        |def nat_add_normalizer : Normalizer := add_normalizer(Nat.zero, add)
        |
        |// Using the additive normalizer over Nat, these equalities become definitional
        |
        |def addZeroRight (a: Nat): Eq(add(a, Nat.zero), a) := {
        |  use nat_add_normalizer
        |  Eq.refl(add(a, Nat.zero))
        |}
        |
        |def addZeroLeft (a: Nat): Eq(add(Nat.zero, a), a) := {
        |  use nat_add_normalizer
        |  Eq.refl(add(Nat.zero, a))
        |}
        |
        |def addComm (a: Nat)(b: Nat): Eq(add(a, b), add(b, a)) := {
        |  use nat_add_normalizer
        |  Eq.refl(add(a, b))
        |}
        |
        |def addAssoc (x: Nat)(y: Nat)(z: Nat): Eq(add(x, add(y, z)), add(add(x, y), z)) := {
        |  use nat_add_normalizer
        |  Eq.refl(add(x, add(y, z)))
        |}
        |
        |""".stripMargin

    typecheckDecls(p)
  }

  test("Negative: commutativity proof without normalizer fails") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |stable def add (a: Nat)(b: Nat): Nat decreases structural(b) := {
        |  match b with
        |  | Nat.zero => a
        |  | Nat.succ x => add(Nat.succ(a), x)
        |}
        |
        |def addCommNoNorm (a: Nat)(b: Nat): Eq(add(a, b), add(b, a)) := Eq.refl(add(a, b))
        |
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        intercept[TypeMismatch] { Interpreter.run(core, Prelude.test) }
      case err: Failure => fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }

  test("Negative: left identity proof without normalizer fails") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |stable def add (a: Nat)(b: Nat): Nat decreases structural(b) := {
        |  match b with
        |  | Nat.zero => a
        |  | Nat.succ x => add(Nat.succ(a), x)
        |}
        |
        |def addZeroLeftNoNorm (a: Nat): Eq(add(Nat.zero, a), a) := Eq.refl(add(Nat.zero, a))
        |
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        intercept[TypeMismatch] { Interpreter.run(core, Prelude.test) }
      case err: Failure => fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }
}
