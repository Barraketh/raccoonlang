package com.raccoonlang

import com.raccoonlang.ErrorReporter.Source

// Temporary probes for the ValueEquivalence review.
class UnifyProbeTest extends munit.FunSuite {
  private def runProgram(src: String): Value = {
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value)
        try {
          Interpreter.run(core).getOrElse(fail("Program has no body"))
        } catch {
          case t: TypeError => fail(ErrorReporter.pretty(t, Source(src)))
        }
      case err: Failure =>
        fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }
  }

  test("PROBE A (fixed by isPropValuedType): predicates are no longer proof-irrelevant") {
    // (n: Nat) -> Prop now lives in Type, so trueP/falseP are data and refl is rejected.
    // Permanent regression coverage lives in PropTests ("predicates are not proof-irrelevant").
    val src =
      """
        |def trueP (n: Nat): Prop := True
        |def falseP (n: Nat): Prop := False
        |
        |def bad : Eq((n: Nat) -> Prop, trueP, falseP) := Eq.refl(trueP)
        |
        |def boom : False := Eq.mp(congrFun(Nat, Prop, trueP, falseP, bad, Nat.zero), True.intro)
        |
        |{
        |  boom
        |}
        |""".stripMargin
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value)
        intercept[TypeMismatch] { Interpreter.run(core) }
      case err: Failure =>
        fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }
  }

  test("PROBE B: inductive family head injectivity via match refinement") {
    val res = runProgram(
      """
        |inductive I (P: Type -> Type) : Type
        | | mk : I(P)
        |
        |def injI (P: Type -> Type)(Q: Type -> Type)(h: Eq(Type, I(P), I(Q))): Eq((T: Type) -> Type, P, Q) := {
        |  match h returning Eq((T: Type) -> Type, P, Q) with
        |  | Eq.refl z => Eq.refl(P)
        |}
        |
        |{
        |  Bool.true
        |}
        |""".stripMargin
    )
    println(s"PRINCIPLE (B): family injectivity lemma typechecks, value = $res")
  }

  test("PROBE C (fixed by UnifyMode.Invert): opaque function injectivity is rejected") {
    // Permanent regression coverage lives in MatchRefinementTests ("opaque function
    // applications do not refine their arguments").
    val src =
      """
        |opaque def f (n: Nat): Nat := n
        |
        |def injF (x: Nat)(y: Nat)(h: Eq(Nat, f(x), f(y))): Eq(Nat, x, y) := {
        |  match h returning Eq(Nat, x, y) with
        |  | Eq.refl z => Eq.refl(x)
        |}
        |
        |{
        |  Bool.true
        |}
        |""".stripMargin
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value)
        intercept[TypeMismatch] { Interpreter.run(core) }
      case err: Failure =>
        fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }
  }
}
