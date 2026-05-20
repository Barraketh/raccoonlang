package com.raccoonlang

import com.raccoonlang.ErrorReporter.Source

class EqualityCommTests extends munit.FunSuite {
  private def typecheckDecls(src: String): Unit = {
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value)
        try {
          Interpreter.run(core)
        } catch {
          case t: TypeError =>
            val source = Source(src)
            fail(ErrorReporter.pretty(t, source))
        }
      case err: Failure => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }
  }

  test("prove add commutativity (a + b = b + a)") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ(_: Nat) : Nat
        |
        |stable def add (a: Nat)(b: Nat): Nat decreases structural(b) := {
        |  match b with
        |  | Nat.zero => a
        |  | Nat.succ x => add(Nat.succ(a), x)
        |}
        |
        |def trans (p: Eq($A, $x, $y))(q: Eq(A, y, $z)): Eq(A, x, z) := {
        |  match p returning Eq(A, x, z) with
        |  | Eq.refl w => q
        |}
        |
        |def symm (p: Eq($A, $x, $y)): Eq(A, y, x) := {
        |  match p returning Eq(A, y, x) with
        |  | Eq.refl w => Eq.refl(w)
        |}
        |
        |def congSucc(p: Eq(Nat, $a, $b)): Eq(Nat, Nat.succ(a), Nat.succ(b)) := {
        |  match p returning Eq(Nat, Nat.succ(a), Nat.succ(b)) with
        |  | Eq.refl x => Eq.refl(Nat.succ(x))
        |}
        |
        |def succAdd (a: Nat)(b: Nat): Eq(Nat, add(Nat.succ(a), b), Nat.succ(add(a, b))) decreases structural(b) := {
        |  match b returning Eq(Nat, add(Nat.succ(a), b), Nat.succ(add(a, b))) with
        |  | Nat.zero => Eq.refl(Nat.succ(a))
        |  | Nat.succ x => succAdd(Nat.succ(a), x)
        |}
        |
        |// add 0 b = b
        |def zeroAdd (b: Nat): Eq(Nat, add(Nat.zero, b), b) decreases structural(b) := {
        |  match b returning Eq(Nat, add(Nat.zero, b), b) with
        |  | Nat.zero => Eq.refl(Nat.zero)
        |  | Nat.succ x => {
        |    let ih := zeroAdd(x)
        |    let step1 := succAdd(Nat.zero, x)
        |    let step2 := congSucc(ih)
        |    trans(step1, step2)
        |  }
        |}
        |
        |// add commutativity: a + b = b + a
        |def addComm (a: Nat)(b: Nat): Eq(Nat, add(a, b), add(b, a)) decreases structural(b) := {
        |  match b returning Eq(Nat, add(a, b), add(b, a)) with
        |  | Nat.zero => symm(zeroAdd(a))
        |  | Nat.succ x => {
        |    let ih := addComm(a, x)
        |    let step1 := succAdd(a, x)
        |    let stepCong := congSucc(ih)
        |    let stepSwap := symm(succAdd(x, a))
        |    let tail := trans(stepCong, stepSwap)
        |    trans(step1, tail)
        |  }
        |}
        |
        |""".stripMargin

    typecheckDecls(p)
  }
}
