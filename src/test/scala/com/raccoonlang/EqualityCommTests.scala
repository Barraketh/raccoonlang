package com.raccoonlang

import com.raccoonlang.ErrorReporter.Source

class EqualityCommTests extends munit.FunSuite {
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

  test("prove add commutativity (a + b = b + a)") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ(_: Peano) : Peano
        |
        |def add (a: Peano)(b: Peano): Peano decreases structural(b) := {
        |  match b with
        |  | Peano.zero => a
        |  | Peano.succ x => add(Peano.succ(a), x)
        |}
        |
        |def trans {A: Type}{x: A}{y: A}{z: A} (p: Eq(A, x, y))(q: Eq(A, y, z)): Eq(A, x, z) := {
        |  match p returning Eq(A, x, z) with
        |  | Eq.refl w => q
        |}
        |
        |def symm {A: Type}{x: A}{y: A} (p: Eq(A, x, y)): Eq(A, y, x) := {
        |  match p returning Eq(A, y, x) with
        |  | Eq.refl w => Eq.refl(w)
        |}
        |
        |def congSucc {a: Peano}{b: Peano} (p: Eq(Peano, a, b)): Eq(Peano, Peano.succ(a), Peano.succ(b)) := {
        |  match p returning Eq(Peano, Peano.succ(a), Peano.succ(b)) with
        |  | Eq.refl x => Eq.refl(Peano.succ(x))
        |}
        |
        |def succAdd (a: Peano)(b: Peano): Eq(Peano, add(Peano.succ(a), b), Peano.succ(add(a, b))) decreases structural(b) := {
        |  match b returning Eq(Peano, add(Peano.succ(a), b), Peano.succ(add(a, b))) with
        |  | Peano.zero => Eq.refl(Peano.succ(a))
        |  | Peano.succ x => succAdd(Peano.succ(a), x)
        |}
        |
        |// add 0 b = b
        |def zeroAdd (b: Peano): Eq(Peano, add(Peano.zero, b), b) decreases structural(b) := {
        |  match b returning Eq(Peano, add(Peano.zero, b), b) with
        |  | Peano.zero => Eq.refl(Peano.zero)
        |  | Peano.succ x => {
        |    let ih := zeroAdd(x)
        |    let step1 := succAdd(Peano.zero, x)
        |    let step2 := congSucc(ih)
        |    trans(step1, step2)
        |  }
        |}
        |
        |// add commutativity: a + b = b + a
        |def addComm (a: Peano)(b: Peano): Eq(Peano, add(a, b), add(b, a)) decreases structural(b) := {
        |  match b returning Eq(Peano, add(a, b), add(b, a)) with
        |  | Peano.zero => symm(zeroAdd(a))
        |  | Peano.succ x => {
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
