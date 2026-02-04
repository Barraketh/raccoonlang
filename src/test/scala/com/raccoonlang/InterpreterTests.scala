package com.raccoonlang

import com.raccoonlang.Interpreter.{ConstType, ConstructorHead, Value}

class InterpreterTests extends munit.FunSuite {
  private def getValue(s: String): Interpreter.Value = {
    LanguageParser.parseProgram(s) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value)
        Interpreter.run(core)
      case err: Failure => fail(s"Failed to parse: $err, ${s.substring(err.curIdx)}")
    }

  }

  // Erased shape comparison helpers
  sealed trait Shape
  case class SConst(name: String, ct: ConstType) extends Shape
  case class SApp(head: Shape, args: Vector[Shape]) extends Shape

  private def toShape(v: Value): Shape = v match {
    case Interpreter.VConst(n, ct, _)         => SConst(n, ct)
    case Interpreter.VApp(h, args, _)         => SApp(toShape(h), args.map(toShape))
    case other                                => SConst(other.toString, ConstructorHead) // fallback, won't be used in this test
  }

  private val zeroS = SConst("Nat.zero", ConstructorHead)
  private def succS(s: Shape) = SApp(SConst("Nat.succ", ConstructorHead), Vector(s))

  test("Nats compute") {
    val p = """
              |inductive Nat : Type
              | | zero : Nat
              | | succ : Nat -> Nat
              |
              |inline def add (a: Nat)(b: Nat): Nat :=
              |  match b as _ returning Nat with
              |  | Nat.zero => a
              |  | Nat.succ x => add (Nat.succ a) x
              |
              |do {
              |  let a := Nat.succ Nat.zero
              |  add a a
              |}
              |""".stripMargin

    val res = getValue(p)
    assertEquals(toShape(res), succS(succS(zeroS)))

  }
}
