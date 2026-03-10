package com.raccoonlang

import com.raccoonlang.Interpreter.{ConstType, ConstructorHead, Value}

class UniversePropTests extends munit.FunSuite {
  private def runProgram(src: String): Interpreter.Value = {
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value)
        Interpreter.run(core)
      case err: Failure => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }
  }

  // Erased shape comparison helpers
  sealed trait Shape
  case class SConst(name: String, ct: ConstType) extends Shape
  case class SApp(head: Shape, args: List[Shape]) extends Shape

  private def toShape(v: Value): Shape = v match {
    case Interpreter.VConst(n, ct, _) => SConst(n, ct)
    case Interpreter.VApp(h, args, _) => SApp(toShape(h), args.toList.map(toShape))
    case other                        => SConst(other.toString, ConstructorHead) // fallback
  }

  private val zeroS = SConst("Nat.zero", ConstructorHead)

  test("Type cumulativity: Type 0 fits Type 1 in polymorphic function") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ : Nat -> Nat
        |
        |inline def lift (A: Type 1)(x: A): A := x
        |
        |do { lift Nat Nat.zero }
        |""".stripMargin

    val res = runProgram(p)
    assertEquals(toShape(res), zeroS)
  }

  test("Prop sort: propositions typecheck with inductive returning Prop") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ : Nat -> Nat
        |
        |inductive True : Prop
        | | intro : True
        |
        |inductive Eq(A: Type)(a: A)(b: A): Prop
        | | refl(A: Type)(x: A) : Eq A x x
        |
        |do { Eq.refl Nat Nat.zero }
        |""".stripMargin

    runProgram(p)
  }

  test("No Prop-to-Type coercion: cannot treat proof as Type") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ : Nat -> Nat
        |
        |inductive Eq(A: Type)(a: A)(b: A): Prop
        | | refl(A: Type)(x: A) : Eq A x x
        |
        |do {
        |  let p := Eq.refl Nat Nat.zero
        |  let bad : Type := p
        |  bad
        |}
        |""".stripMargin

    intercept[TypeMismatch] {
      runProgram(p)
    }
  }

  test("Pi into Prop stays Prop (impredicative)") {
    val p =
      """
        |inductive True : Prop
        | | intro : True
        |
        |inline def imp (P: Prop)(x: P): P := x
        |do { imp True True.intro }
        |""".stripMargin

    val res = runProgram(p)
  }

  test("Type and Prop cannot be shadowed (parse failure)") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ : Nat -> Nat
        |
        |do { let Type := Nat.zero; Type }
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case _: Success[_] => fail("Expected parse failure when shadowing Type keyword")
      case _: Failure    => ()
    }
  }
}
