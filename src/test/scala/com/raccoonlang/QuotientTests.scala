package com.raccoonlang

import com.raccoonlang.ErrorReporter.Source

class QuotientTests extends munit.FunSuite {
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

  sealed trait Shape
  case class SConst(name: String) extends Shape
  case class SApp(head: Shape, args: List[Shape]) extends Shape

  private def toShape(v: Value): Shape = v match {
    case Value.ConstructorHead(n, _, _, _, _) => SConst(n)
    case Value.VCtor(h, fields, _) =>
      if (fields.isEmpty) SConst(h.name) else SApp(SConst(h.name), fields.toList.map(toShape))
    case Value.VConst(n, _, _)  => SConst(n)
    case Value.VApp(h, args, _) => SApp(toShape(h), args.toList.map(toShape))
    case other                  => SConst(other.toString)
  }

  private val natZero = SConst("Nat.zero")
  private def natSucc(value: Shape): Shape = SApp(SConst("Nat.succ"), List(value))

  private val natPrelude =
    """
      |inductive Nat : Type
      | | zero : Nat
      | | succ (_: Nat) : Nat
      |
      |inductive Eq (A: Sort($u))(x: A)(y: A) : Prop
      | | refl {A: Sort($u)} (x: A) : Eq(A, x, x)
      |
      |inline def Rel (a: Nat)(b: Nat): Prop := Eq(Nat, a, b)
      |""".stripMargin

  test("Quot.mk is a constructor head that stores only the representative") {
    val res = runProgram(
      natPrelude +
        """
          |{
          |  Quot.mk(Nat, Rel, Nat.zero)
          |}
          |""".stripMargin
    )

    res match {
      case Value.VCtor(head, fields, _) =>
        assertEquals(head.name, "Quot.mk")
        assertEquals(fields.map(toShape), Vector(natZero))
      case other =>
        fail(s"Expected Quot.mk constructor value, got $other")
    }
  }

  test("Quot.liftCore reduces on Quot.mk") {
    val res = runProgram(
      natPrelude +
        """
          |{
          |  Quot.liftCore(Nat, Rel, Nat, fun (x: Nat): Nat => Nat.succ(x), Quot.mk(Nat, Rel, Nat.zero))
          |}
          |""".stripMargin
    )

    assertEquals(toShape(res), natSucc(natZero))
  }

  test("Quot.indCore reduces on Quot.mk for Prop motives") {
    val res = runProgram(
      natPrelude +
        """
          |inductive True : Prop
          | | intro : True
          |
          |inline def motive (q: Quot(Nat, Rel)): Prop := True
          |
          |{
          |  Quot.indCore(Nat, Rel, motive, fun (a: Nat): motive(Quot.mk(Nat, Rel, a)) => True.intro, Quot.mk(Nat, Rel, Nat.zero))
          |}
          |""".stripMargin
    )

    assertEquals(toShape(res), SConst("True.intro"))
  }

  test("type-pattern wrapper can recover quotient parameters") {
    val res = runProgram(
      natPrelude +
        """
          |namespace Quot {
          |  inline def lift (q: Quot($A, $r))(B: Sort($v))(f: A -> B)(sound: (a: A) -> (b: A) -> (h: r(a, b)) -> Eq(B, f(a), f(b))): B := Quot.liftCore(A, r, B, f, q)
          |}
          |
          |inline def idSound (a: Nat)(b: Nat)(h: Rel(a, b)): Eq(Nat, a, b) := h
          |
          |{
          |  Quot.lift(Quot.mk(Nat, Rel, Nat.zero), Nat, fun (x: Nat): Nat => x, idSound)
          |}
          |""".stripMargin
    )

    assertEquals(toShape(res), natZero)
  }
}
