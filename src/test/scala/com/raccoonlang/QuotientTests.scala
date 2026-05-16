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

  test("Quot.lift reduces on Quot.mk") {
    val res = runProgram(
      natPrelude +
        """
          |inline def sound (a: Nat)(b: Nat)(h: Rel(a, b)): Eq(Nat, Nat.succ(a), Nat.succ(b)) := {
          |  match h returning Eq(Nat, Nat.succ(a), Nat.succ(b)) with
          |  | Eq.refl x => Eq.refl(Nat.succ(x))
          |}
          |
          |{
          |  Quot.lift(Quot.mk(Nat, Rel, Nat.zero), Nat, fun (x: Nat): Nat => Nat.succ(x), sound)
          |}
          |""".stripMargin
    )

    assertEquals(toShape(res), natSucc(natZero))
  }

  test("Quot.ind reduces on Quot.mk for Prop motives") {
    val res = runProgram(
      natPrelude +
        """
          |inductive True : Prop
          | | intro : True
          |
          |inline def motive (q: Quot(Nat, Rel)): Prop := True
          |
          |{
          |  Quot.ind(Quot.mk(Nat, Rel, Nat.zero), motive, fun (a: Nat): motive(Quot.mk(Nat, Rel, a)) => True.intro)
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
          |  inline def liftOn (q: Quot($A, $r))(B: Sort($v))(f: A -> B)(sound: (a: A) -> (b: A) -> (h: r(a, b)) -> Eq(B, f(a), f(b))): B := Quot.lift(q, B, f, sound)
          |}
          |
          |inline def idSound (a: Nat)(b: Nat)(h: Rel(a, b)): Eq(Nat, a, b) := h
          |
          |{
          |  Quot.liftOn(Quot.mk(Nat, Rel, Nat.zero), Nat, fun (x: Nat): Nat => x, idSound)
          |}
          |""".stripMargin
    )

    assertEquals(toShape(res), natZero)
  }

  test("Quot.sound proves related representatives equal in the quotient") {
    val res = runProgram(
      natPrelude +
        """
          |{
          |  Quot.sound(Nat.zero, Nat.zero, Rel, Eq.refl(Nat.zero))
          |}
          |""".stripMargin
    )

    res.tpe match {
      case Value.VApp(Value.VConst("Eq", _, _), Vector(quotTy, left, right), _) =>
        assert(PrettyPrinter.print(quotTy).startsWith("Quot(Nat, "))
        assertEquals(toShape(left), SApp(SConst("Quot.mk"), List(natZero)))
        assertEquals(toShape(right), SApp(SConst("Quot.mk"), List(natZero)))
      case other =>
        fail(s"Expected quotient equality proof, got $other")
    }
  }

  test("unknown builtin declaration is rejected") {
    val src =
      """
        |def bogus : Type := builtin
        |""".stripMargin

    val err = intercept[WTF] {
      LanguageParser.parseProgram(src) match {
        case Success(value, _, _) =>
          Interpreter.run(Elaborator.elab(value))
        case parseErr: Failure =>
          fail(s"Failed to parse: $parseErr, ${src.substring(parseErr.curIdx)}")
      }
    }

    assertEquals(err.msg, "Unknown builtin bogus")
  }
}
