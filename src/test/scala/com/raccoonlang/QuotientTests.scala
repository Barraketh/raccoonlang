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
    case Value.ConstructorHead(n, _, _, _) => SConst(n)
    case Value.VCtor(h, fields, _) =>
      if (fields.isEmpty) SConst(h.name) else SApp(SConst(h.name), fields.toList.map(toShape))
    case Value.VConst(n, _, _)  => SConst(n)
    case Value.VApp(h, args, _, _, _) => SApp(toShape(h), args.toList.map(toShape))
    case other                  => SConst(other.toString)
  }

  private val natZero = SConst("Nat.zero")
  private def natSucc(value: Shape): Shape = SApp(SConst("Nat.succ"), List(value))

  private val natPrelude =
    """
      |def Rel (a: Nat)(b: Nat): Prop := Eq(a, b)
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
          |def sound (a: Nat)(b: Nat)(h: Rel(a, b)): Eq(Nat.succ(a), Nat.succ(b)) := {
          |  match h returning Eq(Nat.succ(a), Nat.succ(b)) with
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
          |def motive (q: Quot(Nat, Rel)): Prop := True
          |
          |{
          |  Quot.inductionOn(
          |    Quot.mk(Nat, Rel, Nat.zero),
          |    motive,
          |    fun (a: Nat): motive(Quot.mk(Nat, Rel, a)) => True.intro
          |  )
          |}
          |""".stripMargin
    )

    assertEquals(toShape(res), SConst("True.intro"))
  }

  test("Quot eliminators reduce on generic Quot.mk in proof types") {
    val res = runProgram(
      natPrelude +
        """
          |def liftMk
          |  (a: Nat)
          |  (f: Nat -> Nat)
          |  (sound: (x: Nat) -> (y: Nat) -> Rel(x, y) -> Eq(f(x), f(y)))
          |  : Eq(Quot.lift(Quot.mk(Nat, Rel, a), Nat, f, sound), f(a)) :=
          |  Eq.refl(f(a))
          |
          |def motive (q: Quot(Nat, Rel)): Prop := True
          |
          |def indMk
          |  (a: Nat)
          |  (mkCase: (x: Nat) -> motive(Quot.mk(Nat, Rel, x)))
          |  : Eq(Quot.ind(Quot.mk(Nat, Rel, a), motive, mkCase), mkCase(a)) :=
          |  Eq.refl(mkCase(a))
          |
          |{
          |  True.intro
          |}
          |""".stripMargin
    )

    assertEquals(toShape(res), SConst("True.intro"))
  }

  test("type-pattern wrapper can recover quotient parameters") {
    val res = runProgram(
      natPrelude +
        """
          |def idSound (a: Nat)(b: Nat)(h: Rel(a, b)): Eq(a, b) := h
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
      case Value.VApp(Value.VConst("Eq", _, _), Vector(left, right), _, _, _) =>
        assert(PrettyPrinter.print(left.tpe).startsWith("Quot(Nat, "))
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
