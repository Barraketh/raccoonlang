package com.raccoonlang

class InterpreterTests extends munit.FunSuite {
  private def getValue(s: String): Value = {
    LanguageParser.parseProgram(s) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        Interpreter.run(core, Prelude.test).getOrElse(fail("Program has no body"))
      case err: Failure => fail(s"Failed to parse: $err, ${s.substring(err.curIdx)}")
    }

  }

  // Erased shape comparison helpers
  sealed trait Shape
  case class SConst(name: String) extends Shape
  case class SApp(head: Shape, args: List[Shape]) extends Shape

  private def toShape(v: Value): Shape = v match {
    case Value.ConstructorHead(n, _, _, _) => SConst(n)
    case Value.VCtor(h, fields, _) =>
      if (fields.isEmpty) SConst(h.name) else SApp(SConst(h.name), fields.toList.map(toShape))
    case Value.VConst(n, _, _)  => SConst(n)
    case Value.VApp(h, args, _, _) => SApp(toShape(h), args.toList.map(toShape))
    case other                  => SConst(other.toString) // fallback, won't be used in this test
  }

  private val zeroS = SConst("Nat.zero")
  private def succS(s: Shape) = SApp(SConst("Nat.succ"), List(s))

  test("Nats compute") {
    val p = """
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
              |{
              |  let a := Nat.succ(Nat.zero)
              |  add(a, a)
              |}
              |""".stripMargin

    val res = getValue(p)
    assertEquals(toShape(res), succS(succS(zeroS)))

  }

  test("zero-arity constructor identifier evaluates to constructor view") {
    val p =
      """
        |inductive Bool : Type
        | | true : Bool
        | | false : Bool
        |
        |{
        |  Bool.true
        |}
        |""".stripMargin

    InterpreterTests.this.getValue(p) match {
      case Value.VCtor(head, fields, _) =>
        assertEquals(head.name, "Bool.true")
        assertEquals(fields, Vector.empty)
      case other =>
        fail(s"expected constructor view, got: $other")
    }
  }

  test("nullary constructor with erased binder evaluates to constructor view after erased application") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive Vec (A: Type) indices (n: Nat) : Sort(Level.one)
        | | nil {A: Type} : Vec(A, Nat.zero)
        | | cons {A: Type} (n: Nat) (xs: Vec(A, n)) (x: A): Vec(A, Nat.succ(n))
        |
        |{
        |  Vec.nil(Nat)
        |}
        |""".stripMargin

    InterpreterTests.this.getValue(p) match {
      case Value.VCtor(head, fields, _) =>
        assertEquals(head.name, "Vec.nil")
        assertEquals(fields, Vector.empty)
      case other =>
        fail(s"expected constructor view, got: $other")
    }
  }
}
