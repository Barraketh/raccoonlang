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

  // Shape comparison helpers use the ordinary pattern view of constructor arguments.
  sealed trait Shape
  case class SConst(name: String) extends Shape
  case class SApp(head: Shape, args: List[Shape]) extends Shape

  private def toShape(v: Value): Shape = v match {
    case Value.ConstructorHead(n, _, _, _, _) => SConst(n)
    case Value.VCtor(h, storedArgs, _) =>
      val args = storedArgs
      if (args.isEmpty) SConst(h.name) else SApp(SConst(h.name), args.toList.map(toShape))
    case Value.VConst(n, _, _)     => SConst(n)
    case Value.VApp(h, args, _, _) => SApp(toShape(h), args.toList.map(toShape))
    case other                     => SConst(other.toString) // fallback, won't be used in this test
  }

  private val zeroS = SConst("Peano.zero")
  private def succS(s: Shape) = SApp(SConst("Peano.succ"), List(s))

  test("Nats compute") {
    val p = """
              |inductive Peano : Type
              | | zero : Peano
              | | succ (_: Peano) : Peano
              |
              |def add (a: Peano)(b: Peano): Peano decreases structural(b) := {
              |  match b with
              |  | Peano.zero => a
              |  | Peano.succ x => add(Peano.succ(a), x)
              |}
              |
              |{
              |  let a := Peano.succ(Peano.zero)
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

  test("nullary constructor with erased family binder evaluates to constructor view after application") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |inductive Vec (A: Type) indices (n: Peano) : Sort(Level.one)
        | | nil : Vec(A, Peano.zero)
        | | cons (n: Peano) (xs: Vec(A, n)) (x: A): Vec(A, Peano.succ(n))
        |
        |{
        |  Vec.nil(Peano)
        |}
        |""".stripMargin

    InterpreterTests.this.getValue(p) match {
      case Value.VCtor(head, storedArgs, _) =>
        assertEquals(head.name, "Vec.nil")
        assertEquals(storedArgs.length, 0)
        assertEquals(storedArgs, Vector.empty)
      case other =>
        fail(s"expected constructor view, got: $other")
    }
  }

  test("a function-valued neutral match can be applied") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |inductive Bool : Type
        | | true : Bool
        | | false : Bool
        |
        |axiom b : Bool
        |def choose : Peano -> Peano := {
        |  match b returning Peano -> Peano with
        |  | Bool.true => fun (n: Peano): Peano => n
        |  | Bool.false => fun (n: Peano): Peano => n
        |}
        |
        |{ choose(Peano.zero) }
        |""".stripMargin

    getValue(p) match {
      case Value.VApp(_: Value.NeutralThunk, Vector(_), _, None) =>
      case other => fail(s"expected a nested application of the neutral match, got: $other")
    }
  }
}
