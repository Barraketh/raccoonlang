package com.raccoonlang

class NamedArgumentTests extends munit.FunSuite {
  private def runProgram(src: String): Value = {
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value)
        Interpreter.run(core).getOrElse(fail("Program has no body"))
      case err: Failure => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }
  }

  private def typecheckProgram(src: String): Unit = {
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value)
        Interpreter.run(core)
      case err: Failure => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
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

  private val natDecl =
    """
      |inductive Nat : Type
      | | zero : Nat
      | | succ (_: Nat) : Nat
      |
      |""".stripMargin

  private val zeroS = SConst("Nat::zero")
  private def succS(s: Shape) = SApp(SConst("Nat::succ"), List(s))

  test("function application accepts positional, named, mixed, and reordered named args") {
    val p =
      natDecl +
        """
          |inline def second (a: Nat)(b: Nat): Nat := b
          |
          |{
          |  let a := Nat::zero
          |  let b := Nat::succ(Nat::zero)
          |  let p1 := second(a, b)
          |  let p2 := second(a := a, b := b)
          |  let p3 := second(a, b := b)
          |  second(b := p3, a := p1)
          |}
          |""".stripMargin

    assertEquals(toShape(runProgram(p)), succS(zeroS))
  }

  test("named arguments work in type and constructor applications") {
    val p =
      natDecl +
        """
          |inductive Vec (A: Type) indices (n: Nat) : Sort(Level::one)
          | | nil : Vec(A, Nat::zero)
          | | cons (n: Nat) (xs: Vec(A, n)) (x: A): Vec(A, Nat::succ(n))
          |
          |inline def keepNil (v: Vec(n := Nat::zero, A := Nat)): Vec(n := Nat::zero, A := Nat) := v
          |
          |{
          |  keepNil(v := Vec::nil(A := Nat))
          |}
          |""".stripMargin

    assertEquals(toShape(runProgram(p)), SConst("Vec::nil"))
  }

  test("anonymous parameters cannot be called by name") {
    val p =
      natDecl +
        """
          |{
          |  Nat::succ(_ := Nat::zero)
          |}
          |""".stripMargin

    intercept[CannotCallAnonymousArgument] {
      runProgram(p)
    }
  }

  test("positional arguments cannot follow named arguments") {
    val p =
      natDecl +
        """
          |inline def second (a: Nat)(b: Nat): Nat := b
          |
          |{
          |  second(a := Nat::zero, Nat::zero)
          |}
          |""".stripMargin

    intercept[PositionalArgumentAfterNamed] {
      runProgram(p)
    }
  }

  test("named argument errors report unknown, duplicate, and positionally supplied names") {
    val unknown =
      natDecl +
        """
          |inline def second (a: Nat)(b: Nat): Nat := b
          |
          |{
          |  second(c := Nat::zero, b := Nat::zero)
          |}
          |""".stripMargin

    intercept[UnknownNamedArgument] {
      typecheckProgram(unknown)
    }

    val duplicate =
      natDecl +
        """
          |inline def second (a: Nat)(b: Nat): Nat := b
          |
          |{
          |  second(a := Nat::zero, a := Nat::zero)
          |}
          |""".stripMargin

    intercept[DuplicateNamedArgument] {
      typecheckProgram(duplicate)
    }

    val alreadySupplied =
      natDecl +
        """
          |inline def second (a: Nat)(b: Nat): Nat := b
          |
          |{
          |  second(Nat::zero, a := Nat::zero)
          |}
          |""".stripMargin

    intercept[NamedArgumentAlreadySupplied] {
      typecheckProgram(alreadySupplied)
    }
  }

  test("all parameters must still be supplied") {
    val p =
      natDecl +
        """
          |inline def second (a: Nat)(b: Nat): Nat := b
          |
          |{
          |  second(a := Nat::zero)
          |}
          |""".stripMargin

    intercept[ArityMismatch] {
      typecheckProgram(p)
    }
  }
}
