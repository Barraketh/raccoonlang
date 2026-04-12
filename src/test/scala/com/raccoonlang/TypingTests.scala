package com.raccoonlang

class TypingTests extends munit.FunSuite {
  private def typecheckDecls(src: String): Unit = {
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value)
        Interpreter.run(core)
      case err: Failure => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }
  }
  private def runProgram(src: String): Value = {
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value)
        Interpreter.run(core).getOrElse(fail("Program has no body"))
      case err: Failure => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }
  }

  // Erased shape comparison helpers
  sealed trait Shape
  case class SConst(name: String) extends Shape
  case class SApp(head: Shape, args: List[Shape]) extends Shape

  private def toShape(v: Value): Shape = v match {
    case Value.ConstructorHead(n, _, _, _, _) => SConst(n)
    case Value.VCtor(h, fields, _) =>
      if (fields.isEmpty) SConst(h.name) else SApp(SConst(h.name), fields.toList.map(toShape))
    case Value.VConst(n, _, _)  => SConst(n)
    case Value.VApp(h, args, _) => SApp(toShape(h), args.toList.map(toShape))
    case other                  => SConst(other.toString) // fallback
  }

  private val zeroS = SConst("Nat.zero")
  private def succS(s: Shape) = SApp(SConst("Nat.succ"), List(s))

  test("inline id typechecks and reduces") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inline def id (A: Type)(x: A): A := x
        |
        |{
        |  id Nat Nat.zero
        |}
        |""".stripMargin

    val res = runProgram(p)
    assertEquals(toShape(res), zeroS)
  }

  test("inline def: declared return too large (A -> A) expected, value A") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inline def bad (A: Type)(x: A): A -> A := x
        |""".stripMargin

    intercept[RuntimeException] {
      typecheckDecls(p)
    }
  }

  test("let with mismatched ascription fails (constructor vs Nat)") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |{
        |  let s : Nat := Nat.succ
        |  s
        |}
        |""".stripMargin

    intercept[TypeMismatch] {
      runProgram(p)
    }
  }

  test("ascribed function type alpha-equals: (x: Nat)->Nat vs fun (y: Nat) => y") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |{
        |  let f : (x: Nat) -> Nat := fun (y: Nat): Nat => y
        |  f Nat.zero
        |}
        |""".stripMargin

    val res = runProgram(p)
    assertEquals(toShape(res), zeroS)
  }

  test("pred on Nat typechecks and reduces via match") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inline def pred (n: Nat): Nat := {
        |  match n as _ returning Nat with
        |  | Nat.zero => Nat.zero
        |  | Nat.succ x => x
        |}
        |
        |{
        |  pred (Nat.succ Nat.zero)
        |}
        |""".stripMargin

    val res = runProgram(p)
    assertEquals(toShape(res), zeroS)
  }

  test("inline def: declared result Type but branch returns Nat => mismatch") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inline def bad (n: Nat): Type := {
        |  match n as _ returning Nat with
        |  | Nat.zero => Nat.zero
        |  | Nat.succ x => x
        |}
        |""".stripMargin

    intercept[RuntimeException] {
      typecheckDecls(p)
    }
  }

  test("unannotated let with constructor synthesizes type and reduces when applied") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |{
        |  let one := Nat.succ Nat.zero
        |  one
        |}
        |""".stripMargin

    val res = runProgram(p)
    assertEquals(toShape(res), succS(zeroS))
  }

  test("Bad metas") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive Vec (A: Type) indices (n: Nat) : Sort Level.one
        | | nil : Vec A Nat.zero
        | | cons (n: Nat) (xs: Vec A n) (x: A): Vec A (Nat.succ n)
        |
        |inline def badVec (A: Type)(n: Nat)(v: Vec A n): Vec A Nat.zero := v
        |""".stripMargin

    intercept[TypeMismatch] {
      typecheckDecls(p)
    }
  }

  test("reachable nullary ctor branch binds scrutName at instantiated result type") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive Vec (A: Type) indices (n: Nat) : Sort Level.one
        | | nil : Vec A Nat.zero
        | | cons (n: Nat) (xs: Vec A n) (x: A): Vec A (Nat.succ n)
        |
        |inline def keepNil (A: Type)(v: Vec A Nat.zero): Vec A Nat.zero := {
        |  match v as self returning Vec A Nat.zero with
        |  | Vec.nil => self
        |}
        |""".stripMargin

    typecheckDecls(p)
  }

  test("nullary top-level inline def body must match declared type") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inline def bad : Nat := Type
        |""".stripMargin

    intercept[TypeMismatch] {
      typecheckDecls(p)
    }
  }

  test("nullary top-level opaque def body must match declared type") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |def bad : Nat := Type
        |""".stripMargin

    intercept[TypeMismatch] {
      typecheckDecls(p)
    }
  }
}
