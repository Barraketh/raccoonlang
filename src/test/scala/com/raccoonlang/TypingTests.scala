package com.raccoonlang

class TypingTests extends munit.FunSuite {
  private def typecheckDecls(src: String): Unit = {
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        Interpreter.run(core, Prelude.test)
      case err: Failure => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }
  }
  private def runProgram(src: String): Value = {
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        Interpreter.run(core, Prelude.test).getOrElse(fail("Program has no body"))
      case err: Failure => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }
  }

  // Erased shape comparison helpers
  sealed trait Shape
  case class SConst(name: String) extends Shape
  case class SApp(head: Shape, args: List[Shape]) extends Shape

  private def toShape(v: Value): Shape = v match {
    case Value.ConstructorHead(n, _, _, _, _) => SConst(n)
    case ctor @ Value.VCtor(h, _, _) =>
      val fields = ctor.fields
      if (fields.isEmpty) SConst(h.name) else SApp(SConst(h.name), fields.toList.map(toShape))
    case Value.VConst(n, _, _)  => SConst(n)
    case Value.VApp(h, args, _) => SApp(toShape(h), args.toList.map(toShape))
    case other                  => SConst(other.toString) // fallback
  }

  private val zeroS = SConst("Nat.zero")
  private def succS(s: Shape) = SApp(SConst("Nat.succ"), List(s))

  test("def typechecks and reduces by default") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |def id (A: Type)(x: A): A := x
        |
        |{
        |  id(Nat, Nat.zero)
        |}
        |""".stripMargin

    val res = runProgram(p)
    assertEquals(toShape(res), zeroS)
  }

  test("def: declared return too large (A -> A) expected, value A") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |def bad (A: Type)(x: A): A -> A := x
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
        |  f(Nat.zero)
        |}
        |""".stripMargin

    val res = runProgram(p)
    assertEquals(toShape(res), zeroS)
  }

  test("nested lambda captures outer local slot") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |{
        |  let k := fun (x: Nat): ((y: Nat) -> Nat) => fun (y: Nat): Nat => x
        |  let h := k(Nat.zero)
        |  h(Nat.succ(Nat.zero))
        |}
        |""".stripMargin

    val res = runProgram(p)
    assertEquals(toShape(res), zeroS)
  }

  test("later let shadowing allocates a new local slot") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |{
        |  let x := Nat.zero
        |  let f := fun (y: Nat): Nat => x
        |  let x := Nat.succ(Nat.zero)
        |  f(x)
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
        |def pred (n: Nat): Nat := {
        |  match n with
        |  | Nat.zero => Nat.zero
        |  | Nat.succ x => x
        |}
        |
        |{
        |  pred(Nat.succ(Nat.zero))
        |}
        |""".stripMargin

    val res = runProgram(p)
    assertEquals(toShape(res), zeroS)
  }

  test("def: declared result Type but branch returns Nat => mismatch") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |def bad (n: Nat): Type := {
        |  match n with
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
        |  let one := Nat.succ(Nat.zero)
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
        |inductive Vec (A: Type) indices (n: Nat) : Sort(Level.one)
        | | nil {A: Type} : Vec(A, Nat.zero)
        | | cons {A: Type} (n: Nat) (xs: Vec(A, n)) (x: A): Vec(A, Nat.succ(n))
        |
        |def badVec (A: Type)(n: Nat)(v: Vec(A, n)): Vec(A, Nat.zero) := v
        |""".stripMargin

    intercept[TypeMismatch] {
      typecheckDecls(p)
    }
  }

  test("reachable nullary ctor branch refines scrutinee at instantiated result type") {
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
        |def keepNil (A: Type)(v: Vec(A, Nat.zero)): Vec(A, Nat.zero) := {
        |  match v with
        |  | Vec.nil => v
        |}
        |""".stripMargin

    typecheckDecls(p)
  }

  test("definition body can start on next line and wrap applications") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |def apply
        |  (f:
        |    Nat ->
        |    Nat
        |  )
        |  (x: Nat)
        |  : Nat :=
        |  f(
        |    x
        |  )
        |
        |def useApply : Nat :=
        |  apply(
        |    fun (n: Nat): Nat =>
        |      n,
        |    Nat.zero
        |  )
        |
        |{
        |  useApply
        |}
        |""".stripMargin

    val res = runProgram(p)
    assertEquals(toShape(res), zeroS)
  }

  test("nullary top-level def body must match declared type") {
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

  test("nullary top-level opaque def body must match declared type") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |opaque def bad : Nat := Type
        |""".stripMargin

    intercept[TypeMismatch] {
      typecheckDecls(p)
    }
  }
}
