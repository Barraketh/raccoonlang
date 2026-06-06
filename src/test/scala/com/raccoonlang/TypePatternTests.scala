package com.raccoonlang

import com.raccoonlang.ErrorReporter.Source

class TypePatternTests extends munit.FunSuite {

  private def typecheckDecls(src: String): Unit = {
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        Interpreter.run(core, Prelude.test)
      case err: Failure =>
        fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }
  }

  private def runProgram(src: String): Value = {
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        try {
          Interpreter.run(core, Prelude.test).getOrElse(fail("Program has no body"))
        } catch {
          case t: TypeError =>
            val source = Source(src)
            fail(ErrorReporter.pretty(t, source))
        }
      case err: Failure =>
        fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
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
    case other                  => SConst(other.toString)
  }

  private val zeroS = SConst("Nat.zero")
  private def succS(s: Shape) = SApp(SConst("Nat.succ"), List(s))
  private def boxMkS(s: Shape) = SApp(SConst("Box.mk"), List(s))
  private def vecConsS(tail: Shape, head: Shape) = SApp(SConst("Vec.cons"), List(tail, head))

  test("positive: capture family argument from binder and use it in codomain/body") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive Box (A: Sort($u)) : Sort(u)
        | | mk {A: Sort($u)} (a: A) : Box(A)
        |
        |def unbox (b: Box($A)): A := {
        |  match b returning A with
        |  | Box.mk a => a
        |}
        |
        |{
        |  unbox(Box.mk(Nat, Nat.zero))
        |}
        |""".stripMargin

    val res = runProgram(p)
    assertEquals(toShape(res), zeroS)
  }

  test("positive: capture indexed argument from binder and use it as a term") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive Vec (A: Sort($u)) indices (n: Nat) : Sort(u)
        | | nil {A: Sort($u)} : Vec(A, Nat.zero)
        | | cons {A: Sort($u)} (tail: Vec(A, $n)) (head: A) : Vec(A, Nat.succ(n))
        |
        |def len (v: Vec(Nat, $n)): Nat := n
        |
        |{
        |  len(Vec.cons(Nat, Vec.nil(Nat), Nat.zero))
        |}
        |""".stripMargin

    val res = runProgram(p)
    assertEquals(toShape(res), succS(zeroS))
  }

  test("positive: visible capture from one binder can be reused in later binders and codomain") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive Box (A: Sort($u)) : Sort(u)
        | | mk {A: Sort($u)} (a: A) : Box(A)
        |
        |def repack (b: Box($A))(x: A): Box(A) := Box.mk(A, x)
        |
        |{
        |  repack(Box.mk(Nat, Nat.zero), Nat.succ(Nat.zero))
        |}
        |""".stripMargin

    val res = runProgram(p)
    assertEquals(toShape(res), boxMkS(succS(zeroS)))
  }

  test("positive: later binder can reuse captured index from earlier binder") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive Vec (A: Sort($u)) indices (n: Nat) : Sort(u)
        | | nil {A: Sort($u)} : Vec(A, Nat.zero)
        | | cons {A: Sort($u)} (tail: Vec(A, $n)) (head: A) : Vec(A, Nat.succ(n))
        |
        |def sameLenLeft (v1: Vec(Nat, $n))(v2: Vec(Nat, n)): Nat := n
        |
        |{
        |  sameLenLeft(Vec.nil(Nat), Vec.nil(Nat))
        |}
        |""".stripMargin

    val res = runProgram(p)
    assertEquals(toShape(res), zeroS)
  }

  test("positive: Pi equality through flattened type patterns succeeds under renaming") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive Vec (A: Sort($u)) indices (n: Nat) : Sort(u)
        | | nil {A: Sort($u)} : Vec(A, Nat.zero)
        | | cons {A: Sort($u)} (tail: Vec(A, $n)) (head: A) : Vec(A, Nat.succ(n))
        |
        |{
        |  let f : (v: Vec(Nat, $n)) -> Vec(Nat, n) := fun (w: Vec(Nat, $m)): Vec(Nat, m) => w
        |  f(Vec.cons(Nat, Vec.nil(Nat), Nat.zero))
        |}
        |""".stripMargin

    val res = runProgram(p)
    assertEquals(toShape(res), vecConsS(SConst("Vec.nil"), zeroS))
  }

  test("positive: type patterns work in inductive constructor fields") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive Vec (A: Sort($u)) indices (n: Nat) : Sort(u)
        | | nil {A: Sort($u)} : Vec(A, Nat.zero)
        | | cons {A: Sort($u)} (tail: Vec(A, $n)) (head: A) : Vec(A, Nat.succ(n))
        |
        |inductive PackedHead (A: Type) : Type
        | | mk {A: Type} (v: Vec(A, $n)) (x: A) : PackedHead(A)
        |
        |""".stripMargin

    typecheckDecls(p)
  }

  test("positive: top-level constrained capture exposes type and level") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |def constrainedId (x: $A in Sort($u)): A := x
        |def capturedType (x: $A in Sort($u)): Sort(u) := A
        |
        |{
        |  let z: Nat := constrainedId(Nat.zero)
        |  capturedType(z)
        |}
        |""".stripMargin

    val res = runProgram(p)
    assertEquals(toShape(res), SConst("Nat"))
  }

  test("positive: constrained captures accept cumulative universe upper bounds") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |def acceptHigh (x: $A in Sort(Level.succ(Level.one))): A := x
        |
        |{
        |  acceptHigh(Nat.zero)
        |}
        |""".stripMargin

    val res = runProgram(p)
    assertEquals(toShape(res), zeroS)
  }

  test("positive: transparent type-pattern heads solve captures by unification") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |def Pred (A: Type): Type := (x: A) -> Nat
        |def pickDomain (p: Pred($A))(x: A): A := x
        |
        |{
        |  pickDomain(fun (n: Nat): Nat => n, Nat.zero)
        |}
        |""".stripMargin

    val res = runProgram(p)
    assertEquals(toShape(res), zeroS)
  }

  test("positive: transparent type-pattern heads solve captures in lambda ascriptions") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |def Pred (A: Type): Type := (x: A) -> Nat
        |
        |{
        |  let f : (p: (x: Nat) -> Nat) -> Nat -> Nat := {
        |    fun (p: Pred($A))(x: A): A => x
        |  }
        |  f(fun (n: Nat): Nat => n, Nat.zero)
        |}
        |""".stripMargin

    val res = runProgram(p)
    assertEquals(toShape(res), zeroS)
  }

  test("positive: type-pattern head binders with captures are opened once and solved") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive Vec (A: Sort($u)) indices (n: Nat) : Sort(u)
        | | nil {A: Sort($u)} : Vec(A, Nat.zero)
        | | cons {A: Sort($u)} (tail: Vec(A, $n)) (head: A) : Vec(A, Nat.succ(n))
        |
        |inductive Tag indices (v: Vec(Nat, $n)) : Type
        | | mk (v: Vec(Nat, $n)) : Tag(v)
        |
        |def Head (v: Vec(Nat, $n)): Type := Tag(v)
        |def keepHead (x: Head($v)): Head(v) := x
        |
        |{
        |  keepHead(Tag.mk(Vec.nil(Nat)))
        |}
        |""".stripMargin

    val res = runProgram(p)
    assertEquals(toShape(res), SApp(SConst("Tag.mk"), List(SConst("Vec.nil"))))
  }

  test("negative: bare capture in binder type is rejected") {
    val p =
      """
        |def bad (x: $A): Type := A
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case _: Success[_] => fail("Bare top-level capture parsed successfully")
      case _: Failure    =>
    }
  }

  test("negative: constrained capture syntax is binder-only") {
    val p =
      """
        |def bad : $A in Type := Type
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case _: Success[_] => fail("Constrained capture parsed as an ordinary type")
      case _: Failure    =>
    }
  }

  test("negative: top-level constrained capture enforces constraint") {
    val p =
      """
        |def bad (x: $A in Type): A := x
        |
        |{
        |  bad(Type)
        |}
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        intercept[UnificationFailed] {
          Interpreter.run(core, Prelude.test)
        }
      case err: Failure =>
        fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }

  test("negative: pattern arity mismatch in function binder is rejected") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive Vec (A: Sort($u)) indices (n: Nat) : Sort(u)
        | | nil {A: Sort($u)} : Vec(A, Nat.zero)
        | | cons {A: Sort($u)} (tail: Vec(A, $n)) (head: A) : Vec(A, Nat.succ(n))
        |
        |def bad (v: Vec($A)): Nat := Nat.zero
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        intercept[ArityMismatch] {
          Interpreter.run(core, Prelude.test)
        }
      case err: Failure =>
        fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }

  test("negative: pattern arity mismatch in constructor field is rejected") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive Vec (A: Sort($u)) indices (n: Nat) : Sort(u)
        | | nil {A: Sort($u)} : Vec(A, Nat.zero)
        | | cons {A: Sort($u)} (tail: Vec(A, $n)) (head: A) : Vec(A, Nat.succ(n))
        |
        |inductive Bad : Type
        | | mk (v: Vec($A)) : Bad
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        intercept[ArityMismatch] {
          Interpreter.run(core, Prelude.test)
        }
      case err: Failure =>
        fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }

  test("negative: extra pattern arguments are rejected") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        |
        |inductive Box (A: Type) : Type
        | | mk {A: Type} (a: A) : Box(A)
        |
        |def bad (b: Box(Nat, Nat.zero)): Type := Nat
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        intercept[ArityMismatch] {
          Interpreter.run(core, Prelude.test)
        }
      case err: Failure =>
        fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }

  test("negative: concrete type pattern arguments are checked") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive Box (A: Type) : Type
        | | mk {A: Type} (a: A) : Box(A)
        |
        |def bad (b: Box(Nat.zero)): Type := Nat
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        intercept[TypeMismatch] {
          Interpreter.run(core, Prelude.test)
        }
      case err: Failure =>
        fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }

  test("negative: checked struct type pattern validates concrete family arguments") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        |
        |inductive Bool : Type
        | | tt : Bool
        |
        |struct ChooseLeft (A: Type)(B: Type) indices (Out: Type) : Type
        | | mk {A: Type}{B: Type} (x: A) : ChooseLeft(A, B, A)
        |
        |def bad (w: ChooseLeft(Nat, Bool, Bool)): Type := Type
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        intercept[TypeMismatch] {
          Interpreter.run(core, Prelude.test)
        }
      case err: Failure =>
        fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }

  test("negative: call-site type pattern head mismatch is rejected") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive Box (A: Sort($u)) : Sort(u)
        | | mk {A: Sort($u)} (a: A) : Box(A)
        |
        |def unbox (b: Box($A)): A := {
        |  match b returning A with
        |  | Box.mk a => a
        |}
        |
        |{
        |  unbox(Nat.zero)
        |}
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        intercept[UnificationFailed] {
          Interpreter.run(core, Prelude.test)
        }
      case err: Failure =>
        fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }

  test("negative: type-pattern captures are not visible in the codomain") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive Box (A: Sort($u)) : Sort(u)
        | | mk {A: Sort($u)} (a: A) : Box(A)
        |
        |def bad (b: Box($A)): Sort(u) := A
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        intercept[NotFound] {
          Elaborator.elab(value, Prelude.test)
        }
      case err: Failure =>
        fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }

  test("negative: later binder using captured index rejects mismatched actual argument") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive Vec (A: Sort($u)) indices (n: Nat) : Sort(u)
        | | nil {A: Sort($u)} : Vec(A, Nat.zero)
        | | cons {A: Sort($u)} (tail: Vec(A, $n)) (head: A) : Vec(A, Nat.succ(n))
        |
        |def sameLenLeft (v1: Vec(Nat, $n))(v2: Vec(Nat, n)): Nat := n
        |
        |{
        |  sameLenLeft(Vec.nil(Nat), Vec.cons(Nat, Vec.nil(Nat), Nat.zero))
        |}
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        intercept[TypeMismatch] {
          Interpreter.run(core, Prelude.test)
        }
      case err: Failure =>
        fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }

  test("negative: Pi equality through flattened type patterns rejects changed dependent codomain") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive Vec (A: Sort($u)) indices (n: Nat) : Sort(u)
        | | nil {A: Sort($u)} : Vec(A, Nat.zero)
        | | cons {A: Sort($u)} (tail: Vec(A, $n)) (head: A) : Vec(A, Nat.succ(n))
        |
        |{
        |  let f : (v: Vec(Nat, $n)) -> Vec(Nat, n) := {
        |    fun (w: Vec(Nat, $m)): Vec(Nat, Nat.succ(m)) => Vec.cons(Nat, w, Nat.zero)
        |  }
        |  f
        |}
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        intercept[TypeMismatch] {
          Interpreter.run(core, Prelude.test)
        }
      case err: Failure =>
        fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }
}
