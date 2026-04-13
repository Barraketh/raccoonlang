package com.raccoonlang

import com.raccoonlang.ErrorReporter.Source

class ProjectionTests extends munit.FunSuite {

  private def typecheckDecls(src: String): Unit = {
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value)
        try {
          Interpreter.run(core)
        } catch {
          case t: TypeError =>
            val source = Source(src)
            fail(ErrorReporter.pretty(t, source))
        }
      case err: Failure =>
        fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }
  }

  private def runProgram(src: String): Value = {
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value)
        try {
          Interpreter.run(core).getOrElse(fail("Program has no body"))
        } catch {
          case t: TypeError =>
            val source = Source(src)
            fail(ErrorReporter.pretty(t, source))
        }
      case err: Failure =>
        fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }
  }

  // Simple erased shapes for results
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

  private val zeroS = SConst("Nat::zero")
  private def succS(s: Shape) = SApp(SConst("Nat::succ"), List(s))

  test("non-dependent projections: Pair.fst and Pair.snd") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |struct Pair (A: Type)(B: Type) : Type
        | | mk (fst: A)(snd: B) : Pair A B
        |
        |inline def first (p: Pair $A1 $B1): A1 := p.fst
        |inline def second (p: Pair $A2 $B2): B2 := p.snd
        |
        |{
        |  let p : Pair Nat Nat := Pair::mk Nat Nat Nat::zero (Nat::succ Nat::zero)
        |  first p
        |}
        |""".stripMargin

    val res = runProgram(p)
    assertEquals(toShape(res), zeroS)
  }

  test("dependent projections on indices: WrapIdx.x") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive Vec (A: Type) indices (n: Nat) : Type
        | | nil : Vec A Nat::zero
        | | cons (tail: Vec A $n) (head: A) : Vec A (Nat::succ n)
        |
        |struct WrapIdx (A: Type)(n: Nat) : Type
        | | mk (x: Vec A n) : WrapIdx A n
        |
        |inline def get (A: Type)(n: Nat)(w: WrapIdx A n): Vec A n := w.x
        |
        |{
        |  let v : Vec Nat Nat::zero := Vec::nil Nat
        |  let w : WrapIdx Nat Nat::zero := WrapIdx::mk Nat Nat::zero v
        |  get Nat Nat::zero w
        |}
        |""".stripMargin

    val res = runProgram(p)
    assertEquals(toShape(res), SConst("Vec::nil"))
  }

  test("typecheck: dependent projection works in types with indices") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive Vec (A: Type) indices (n: Nat) : Type
        | | nil : Vec A Nat::zero
        | | cons (tail: Vec A $n) (head: A) : Vec A (Nat::succ n)
        |
        |struct WrapIdx (A: Type)(n: Nat) : Type
        | | mk (x: Vec A n) : WrapIdx A n
        |
        |def useGet (A: Type)(n: Nat)(w: WrapIdx A n): Vec A n := w.x
        |""".stripMargin

    typecheckDecls(p)
  }

  test("typecheck: dependent projection works with type patterns") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive Vec (A: Type) indices (n: Nat) : Type
        | | nil : Vec A Nat::zero
        | | cons (tail: Vec A $n) (head: A) : Vec A (Nat::succ n)
        |
        |struct WrapIdx (A: Type)(n: Nat): Type
        | | mk (x: Vec A n) : WrapIdx A n
        |
        |def useGet (w: WrapIdx $A $n): Vec A n := w.x
        |""".stripMargin

    typecheckDecls(p)
  }

  test("regression: projection from opaque struct-valued def stays neutral") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |struct Pair (A: Type)(B: Type) : Type
        | | mk (fst: A)(snd: B) : Pair A B
        |
        |// Opaque on purpose
        |def mkPair (a: Nat)(b: Nat): Pair Nat Nat := Pair::mk Nat Nat a b
        |
        |def firstOpaque (a: Nat)(b: Nat): Nat := {
        |  let p := mkPair a b
        |  p.fst
        |}
        |""".stripMargin

    typecheckDecls(p)
  }

  test("regression: projection in type position from opaque struct constant stays neutral") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |struct PairU (A: Sort $u1)(B: Sort $u2) : Sort (Level::max u1 u2)
        | | mk (fst: A)(snd: B) : PairU A B
        |
        |// Opaque on purpose
        |def F : PairU Type Type := PairU::mk Type Type Nat Nat
        |
        |def idF (x: F.fst): F.fst := x
        |""".stripMargin

    typecheckDecls(p)
  }

  test("regression: projection from stuck match returning a struct stays neutral") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |struct Pair (A: Type)(B: Type) : Type
        | | mk (fst: A)(snd: B) : Pair A B
        |
        |// Opaque on purpose
        |def step (n: Nat): Nat := n
        |
        |inline def choose (n: Nat): Pair Nat Nat := {
        |  match step n as m returning Pair Nat Nat with
        |  | Nat::zero => Pair::mk Nat Nat Nat::zero Nat::zero
        |  | Nat::succ k => Pair::mk Nat Nat (Nat::succ k) k
        |}
        |
        |def fstChoose (n: Nat): Nat := {
        |  let p := choose n
        |  p.fst
        |}
        |""".stripMargin

    typecheckDecls(p)
  }

  test("invalid: struct with indices is rejected") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |struct IndexedWrap (A: Type) indices (n: Nat) : Type
        | | mk (x: A) : IndexedWrap A n
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value)
        intercept[InvalidStruct] { Interpreter.run(core) }
      case err: Failure =>
        fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }

  test("optional regression: repeated projection of captured field type is stable") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive Vec (A: Type) indices (n: Nat) : Type
        | | nil : Vec A Nat::zero
        | | cons (tail: Vec A $n) (head: A) : Vec A (Nat::succ n)
        |
        |struct HiddenVec (A: Type) : Type
        | | mk (v: Vec A $n) : HiddenVec A
        |
        |inline def sameLenLeft (v1: Vec Nat $n)(v2: Vec Nat n): Nat := n
        |
        |def lenTwice (h: HiddenVec Nat): Nat := sameLenLeft h.v h.v
        |""".stripMargin

    typecheckDecls(p)
  }

  test("negative: selecting from non-struct Prop family throws") {
    val p =
      """
        |inductive And (P: Prop)(Q: Prop) : Prop
        | | intro (p: P)(q: Q) : And P Q
        |
        |inline def bad (P: Prop)(Q: Prop)(h: And P Q): P := h.fst
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value)
        intercept[NotAStruct] { Interpreter.run(core) }
      case err: Failure => fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }

  test("negative: selecting from non-struct multi-ctor inductive throws") {
    val p =
      """
        |inductive Or (A: Type)(B: Type) : Type
        | | inl (a: A) : Or A B
        | | inr (b: B) : Or A B
        |
        |inline def bad (A: Type)(B: Type)(h: Or A B): A := h.fst
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value)
        intercept[NotAStruct] { Interpreter.run(core) }
      case err: Failure => fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }

  test("negative: unknown field name on struct throws NotFound") {
    val p =
      """
        |struct Pair (A: Type)(B: Type) : Type
        | | mk (fst: A)(snd: B) : Pair A B
        |
        |inline def bad (A: Type)(B: Type)(p: Pair A B): A := p.foo
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value)
        intercept[NotFound] { Interpreter.run(core) }
      case err: Failure => fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }

  test("invalid: struct with multiple constructors is rejected") {
    val p =
      """
        |struct Bad (A: Type) : Type
        | | mk1 (a: A) : Bad A
        | | mk2 (a: A) : Bad A
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) => fail("Struct parsed successfully with multiple params")
      case err: Failure         =>
    }
  }

  test("invalid: struct living in Prop is rejected") {
    val p =
      """
        |struct And (P: Prop)(Q: Prop) : Prop
        | | intro (p: P)(q: Q) : And P Q
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value)
        intercept[InvalidStruct] { Interpreter.run(core) }
      case err: Failure => fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }

  test("invalid: struct with '_' anonymous field is rejected") {
    val p =
      """
        |struct Bad (A: Type) : Type
        | | mk (_: A) : Bad A
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value)
        intercept[InvalidStruct] { Interpreter.run(core) }
      case err: Failure => fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }

}
