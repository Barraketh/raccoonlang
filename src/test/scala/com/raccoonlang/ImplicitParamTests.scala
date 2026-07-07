package com.raccoonlang

import com.raccoonlang.ErrorReporter.Source

class ImplicitParamTests extends munit.FunSuite {

  private def typecheckDecls(src: String): Unit =
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        try Interpreter.run(core, Prelude.test)
        catch {
          case t: TypeError => fail(ErrorReporter.pretty(t, Source(src)))
        }
      case err: Failure =>
        fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }

  private def typeError[T <: TypeError](src: String)(implicit ct: reflect.ClassTag[T]): T =
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        intercept[T] { Interpreter.run(core, Prelude.test) }
      case err: Failure =>
        fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }

  private def runProgram(src: String): Value =
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        try Interpreter.run(core, Prelude.test).getOrElse(fail("Program has no body"))
        catch {
          case t: TypeError => fail(ErrorReporter.pretty(t, Source(src)))
        }
      case err: Failure =>
        fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }

  sealed trait Shape
  case class SConst(name: String) extends Shape
  case class SApp(head: Shape, args: List[Shape]) extends Shape

  private def toShape(v: Value): Shape = v match {
    case Value.ConstructorHead(n, _, _, _) => SConst(n)
    case Value.VCtor(h, storedArgs, _) =>
      val args = Value.constructorPatternArgs(h, storedArgs)
      if (args.isEmpty) SConst(h.name) else SApp(SConst(h.name), args.toList.map(toShape))
    case Value.VConst(n, _, _)     => SConst(n)
    case Value.VApp(h, args, _, _) => SApp(toShape(h), args.toList.map(toShape))
    case other                     => SConst(other.toString)
  }

  private val zeroS = SConst("Nat.zero")
  private def succS(s: Shape) = SApp(SConst("Nat.succ"), List(s))

  test("implicit family argument can be used in codomain and body") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive Box {u: Level}(A: Sort(u)) : Sort(u)
        | | mk (a: A) : Box(A)
        |
        |def unbox {u: Level}{A: Sort(u)} (b: Box(A)): A := {
        |  match b returning A with
        |  | Box.mk a => a
        |}
        |
        |{
        |  unbox(Box.mk(Nat, Nat.zero))
        |}
        |""".stripMargin

    assertEquals(toShape(runProgram(p)), zeroS)
  }

  test("implicit index can be used as an ordinary term") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive Vec {u: Level}(A: Sort(u)) indices (n: Nat) : Sort(Level.max(Level.one, u))
        | | nil : Vec(A, Nat.zero)
        | | cons {n: Nat} (tail: Vec(A, n)) (head: A) : Vec(A, Nat.succ(n))
        |
        |def len {n: Nat} (v: Vec(Nat, n)): Nat := n
        |
        |{
        |  len(Vec.cons(Nat, Vec.nil(Nat), Nat.zero))
        |}
        |""".stripMargin

    assertEquals(toShape(runProgram(p)), succS(zeroS))
  }

  test("explicit hidden arguments can be supplied positionally") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |def id {A: Type} (x: A): A := x
        |
        |{
        |  id(Nat, Nat.succ(Nat.zero))
        |}
        |""".stripMargin

    assertEquals(toShape(runProgram(p)), succS(zeroS))
  }

  test("implicit binders must be a prefix of their telescope") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        |
        |axiom bad : Nat -> {A: Type} -> A
        |""".stripMargin

    typeError[NonLeadingImplicitParam](p)
  }

  test("ordinary hidden constructor binders cannot stand in for family params") {
    val p =
      """
        |inductive Bad (A: Type) : Type
        | | mk {B: Type} : Bad(B)
        |""".stripMargin

    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        intercept[NonUniformInductiveParam] { Interpreter.run(core, Prelude.test) }
      case err: Failure =>
        fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }

  test("constructor implicit binders may include indices after family params") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive Vec (A: Type) indices (n: Nat) : Type
        | | nil : Vec(A, Nat.zero)
        | | cons {n: Nat} (tail: Vec(A, n)) (head: A) : Vec(A, Nat.succ(n))
        |""".stripMargin

    typecheckDecls(p)
  }

  test("match patterns bind implicit constructor fields") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        |
        |inductive Pack : Sort(Level.succ(Level.one))
        | | mk {A: Type} (x: A) : Pack
        |
        |def carrier (p: Pack): Type := {
        |  match p returning Type with
        |  | Pack.mk A x => A
        |}
        |
        |{
        |  carrier(Pack.mk(Nat.zero))
        |}
        |""".stripMargin

    assertEquals(toShape(runProgram(p)), SConst("Nat"))
  }

  test("annotated let supplies expected type for omitted implicit result") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |axiom arbitrary : {A: Type} -> A
        |
        |{
        |  let z : Nat := arbitrary()
        |  z
        |}
        |""".stripMargin

    runProgram(p)
  }

  test("bare implicit-only constructor is instantiated from expected type") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive Vec (A: Type) indices (n: Nat) : Type
        | | nil : Vec(A, Nat.zero)
        | | cons {n: Nat} (tail: Vec(A, n)) (head: A) : Vec(A, Nat.succ(n))
        |
        |{
        |  let xs : Vec(Nat, Nat.zero) := Vec.nil
        |  xs
        |}
        |""".stripMargin

    assertEquals(toShape(runProgram(p)), SConst("Vec.nil"))
  }

  test("application expected result refines omitted implicit before checking argument") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive Vec (A: Type) indices (n: Nat) : Type
        | | nil : Vec(A, Nat.zero)
        | | cons {n: Nat} (tail: Vec(A, n)) (head: A) : Vec(A, Nat.succ(n))
        |
        |def use {A: Type} (v: Vec(A, Nat.zero)): Vec(A, Nat.zero) := v
        |
        |{
        |  let xs : Vec(Nat, Nat.zero) := use(Vec.nil)
        |  xs
        |}
        |""".stripMargin

    assertEquals(toShape(runProgram(p)), SConst("Vec.nil"))
  }

  test("expected function type instantiates leading implicit binders") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |def id {A: Type}(x: A): A := x
        |
        |{
        |  let f : Nat -> Nat := id
        |  f(Nat.succ(Nat.zero))
        |}
        |""".stripMargin

    assertEquals(toShape(runProgram(p)), succS(zeroS))
  }

  test("expected function type instantiates leading implicit binders through local alias") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |def id {A: Type}(x: A): A := x
        |
        |{
        |  let t : Type := (_: Nat) -> Nat
        |  let f : t := id
        |  f(Nat.succ(Nat.zero))
        |}
        |""".stripMargin

    assertEquals(toShape(runProgram(p)), succS(zeroS))
  }

  test("explicit arguments are checked against binder types before implicit insertion is quoted") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive Vec (A: Type) indices (n: Nat) : Type
        | | nil : Vec(A, Nat.zero)
        | | cons {n: Nat} (tail: Vec(A, n)) (head: A) : Vec(A, Nat.succ(n))
        |
        |def useNil (v: Vec(Nat, Nat.zero)): Nat := Nat.zero
        |
        |{
        |  useNil(Vec.nil)
        |}
        |""".stripMargin

    assertEquals(toShape(runProgram(p)), zeroS)
  }

  test("lambda body and match branches use expected result type for implicit constructors") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive Bool : Type
        | | true : Bool
        | | false : Bool
        |
        |inductive Vec (A: Type) indices (n: Nat) : Type
        | | nil : Vec(A, Nat.zero)
        | | cons {n: Nat} (tail: Vec(A, n)) (head: A) : Vec(A, Nat.succ(n))
        |
        |def chooseNil (b: Bool): Vec(Nat, Nat.zero) := {
        |  match b with
        |  | Bool.true => Vec.nil
        |  | Bool.false => Vec.nil
        |}
        |
        |{
        |  chooseNil(Bool.true)
        |}
        |""".stripMargin

    assertEquals(toShape(runProgram(p)), SConst("Vec.nil"))
  }
}
