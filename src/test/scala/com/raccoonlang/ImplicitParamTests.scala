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
    case Value.ConstructorHead(n, _, _, _, _) => SConst(n)
    case Value.VCtor(h, storedArgs, _) =>
      val args = storedArgs
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
        |  unbox(Box.mk(Nat.zero))
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
        |  len(Vec.cons(Vec.nil(Nat), Nat.zero))
        |}
        |""".stripMargin

    assertEquals(toShape(runProgram(p)), succS(zeroS))
  }

  test("def implicits are reconstructed, never supplied positionally") {
    val decls =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |def id {A: Type} (x: A): A := x
        |""".stripMargin

    // Old positional supply of the implicit is now an arity error...
    typeError[ArityMismatch](
      decls +
        """
          |{
          |  id(Nat, Nat.succ(Nat.zero))
          |}
          |""".stripMargin
    )

    // ...and the implicit is reconstructed from the explicit argument's type.
    val ok =
      decls +
        """
          |{
          |  id(Nat.succ(Nat.zero))
          |}
          |""".stripMargin

    assertEquals(toShape(runProgram(ok)), succS(zeroS))
  }

  test("implicit binder not forced by any later non-implicit binder is rejected") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        |
        |axiom bad : Nat -> {A: Type} -> A
        |""".stripMargin

    typeError[NonForcedImplicitParam](p)
  }

  test("implicit binders may sit mid-telescope when forced by later binders") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |def pick (n: Nat){A: Type}(x: A)(y: A): A := {
        |  match n returning A with
        |  | Nat.zero => x
        |  | Nat.succ p => y
        |}
        |
        |{
        |  pick(Nat.zero, Nat.zero, Nat.succ(Nat.zero))
        |}
        |""".stripMargin

    assertEquals(toShape(runProgram(p)), zeroS)
  }

  test("ordinary hidden constructor binders cannot stand in for family params") {
    val p =
      """
        |inductive Bad (A: Type) : Type
        | | mk {B: Type} : Bad(B)
        |""".stripMargin

    // The unforced user-written {B} is rejected at Pi formation, before the uniformity check even
    // runs (family demotion applies only to synthesized family params). The explicit-(B) variant
    // of this smuggle is guarded by InductiveCheckTest's NonUniformInductiveParam test.
    LanguageParser.parseProgram(p) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        intercept[NonForcedImplicitParam] { Interpreter.run(core, Prelude.test) }
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

  test("implicit-only axiom has no forcing binder and is rejected") {
    // Expected-type-driven instantiation is gone, so `arbitrary` could never be
    // applied; the axiom itself is now rejected at declaration time.
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |axiom arbitrary : {A: Type} -> A
        |""".stripMargin

    typeError[NonForcedImplicitParam](p)
  }

  test("unforced constructor family param is demoted to an explicit argument") {
    // No field of Vec.nil forces A, so A demotes to an explicit arg: Vec.nil(Nat).
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
        |  let xs : Vec(Nat, Nat.zero) := Vec.nil(Nat)
        |  xs
        |}
        |""".stripMargin

    assertEquals(toShape(runProgram(p)), SConst("Vec.nil"))
  }

  test("def implicit is reconstructed by projection from the explicit argument's type") {
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
        |  let xs : Vec(Nat, Nat.zero) := use(Vec.nil(Nat))
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

  test("explicit arguments are checked against binder types") {
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
        |  useNil(Vec.nil(Nat))
        |}
        |""".stripMargin

    assertEquals(toShape(runProgram(p)), zeroS)
  }

  test("match branches check constructor results against the def result type") {
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
        |  | Bool.true => Vec.nil(Nat)
        |  | Bool.false => Vec.nil(Nat)
        |}
        |
        |{
        |  chooseNil(Bool.true)
        |}
        |""".stripMargin

    assertEquals(toShape(runProgram(p)), SConst("Vec.nil"))
  }

  test("unused implicit level binder is rejected") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        |
        |def bad {A: Type}{u: Level} (x: A): A := x
        |""".stripMargin

    typeError[NonForcedImplicitParam](p)
  }

  test("supplying implicit args positionally is an arity error") {
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
        |{
        |  Vec.cons(Nat, Vec.nil(Nat), Nat.zero)
        |}
        |""".stripMargin

    // Vec.cons's telescope is {u}{A}{n}(tail)(head): callers supply exactly the
    // 2 explicit args; every implicit is reconstructed.
    typeError[ArityMismatch](p)
  }

  test("level implicits cannot be supplied positionally") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        |
        |inductive Box {u: Level}(A: Sort(u)) : Sort(u)
        | | mk (a: A) : Box(A)
        |
        |{
        |  Box.mk(Level.one, Nat, Nat.zero)
        |}
        |""".stripMargin

    typeError[ArityMismatch](p)
  }

  test("all implicits are inferred when only explicit args are supplied") {
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
        |  len(Vec.cons(Vec.nil(Nat), Nat.zero))
        |}
        |""".stripMargin

    assertEquals(toShape(runProgram(p)), succS(zeroS))
  }
}
