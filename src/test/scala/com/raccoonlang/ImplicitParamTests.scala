package com.raccoonlang

class ImplicitParamTests extends munit.FunSuite with TestSupport {
  override protected val suitePrelude: Prelude.Config = Prelude.test

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

  private val zeroS = SConst("Peano.zero")
  private def succS(s: Shape) = SApp(SConst("Peano.succ"), List(s))

  test("implicit family argument can be used in codomain and body") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |inductive Box {u: Level}(A: Sort { level = u }) : Sort { level = u }
        | | mk (a: A) : Box(A)
        |
        |def unbox {u: Level}{A: Sort { level = u }} (b: Box(A)): A := {
        |  match b returning A with
        |  | Box.mk a => a
        |}
        |
        |{
        |  unbox(Box.mk(Peano.zero))
        |}
        |""".stripMargin

    assertEquals(toShape(runProgram(p)), zeroS)
  }

  test("implicit index can be used as an ordinary term") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |inductive Vec {u: Level}(A: Sort { level = u }) indices (n: Peano) : Sort { level = max(one, u) }
        | | nil : Vec(A, Peano.zero)
        | | cons {n: Peano} (tail: Vec(A, n)) (head: A) : Vec(A, Peano.succ(n))
        |
        |def len {n: Peano} (v: Vec(Peano, n)): Peano := n
        |
        |{
        |  len(Vec.cons(Vec.nil(Peano), Peano.zero))
        |}
        |""".stripMargin

    assertEquals(toShape(runProgram(p)), succS(zeroS))
  }

  test("def implicits are reconstructed, never supplied positionally") {
    val decls =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |def id {A: Type} (x: A): A := x
        |""".stripMargin

    // Positional supply of the implicit is an arity error: a call supplies exactly the Pi's own
    // explicit binders, and `id` has one.
    expectTypeError[ArityMismatch](
      decls +
        """
          |{
          |  id(Peano, Peano.succ(Peano.zero))
          |}
          |""".stripMargin
    )

    // ...and the implicit is reconstructed from the explicit argument's type.
    val ok =
      decls +
        """
          |{
          |  id(Peano.succ(Peano.zero))
          |}
          |""".stripMargin

    assertEquals(toShape(runProgram(ok)), succS(zeroS))
  }

  test("implicit binder not forced by any later non-implicit binder is rejected") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        |
        |def use (bad: Peano -> {A: Type} -> A): Peano := Peano.zero
        |""".stripMargin

    expectTypeError[NonForcedImplicitParam](p)
  }

  test("implicit binders may sit mid-telescope when forced by later binders") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |def pick (n: Peano){A: Type}(x: A)(y: A): A := {
        |  match n returning A with
        |  | Peano.zero => x
        |  | Peano.succ p => y
        |}
        |
        |{
        |  pick(Peano.zero, Peano.zero, Peano.succ(Peano.zero))
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
        interceptError[NonForcedImplicitParam] { Interpreter.run(core, Prelude.test) }
      case err: Failure =>
        fail(s"Failed to parse: $err, ${p.substring(err.curIdx)}")
    }
  }

  test("constructor implicit binders may include indices after family params") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |inductive Vec (A: Type) indices (n: Peano) : Type
        | | nil : Vec(A, Peano.zero)
        | | cons {n: Peano} (tail: Vec(A, n)) (head: A) : Vec(A, Peano.succ(n))
        |""".stripMargin

    typecheckDecls(p)
  }

  test("match patterns bind implicit constructor fields") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        |
        |inductive Pack : Sort { level = succ(one) }
        | | mk {A: Type} (x: A) : Pack
        |
        |def carrier (p: Pack): Type := {
        |  match p returning Type with
        |  | Pack.mk A x => A
        |}
        |
        |{
        |  carrier(Pack.mk(Peano.zero))
        |}
        |""".stripMargin

    assertEquals(toShape(runProgram(p)), SConst("Peano"))
  }

  test("an implicit-only function type has no forcing binder and is rejected") {
    // Expected-type-driven instantiation is gone, so `arbitrary` could never be
    // applied; its function type itself is rejected.
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |def use (arbitrary: {A: Type} -> A): Peano := Peano.zero
        |""".stripMargin

    expectTypeError[NonForcedImplicitParam](p)
  }

  test("unforced constructor family param is demoted to an explicit argument") {
    // No field of Vec.nil forces A, so A demotes to an explicit arg: Vec.nil(Peano).
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |inductive Vec (A: Type) indices (n: Peano) : Type
        | | nil : Vec(A, Peano.zero)
        | | cons {n: Peano} (tail: Vec(A, n)) (head: A) : Vec(A, Peano.succ(n))
        |
        |{
        |  let xs : Vec(Peano, Peano.zero) := Vec.nil(Peano)
        |  xs
        |}
        |""".stripMargin

    assertEquals(toShape(runProgram(p)), SConst("Vec.nil"))
  }

  test("def implicit is reconstructed by projection from the explicit argument's type") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |inductive Vec (A: Type) indices (n: Peano) : Type
        | | nil : Vec(A, Peano.zero)
        | | cons {n: Peano} (tail: Vec(A, n)) (head: A) : Vec(A, Peano.succ(n))
        |
        |def use {A: Type} (v: Vec(A, Peano.zero)): Vec(A, Peano.zero) := v
        |
        |{
        |  let xs : Vec(Peano, Peano.zero) := use(Vec.nil(Peano))
        |  xs
        |}
        |""".stripMargin

    assertEquals(toShape(runProgram(p)), SConst("Vec.nil"))
  }

  // Neither a written Pi nor an alias of one adapts a polymorphic function: the let's value is
  // synthesized and compared by equality, so the syntax of its declared type is never read.
  test("a let's declared function type does not adapt a polymorphic function") {
    def program(declaredTy: String, value: String): String =
      s"""
         |inductive Peano : Type
         | | zero : Peano
         | | succ (_: Peano) : Peano
         |
         |def id {A: Type}(x: A): A := x
         |
         |{
         |  let t : Type := (_: Peano) -> Peano
         |  let f : $declaredTy := $value
         |  f(Peano.succ(Peano.zero))
         |}
         |""".stripMargin

    val lambda = "fun (x: Peano): Peano => id(x)"
    assertEquals(toShape(runProgram(program("(_: Peano) -> Peano", lambda))), succS(zeroS))
    assertEquals(toShape(runProgram(program("t", lambda))), succS(zeroS))
    expectOnly[TypeMismatch](typecheckDecls(program("(_: Peano) -> Peano", "id")))
    expectOnly[TypeMismatch](typecheckDecls(program("t", "id")))
  }

  test("explicit arguments are checked against binder types") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |inductive Vec (A: Type) indices (n: Peano) : Type
        | | nil : Vec(A, Peano.zero)
        | | cons {n: Peano} (tail: Vec(A, n)) (head: A) : Vec(A, Peano.succ(n))
        |
        |def useNil (v: Vec(Peano, Peano.zero)): Peano := Peano.zero
        |
        |{
        |  useNil(Vec.nil(Peano))
        |}
        |""".stripMargin

    assertEquals(toShape(runProgram(p)), zeroS)
  }

  test("match branches check constructor results against the def result type") {
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
        |inductive Vec (A: Type) indices (n: Peano) : Type
        | | nil : Vec(A, Peano.zero)
        | | cons {n: Peano} (tail: Vec(A, n)) (head: A) : Vec(A, Peano.succ(n))
        |
        |def chooseNil (b: Bool): Vec(Peano, Peano.zero) := {
        |  match b returning Vec(Peano, Peano.zero) with
        |  | Bool.true => Vec.nil(Peano)
        |  | Bool.false => Vec.nil(Peano)
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
        |inductive Peano : Type
        | | zero : Peano
        |
        |def bad {A: Type}{u: Level} (x: A): A := x
        |""".stripMargin

    expectTypeError[NonForcedImplicitParam](p)
  }

  test("supplying implicit args positionally is an arity error") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |inductive Vec {u: Level}(A: Sort { level = u }) indices (n: Peano) : Sort { level = max(one, u) }
        | | nil : Vec(A, Peano.zero)
        | | cons {n: Peano} (tail: Vec(A, n)) (head: A) : Vec(A, Peano.succ(n))
        |
        |{
        |  Vec.cons(Peano, Vec.nil(Peano), Peano.zero)
        |}
        |""".stripMargin

    // Vec.cons's telescope is {u}{A}{n}(tail)(head): callers supply exactly the
    // 2 explicit args; every implicit is reconstructed.
    expectTypeError[ArityMismatch](p)
  }

  test("level implicits cannot be supplied positionally") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        |
        |inductive Box {u: Level}(A: Sort { level = u }) : Sort { level = u }
        | | mk (a: A) : Box(A)
        |
        |{
        |  Box.mk(Level.one, Peano, Peano.zero)
        |}
        |""".stripMargin

    expectTypeError[ArityMismatch](p)
  }

  test("all implicits are inferred when only explicit args are supplied") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |inductive Vec {u: Level}(A: Sort { level = u }) indices (n: Peano) : Sort { level = max(one, u) }
        | | nil : Vec(A, Peano.zero)
        | | cons {n: Peano} (tail: Vec(A, n)) (head: A) : Vec(A, Peano.succ(n))
        |
        |def len {n: Peano} (v: Vec(Peano, n)): Peano := n
        |
        |{
        |  len(Vec.cons(Vec.nil(Peano), Peano.zero))
        |}
        |""".stripMargin

    assertEquals(toShape(runProgram(p)), succS(zeroS))
  }
}
