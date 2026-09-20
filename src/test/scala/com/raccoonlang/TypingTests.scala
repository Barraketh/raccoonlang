package com.raccoonlang

class TypingTests extends munit.FunSuite with TestSupport {
  override protected val suitePrelude: Prelude.Config = Prelude.test

  // Erased shape comparison helpers
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
    case other                     => SConst(other.toString) // fallback
  }

  private val zeroS = SConst("Peano.zero")
  private def succS(s: Shape) = SApp(SConst("Peano.succ"), List(s))

  test("bare-body def of function type aliases a function without eta-expansion") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |def myFn (n: Peano): Peano := Peano.succ(n)
        |
        |def alias : Peano -> Peano := myFn
        |
        |{
        |  alias(Peano.zero)
        |}
        |""".stripMargin

    assertEquals(toShape(runProgram(p)), succS(zeroS))
  }

  test("bare-body def eta-adapts a polymorphic function like a let does") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |def polyId {u: Level}{A: Sort(u)} (x: A): A := x
        |
        |def monoId : Peano -> Peano := polyId
        |
        |{
        |  monoId(Peano.zero)
        |}
        |""".stripMargin

    assertEquals(toShape(runProgram(p)), zeroS)
  }

  test("def typechecks and reduces by default") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |def id (A: Type)(x: A): A := x
        |
        |{
        |  id(Peano, Peano.zero)
        |}
        |""".stripMargin

    val res = runProgram(p)
    assertEquals(toShape(res), zeroS)
  }

  test("def: declared return too large (A -> A) expected, value A") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |def bad (A: Type)(x: A): A -> A := x
        |""".stripMargin

    intercept[RuntimeException] {
      typecheckDecls(p)
    }
  }

  test("let with mismatched ascription fails (constructor vs Peano)") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |{
        |  let s : Peano := Peano.succ
        |  s
        |}
        |""".stripMargin

    expectTypeError[TypeMismatch](p)
  }

  test("ascribed function type alpha-equals: (x: Peano)->Peano vs fun (y: Peano) => y") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |{
        |  let f : (x: Peano) -> Peano := fun (y: Peano): Peano => y
        |  f(Peano.zero)
        |}
        |""".stripMargin

    val res = runProgram(p)
    assertEquals(toShape(res), zeroS)
  }

  test("nested lambda captures outer local ref") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |{
        |  let k := fun (x: Peano): ((y: Peano) -> Peano) => fun (y: Peano): Peano => x
        |  let h := k(Peano.zero)
        |  h(Peano.succ(Peano.zero))
        |}
        |""".stripMargin

    val res = runProgram(p)
    assertEquals(toShape(res), zeroS)
  }

  test("later let shadowing allocates a new local ref") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |{
        |  let x := Peano.zero
        |  let f := fun (y: Peano): Peano => x
        |  let x := Peano.succ(Peano.zero)
        |  f(x)
        |}
        |""".stripMargin

    val res = runProgram(p)
    assertEquals(toShape(res), zeroS)
  }

  test("pred on Peano typechecks and reduces via match") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |def pred (n: Peano): Peano := {
        |  match n with
        |  | Peano.zero => Peano.zero
        |  | Peano.succ x => x
        |}
        |
        |{
        |  pred(Peano.succ(Peano.zero))
        |}
        |""".stripMargin

    val res = runProgram(p)
    assertEquals(toShape(res), zeroS)
  }

  test("def: declared result Type but branch returns Peano => mismatch") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |def bad (n: Peano): Type := {
        |  match n with
        |  | Peano.zero => Peano.zero
        |  | Peano.succ x => x
        |}
        |""".stripMargin

    intercept[RuntimeException] {
      typecheckDecls(p)
    }
  }

  test("def: explicit match motive must fit declared result") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |def bad (n: Peano): Type := {
        |  match n returning Peano with
        |  | Peano.zero => Peano.zero
        |  | Peano.succ x => x
        |}
        |""".stripMargin

    interceptError[TypeMismatch] {
      typecheckDecls(p)
    }
  }

  test("unannotated let with constructor synthesizes type and reduces when applied") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |{
        |  let one := Peano.succ(Peano.zero)
        |  one
        |}
        |""".stripMargin

    val res = runProgram(p)
    assertEquals(toShape(res), succS(zeroS))
  }

  test("Bad metas") {
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
        |def badVec (A: Type)(n: Peano)(v: Vec(A, n)): Vec(A, Peano.zero) := v
        |""".stripMargin

    interceptError[TypeMismatch] {
      typecheckDecls(p)
    }
  }

  test("reachable nullary ctor branch refines scrutinee at instantiated result type") {
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
        |def keepNil (A: Type)(v: Vec(A, Peano.zero)): Vec(A, Peano.zero) := {
        |  match v with
        |  | Vec.nil => v
        |}
        |""".stripMargin

    typecheckDecls(p)
  }

  test("definition body can start on next line and wrap applications") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |def apply
        |  (f:
        |    Peano ->
        |    Peano
        |  )
        |  (x: Peano)
        |  : Peano :=
        |  f(
        |    x
        |  )
        |
        |def useApply : Peano :=
        |  apply(
        |    fun (n: Peano): Peano =>
        |      n,
        |    Peano.zero
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
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |def bad : Peano := Type
        |""".stripMargin

    interceptError[TypeMismatch] {
      typecheckDecls(p)
    }
  }

  test("nullary top-level opaque def body must match declared type") {
    val p =
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (_: Peano) : Peano
        |
        |opaque def bad : Peano := Type
        |""".stripMargin

    interceptError[TypeMismatch] {
      typecheckDecls(p)
    }
  }

  /**
   * Grouping is part of a function type's identity, and the surface syntax is where a written type's grouping is
   * decided: an unparenthesised arrow chain is ONE binder group, while a parenthesised Pi in body position is a nested,
   * separate group.
   */
  test("arrow chains group, parenthesised Pi bodies nest") {
    def elabType(src: String): CoreAst.Term =
      LanguageParser.parseFuncHeader(src) match {
        case Success(header, _, _) => Elaborator.getType(header)
        case err: Failure          => fail(s"Failed to parse: $err")
      }

    // `(a: A) -> (b: B) -> C` is a single 2-binder group whose out is not a Pi.
    elabType(": (a: Type) -> (b: Type) -> Type") match {
      case pi: CoreAst.Term.Pi =>
        assertEquals(pi.binders.length, 2)
        assert(!pi.out.isInstanceOf[CoreAst.Term.Pi], s"expected a non-Pi out, got ${pi.out}")
      case other => fail(s"expected a Pi, got $other")
    }

    // Parenthesising the body makes it a nested 1-ary Pi returning a Pi.
    elabType(": (a: Type) -> ((b: Type) -> Type)") match {
      case pi: CoreAst.Term.Pi =>
        assertEquals(pi.binders.length, 1)
        pi.out match {
          case inner: CoreAst.Term.Pi => assertEquals(inner.binders.length, 1)
          case other                  => fail(s"expected a nested Pi out, got $other")
        }
      case other => fail(s"expected a Pi, got $other")
    }

    // The anonymous chain groups the same way.
    elabType(": Type -> Type -> Type") match {
      case pi: CoreAst.Term.Pi =>
        assertEquals(pi.binders.length, 2)
        assert(!pi.out.isInstanceOf[CoreAst.Term.Pi], s"expected a non-Pi out, got ${pi.out}")
      case other => fail(s"expected a Pi, got $other")
    }
  }
}
