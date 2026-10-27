package com.raccoonlang

import com.raccoonlang.ErrorReporter.Source

class TerminationTests extends munit.FunSuite {
  private def runProgram(src: String): Option[Value] =
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        try Interpreter.run(core, Prelude.test)
        catch {
          case t: TypeError => fail(ErrorReporter.pretty(t, Source(src)))
        }
      case err: Failure => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }

  private def typeError[T <: TypeError](src: String)(implicit ct: reflect.ClassTag[T]): T =
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        intercept[T] {
          val core = Elaborator.elab(value, Prelude.test)
          Interpreter.run(core, Prelude.test)
        }
      case err: Failure => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }

  sealed trait Shape
  case class SConst(name: String) extends Shape
  case class SApp(head: Shape, args: List[Shape]) extends Shape

  private def toShape(v: Value): Shape = v match {
    case Value.ConstructorHead(n, _, _, _) => SConst(n)
    case ConstructorValue(h, fields) =>
      if (fields.isEmpty) SConst(h.name) else SApp(SConst(h.name), fields.toList.map(toShape))
    case Value.VConst(n, _, _)     => SConst(n)
    case Value.VApp(h, args, _, _) => SApp(toShape(h), args.toList.map(toShape))
    case other                     => SConst(other.toString)
  }

  private val zeroS = SConst("Nat.zero")
  private def succS(s: Shape): Shape = SApp(SConst("Nat.succ"), List(s))

  test("structural recursion accepts direct recursive calls") {
    val p =
      """
        |def add (a: Nat)(b: Nat): Nat decreases structural(b) := {
        |  match b with
        |  | Nat.zero => a
        |  | Nat.succ x => add(Nat.succ(a), x)
        |}
        |
        |{
        |  let one := Nat.succ(Nat.zero)
        |  add(one, one)
        |}
        |""".stripMargin

    assertEquals(toShape(runProgram(p).get), succS(succS(zeroS)))
  }

  test("raw recursive self cannot be stored as a direct local alias") {
    val p =
      """
        |def bad (n: Nat): Nat decreases structural(n) := {
        |  let go := bad
        |  match n with
        |  | Nat.zero => Nat.zero
        |  | Nat.succ x => go(x)
        |}
        |""".stripMargin

    typeError[CannotQuoteValue](p)
  }

  test("structural recursion searches through transitive constructor fields") {
    val p =
      """
        |def skipTwo (n: Nat): Nat decreases structural(n) := {
        |  match n with
        |  | Nat.zero => Nat.zero
        |  | Nat.succ x => {
        |    match x with
        |    | Nat.zero => Nat.zero
        |    | Nat.succ y => skipTwo(y)
        |  }
        |}
        |""".stripMargin

    runProgram(p)
  }

  test("recursive ref is available in nested binder types under match refinements") {
    val p =
      """
        |inductive Box (n: Nat) : Type
        | | mk {n: Nat} : Box(n)
        |
        |def f (n: Nat): Nat decreases structural(n) := {
        |  match n with
        |  | Nat.zero => Nat.zero
        |  | Nat.succ k => {
        |    let g := fun (x: Box(f(k))): Nat => Nat.zero
        |    Nat.zero
        |  }
        |}
        |""".stripMargin

    runProgram(p)
  }

  test("lexicographic recursion accepts an earlier decrease or equal-prefix later decrease") {
    val p =
      """
        |def lex (a: Nat)(b: Nat): Nat decreases lexicographic(a, b) := {
        |  match a with
        |  | Nat.zero => {
        |    match b with
        |    | Nat.zero => Nat.zero
        |    | Nat.succ b0 => lex(Nat.zero, b0)
        |  }
        |  | Nat.succ a0 => lex(a0, b)
        |}
        |""".stripMargin

    runProgram(p)
  }

  test("measure recursion compares the evaluated measure structurally") {
    val p =
      """
        |inductive List (A: Type) : Type
        | | nil {A: Type} : List(A)
        | | cons {A: Type} (tail: List(A)) (head: A) : List(A)
        |
        |def length (A: Type)(xs: List(A)): Nat decreases structural(xs) := {
        |  match xs returning Nat with
        |  | List.nil => Nat.zero
        |  | List.cons tail _ => Nat.succ(length(A, tail))
        |}
        |
        |def consume (A: Type)(xs: List(A)): Nat decreases measure(length(A, xs)) := {
        |  match xs returning Nat with
        |  | List.nil => Nat.zero
        |  | List.cons tail _ => consume(A, tail)
        |}
        |""".stripMargin

    runProgram(p)
  }

  test("recursive self call without decreases is rejected") {
    val p =
      """
        |def bad (n: Nat): Nat := bad(n)
        |""".stripMargin

    typeError[NotFound](p)
  }

  test("qualified recursive self references resolve to recursive local") {
    val rootQualified =
      """
        |def pred (n: Nat): Nat decreases structural(n) := {
        |  match n with
        |  | Nat.zero => Nat.zero
        |  | Nat.succ x => _root_.pred(x)
        |}
        |
        |pred(Nat.succ(Nat.succ(Nat.zero)))
        |""".stripMargin

    assertEquals(toShape(runProgram(rootQualified).get), zeroS)

    val namespaced =
      """
        |namespace Math {
        |  def pred (n: Nat): Nat decreases structural(n) := {
        |    match n with
        |    | Nat.zero => Nat.zero
        |    | Nat.succ x => _root_.Math.pred(x)
        |  }
        |}
        |
        |Math.pred(Nat.succ(Nat.succ(Nat.zero)))
        |""".stripMargin

    assertEquals(toShape(runProgram(namespaced).get), zeroS)

    val namespaceQualified =
      """
        |namespace Math {
        |  def pred (n: Nat): Nat decreases structural(n) := {
        |    match n with
        |    | Nat.zero => Nat.zero
        |    | Nat.succ x => Math.pred(x)
        |  }
        |}
        |
        |Math.pred(Nat.succ(Nat.succ(Nat.zero)))
        |""".stripMargin

    assertEquals(toShape(runProgram(namespaceQualified).get), zeroS)
  }

  test("recursive function name cannot be shadowed by a parameter") {
    val p =
      """
        |def bad (bad: Nat): Nat decreases structural(bad) := bad
        |""".stripMargin

    typeError[AlreadyDefined](p)
  }

  test("recursive function name cannot be shadowed by a local") {
    val p =
      """
        |def bad (n: Nat): Nat decreases structural(n) := {
        |  let bad := n
        |  Nat.zero
        |}
        |""".stripMargin

    typeError[AlreadyDefined](p)
  }

  test("non-decreasing structural recursion is rejected") {
    val p =
      """
        |def bad (n: Nat): Nat decreases structural(n) := bad(n)
        |""".stripMargin

    typeError[NonDecreasingRecursiveCall](p)
  }

  test("structural decrease metrics cannot live in Prop") {
    val p =
      """
        |inductive P : Prop
        | | base : P
        | | wrap (p: P) : P
        |
        |def bad (p: P): P decreases structural(p) := {
        |  match p returning P with
        |  | P.base => P.base
        |  | P.wrap x => bad(p)
        |}
        |""".stripMargin

    val error = typeError[InvalidDecreaseSpec](p)
    assert(error.reason.contains("Prop"))
    assert(error.span.nonEmpty)
  }

  test("every lexicographic decrease component must live in Type") {
    Vector("p, n", "n, p").foreach { metrics =>
      val p =
        s"""
           |inductive P : Prop
           | | intro : P
           |
           |def bad (n: Nat)(p: P): Nat decreases lexicographic($metrics) := {
           |  match n returning Nat with
           |  | Nat.zero => Nat.zero
           |  | Nat.succ k => bad(k, p)
           |}
           |""".stripMargin

      val error = typeError[InvalidDecreaseSpec](p)
      assert(error.reason.contains("Prop"))
    }
  }

  test("constructor-valued proof measures cannot justify unchanged recursive calls") {
    val p =
      """
        |inductive P : Prop
        | | base : P
        | | wrap (p: P) : P
        |
        |def bad (p: P): P decreases measure(P.wrap(p)) := bad(p)
        |""".stripMargin

    val error = typeError[InvalidDecreaseSpec](p)
    assert(error.reason.contains("Prop"))
  }

  test("subterm search cannot descend through proof fields of Type-valued measures") {
    val p =
      """
        |inductive Box (A: Type) : Prop
        | | intro {A: Type} (x: A) : Box(A)
        |
        |inductive Tree : Type
        | | leaf : Tree
        | | wrap (proof: Box(Tree)) : Tree
        |
        |def bad (t: Tree): Tree decreases measure(Tree.wrap(Box.intro(Tree, Tree.wrap(Box.intro(Tree, t))))) := bad(t)
        |""".stripMargin

    typeError[NonDecreasingRecursiveCall](p)
  }

  test("proof-returning recursion can decrease Type-valued metrics") {
    Vector("structural(n)", "lexicographic(n)", "measure(n)").foreach { decreases =>
      val p =
        s"""
           |inductive True : Prop
           | | intro : True
           |
           |def prove (n: Nat): True decreases $decreases := {
           |  match n returning True with
           |  | Nat.zero => True.intro
           |  | Nat.succ k => prove(k)
           |}
           |
           |prove(Nat.succ(Nat.succ(Nat.zero)))
           |""".stripMargin

      assertEquals(toShape(runProgram(p).get), SConst("True.intro"))
    }
  }

  test("subterm search skips proof fields and still follows data fields") {
    val p =
      """
        |inductive True : Prop
        | | intro : True
        |
        |inductive Tree : Type
        | | leaf : Tree
        | | node (proof: True)(child: Tree) : Tree
        |
        |def prune (t: Tree): Tree decreases structural(t) := {
        |  match t returning Tree with
        |  | Tree.leaf => Tree.leaf
        |  | Tree.node _ child => prune(child)
        |}
        |
        |prune(Tree.node(True.intro, Tree.node(True.intro, Tree.leaf)))
        |""".stripMargin

    assertEquals(toShape(runProgram(p).get), SConst("Tree.leaf"))
  }

  test("lexicographic equality still ignores proof fields when a data component decreases") {
    val p =
      """
        |inductive P : Prop
        | | left : P
        | | right : P
        |
        |inductive Tag : Type
        | | mk (proof: P) : Tag
        |
        |def consume (tag: Tag)(n: Nat): Nat decreases lexicographic(tag, n) := {
        |  match tag returning Nat with
        |  | Tag.mk h => {
        |    match n returning Nat with
        |    | Nat.zero => Nat.zero
        |    | Nat.succ k => consume(Tag.mk(P.right), k)
        |  }
        |}
        |
        |consume(Tag.mk(P.left), Nat.succ(Nat.succ(Nat.zero)))
        |""".stripMargin

    assertEquals(toShape(runProgram(p).get), zeroS)
  }

  test("lexicographic recursion requires some component to decrease") {
    val p =
      """
        |def bad (a: Nat)(b: Nat): Nat decreases lexicographic(a, b) := bad(a, b)
        |""".stripMargin

    typeError[NonDecreasingRecursiveCall](p)
  }

  test("decreases structural must name a function binder") {
    val p =
      """
        |def bad (n: Nat): Nat decreases structural(Nat) := n
        |""".stripMargin

    typeError[InvalidDecreaseSpec](p)
  }

  test("measure expression must have an inductive type") {
    val p =
      """
        |def bad (n: Nat): Nat decreases measure(Type) := n
        |""".stripMargin

    typeError[InvalidDecreaseSpec](p)
  }

  test("raw recursive self cannot be stored inside a residual let value") {
    val p =
      """
        |axiom opaqueApply (h: Nat -> Nat)(n: Nat): Nat
        |
        |def bad (n: Nat): Nat decreases structural(n) := {
        |  let x := opaqueApply(bad, n)
        |  Nat.zero
        |}
        |""".stripMargin

    typeError[CannotQuoteValue](p)
  }
}
