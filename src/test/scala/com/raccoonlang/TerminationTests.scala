package com.raccoonlang

import com.raccoonlang.ErrorReporter.Source

class TerminationTests extends munit.FunSuite with TestSupport {
  override protected val suitePrelude: Prelude.Config = Prelude.test

  private def runProgramOption(src: String): Option[Value] =
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        try Interpreter.run(core, Prelude.test)
        catch {
          case t: TypeError => fail(ErrorReporter.pretty(t, Source(src)))
        }
      case err: Failure => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }

  private val natDecls =
    """
      |inductive Peano : Type
      | | zero : Peano
      | | succ (_: Peano) : Peano
      |""".stripMargin

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
  private def succS(s: Shape): Shape = SApp(SConst("Peano.succ"), List(s))

  test("structural recursion accepts direct recursive calls") {
    val p =
      natDecls +
        """
          |def add (a: Peano)(b: Peano): Peano decreases structural(b) := {
          |  match b with
          |  | Peano.zero => a
          |  | Peano.succ x => add(Peano.succ(a), x)
          |}
          |
          |{
          |  let one := Peano.succ(Peano.zero)
          |  add(one, one)
          |}
          |""".stripMargin

    assertEquals(toShape(runProgramOption(p).get), succS(succS(zeroS)))
  }

  test("structural recursion searches through transitive constructor fields") {
    val p =
      natDecls +
        """
          |def skipTwo (n: Peano): Peano decreases structural(n) := {
          |  match n with
          |  | Peano.zero => Peano.zero
          |  | Peano.succ x => {
          |    match x returning Peano with
          |    | Peano.zero => Peano.zero
          |    | Peano.succ y => skipTwo(y)
          |  }
          |}
          |""".stripMargin

    runProgramOption(p)
  }

  test("recursive ref is available in nested binder types under match refinements") {
    val p =
      natDecls +
        """
          |inductive Box (n: Peano) : Type
          | | mk : Box(n)
          |
          |def f (n: Peano): Peano decreases structural(n) := {
          |  match n with
          |  | Peano.zero => Peano.zero
          |  | Peano.succ k => {
          |    let g := fun (x: Box(f(k))): Peano => Peano.zero
          |    Peano.zero
          |  }
          |}
          |""".stripMargin

    runProgramOption(p)
  }

  test("lexicographic recursion accepts an earlier decrease or equal-prefix later decrease") {
    val p =
      natDecls +
        """
          |def lex (a: Peano)(b: Peano): Peano decreases lexicographic(a, b) := {
          |  match a with
          |  | Peano.zero => {
          |    match b returning Peano with
          |    | Peano.zero => Peano.zero
          |    | Peano.succ b0 => lex(Peano.zero, b0)
          |  }
          |  | Peano.succ a0 => lex(a0, b)
          |}
          |""".stripMargin

    runProgramOption(p)
  }

  test("measure recursion compares the evaluated measure structurally") {
    val p =
      natDecls +
        """
          |inductive List (A: Type) : Type
          | | nil : List(A)
          | | cons (tail: List(A)) (head: A) : List(A)
          |
          |def length (A: Type)(xs: List(A)): Peano decreases structural(xs) := {
          |  match xs returning Peano with
          |  | List.nil => Peano.zero
          |  | List.cons tail _ => Peano.succ(length(A, tail))
          |}
          |
          |def consume (A: Type)(xs: List(A)): Peano decreases measure(length(A, xs)) := {
          |  match xs returning Peano with
          |  | List.nil => Peano.zero
          |  | List.cons tail _ => consume(A, tail)
          |}
          |""".stripMargin

    runProgramOption(p)
  }

  test("recursive self call without decreases is rejected") {
    val p =
      natDecls +
        """
          |def bad (n: Peano): Peano := bad(n)
          |""".stripMargin

    expectTypeError[NotFound](p)
  }

  test("qualified recursive self references resolve to recursive local") {
    val rootQualified =
      natDecls +
        """
          |def pred (n: Peano): Peano decreases structural(n) := {
          |  match n with
          |  | Peano.zero => Peano.zero
          |  | Peano.succ x => _root_.pred(x)
          |}
          |
          |pred(Peano.succ(Peano.succ(Peano.zero)))
          |""".stripMargin

    assertEquals(toShape(runProgramOption(rootQualified).get), zeroS)

    val namespaced =
      natDecls +
        """
          |namespace Math {
          |  def pred (n: Peano): Peano decreases structural(n) := {
          |    match n with
          |    | Peano.zero => Peano.zero
          |    | Peano.succ x => _root_.Math.pred(x)
          |  }
          |}
          |
          |Math.pred(Peano.succ(Peano.succ(Peano.zero)))
          |""".stripMargin

    assertEquals(toShape(runProgramOption(namespaced).get), zeroS)

    val namespaceQualified =
      natDecls +
        """
          |namespace Math {
          |  def pred (n: Peano): Peano decreases structural(n) := {
          |    match n with
          |    | Peano.zero => Peano.zero
          |    | Peano.succ x => Math.pred(x)
          |  }
          |}
          |
          |Math.pred(Peano.succ(Peano.succ(Peano.zero)))
          |""".stripMargin

    assertEquals(toShape(runProgramOption(namespaceQualified).get), zeroS)
  }

  test("recursive function name cannot be shadowed by a parameter") {
    val p =
      natDecls +
        """
          |def bad (bad: Peano): Peano decreases structural(bad) := bad
          |""".stripMargin

    expectTypeError[AlreadyDefined](p)
  }

  test("recursive function name cannot be shadowed by a local") {
    val p =
      natDecls +
        """
          |def bad (n: Peano): Peano decreases structural(n) := {
          |  let bad := n
          |  Peano.zero
          |}
          |""".stripMargin

    expectTypeError[AlreadyDefined](p)
  }

  test("non-decreasing structural recursion is rejected") {
    val p =
      natDecls +
        """
          |def bad (n: Peano): Peano decreases structural(n) := bad(n)
          |""".stripMargin

    expectTypeError[NonDecreasingRecursiveCall](p)
  }

  test("structural decrease on a proof argument is rejected outright") {
    // Proof structure is not invariant under an equality that identifies wrap(x) with base, and
    // erased proofs have no subterms, so the declaration itself is invalid
    // (docs/kernel.md#termination). This subsumes the old pin that proof irrelevance cannot fake
    // a structural decrease.
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

    expectTypeError[InvalidDecreaseSpec](p)
  }

  test("lexicographic recursion requires some component to decrease") {
    val p =
      natDecls +
        """
          |def bad (a: Peano)(b: Peano): Peano decreases lexicographic(a, b) := bad(a, b)
          |""".stripMargin

    expectTypeError[NonDecreasingRecursiveCall](p)
  }

  test("decreases structural must name a function binder") {
    val p =
      natDecls +
        """
          |def bad (n: Peano): Peano decreases structural(Peano) := n
          |""".stripMargin

    expectTypeError[InvalidDecreaseSpec](p)
  }

  test("measure expression must have an inductive type") {
    val p =
      natDecls +
        """
          |def bad (n: Peano): Peano decreases measure(Type) := n
          |""".stripMargin

    expectTypeError[InvalidDecreaseSpec](p)
  }

  private val treeDecls =
    natDecls +
      """
        |inductive Tree : Type
        | | leaf : Tree
        | | node (f: Peano -> Tree) : Tree
        |""".stripMargin

  test("structural recursion descends through applications of function-typed fields") {
    // f is the node's child-selector: f(b) is a child of node(f) in the well-founded tree
    // semantics of a strictly positive inductive, so recursing on it terminates (the rule that
    // makes recursors for infinitary inductives like WType/PGame definable).
    val p =
      treeDecls +
        """
          |def leftDepth (t: Tree): Peano decreases structural(t) := {
          |  match t with
          |  | Tree.leaf => Peano.zero
          |  | Tree.node f => Peano.succ(leftDepth(f(Peano.zero)))
          |}
          |
          |leftDepth(Tree.node(fun (n: Peano): Tree => Tree.leaf))
          |""".stripMargin

    assertEquals(toShape(runProgramOption(p).get), succS(zeroS))
  }

  test("synthesized recursor shape: induction hypotheses apply selectors under binders") {
    // The exact term shape a translator emits for Foo.rec on an infinitary inductive: the IH is a
    // lambda applying the selector to a fresh binder.
    val p =
      natDecls +
        """
          |inductive Game : Type
          | | halt : Game
          | | mk (l: Peano -> Game)(r: Peano -> Game) : Game
          |
          |def score (g: Game): Peano decreases structural(g) := {
          |  match g with
          |  | Game.halt => Peano.zero
          |  | Game.mk l r => {
          |    let ihl := fun (b: Peano): Peano => score(l(b))
          |    let ihr := fun (b: Peano): Peano => score(r(b))
          |    Peano.succ(ihl(Peano.zero))
          |  }
          |}
          |
          |score(Game.mk(fun (n: Peano): Game => Game.halt, fun (n: Peano): Game => Game.halt))
          |""".stripMargin

    assertEquals(toShape(runProgramOption(p).get), succS(zeroS))
  }

  test("selector applications compose with transitive constructor-field descent") {
    val p =
      natDecls +
        """
          |inductive Tree : Type
          | | leaf : Tree
          | | node (f: Peano -> Tree) : Tree
          | | wrap (t: Tree) : Tree
          |
          |def deep (t: Tree): Peano decreases structural(t) := {
          |  match t with
          |  | Tree.leaf => Peano.zero
          |  | Tree.node f => deep(f(Peano.zero))
          |  | Tree.wrap inner => {
          |    match inner returning Peano with
          |    | Tree.leaf => Peano.zero
          |    | Tree.node f => deep(f(Peano.zero))
          |    | Tree.wrap t2 => Peano.zero
          |  }
          |}
          |""".stripMargin

    runProgramOption(p)
  }

  test("applications of non-subterm functions do not count as structural decrease") {
    // The soundness boundary: stripping application frames may only bottom out at a field of the
    // refined root. g is a parameter, not a field of t, so g(0) proves nothing about descent.
    val p =
      treeDecls +
        """
          |def bad (t: Tree)(g: Peano -> Tree): Peano decreases structural(t) := {
          |  match t with
          |  | Tree.leaf => Peano.zero
          |  | Tree.node f => bad(g(Peano.zero), g)
          |}
          |""".stripMargin

    expectTypeError[NonDecreasingRecursiveCall](p)
  }

  test("decrease metric on an axiom-typed value is rejected") {
    // Quot and user axioms are Symbol consts, not inductives: their values are not well-founded
    // trees the structural order could descend.
    val p =
      natDecls +
        """
          |axiom Opaque : Type
          |
          |def bad (q: Opaque): Peano decreases structural(q) := Peano.zero
          |""".stripMargin

    expectTypeError[InvalidDecreaseSpec](p)
  }

  test("raw recursive self cannot be stored inside a residual let value") {
    val p =
      natDecls +
        """
          |opaque def opaqueApply (h: Peano -> Peano)(n: Peano): Peano := h(n)
          |
          |def bad (n: Peano): Peano decreases structural(n) := {
          |  let x := opaqueApply(bad, n)
          |  Peano.zero
          |}
          |""".stripMargin

    expectTypeError[InvalidRecursiveOccurrence](p)
  }

}
