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
    case Value.ConstructorHead(n, _, _, _, _) => SConst(n)
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
        |inductive Snoc (A: Type) : Type
        | | nil {A: Type} : Snoc(A)
        | | cons {A: Type} (tail: Snoc(A)) (head: A) : Snoc(A)
        |
        |def length (A: Type)(xs: Snoc(A)): Nat decreases structural(xs) := {
        |  match xs returning Nat with
        |  | Snoc.nil => Nat.zero
        |  | Snoc.cons tail _ => Nat.succ(length(A, tail))
        |}
        |
        |def consume (A: Type)(xs: Snoc(A)): Nat decreases measure(length(A, xs)) := {
        |  match xs returning Nat with
        |  | Snoc.nil => Nat.zero
        |  | Snoc.cons tail _ => consume(A, tail)
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

  test("structural recursion on a proof rejects a call on the matched proof itself") {
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

    typeError[NonDecreasingRecursiveCall](p)
  }

  test("a structural decrease metric in Prop needs a function returning a proposition") {
    val p =
      """
        |inductive P : Prop
        | | base : P
        | | wrap (p: P) : P
        |
        |def bad (p: P): Nat decreases structural(p) := {
        |  match p returning Nat with
        |  | P.base => Nat.zero
        |  | P.wrap x => bad(x)
        |}
        |""".stripMargin

    val error = typeError[InvalidDecreaseSpec](p)
    assert(error.reason.contains("Prop"))
    assert(error.span.nonEmpty)
  }

  test("recursion on a proof rejects rebuilt proofs of a field's proposition") {
    Vector("P.wrap(x)", "P.base").foreach { argument =>
      val p =
        s"""
           |inductive P : Prop
           | | base : P
           | | wrap (p: P) : P
           |
           |def bad (p: P): P decreases structural(p) := {
           |  match p returning P with
           |  | P.base => P.base
           |  | P.wrap x => bad($argument)
           |}
           |""".stripMargin

      typeError[NonDecreasingRecursiveCall](p)
    }
  }

  test("recursion on a proof proves transitivity of a closure") {
    val p =
      """
        |inductive Le indices (a: Nat)(b: Nat) : Prop
        | | refl (n: Nat) : Le(n, n)
        | | step (a: Nat)(b: Nat)(h: Le(a, b)) : Le(a, Nat.succ(b))
        |
        |def trans (a: Nat)(b: Nat)(c: Nat)(h1: Le(a, b))(h2: Le(b, c)): Le(a, c) decreases structural(h2) := {
        |  match h2 returning Le(a, c) with
        |  | Le.refl n => h1
        |  | Le.step x y h => Le.step(a, y, trans(a, b, y, h1, h))
        |}
        |
        |def two : Nat := Nat.succ(Nat.succ(Nat.zero))
        |def oneTwo : Le(Nat.succ(Nat.zero), two) := Le.step(Nat.succ(Nat.zero), Nat.succ(Nat.zero), Le.refl(Nat.succ(Nat.zero)))
        |def zeroOne : Le(Nat.zero, Nat.succ(Nat.zero)) := Le.step(Nat.zero, Nat.zero, Le.refl(Nat.zero))
        |def zeroTwo : Le(Nat.zero, two) := trans(Nat.zero, Nat.succ(Nat.zero), two, zeroOne, oneTwo)
        |""".stripMargin

    runProgram(p)
  }

  test("recursion on a local reachability relation proves a conservation law") {
    val p =
      """
        |inductive Step indices (A: List(Nat))(B: List(Nat)) : Prop
        | | swap (x: Nat)(y: Nat) : Step(List.cons(x, List.cons(y, List.nil(Nat))), List.cons(y, List.cons(x, List.nil(Nat))))
        |
        |inductive Reach (init: List(Nat)) indices (C: List(Nat)) : Prop
        | | initial {init: List(Nat)} : Reach(init, init)
        | | step {init: List(Nat)} (A: List(Nat))(B: List(Nat))(frame: List(Nat))(h: Step(A, B))
        |     (prev: Reach(init, List.append(A, frame))) : Reach(init, List.append(B, frame))
        |
        |def conserved (init: List(Nat))(C: List(Nat))(r: Reach(init, C)):
        |    Eq(Nat, List.length(C), List.length(init)) decreases structural(r) := {
        |  match r returning Eq(Nat, List.length(C), List.length(init)) with
        |  | Reach.initial => Eq.refl(List.length(init))
        |  | Reach.step A B frame h prev => {
        |    match h returning Eq(Nat, List.length(List.append(B, frame)), List.length(init)) with
        |    | Step.swap x y => conserved(init, List.append(A, frame), prev)
        |  }
        |}
        |""".stripMargin

    runProgram(p)
  }

  test("lexicographic recursion may decrease a proof component of a proposition-valued function") {
    val p =
      """
        |inductive P : Prop
        | | base : P
        | | wrap (p: P) : P
        |
        |def flatten (p: P)(n: Nat): P decreases lexicographic(p, n) := {
        |  match p returning P with
        |  | P.base => {
        |    match n returning P with
        |    | Nat.zero => P.base
        |    | Nat.succ k => flatten(p, k)
        |  }
        |  | P.wrap x => flatten(x, n)
        |}
        |
        |def flat : P := flatten(P.wrap(P.wrap(P.base)), Nat.succ(Nat.succ(Nat.zero)))
        |""".stripMargin

    runProgram(p)
  }

  test("lexicographic recursion rejects a proof component that grows while a later one decreases") {
    val p =
      """
        |inductive P : Prop
        | | base : P
        | | wrap (p: P) : P
        |
        |def grow (p: P)(n: Nat): P decreases lexicographic(p, n) := {
        |  match n returning P with
        |  | Nat.zero => p
        |  | Nat.succ k => grow(P.wrap(p), k)
        |}
        |""".stripMargin

    typeError[NonDecreasingRecursiveCall](p)
  }

  test("a nested match on a matched proof variable sees the constructor it matched") {
    val p =
      """
        |inductive P : Prop
        | | base : P
        | | wrap (p: P) : P
        |
        |def unwrap (p: P): P := {
        |  match p returning P with
        |  | P.base => P.base
        |  | P.wrap x => {
        |    match p returning P with
        |    | P.wrap y => y
        |  }
        |}
        |""".stripMargin

    runProgram(p)

    val unreachable =
      """
        |inductive P : Prop
        | | base : P
        | | wrap (p: P) : P
        |
        |def unwrap (p: P): P := {
        |  match p returning P with
        |  | P.base => P.base
        |  | P.wrap x => {
        |    match p returning P with
        |    | P.base => P.base
        |    | P.wrap y => y
        |  }
        |}
        |""".stripMargin

    typeError[UnreachableCase](unreachable)
  }

  test("a stuck branch does not link a proof variable to a constructor its type was never unified with") {
    // Both the value and the result-type refinement of `T.z` against `T(f(x))` are stuck on `f(x)`, so the branch
    // keeps `p : T(f(x))`; a link to `T.z : T(Nat.zero)` would make returning `p` a `TypeMismatch`.
    val p =
      """
        |inductive T indices (n: Nat) : Prop
        | | z : T(Nat.zero)
        |
        |def f (n: Nat): Nat decreases structural(n) := {
        |  match n returning Nat with
        |  | Nat.zero => Nat.zero
        |  | Nat.succ k => f(k)
        |}
        |
        |def g (x: Nat)(p: T(f(x))): T(f(x)) := {
        |  match p returning T(f(x)) with
        |  | T.z => p
        |}
        |""".stripMargin

    runProgram(p)
  }

  test("a lexicographic decrease component of a function not returning a proposition must live in Type") {
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
      assert(error.reason.contains("only for functions returning a proposition"), error.reason)
    }
  }

  test("a proof measure is rejected as a measure, whatever the function returns") {
    Vector("Nat", "P").foreach { result =>
      val p =
        s"""
           |inductive P : Prop
           | | intro : P
           |
           |def bad (p: P): $result decreases measure(p) := bad(p)
           |""".stripMargin

      val error = typeError[InvalidDecreaseSpec](p)
      assert(error.reason.contains("decrease measures must live in Type"), error.reason)
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

  // KERNEL_FOLLOWUPS 2.4: at a variable index, captured or a parameter, matching refines the index and links the
  // scrutinee to its constructor, whose fields are then structural subterms of it.
  private val vec =
    """
      |inductive Vec (A: Type) indices (n: Nat) : Type
      | | nil {A: Type} : Vec(A, Nat.zero)
      | | cons {A: Type} (m: Nat)(tail: Vec(A, m)) (head: A) : Vec(A, Nat.succ(m))
      |""".stripMargin

  test("structural recursion on an indexed family at a variable index") {
    val p =
      vec +
        """
          |def len (A: Type)(n: Nat)(v: Vec(A, n)): Nat decreases structural(v) := {
          |  match v returning Nat with
          |  | Vec.nil => Nat.zero
          |  | Vec.cons m tail head => Nat.succ(len(A, m, tail))
          |}
          |
          |def lenCaptured (v: Vec($A, $n)): Nat decreases structural(v) := {
          |  match v returning Nat with
          |  | Vec.nil => Nat.zero
          |  | Vec.cons m tail head => Nat.succ(lenCaptured(tail))
          |}
          |
          |{
          |  lenCaptured(Vec.cons(Nat, Nat.succ(Nat.zero), Vec.cons(Nat, Nat.zero, Vec.nil(Nat), Nat.zero), Nat.zero))
          |}
          |""".stripMargin
    assertEquals(runProgram(p).map(toShape), Some(succS(succS(zeroS))))
    typeError[NonDecreasingRecursiveCall](
      vec +
        """
          |def loop (A: Type)(n: Nat)(v: Vec(A, n)): Nat decreases structural(v) := {
          |  match v returning Nat with
          |  | Vec.nil => Nat.zero
          |  | Vec.cons m tail head => loop(A, Nat.succ(m), Vec.cons(A, m, tail, head))
          |}
          |""".stripMargin
    )
  }

  test("at a variable index, a nested match on the linked scrutinee sees its constructor") {
    runProgram(
      vec +
        """
          |def again (A: Type)(k: Nat)(v: Vec(A, k)): Nat := {
          |  match v returning Nat with
          |  | Vec.nil => Nat.zero
          |  | Vec.cons m tail head => {
          |    match v returning Nat with
          |    | Vec.cons m2 tail2 head2 => (fun (e: Eq(Vec(A, m), tail2, tail)): Nat => m)(Eq.refl(tail))
          |  }
          |}
          |""".stripMargin
    )
  }
}
