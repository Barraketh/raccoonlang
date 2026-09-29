package com.raccoonlang

/**
 * Siblings of a `mutual` block at their own sorts (spec §5.1): each family is checked against its own declared sort,
 * and a sibling is read by its declared classifier. Where siblings hold each other, the per-field bounds force
 * compatible sorts and name the field. Everything computed for a whole block (proof recovery, the `Prop` elimination
 * restriction, structural descent, structure eta, positivity, literal layouts) reads each family's own sort.
 */
class MutualSiblingSortTests extends munit.FunSuite with TestSupport {

  /** A linear token that holds an unrestricted factory of tokens; a function type is at its closure kind. */
  private val tokens =
    """
      |mutual {
      |  inductive Tok : Type { kind = lin }
      |   | mk (next: Factory) : Tok
      |
      |  inductive Factory : Type
      |   | mk (make: Unit -> Tok) : Factory
      |}
      |
      |def eat (t: Tok): Nat := match t returning Nat with
      | | Tok.mk n => 0
      |
      |def mint (f: Factory): Tok := match f returning Tok with
      | | Factory.mk make => make(Unit.unit)
      |""".stripMargin

  /** A data type and a proposition about it, each holding the other. */
  private val trees =
    """
      |mutual {
      |  inductive Tree : Type
      |   | leaf : Tree
      |   | node (l: Tree) (r: Tree) (ok: Balanced) : Tree
      |
      |  inductive Balanced : Prop
      |   | intro (witness: Tree) : Balanced
      |}
      |""".stripMargin

  test("a linear family and an unrestricted factory of it share a block, and its tokens stay linear") {
    typecheckDecls(
      tokens +
        """
          |def once (f: Factory): Nat := eat(mint(f))
          |
          |def each (f: Factory): Nat := Nat.add(eat(mint(f)), eat(mint(f)))
          |
          |def forward (t: Tok): Factory := match t returning Factory with
          | | Tok.mk n => n
          |""".stripMargin
    )
    val twice = tokens + "\ndef twice (f: Factory): Nat := {\n  let t := mint(f)\n  Nat.add(eat(t), eat(t))\n}\n"
    assertEquals(expectOnly[LinearReused](typecheckDecls(twice)), LinearReused("t"))
    // The factory's function is unrestricted, so it cannot hand out one token many times.
    expectOnly[TypeMismatch](
      typecheckDecls(tokens + "\ndef smuggle (t: Tok): Factory := Factory.mk(fun (u: Unit): Tok => t)\n")
    )
  }

  test("siblings holding each other are bounded at each field") {
    def block(first: String, firstField: String, second: String, secondField: String): String =
      s"""
         |mutual {
         |  inductive A : $first
         |   | mk (b: $firstField) : A
         |   | stop : A
         |
         |  inductive B : $second
         |   | mk (a: $secondField) : B
         |}
         |""".stripMargin

    val kinds = expectOnly[KindExceeded](typecheckDecls(block("Type { kind = lin }", "B", "Type", "A")))
    assertEquals((kinds.declaration, kinds.part), ("Family B", "field B.mk.a : A"))
    val levels = expectOnly[InductiveUniverseTooSmall](
      typecheckDecls(block("Type", "B", "Sort { level = succ(one) }", "A"))
    )
    assertEquals((levels.inductive, levels.where), ("A", "A.mk.b"))
    // A proposition holds no linear field, a linear sibling's included.
    val proposition = expectOnly[KindExceeded](typecheckDecls(block("Type { kind = lin }", "B", "Prop", "A")))
    assertEquals(proposition.part, "field B.mk.a : A")
  }

  test("a proposition holding a data sibling eliminates like any proposition holding data") {
    val size =
      """
        |def size (t: Tree): Nat decreases structural(t) := match t returning Nat with
        | | Tree.leaf => 0
        | | Tree.node l r ok => Nat.succ(Nat.add(size(l), size(r)))
        |
        |def small (b: Balanced): True := match b returning True with
        | | Balanced.intro w => True.intro
        |
        |{ size(Tree.node(Tree.leaf, Tree.leaf, Balanced.intro(Tree.leaf))) }
        |""".stripMargin
    assert(ValueEquivalence.defEq(runProgram(trees + size), runProgram("{ 1 }")))

    val witness = "\ndef witness (b: Balanced): Tree := match b returning Tree with\n | Balanced.intro w => w\n"
    val nonMutual =
      """
        |inductive Tree : Type
        | | leaf : Tree
        |
        |inductive Balanced : Prop
        | | intro (witness: Tree) : Balanced
        |""".stripMargin
    assertEquals(
      expectOnly[PropEliminationRestricted](typecheckDecls(trees + witness)).inductive,
      expectOnly[PropEliminationRestricted](typecheckDecls(nonMutual + witness)).inductive
    )
  }

  test("proofs of a propositional sibling are irrelevant, inside a data sibling too") {
    typecheckDecls(
      trees +
        """
          |def proofs (s: Tree)(t: Tree): Eq(Balanced, Balanced.intro(s), Balanced.intro(t)) :=
          |  Eq.refl(Balanced.intro(s))
          |
          |def nodes (l: Tree)(r: Tree)(p: Balanced)(q: Balanced): Eq(Tree, Tree.node(l, r, p), Tree.node(l, r, q)) :=
          |  Eq.refl(Tree.node(l, r, p))
          |""".stripMargin
    )
  }

  test("proof recovery reads each sibling's own sort") {
    // `Sound`'s field is a proof of its propositional sibling, so it is recovered and `Sound` eliminates into data;
    // `Opt` is a proposition exactly at the instances whose level is zero, and its data sibling holds such proofs.
    val result = runProgram(
      """
        |mutual {
        |  inductive Tree : Type
        |   | leaf : Tree
        |   | node (ok: Balanced) : Tree
        |
        |  inductive Balanced : Prop
        |   | intro (w: Tree) : Balanced
        |
        |  inductive Sound : Prop
        |   | intro (b: Balanced) : Sound
        |}
        |
        |def fromSound (s: Sound): Nat := match s returning Nat with
        | | Sound.intro b => 7
        |
        |mutual {
        |  inductive Opt {u: Level}(A: Sort { level = u }) : Sort { level = u }
        |   | none : Opt(A)
        |
        |  inductive Box {u: Level}(A: Sort { level = u }) : Sort { level = max(one, u) }
        |   | mk (o: Opt(A)) (a: A) : Box(A)
        |}
        |
        |def fromOpt (o: Opt(True)): Nat := match o returning Nat with
        | | Opt.none => 3
        |
        |def boxed : Box(True) := Box.mk(Opt.none(True), True.intro)
        |
        |{ Nat.add(fromSound(Sound.intro(Balanced.intro(Tree.leaf))), fromOpt(Opt.none(True))) }
        |""".stripMargin
    )
    assert(ValueEquivalence.defEq(result, runProgram("{ 10 }")))
  }

  test("structural recursion crosses siblings at different kinds, but not a propositional sibling's proof") {
    val spent = runProgram(
      """
        |mutual {
        |  inductive Tok : Type { kind = lin }
        |   | mk (next: Factory) : Tok
        |   | last : Tok
        |
        |  inductive Factory : Type
        |   | mk (make: Unit -> Tok) : Factory
        |}
        |
        |mutual {
        |  def spend (t: Tok): Nat decreases structural(t) := match t returning Nat with
        |   | Tok.mk f => Nat.succ(drain(f))
        |   | Tok.last => 0
        |
        |  def drain (f: Factory): Nat decreases structural(f) := match f returning Nat with
        |   | Factory.mk make => spend(make(Unit.unit))
        |}
        |
        |{ spend(Tok.mk(Factory.mk(fun (u: Unit): Tok => Tok.last))) }
        |""".stripMargin
    )
    assert(ValueEquivalence.defEq(spent, runProgram("{ 1 }")))

    val deep =
      """
        |def deep (t: Tree): True decreases structural(t) := match t returning True with
        | | Tree.leaf => True.intro
        | | Tree.node l r ok => {
        |   match ok returning True with
        |   | Balanced.intro w => deep(w)
        | }
        |""".stripMargin
    assertEquals(expectOnly[NonDecreasingRecursiveCall](typecheckDecls(trees + deep)).function, "deep")
  }

  test("structure eta excludes propositional instances and recursive blocks, whatever the siblings' sorts") {
    typecheckDecls(
      """
        |mutual {
        |  struct Pair : Type
        |   | mk (a: Nat) (b: Nat) : Pair
        |
        |  struct Fact : Prop
        |   | mk (h: True) : Fact
        |}
        |
        |def etaPair (p: Pair): Eq(Pair, p, Pair.mk(p.a, p.b)) := Eq.refl(p)
        |""".stripMargin
    )
    // `Box` holds a proof of `Fine`, which holds a `Box`: the block is recursive, so no family in it has eta.
    expectOnly[TypeMismatch](
      typecheckDecls(
        """
          |mutual {
          |  struct Box : Type
          |   | mk (n: Nat) (ok: Fine) : Box
          |
          |  inductive Fine : Prop
          |   | intro (b: Box) : Fine
          |}
          |
          |def etaBox (b: Box): Eq(Box, b, Box.mk(b.n, b.ok)) := Eq.refl(b)
          |""".stripMargin
      )
    )
  }

  test("strict positivity spans siblings at different sorts") {
    val error = expectOnly[NonStrictlyPositive](
      typecheckDecls(
        """
          |mutual {
          |  inductive T : Type
          |   | mk (f: P -> Nat) : T
          |
          |  inductive P : Prop
          |   | intro (t: T) : P
          |}
          |""".stripMargin
      )
    )
    assertEquals((error.ctor, error.field), ("T.mk", "f"))
  }

  test("the Nat literal layout holds when Nat shares a block with a propositional sibling") {
    val natDecl = "inductive Nat : Type\n | zero : Nat\n | succ (_: Nat) : Nat\n"
    assert(TestSupport.bundledPreludeSource.contains(natDecl))
    val mutualNat =
      """mutual {
        |  inductive Nat : Type
        |   | zero : Nat
        |   | succ (_: Nat) : Nat
        |
        |  inductive Counted : Prop
        |   | intro (n: Nat) : Counted
        |}
        |""".stripMargin
    val prelude = Prelude.fromSource(
      "mutual-nat",
      TestSupport.bundledPreludeSource.replace(natDecl, mutualNat),
      Set(Prelude.ImportPath)
    )
    runProgram("{ Nat.succ(41) }", prelude) match {
      case packed: Value.VPacked => assertEquals(packed.natValue, Some(BigInt(42)))
      case other                 => fail(s"Expected a packed Nat, got $other")
    }
  }
}
