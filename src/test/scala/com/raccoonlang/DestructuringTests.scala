package com.raccoonlang

/**
 * Destructuring (docs/implemented/PAIRS_AND_PRELUDE.md §3): `let (a, b) := e` binds a local for each stored field of
 * `e` 's value, transparently, to its eta view, for a family with one constructor, no indices, no recursive field, and
 * outside `Prop` under every instantiation. Each rule has an admitted program and the smallest mutation that reaches
 * its diagnostic.
 */
class DestructuringTests extends munit.FunSuite with TestSupport {

  private def evaluatesTo(source: String, expected: String)(implicit loc: munit.Location): Unit =
    assertEquals(PrettyPrinter.print(runProgram(source)), expected)

  /** Where the single diagnostic `source` reports starts, as the text from there on. */
  private def reportedAt(source: String)(implicit loc: munit.Location): String =
    source.substring(interceptDiagnostic(typecheckDecls(source)).span.get.start)

  private val nestedValue = "Prod.mk(1, Prod.mk(2, 3))"

  private val triple =
    """
      |struct Triple : Type
      | | mk (a: Nat)(b: Nat)(c: Bool) : Triple
      |""".stripMargin

  test("a destructuring binds each stored field of a Prod or a struct, in order") {
    evaluatesTo("{\n  let (n, b) := Prod.mk(3, Bool.true)\n  Prod.mk(b, n)\n}\n", "Prod.mk(Bool.true, 3)")
    evaluatesTo(
      triple + "{\n  let (x, y, z) := Triple.mk(1, 2, Bool.false)\n  Prod.mk(z, Nat.sub(y, x))\n}\n",
      "Prod.mk(Bool.false, 1)"
    )
    // Names shadow earlier locals, the scrutinee's included.
    evaluatesTo("{\n  let p := Prod.mk(1, 2)\n  let (p, q) := p\n  Nat.add(p, Nat.mul(q, 10))\n}\n", "21")
    // A `_` component binds an anonymous local.
    evaluatesTo(triple + "{\n  let (_, y, _) := Triple.mk(1, 2, Bool.false)\n  y\n}\n", "2")
  }

  test("a nested pattern takes a nested value apart, with no flattening") {
    evaluatesTo(
      s"{\n  let (e, (a, b)) := $nestedValue\n  Nat.add(e, Nat.add(Nat.mul(a, 10), Nat.mul(b, 100)))\n}\n",
      "321"
    )
    evaluatesTo(s"{\n  let (e, (_, b)) := $nestedValue\n  Nat.add(e, b)\n}\n", "4")
    evaluatesTo(s"{\n  let (e, t) := $nestedValue\n  let (a, b) := t\n  Nat.add(e, Nat.add(a, b))\n}\n", "6")
    // Patterns do not flatten: three components against a pair whose second field is a pair.
    assertEquals(
      expectOnly[ArityMismatch](typecheckDecls(s"def x : Nat := {\n  let (e, a, b) := $nestedValue\n  e\n}\n")),
      ArityMismatch(2, 3, ArityMismatch.Fields)
    )
  }

  test("a pattern has a component for each stored field") {
    typecheckDecls(triple + "def x (t: Triple): Bool := {\n  let (a, b, c) := t\n  c\n}\n")
    assertEquals(
      expectOnly[ArityMismatch](typecheckDecls(triple + "def x (t: Triple): Nat := {\n  let (a, b) := t\n  a\n}\n")),
      ArityMismatch(3, 2, ArityMismatch.Fields)
    )
    val tooMany = "def x (p: Prod(Nat, Nat)): Nat := {\n  let (a, b, c) := p\n  a\n}\n"
    assertEquals(expectOnly[ArityMismatch](typecheckDecls(tooMany)), ArityMismatch(2, 3, ArityMismatch.Fields))
    assert(reportedAt(tooMany).startsWith("(a, b, c) := p"))
    assertEquals(
      interceptDiagnostic(typecheckDecls(tooMany)).getMessage,
      "Cannot bind the constructor's fields - expected 2 fields, got 3"
    )
  }

  test("a name occurs once in a pattern, at any depth") {
    typecheckDecls("def x (p: Prod(Nat, Nat)): Nat := {\n  let (_, _) := p\n  0\n}\n")
    val repeated = "def x (p: Prod(Nat, Nat)): Nat := {\n  let (a, a) := p\n  a\n}\n"
    assertEquals(expectOnly[AlreadyDefined](typecheckDecls(repeated)), AlreadyDefined("a"))
    assert(reportedAt(repeated).startsWith("a) := p"))
    val nested = s"def x : Nat := {\n  let (a, (b, a)) := $nestedValue\n  a\n}\n"
    assertEquals(expectOnly[AlreadyDefined](typecheckDecls(nested)), AlreadyDefined("a"))
    // Separate lets may rebind a name, as shadowing.
    typecheckDecls(s"def x : Nat := {\n  let (a, t) := $nestedValue\n  let (a, b) := t\n  a\n}\n")
  }

  test("an annotated destructuring checks its value against the annotation") {
    typecheckDecls("def x : Nat := {\n  let (a, b) : Prod(Nat, Bool) := Prod.mk(1, Bool.true)\n  a\n}\n")
    expectOnly[TypeMismatch](
      typecheckDecls("def x : Nat := {\n  let (a, b) : Prod(Nat, Nat) := Prod.mk(1, Bool.true)\n  a\n}\n")
    )
  }

  test("only a one-constructor, index-free, nonrecursive family outside Prop is destructurable") {
    def program(binders: String, tpe: String): String =
      s"def x $binders(v: $tpe): Nat := {\n  let (a, b) := v\n  0\n}\n"
    def notDestructurable(decls: String, binders: String, tpe: String)(implicit loc: munit.Location): String =
      PrettyPrinter.print(expectOnly[NotDestructurable](typecheckDecls(decls + program(binders, tpe))).tpe)

    val families =
      """
        |inductive Sized indices (n: Nat) : Type
        | | mk (n: Nat)(x: Nat) : Sized(n)
        |
        |inductive Tree : Type
        | | node (x: Nat)(kids: Nat -> Tree) : Tree
        |
        |struct Loose {u: Level}{v: Level}(A: Type { level = u})(B: Type { level = v}) : Type { level = max(u, v) }
        | | mk (a: A)(b: B) : Loose(A, B)
        |
        |def NatPair : Type := Prod(Nat, Nat)
        |""".stripMargin
    // A type a transparent definition computes to an instance is one.
    typecheckDecls(families + program("", "NatPair"))
    typecheckDecls(families + program("{A: Type}{B: Type}", "Prod(A, B)"))
    assertEquals(notDestructurable(families, "", "Sum(Nat, Nat)"), "Sum(Nat, Nat)")
    assertEquals(notDestructurable(families, "", "Option(Nat)"), "Option(Nat)")
    assertEquals(notDestructurable(families, "", "Sized(0)"), "Sized(0)")
    assertEquals(notDestructurable(families, "", "Tree"), "Tree")
    assertEquals(notDestructurable(families, "", "List(Nat)"), "List(Nat)")
    assertEquals(notDestructurable(families, "", "And(True, True)"), "And(True, True)")
    assertEquals(notDestructurable(families, "{A: Type}", "A"), "A")
    assertEquals(notDestructurable(families, "", "Nat -> Nat"), "Nat -> Nat")
    assertEquals(notDestructurable(families, "(F: Nat -> Type)", "F(0)"), "F(0)")
    // An instance at a level that may be zero is outside Prop where it is checked.
    typecheckDecls(families + program("{u: Level}{A: Type { level = u}}", "Loose(A, A)"))
    expectOnly[ImplicitReconstructionFailed](typecheckDecls(families + program("", "Loose(True, True)")))
    // Reported where the value's type comes from: the annotation when one is written.
    assert(reportedAt(families + program("", "Sum(Nat, Nat)")).startsWith("v\n"))
    val annotated = "def x : Nat := {\n  let (a, b) : Option(Nat) := Option.none(Nat)\n  0\n}\n"
    assert(reportedAt(annotated).startsWith("Option(Nat) := "))
  }

  test("a level-polymorphic destructuring rejects proposition components") {
    val defs =
      "def count {u: Level}{v: Level}{A: Type { level = u }}{B: Type { level = v }}(p: Prod(A, B)): Nat := { let (a, b) := p\n 2 }\n"
    evaluatesTo(defs + "{ count(Prod.mk(1, Bool.true)) }\n", "2")
    expectOnly[ImplicitReconstructionFailed](
      typecheckDecls(defs + "def bad : Nat := count(Prod.mk(True.intro, True.intro))\n")
    )
  }

  test("the scrutinee is a use, and each destructured field is tracked by its own kind") {
    val families =
      """
        |inductive Tok (l: Lifetime) : Type { kind = lin, scope = l }
        | | mk : Tok(l)
        |
        |inductive Two (l: Lifetime) : Type { kind = lin, scope = l }
        | | mk (a: Tok(l))(b: Tok(l)) : Two(l)
        |
        |inductive Nest (l: Lifetime) : Type { kind = lin, scope = l }
        | | mk (t: Tok(l))(w: Two(l))(n: Nat) : Nest(l)
        |
        |def eat {l: Lifetime}(t: Tok(l)): Nat := match t returning Nat with
        | | Tok.mk => 1
        |
        |def drop {l: Lifetime}(w: Two(l)): Nat := match w returning Nat with
        | | Two.mk a b => Nat.add(eat(a), eat(b))
        |""".stripMargin
    def both(body: String): String =
      families + s"def both {l: Lifetime}(w: Two(l)): Nat := {\n  let (a, b) := w\n  $body\n}\n"

    evaluatesTo(
      both("Nat.add(eat(a), eat(b))") + "{ scope l => both(Two.mk(Tok.mk(l), Tok.mk(l))) }\n",
      "2"
    )
    assertEquals(expectOnly[LinearUnused](typecheckDecls(both("eat(a)"))), LinearUnused("b"))
    assertEquals(
      expectOnly[LinearReused](typecheckDecls(both("Nat.add(eat(a), Nat.add(eat(a), eat(b)))"))),
      LinearReused("a")
    )
    // Destructuring consumes the scrutinee.
    assertEquals(
      expectOnly[LinearReused](typecheckDecls(both("Nat.add(eat(a), Nat.add(eat(b), drop(w)))"))),
      LinearReused("w")
    )
    val wildcard = families + "def first {l: Lifetime}(w: Two(l)): Nat := {\n  let (a, _) := w\n  eat(a)\n}\n"
    assertEquals(expectOnly[LinearUnused](typecheckDecls(wildcard)), LinearUnused("_"))
    assert(reportedAt(wildcard).startsWith("_) := w"))

    // Through a nesting, each level consumes what it takes apart, and an unrestricted field is not tracked.
    def nest(pattern: String, body: String): String =
      both("Nat.add(eat(a), eat(b))") +
        s"def all {l: Lifetime}(x: Nest(l)): Nat := {\n  let $pattern := x\n  $body\n}\n"
    typecheckDecls(nest("(t, (a, b), n)", "Nat.add(eat(t), Nat.add(eat(a), eat(b)))"))
    typecheckDecls(nest("(t, w, _)", "Nat.add(eat(t), both(w))"))
    assertEquals(
      expectOnly[LinearUnused](typecheckDecls(nest("(t, (a, _), n)", "Nat.add(eat(t), eat(a))"))),
      LinearUnused("_")
    )
    assertEquals(
      expectOnly[LinearReused](
        typecheckDecls(nest("(t, (a, b), n)", "Nat.add(eat(t), Nat.add(eat(a), Nat.add(eat(b), eat(t))))"))
      ),
      LinearReused("t")
    )
  }

  test("a destructuring is a match, so it opens a sealed family only in its module") {
    val module =
      """
        |sealed struct Box : Type
        | | mk (n: Nat)(m: Nat) : Box
        |
        |def box (n: Nat): Box := Box.mk(n, n)
        |""".stripMargin
    val client = "def sum (b: Box): Nat := {\n  let (n, m) := b\n  Nat.add(n, m)\n}\n\n{ sum(box(2)) }\n"
    assertEquals(inside(module, client).map(PrettyPrinter.print), Some("4"))
    assertEquals(expectOnly[SealedConstructor](outside(module, client)), SealedConstructor("Box", None))
    assertEquals(outside(module.replace("sealed ", ""), client).map(PrettyPrinter.print), Some("4"))
  }

  test("a field is typed at the scrutinee: a dependent field at its first projection") {
    val tag = "inductive Tag (n: Nat) : Type\n | mk : Tag(n)\n\ndef fam (n: Nat): Type := Tag(n)\n\n"
    def second(result: String): String =
      tag + s"def second (p: Sigma(Nat, fam)): $result := {\n  let (n, t) := p\n  t\n}\n"
    typecheckDecls(second("Tag(p.fst)"))
    typecheckDecls(second("Tag(Sigma.fst(p))"))
    expectOnly[TypeMismatch](typecheckDecls(second("Tag(0)")))
  }

  test("a destructured name is transparent: a type about it is a statement about the scrutinee") {
    def program(claim: String, proof: String): String =
      s"def same (p: Prod(Nat, Nat)): Nat := {\n  let (a, b) := p\n  let h : $claim := $proof\n  b\n}\n"
    typecheckDecls(program("Eq(Nat, a, p.fst)", "Eq.refl(a)"))
    typecheckDecls(program("Eq(Prod(Nat, Nat), Prod.mk(a, b), p)", "Eq.refl(p)"))
    expectOnly[TypeMismatch](typecheckDecls(program("Eq(Nat, a, p.snd)", "Eq.refl(a)")))
  }

  test("a destructuring of a neutral value reads its eta view, and its residual re-evaluates when applied") {
    val defs =
      """
        |def firstOf (p: Prod(Nat, Nat)): Nat := {
        |  let (a, _) := p
        |  a
        |}
        |
        |def adder (p: Prod(Nat, Nat)): Nat -> Nat := fun (m: Nat): Nat => {
        |  let (a, b) := p
        |  Nat.add(Nat.add(a, b), m)
        |}
        |
        |def viaEta (p: Prod(Nat, Nat)): Eq(Nat, firstOf(p), p.fst) := Eq.refl(p.fst)
        |""".stripMargin
    evaluatesTo(defs + "{ Nat.add(firstOf(Prod.mk(3, 4)), adder(Prod.mk(1, 2))(10)) }\n", "16")
    expectOnly[TypeMismatch](typecheckDecls(defs.replace("Eq.refl(p.fst)", "Eq.refl(p.snd)")))
  }

  test("a value whose type a branch refines to an instance is destructured there, and evaluates once it is taken") {
    def program(body: String): String =
      """
        |inductive Tag indices (A: Type) : Type
        | | isProd : Tag(Prod(Nat, Nat))
        |
        |def f (A: Type)(x: A)(t: Tag(A)): Nat := BODY
        |
        |def h (B: Type)(y: B)(s: Tag(B)): Nat := match s returning Nat with
        | | Tag.isProd => f(B, y, s)
        |
        |{ Nat.add(h(Prod(Nat, Nat), Prod.mk(4, 5), Tag.isProd), f(Prod(Nat, Nat), Prod.mk(1, 5), Tag.isProd)) }
        |""".stripMargin.replace("BODY", body)
    val destructure = "{\n   let (a, b) := x\n   a\n }"
    evaluatesTo(program(s"match t returning Nat with\n | Tag.isProd => $destructure"), "5")
    assertEquals(PrettyPrinter.print(expectOnly[NotDestructurable](typecheckDecls(program(destructure))).tpe), "A")
  }

  test("a destructured field of a pattern field is a structural subterm of the decreasing argument") {
    def program(recurse: String): String =
      s"""
         |inductive Tree : Type
         | | leaf : Tree
         | | node (kids: Prod(Tree, Tree)) : Tree
         |
         |def size (t: Tree): Nat decreases structural(t) := match t returning Nat with
         | | Tree.leaf => 1
         | | Tree.node kids => {
         |   let (l, r) := kids
         |   Nat.add(size(l), size($recurse))
         | }
         |
         |{ size(Tree.node(Prod.mk(Tree.leaf, Tree.node(Prod.mk(Tree.leaf, Tree.leaf))))) }
         |""".stripMargin
    evaluatesTo(program("r"), "3")
    expectOnly[NonDecreasingRecursiveCall](typecheckDecls(program("t")))
  }

  test("a destructuring prints as written, a nested one included, before checking and after") {
    val lets = "let (a, _) := p\n  let ((b, c), (d, (e, f))) := q\n  let g := b"
    val source =
      s"def x (p: Prod(Nat, Nat))(q: Prod(Prod(Nat, Nat), Prod(Nat, Prod(Nat, Nat)))): Nat := {\n  $lets\n  a\n}\n"
    val body = parse(source).decls.collectFirst { case CoreAst.Decl.ConstDecl("x", _, body, _, _) => body }
    val elaborated = body match {
      case Some(CoreAst.ConstBody.TermBody(lam: CoreAst.Term.Lam)) => lam
      case other                                                   => fail(s"Expected a lambda, got $other")
    }
    val printed = s"{ ${lets.replace("\n  ", "\n")} \n a }"
    assertEquals(PrettyPrinter.printTerm(elaborated.body), printed)
    TypeChecker.checkTerm(elaborated, Prelude.default.checkedEnv).residual match {
      case checked: CoreAst.Term.Lam => assertEquals(PrettyPrinter.printTerm(checked.body), printed)
      case other                     => fail(s"Expected a checked lambda, got $other")
    }
    // A destructuring of a named field stays its own let.
    val separate = "def y (q: Prod(Prod(Nat, Nat), Nat)): Nat := {\n  let (t, d) := q\n  let (b, c) := t\n  b\n}\n"
    parse(separate).decls.collectFirst {
      case CoreAst.Decl.ConstDecl("y", _, CoreAst.ConstBody.TermBody(lam: CoreAst.Term.Lam), _, _) => lam.body
    } match {
      case Some(body) => assertEquals(PrettyPrinter.printTerm(body), "{ let (t, d) := q\nlet (b, c) := t \n b }")
      case None       => fail("Expected a lambda")
    }
  }

}
