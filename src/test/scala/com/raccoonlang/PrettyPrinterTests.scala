package com.raccoonlang

class PrettyPrinterTests extends munit.FunSuite with TestSupport {
  override protected val suitePrelude: Prelude.Config = Prelude.test

  /** The elaborated type of axiom `name` in `src`, read as a prelude: only a prelude declares axioms (spec §7.3). */
  private def axiomType(src: String, name: String): CoreAst.Term =
    Prelude
      .fromSource("printer", src)
      .core
      .decls
      .collectFirst { case CoreAst.Decl.AxiomDecl(n, ty, _) if n == name => ty }
      .getOrElse(fail(s"Expected axiom $name"))

  test("implicit binder prints with braces") {
    val src = "axiom f : {A: Type} -> A\n"
    val printed = PrettyPrinter.printTerm(axiomType(src, "f"))

    assertEquals(printed, "{A: Type} -> A")
    axiomType(s"axiom g : $printed\n", "g")
  }

  test("anonymous applied type binder prints as explicit binder") {
    val prelude =
      """
        |inductive Box (A: Type) : Type
        | | mk (a: A) : Box(A)
        |
        |""".stripMargin
    val printed = PrettyPrinter.printTerm(axiomType(prelude + "axiom f : (_: Box(Type)) -> Type\n", "f"))

    assertEquals(printed, "Box(Type) -> Type")
    axiomType(prelude + s"axiom g : $printed\n", "g")
  }

  test("sorts print as their formers") {
    val src = "axiom f : {u: Level} -> (A: Sort { level = succ(u) }) -> (P: Prop) -> Sort { level = max(u, one) }\n"
    val printed = PrettyPrinter.printTerm(axiomType(src, "f"))

    assertEquals(
      printed,
      "{u: Level} -> (A: Sort { level = Level.succ(u) }) -> (P: Prop) -> Sort { level = Level.max(u, Level.one) }"
    )
    axiomType(s"axiom g : $printed\n", "g")
    val two = PrettyPrinter.print(runProgram("{ Sort { level = succ(one) } }"))
    assertEquals(two, "Sort { level = Level.succ(Level.one) }")
    // A constant level prints as its forms, not a numeral, so the sort reads back as itself.
    assert(ValueEquivalence.defEq(runProgram(s"{ $two }"), runProgram("{ Sort { level = succ(one) } }")))
    assertEquals(PrettyPrinter.print(runProgram("{ Sort { level = one } }")), "Type")
  }

  test("a sort prints the kind and scope it does not leave at their defaults") {
    val src = "axiom f : (l: Lifetime) -> (A: Type { scope = union(l, empty), kind = lin }) -> Prop { scope = l }\n"
    val printed = PrettyPrinter.printTerm(axiomType(src, "f"))

    assertEquals(
      printed,
      "(l: Lifetime) -> (A: Type { kind = Kind.lin, scope = Lifetime.union(l, Lifetime.empty) }) -> " +
        "Prop { scope = l }"
    )
    axiomType(s"axiom g : $printed\n", "g")
    assertEquals(PrettyPrinter.print(runProgram("{ Type { kind = lin, scope = empty } }")), "Type { kind = Kind.lin }")
    assertEquals(
      PrettyPrinter.print(runProgram("{ Sort { level = succ(one), kind = unr } }")),
      "Sort { level = Level.succ(Level.one) }"
    )
  }

  test("syntax a value holds prints under its environment, so a bound local prints as its value") {
    def expected(source: String): String =
      PrettyPrinter.print(expectTypeError[TypeMismatch](source, Prelude.default).expected)

    // A function type's binder types name the locals of the scope it was built in.
    assertEquals(expected("def f (A: Type): Type := (x: A) -> A\n\ndef bad : f(Nat) := 0\n"), "(x: Nat) -> Nat")
    // A stuck selector prints its argument for the parameter that stands for it, through eta or its own match.
    val box = "struct Box : Type\n | mk (n: Nat) (m: Nat) : Box\n\n"
    assertEquals(
      expected(box + "def bad (b: Box): Eq(Nat, Box.n(b), 3) := Eq.refl(3)\n"),
      "Eq(Nat, match b returning Nat with | Box.mk x0 x1 => x0, 3)"
    )
    val sized = "struct Sized indices (k: Nat) : Type\n | mk (k: Nat) (v: Nat) : Sized(k)\n\n"
    assertEquals(
      expected(sized + "def bad (s: Sized(0)): Eq(Nat, Sized.v(s), 3) := Eq.refl(3)\n"),
      "Eq(Nat, match s returning Nat with | Sized.mk k v => v, 3)"
    )
    // A local bound to a stuck match prints as that match, parenthesized as a scrutinee.
    val stacked =
      "def pred (n: Nat): Nat := match n returning Nat with\n | .zero => 0\n | .succ k => k\n\n" +
        "def two (n: Nat): Nat := {\n  let m := pred(n)\n  match m returning Nat with\n  | .zero => 1\n  | .succ j => 2\n}\n\n" +
        "def bad (n: Nat): Eq(Nat, two(n), 3) := Eq.refl(3)\n"
    assertEquals(
      expected(stacked),
      "Eq(Nat, match (match n returning Nat with | Nat.zero => 0 | Nat.succ k => k) returning Nat with " +
        "| Nat.zero => 1 | Nat.succ j => 2, 3)"
    )
  }

  test("a selector's parameter is self, unless that would capture a name its declaration mentions") {
    val box = "struct Box : Type\n | mk (n: Nat) : Box\n\ndef bad : Nat := Box.n\n"
    assertEquals(PrettyPrinter.print(expectTypeError[TypeMismatch](box, Prelude.default).actual), "(self: Box) -> Nat")
    val named = "def self : Type := Nat\n\nstruct Box : Type\n | mk (n: self) : Box\n\n"
    assertEquals(PrettyPrinter.print(runProgram(named + "{ Box.n(Box.mk(4)) }", Prelude.default)), "4")
    assertEquals(
      PrettyPrinter.print(expectTypeError[TypeMismatch](named + "def bad : Nat := Box.n\n", Prelude.default).actual),
      "(self1: Box) -> Nat"
    )
  }

  test("anonymous function domain remains parenthesized in arrow shorthand") {
    val printed = PrettyPrinter.printTerm(axiomType("axiom f : (_: Type -> Type) -> Type\n", "f"))

    assertEquals(printed, "(Type -> Type) -> Type")
    axiomType(s"axiom g : $printed\n", "g")
  }
}
