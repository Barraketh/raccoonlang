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
    // A stuck selector prints as its call, with its argument for the parameter that stands for it, whether it is
    // stuck in structure eta's projection or in its own match.
    val box = "struct Box : Type\n | mk (n: Nat) (m: Nat) : Box\n\n"
    assertEquals(expected(box + "def bad (b: Box): Eq(Nat, Box.m(b), 3) := Eq.refl(3)\n"), "Eq(Nat, Box.m(b), 3)")
    val sized = "struct Sized indices (k: Nat) : Type\n | mk (k: Nat) (v: Nat) : Sized(k)\n\n"
    assertEquals(
      expected(sized + "def bad (s: Sized(0)): Eq(Nat, Sized.v(s), 3) := Eq.refl(3)\n"),
      "Eq(Nat, Sized.v(s), 3)"
    )
    // A match that projects no field prints as itself.
    val constant = "def zero (s: Sized(0)): Nat := match s returning Nat with\n | .mk k v => 0\n\n"
    assertEquals(
      expected(sized + constant + "def bad (s: Sized(0)): Eq(Nat, zero(s), 3) := Eq.refl(3)\n"),
      "Eq(Nat, match s returning Nat with | Sized.mk k v => 0, 3)"
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

  // Grouping is part of a function type's identity, so a function type in codomain position is parenthesized: bare, it
  // would read back as part of the enclosing group, and a closure there would be misplaced (spec §1).
  test("a function-type codomain stays parenthesized, so a printed type reads back as the same type") {
    val types = Vector(
      "Type -> (Type -> Type)" -> "Type -> (Type -> Type)",
      "(A: Type) -> ((x: A) -> A)" -> "(A: Type) -> ((x: A) -> A)",
      "(l: Lifetime) -> Type -> ({ scope = l } Type -> Type)" -> "(l: Lifetime) -> Type -> ({ scope = l } Type -> Type)",
      "Type -> Type -> Type" -> "Type -> Type -> Type"
    )
    // The binder groups down a chain of codomains.
    def groups(term: CoreAst.Term): Vector[Int] = term match {
      case CoreAst.Term.Pi(binders, out, _, _, _, _) => binders.length +: groups(out)
      case _                                         => Vector.empty
    }
    types.foreach { case (written, printed) =>
      val core = axiomType(s"axiom f : $written\n", "f")
      assertEquals(PrettyPrinter.printTerm(core), printed)
      assertEquals(groups(axiomType(s"axiom g : $printed\n", "g")), groups(core))
    }
    def actual(source: String): String =
      PrettyPrinter.print(expectTypeError[TypeMismatch](source, Prelude.default).actual)
    assertEquals(actual("def bad (g: Nat -> (Nat -> Nat)): Nat := g\n"), "Nat -> (Nat -> Nat)")
    assertEquals(
      actual("def bad (l: Lifetime)(g: Nat -> ({ scope = l } Nat -> Nat)): Nat := g\n"),
      "Nat -> ({ scope = l } Nat -> Nat)"
    )
    assertEquals(actual("def bad (g: Nat -> Nat -> Nat): Nat := g\n"), "Nat -> Nat -> Nat")
  }

  // Printing is a loop over an explicit stack (PROOF_BY_EVALUATION §2.2); these pin what it prints for each kind of
  // value, as printing did when it recursed.
  test("each kind of value prints as source") {
    val values = Vector(
      "{ Option.some(3) }" -> "Option.some(3)",
      "{ Option.none(Nat) }" -> "Option.none",
      "{ Prod.mk(1, Bool.true) }" -> "Prod.mk(1, Bool.true)",
      "{ List.cons(1, List.cons(2, List.nil(Nat))) }" -> "List.cons(1, List.cons(2, List.nil))",
      "{ Nat.add }" -> "Nat.add",
      "{ fun (A: Type)(x: A): A => x }" -> "fun (A: Type) (x: A) => …",
      "{ (A: Type) -> (x: A) -> Eq(A, x, x) }" -> "(A: Type) -> (x: A) -> Eq(A, x, x)",
      "{ (l: Lifetime) -> Type -> ({ scope = l } Type -> Type) }" ->
        "(l: Lifetime) -> Type -> ({ scope = l } Type -> Type)",
      "{ Type { kind = lin } }" -> "Type { kind = Kind.lin }",
      "{ 1267650600228229401496703205376 }" -> "1267650600228229401496703205376",
      "{ Eq.refl(3) }" -> "Eq.refl(3)"
    )
    values.foreach { case (source, printed) =>
      assertEquals(PrettyPrinter.print(runProgram(source, Prelude.default)), printed)
    }
    // Neutral values: a native operation's application, a stuck call, a stuck selector, and an applied variable.
    val expected = Vector(
      "def bad (x: Nat): Eq(Nat, Nat.add(x, 2000), 0) := Eq.refl(0)\n" -> "Eq(Nat, Nat.add(x, 2000), 0)",
      "def bad (xs: List(Nat)): Eq(Nat, List.length(xs), 3) := Eq.refl(3)\n" -> "Eq(Nat, List.length(xs), 3)",
      "def bad (p: Prod(Nat, Bool)): Eq(Nat, Prod.fst(p), 3) := Eq.refl(3)\n" -> "Eq(Nat, Prod.fst(p), 3)",
      "def bad (f: Nat -> Nat)(x: Nat): Eq(Nat, f(x), 3) := Eq.refl(3)\n" -> "Eq(Nat, f(x), 3)"
    )
    expected.foreach { case (source, printed) =>
      assertEquals(PrettyPrinter.print(expectTypeError[TypeMismatch](source, Prelude.default).expected), printed)
    }
    val proposition = runProgram("{ Or(True, True) }", Prelude.default)
    assertEquals(PrettyPrinter.print(Value.VProof(proposition)), "‹proof of Or(True, True)›")
  }

  test("deep values and deep syntax print without host stack") {
    val env = Prelude.default.checkedEnv
    val nat = env("Nat")
    val depth = 200000
    val x = FreshVar.freshVar("x", nat)
    val sum = (1 to depth).foldLeft[Value](x) { (acc, _) =>
      Value.VApp(env("Nat.add"), Vector(acc, Value.VPacked.nat(1, nat)), nat, DepSet(x.id))
    }
    assertEquals(onDefaultStack(PrettyPrinter.print(sum)), "Nat.add(" * depth + "x" + ", 1)" * depth)
    assertEquals(
      onDefaultStack(PrettyPrinter.print(Value.Level.const(depth))),
      "Level.succ(" * (depth - 1) + "Level.one" + ")" * (depth - 1)
    )
    val names = Vector.tabulate(depth)(idx => s"l$idx")
    val union = Value.Lifetime.union(
      names.map(name =>
        FreshVar.freshValue(name, Value.LifetimeTpe)._2 match {
          case lifetime: Value.Lifetime => lifetime
          case other                    => fail(s"Expected a lifetime variable, got $other")
        }
      )
    )
    assertEquals(
      onDefaultStack(PrettyPrinter.print(union)),
      "Lifetime.union(" * (depth - 1) + names.head + names.tail.map(name => s", $name)").mkString
    )
    val span = Span(0, 0)
    val nested = (1 to depth).foldLeft[CoreAst.Term](CoreAst.Term.NatLit(0, span)) { (acc, _) =>
      CoreAst.Term.App(CoreAst.Term.GlobalRef("f", span), Vector(acc), span)
    }
    assertEquals(onDefaultStack(PrettyPrinter.printTerm(nested)), "f(" * depth + "0" + ")" * depth)
  }
}
