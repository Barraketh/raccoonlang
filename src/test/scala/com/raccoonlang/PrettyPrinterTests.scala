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
    assertEquals(PrettyPrinter.print(runProgram("{ Sort { level = succ(one) } }")), "Sort { level = 2 }")
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
    assertEquals(PrettyPrinter.print(runProgram("{ Sort { level = succ(one), kind = unr } }")), "Sort { level = 2 }")
  }

  test("anonymous function domain remains parenthesized in arrow shorthand") {
    val printed = PrettyPrinter.printTerm(axiomType("axiom f : (_: Type -> Type) -> Type\n", "f"))

    assertEquals(printed, "(Type -> Type) -> Type")
    axiomType(s"axiom g : $printed\n", "g")
  }
}
