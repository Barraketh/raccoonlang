package com.raccoonlang

class PrettyPrinterTests extends munit.FunSuite {
  private def parseCore(src: String): CoreAst.Program =
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) => Elaborator.elab(value, Prelude.test)
      case err: Failure        => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }

  private def axiomType(src: String, name: String): CoreAst.TypeTerm =
    parseCore(src).decls
      .collectFirst { case CoreAst.Decl.AxiomDecl(n, ty, _, _) if n == name => ty }
      .getOrElse(fail(s"Expected axiom $name"))

  test("anonymous constrained capture binder prints as explicit binder") {
    val src = "axiom f : (_: $A in Type) -> A\n"
    val printed = PrettyPrinter.printTerm(axiomType(src, "f"))

    assertEquals(printed, "(_: $A in Type) -> A")
    parseCore(s"axiom g : $printed\n")

    val span = Span(0, 0)
    val ref = CoreAst.LocalRef(0, "A")
    val typeRef = ElabAst.Term.GlobalRef("Type", span)
    val constraint = ElabAst.TypePattern.Type(typeRef)
    val binder = ElabAst.Binder(
      CoreAst.LocalRef(1, "_"),
      ElabAst.BinderType.ConstrainedCapture(ref, constraint, span),
      span
    )
    val pi = ElabAst.Term.Pi(Vector(binder), ElabAst.Term.LocalRef(ref, span), Value.VSort(Value.Level.zero), span)

    assertEquals(PrettyPrinter.printElabTerm(pi), printed)
  }

  test("anonymous type-pattern binder prints as explicit binder") {
    val prelude =
      """
        |inductive Box (A: Type) : Type
        | | mk {A: Type} (a: A) : Box(A)
        |
        |""".stripMargin
    val printed = PrettyPrinter.printTerm(axiomType(prelude + "axiom f : (_: Box($A)) -> A\n", "f"))

    assertEquals(printed, "(_: Box($A)) -> A")
    parseCore(prelude + s"axiom g : $printed\n")
  }

  test("anonymous function domain remains parenthesized in arrow shorthand") {
    val printed = PrettyPrinter.printTerm(axiomType("axiom f : (_: Type -> Type) -> Type\n", "f"))

    assertEquals(printed, "(Type -> Type) -> Type")
    parseCore(s"axiom g : $printed\n")
  }
}
