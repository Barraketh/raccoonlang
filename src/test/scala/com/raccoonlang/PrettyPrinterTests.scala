package com.raccoonlang

class PrettyPrinterTests extends munit.FunSuite with TestSupport {
  override protected val suitePrelude: Prelude.Config = Prelude.test

  private def axiomType(src: String, name: String): CoreAst.Term =
    parse(src).decls
      .collectFirst { case CoreAst.Decl.AxiomDecl(n, ty, _) if n == name => ty }
      .getOrElse(fail(s"Expected axiom $name"))

  test("implicit binder prints with braces") {
    val src = "axiom f : {A: Type} -> A\n"
    val printed = PrettyPrinter.printTerm(axiomType(src, "f"))

    assertEquals(printed, "{A: Type} -> A")
    parse(s"axiom g : $printed\n")
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
    parse(prelude + s"axiom g : $printed\n")
  }

  test("anonymous function domain remains parenthesized in arrow shorthand") {
    val printed = PrettyPrinter.printTerm(axiomType("axiom f : (_: Type -> Type) -> Type\n", "f"))

    assertEquals(printed, "(Type -> Type) -> Type")
    parse(s"axiom g : $printed\n")
  }
}
