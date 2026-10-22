package com.raccoonlang

/** Declared family kinds contain each constructor field's kind; instances retain the declared kind. */
class FamilyKindTests extends munit.FunSuite with TestSupport {
  test("the declared kind contains each field's kind") {
    def program(sort: String): String =
      s"inductive Holder {k: Kind}(A: Type { kind = k }) : $sort\n | mk (held: A) : Holder(A)\n"

    typecheckDecls(program("Type { kind = k }"))
    typecheckDecls(program("Type { kind = lin }"))
    val error = expectOnly[KindExceeded](typecheckDecls(program("Type")))
    assert(PartialFunction.cond(error.part) { case ContainedPart.Field("Holder.mk.held", _) => true }, error.part)
    expectOnly[KindExceeded](
      typecheckDecls("struct Box {k: Kind}(A: Type { kind = k }) : Type\n | mk (value: A) : Box(A)\n")
    )
  }

  test("a family instance has its declared kind under its arguments") {
    val source =
      """
        |inductive Holder {k: Kind}(A: Type { kind = k }) : Type { kind = k }
        | | mk (held: A) : Holder(A)
        |
        |def linear : Type { kind = lin } := Holder({ kind = lin } Nat -> Nat)
        |def plain : Type := Holder(Nat)
        |""".stripMargin

    typecheckDecls(source)
    expectOnly[TypeMismatch](
      typecheckDecls(source.replace("def linear : Type { kind = lin }", "def linear : Type"))
    )
  }

  test("a mutual sibling is checked against its own declared classifier") {
    def program(secondSort: String): String =
      "inductive Token : Type { kind = lin }\n | mk : Token\n\n" +
        s"""mutual {
           |  inductive First : Type { kind = lin }
           |   | mk (second: Second) : First
           |
           |  inductive Second : $secondSort
           |   | stop (token: Token) : Second
           |}
           |""".stripMargin

    typecheckDecls(program("Type { kind = lin }"))
    val error = expectOnly[KindExceeded](typecheckDecls(program("Type")))
    assert(PartialFunction.cond(error.part) { case ContainedPart.Field("Second.stop.token", _) => true }, error.part)
  }

  test("Prop has no fields, and Type retains kind fields") {
    assert(LanguageParser.parseProgram("def bad (P: Prop { kind = lin }): Prop := P\n").isInstanceOf[Failure])
    typecheckDecls("def keep {k: Kind}{A: Type { kind = k }}(x: A): A := x\n")
  }
}
