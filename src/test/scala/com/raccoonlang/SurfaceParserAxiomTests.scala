package com.raccoonlang

import com.raccoonlang.SurfaceAst._
import com.raccoonlang.SurfaceParserRec

class SurfaceParserAxiomTests extends munit.FunSuite {
  private def ok(src: String, expect: Decl.Axiom): Unit = {
    SurfaceParserRec.parseDecl(src) match {
      case Right(value: Decl.Axiom) => assertEquals(value, expect)
      case Left(err)                => fail(s"failed to parse: $err\n$src")
      case other                    => fail(s"unexpected parse result: $other")
    }
  }

  // 3) Multi-level params and complex result level
  test("axiom_multi_lparams_and_max") {
    val src =
      """
        |axiom D.{u, v} (A : Type u) (B : Type v) : Type max(u, v)
        |""".stripMargin
    ok(src,
      Decl.Axiom(
        name = "D",
        levelParams = List("u", "v"),
        params = List(
          Binder(SRelevance.Rel, "A", Term.Type(SLevel.Ident("u"))),
          Binder(SRelevance.Rel, "B", Term.Type(SLevel.Ident("v")))
        ),
        resultType = Term.Type(SLevel.Max(SLevel.Ident("u"), SLevel.Ident("v")))
      )
    )
  }

  // 1) Simple axiom
  test("axiom_simple") {
    val src =
      """
        |axiom K : Type 0
        |""".stripMargin
    ok(src,
      Decl.Axiom(
        name = "K",
        levelParams = Nil,
        params = Nil,
        resultType = Term.Type(SLevel.NatLit(0))
      )
    )
  }

  // 2) With level params and binders
  test("axiom_with_lparams_binders") {
    val src =
      """
        |axiom C.{u} (A : Type u) : A -> A -> A
        |""".stripMargin
    ok(src,
      Decl.Axiom(
        name = "C",
        levelParams = List("u"),
        params = List(Binder(SRelevance.Rel, "A", Term.Type(SLevel.Ident("u")))),
        resultType = Term.Forall(
          Binder(SRelevance.Rel, "_", Term.Ident("A")),
          Term.Forall(Binder(SRelevance.Rel, "_", Term.Ident("A")), Term.Ident("A"))
        )
      )
    )
  }
}
