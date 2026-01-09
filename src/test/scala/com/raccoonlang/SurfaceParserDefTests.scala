package com.raccoonlang

import com.raccoonlang.SurfaceAst._
import com.raccoonlang.SurfaceParserRec

class SurfaceParserDefTests extends munit.FunSuite {
  private def ok(src: String, expect: Decl.Def): Unit = {
    SurfaceParserRec.parseDecl(src) match {
      case Right(value: Decl.Def) => assertEquals(value, expect)
      case Left(err)              => fail(s"failed to parse: $err\n$src")
      case other                  => fail(s"unexpected parse result: $other")
    }
  }

  test("def_irrelevant_binder_param") {
    val src =
      """
        |inline def ignoreProof (A : Type 0) (x : A) (.p : Eq A x x) : A := x
        |""".stripMargin
    val expect = Decl.Def(
      isInline = true,
      name = "ignoreProof",
      levelParams = Nil,
      params = List(
        Binder(SRelevance.Rel, "A", Term.Type(SLevel.NatLit(0))),
        Binder(SRelevance.Rel, "x", Term.Ident("A")),
        Binder(SRelevance.Irr, "p",
          Term.App(
            Term.App(
              Term.App(Term.Ident("Eq"), Term.Ident("A")),
              Term.Ident("x")
            ),
            Term.Ident("x")
          )
        )
      ),
      resultType = Term.Ident("A"),
      body = Term.Ident("x")
    )
    ok(src, expect)
  }

  test("def_let_and_ascription") {
    val src =
      """
        |def useLet (A : Type 0) (x : A) : A := let y : A := x in (y : A)
        |""".stripMargin
    val expect = Decl.Def(
      isInline = false,
      name = "useLet",
      levelParams = Nil,
      params = List(
        Binder(SRelevance.Rel, "A", Term.Type(SLevel.NatLit(0))),
        Binder(SRelevance.Rel, "x", Term.Ident("A"))
      ),
      resultType = Term.Ident("A"),
      body = Term.Let(
        name = "y",
        ty = Term.Ident("A"),
        value = Term.Ident("x"),
        in = Term.Ascribe(Term.Ident("y"), Term.Ident("A"))
      )
    )
    ok(src, expect)
  }

  test("def_lambda_body_and_grouped_params") {
    val src =
      """
        |def lam (A : Type 0) : A -> A := \(x : A) => x
        |""".stripMargin
    val expect = Decl.Def(
      isInline = false,
      name = "lam",
      levelParams = Nil,
      params = List(
        Binder(SRelevance.Rel, "A", Term.Type(SLevel.NatLit(0)))
      ),
      resultType = Term.Forall(Binder(SRelevance.Rel, "_", Term.Ident("A")), Term.Ident("A")),
      body = Term.Lam(Binder(SRelevance.Rel, "x", Term.Ident("A")), Term.Ident("x"))
    )
    ok(src, expect)
  }

  test("def_implicit_site_body") {
    val src =
      """
        |def useImplicit (x a b : Nat) : Nat := implicit[Decidable (Or (Lt x a) (Lt b x))]
        |""".stripMargin
    val expect = Decl.Def(
      isInline = false,
      name = "useImplicit",
      levelParams = Nil,
      params = List(
        Binder(SRelevance.Rel, "x", Term.Ident("Nat")),
        Binder(SRelevance.Rel, "a", Term.Ident("Nat")),
        Binder(SRelevance.Rel, "b", Term.Ident("Nat"))
      ),
      resultType = Term.Ident("Nat"),
      body = Term.ImplicitSite(
        Term.App(
          Term.Ident("Decidable"),
          Term.App(
            Term.App(
              Term.Ident("Or"),
              Term.App(Term.App(Term.Ident("Lt"), Term.Ident("x")), Term.Ident("a"))
            ),
            Term.App(Term.App(Term.Ident("Lt"), Term.Ident("b")), Term.Ident("x"))
          )
        )
      )
    )
    ok(src, expect)
  }

  test("def_simple") {
    val src =
      """
        |def id (A : Type _) (x : A) : A := x
        |""".stripMargin
    val expect = Decl.Def(
      isInline = false,
      name = "id",
      levelParams = Nil,
      params = List(
        Binder(SRelevance.Rel, "A", Term.TypeHole),
        Binder(SRelevance.Rel, "x", Term.Ident("A"))
      ),
      resultType = Term.Ident("A"),
      body = Term.Ident("x")
    )
    ok(src, expect)
  }

  test("def_inline") {
    val src =
      """
        |inline def k (A : Type _) (x : A) : A := x
        |""".stripMargin
    val expect = Decl.Def(
      isInline = true,
      name = "k",
      levelParams = Nil,
      params = List(
        Binder(SRelevance.Rel, "A", Term.TypeHole),
        Binder(SRelevance.Rel, "x", Term.Ident("A"))
      ),
      resultType = Term.Ident("A"),
      body = Term.Ident("x")
    )
    ok(src, expect)
  }

  test("def_with_lparams_multiline_body") {
    val src =
      """
        |def head.{u} (A : Type u) (n : Nat) (v : Vec A (succ n)) : A :=
        |  match v as w returning A with {
        |  | cons a xs => a
        |  }
        |""".stripMargin
    val expect = Decl.Def(
      isInline = false,
      name = "head",
      levelParams = List("u"),
      params = List(
        Binder(SRelevance.Rel, "A", Term.Type(SLevel.Ident("u"))),
        Binder(SRelevance.Rel, "n", Term.Ident("Nat")),
        Binder(
          SRelevance.Rel,
          "v",
          Term.App(
            Term.App(Term.Ident("Vec"), Term.Ident("A")),
            Term.App(Term.Ident("succ"), Term.Ident("n"))
          )
        )
      ),
      resultType = Term.Ident("A"),
      body = Term.Match(
        scrut = Term.Ident("v"),
        asName = "w",
        returning = Term.Ident("A"),
        cases = List(
          Case(Pattern.Ctor("cons", List("a","xs")), Term.Ident("a"))
        )
      )
    )
    ok(src, expect)
  }
}
