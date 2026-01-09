package com.raccoonlang

import com.raccoonlang.SurfaceAst._
import com.raccoonlang.SurfaceParserRec

class SurfaceParserTheoremTests extends munit.FunSuite {
  private def ok(src: String, expect: Decl.Theorem): Unit = {
    SurfaceParserRec.parseDecl(src) match {
      case Right(value: Decl.Theorem) => assertEquals(value, expect)
      case Left(err)                  => fail(s"failed to parse: $err\n$src")
      case other                      => fail(s"unexpected parse result: $other")
    }
  }

  test("theorem_empty_match") {
    val src =
      """
        |theorem absurdVec (A : Type _) (n : Nat) (v : Vec A (succ n)) : False :=
        |  match v as w returning False with { }
        |""".stripMargin
    val expect = Decl.Theorem(
      name = "absurdVec",
      levelParams = Nil,
      params = List(
        Binder(SRelevance.Rel, "A", Term.TypeHole),
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
      resultType = Term.Ident("False"),
      body = Term.Match(
        scrut = Term.Ident("v"),
        asName = "w",
        returning = Term.Ident("False"),
        cases = Nil
      )
    )
    ok(src, expect)
  }

  test("theorem_match_multiple_cases") {
    val src =
      """
        |theorem headOrZero (A : Type 0) (n : Nat) (v : Vec A n) : A :=
        |  match v as w returning A with {
        |  | nil => ?nz
        |  | cons a xs => a
        |  }
        |""".stripMargin
    val expect = Decl.Theorem(
      name = "headOrZero",
      levelParams = Nil,
      params = List(
        Binder(SRelevance.Rel, "A", Term.Type(SLevel.NatLit(0))),
        Binder(SRelevance.Rel, "n", Term.Ident("Nat")),
        Binder(SRelevance.Rel, "v", Term.App(Term.App(Term.Ident("Vec"), Term.Ident("A")), Term.Ident("n")))
      ),
      resultType = Term.Ident("A"),
      body = Term.Match(
        scrut = Term.Ident("v"),
        asName = "w",
        returning = Term.Ident("A"),
        cases = List(
          Case(SurfaceAst.Pattern.Ctor("nil", Nil), Term.Hole("nz")),
          Case(SurfaceAst.Pattern.Ctor("cons", List("a", "xs")), Term.Ident("a"))
        )
      )
    )
    ok(src, expect)
  }

  test("theorem_simple") {
    val src =
      """
        |theorem refl (A : Type _) (x : A) : Eq A x x := ?h
        |""".stripMargin
    val expect = Decl.Theorem(
      name = "refl",
      levelParams = Nil,
      params = List(
        Binder(SRelevance.Rel, "A", Term.TypeHole),
        Binder(SRelevance.Rel, "x", Term.Ident("A"))
      ),
      resultType = Term.App(
        Term.App(
          Term.App(Term.Ident("Eq"), Term.Ident("A")),
          Term.Ident("x")
        ),
        Term.Ident("x")
      ),
      body = Term.Hole("h")
    )
    ok(src, expect)
  }

  test("theorem_with_lparams") {
    val src =
      """
        |theorem symm.{u} (A : Type u) (x y : A) : Eq A x y := ?goal
        |""".stripMargin
    val expect = Decl.Theorem(
      name = "symm",
      levelParams = List("u"),
      params = List(
        Binder(SRelevance.Rel, "A", Term.Type(SLevel.Ident("u"))),
        Binder(SRelevance.Rel, "x", Term.Ident("A")),
        Binder(SRelevance.Rel, "y", Term.Ident("A"))
      ),
      resultType = Term.App(
        Term.App(
          Term.App(Term.Ident("Eq"), Term.Ident("A")),
          Term.Ident("x")
        ),
        Term.Ident("y")
      ),
      body = Term.Hole("goal")
    )
    ok(src, expect)
  }
}
