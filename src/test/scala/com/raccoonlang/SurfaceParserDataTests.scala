package com.raccoonlang

import com.raccoonlang.SurfaceAst._
import com.raccoonlang.SurfaceParserRec

class SurfaceParserDataTests extends munit.FunSuite {
  private def ok(src: String, expect: Decl.Data): Unit = {
    SurfaceParserRec.parseDecls(src) match {
      case Right(List(value: Decl.Data)) => assertEquals(value, expect)
      case Left(err)                     => fail(s"failed to parse: $err\n$src")
      case other                         => fail(s"unexpected parse result: $other")
    }
  }

  // 4) Multiple level params and mixed param kinds
  test("data_multi_level_params") {
    val src =
      """
        |data Box.{u, v} (A : Type u) (B : Type v) : Type max(u, v) where {
        |  | mk (a : A) (b : B) : Box A B
        |}
        |""".stripMargin
    ok(src,
    Decl.Data(
      name = "Box",
      levelParams = List("u", "v"),
      params = List(
        Binder(SRelevance.Rel, "A", Term.Type(SLevel.Ident("u"))),
        Binder(SRelevance.Rel, "B", Term.Type(SLevel.Ident("v")))
      ),
      resultType = Term.Type(SLevel.Max(SLevel.Ident("u"), SLevel.Ident("v"))),
      ctors = List(
        Ctor(
          "mk",
          List(
            Binder(SRelevance.Rel, "a", Term.Ident("A")),
            Binder(SRelevance.Rel, "b", Term.Ident("B"))
          ),
          Term.App(Term.App(Term.Ident("Box"), Term.Ident("A")), Term.Ident("B"))
        )
      )
    ))
  }

  // 5) Constructor with irrelevant binder
  test("data_ctor_irrelevant_binder") {
    val src =
      """
        |data D (A : Type 0) : Type 0 where {
        |  | mk (.x : A) : D A
        |}
        |""".stripMargin
    ok(src,
    Decl.Data(
      name = "D",
      levelParams = Nil,
      params = List(Binder(SRelevance.Rel, "A", Term.Type(SLevel.NatLit(0)))),
      resultType = Term.Type(SLevel.NatLit(0)),
      ctors = List(
        Ctor(
          "mk",
          List(Binder(SRelevance.Irr, "x", Term.Ident("A"))),
          Term.App(Term.Ident("D"), Term.Ident("A"))
        )
      )
    ))
  }

  // 1) Minimal single-line data
  test("data_minimal") {
    val src =
      """
        |data Nat : Type 0 where {
        | | zero : Nat
        | | succ (n : Nat) : Nat
        |}
        |""".stripMargin
    ok(src,
    Decl.Data(
      name = "Nat",
      levelParams = Nil,
      params = Nil,
      resultType = Term.Type(SLevel.NatLit(0)),
      ctors = List(
        Ctor("zero", Nil, Term.Ident("Nat")),
        Ctor("succ", List(Binder(SRelevance.Rel, "n", Term.Ident("Nat"))), Term.Ident("Nat"))
      )
    ))
  }

  // 2) With params and inferred levels via Type _
  test("data_with_params_levels") {
    val src =
      """
        |data Vec (A : Type _) : Nat -> Type _ where {
        |  | nil  : Vec A zero
        |  | cons (n : Nat) (a : A) (xs : Vec A n) : Vec A (succ n)
        |}
        |""".stripMargin
    ok(src,
    Decl.Data(
      name = "Vec",
      levelParams = Nil,
      params = List(
        Binder(SRelevance.Rel, "A", Term.TypeHole)
      ),
      resultType = Term.Forall(Binder(SRelevance.Rel, "_", Term.Ident("Nat")), Term.TypeHole),
      ctors = List(
        Ctor("nil", Nil, Term.App(Term.App(Term.Ident("Vec"), Term.Ident("A")), Term.Ident("zero"))),
        Ctor(
          "cons",
          List(
            Binder(SRelevance.Rel, "n", Term.Ident("Nat")),
            Binder(SRelevance.Rel, "a", Term.Ident("A")),
            Binder(SRelevance.Rel, "xs", Term.App(Term.App(Term.Ident("Vec"), Term.Ident("A")), Term.Ident("n")))
          ),
          Term.App(
            Term.App(Term.Ident("Vec"), Term.Ident("A")),
            Term.App(Term.Ident("succ"), Term.Ident("n"))
          )
        )
      )
    ))
  }

  // 3) With level params .{u} and newlines between ctors
  test("data_with_lparams_and_newlines") {
    val src =
      """
        |data Vec.{u} (A : Type u) : Nat -> Type u where {
        |  | nil : Vec A zero
        |
        |  | cons (n : Nat) (a : A) (xs : Vec A n) : Vec A (succ n)
        |}
        |""".stripMargin
    ok(src,
    Decl.Data(
      name = "Vec",
      levelParams = List("u"),
      params = List(Binder(SRelevance.Rel, "A", Term.Type(SLevel.Ident("u")))),
      resultType = Term.Forall(Binder(SRelevance.Rel, "_", Term.Ident("Nat")), Term.Type(SLevel.Ident("u"))),
      ctors = List(
        Ctor("nil", Nil, Term.App(Term.App(Term.Ident("Vec"), Term.Ident("A")), Term.Ident("zero"))),
        Ctor(
          "cons",
          List(
            Binder(SRelevance.Rel, "n", Term.Ident("Nat")),
            Binder(SRelevance.Rel, "a", Term.Ident("A")),
            Binder(SRelevance.Rel, "xs", Term.App(Term.App(Term.Ident("Vec"), Term.Ident("A")), Term.Ident("n")))
          ),
          Term.App(
            Term.App(Term.Ident("Vec"), Term.Ident("A")),
            Term.App(Term.Ident("succ"), Term.Ident("n"))
          )
        )
      )
    ))
  }
}
