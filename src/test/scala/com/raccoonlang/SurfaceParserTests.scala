package com.raccoonlang

import com.raccoonlang.SurfaceAst.Term.{Ident, Pi, TApp}
import com.raccoonlang.SurfaceAst._

class SurfaceParserTests extends munit.FunSuite {
  private def ok(src: String, expect: Decl): Unit = {
    LanguageParser.parseDecls(src) match {
      case Success(value, _, _) => assertEquals(value(0), expect)
      case err: Failure         => fail(s"failed to parse: $err\n$src")
    }
  }

  test("def_lambda_body_and_grouped_params") {
    val src =
      """
        |def lam (A : Type) : A -> A := fun (x : A) => x
        |""".stripMargin
    val expect = Decl.ConstDecl(
      isInline = false,
      header = DeclHeader(
        name = "lam",
        params = Vector(
          Binder("A", Ident("Type"))
        ),
        ty = Term.Pi(Binder("_", Ident("A")), Ident("A"))
      ),
      body = Some(
        Body(
          Vector.empty,
          Term.Lam(Vector(Binder("x", Ident("A"))), Body(Vector.empty, Ident("x")))
        )
      )
    )
    ok(src, expect)
  }

  test("inductive vector") {
    val src =
      """
        |inductive Vec: Type -> Nat -> Type
        | | nil (A: Type): Type
        | | cons : A -> Vec A n -> Type
        |""".stripMargin

    val expect = Decl.InductiveDecl(
      DeclHeader("Vec", Vector(), Pi(Binder("_", Ident("Type")), Pi(Binder("_", Ident("Nat")), Ident("Type")))),
      Vector(
        DeclHeader("nil", Vector(Binder("A", Ident("Type"))), Ident("Type")),
        DeclHeader(
          "cons",
          Vector.empty,
          Pi(Binder("_", Ident("A")), Pi(Binder("_", TApp(TApp(Ident("Vec"), Ident("A")), Ident("n"))), Ident("Type")))
        )
      )
    )

    ok(src, expect)
  }

}
