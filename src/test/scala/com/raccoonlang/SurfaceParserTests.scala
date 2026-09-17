package com.raccoonlang

import com.raccoonlang.SurfaceAst.Command.Decl.ConstDecl
import com.raccoonlang.SurfaceAst.Command._
import com.raccoonlang.SurfaceAst.ConstBody.TermBody
import com.raccoonlang.SurfaceAst.Term._
import com.raccoonlang.SurfaceAst._

class SurfaceParserTests extends munit.FunSuite {
  private def parsed(source: String): Program = LanguageParser.parseProgram(source) match {
    case Success(program, _, _) => program
    case failure                => fail(s"Expected parse success, got $failure")
  }

  private def rejected(source: String): Unit =
    assert(LanguageParser.parseProgram(source).isInstanceOf[Failure], source)

  test("identifier boundaries accept atoms and reject keywords") {
    parsed("raccoon_2").body match {
      case Some(Ident(name, _)) => assertEquals(name, "raccoon_2")
      case other                => fail(s"Expected identifier body, got $other")
    }
    parsed("funny").body match {
      case Some(Ident(name, _)) => assertEquals(name, "funny")
      case other                => fail(s"Expected identifier body, got $other")
    }
    rejected("fun")
    rejected("let")
    rejected("decreases")
  }

  test("Unicode scalar strings decode and malformed escapes are rejected") {
    parsed("\"A\\n\\u03bb😀\"").body match {
      case Some(StrLit(scalars, _)) =>
        assertEquals(scalars, Vector('A'.toInt, '\n'.toInt, 0x03bb, 0x1f600))
      case other => fail(s"Expected string literal body, got $other")
    }
    rejected("\"\\uD800\"")
    rejected("\"\\q\"")
    rejected("\"unterminated")
  }

  test("arrow chains preserve grouped and nested Pi structure") {
    parsed("(A: Type) -> A -> A").body match {
      case Some(Pi(binders, Ident("A", _), _)) => assertEquals(binders.size, 2)
      case other                               => fail(s"Expected grouped Pi, got $other")
    }
    parsed("(A: Type) -> (A -> A)").body match {
      case Some(Pi(outerBinders, Pi(innerBinders, _, _), _)) =>
        assertEquals(outerBinders.size, 1)
        assertEquals(innerBinders.size, 1)
      case other => fail(s"Expected nested Pi, got $other")
    }
  }

  test("lambdas, applications, and let bodies parse") {
    parsed("fun (x: Type): Type => x").body match {
      case Some(Lam(FuncHeader(params, _, _), Ident("x", _), _)) => assertEquals(params.size, 1)
      case other                                                 => fail(s"Expected lambda, got $other")
    }
    parsed("f(x, 1).field").body match {
      case Some(Select(App(Ident("f", _), args, _), "field", _)) => assertEquals(args.size, 2)
      case other => fail(s"Expected application and selection, got $other")
    }
    parsed("{\nlet x := 1\nx\n}").body match {
      case Some(Body(Vector(LetStmt(Let("x", None, NatLit(value, _), _))), Ident("x", _), _)) =>
        assertEquals(value, BigInt(1))
      case other => fail(s"Expected let body, got $other")
    }
  }

  test("transparent and opaque definitions retain their declaration shape") {
    parsed("def id (A: Type)(x: A): A := x").decls match {
      case Vector(ConstDecl(false, DeclHeader("id", FuncHeader(params, _, _), _), None, TermBody(Ident("x", _)), _)) =>
        assertEquals(params.map(_.name), Vector("A", "x"))
      case other => fail(s"Expected transparent definition, got $other")
    }
    parsed("opaque def hidden : Type := 0").decls match {
      case Vector(ConstDecl(true, DeclHeader("hidden", _, _), None, TermBody(NatLit(value, _)), _)) =>
        assertEquals(value, BigInt(0))
      case other => fail(s"Expected opaque definition, got $other")
    }
  }

  test("spans retain explicit source identity") {
    val source = SourceId(91)
    LanguageParser.parseProgram("def x : Type := 0", source) match {
      case Success(program, _, _) =>
        val declaration = program.decls.head.asInstanceOf[ConstDecl]
        assertEquals(declaration.span.source, Some(source))
        assertEquals(declaration.header.span.source, Some(source))
        assertEquals(declaration.header.name, "x")
      case failure => fail(s"Expected parse success, got $failure")
    }
  }

  test("comments and whitespace are accepted around declarations and terms") {
    val source = "  // leading comment\n\n def x : Type := 0\n\n // trailing comment\n  x  "
    val program = parsed(source)
    assertEquals(program.decls.size, 1)
    assertEquals(program.body.collect { case Ident(name, _) => name }, Some("x"))
  }

  test("whole-input checking rejects trailing garbage") {
    rejected("def x : Type := 0 @")
    rejected("0 @")
  }

  test("later language constructs are rejected by the base grammar") {
    rejected("import Init.Prelude\n")
    rejected("namespace N {}")
    rejected("open N")
    rejected("{ def x : Type := 0 }")
    rejected("axiom choice : Type")
    rejected("inductive Nat : Type\n | zero : Nat\n")
    rejected("struct Pair : Type\n | mk : Pair\n")
    rejected("match x with\n")
    rejected("def f : Type := 0 decreases structural(x)")
    rejected("def f : Type := builtin")
  }
}
