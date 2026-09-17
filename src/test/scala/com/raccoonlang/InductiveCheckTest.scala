package com.raccoonlang

class InductiveCheckTest extends munit.FunSuite {
  test("basic inductive formation and constructor publication typecheck") {
    val (env, _) = TestSupport.check("inductive Bool : Type\n | true : Bool\n | false : Bool\n\nBool.true")
    assert(env.globals.contains("Bool.true"))
  }

  test("malformed constructor results are rejected") {
    intercept[WTF] {
      TestSupport.check("inductive Bool : Type\n | bad : Type\n")
    }
  }

  test("inductive publication is atomic when a constructor fails") {
    val core = TestSupport.core("inductive Bool : Type\n | bad : Type\n")
    val env = Interpreter.builtins
    intercept[WTF] { TypeChecker.checkDecl(core.decls.head, env) }
    assert(!env.globals.contains("Bool"))
  }

  test("non-positive recursive occurrences remain accepted before positivity") {
    val (env, _) = TestSupport.check("inductive Bad : Type\n | mk (f: Bad -> Type) : Bad\n")
    assert(env.globals.contains("Bad.mk"))
  }

  test("duplicate constructors are rejected before publication") {
    intercept[AlreadyDefined] {
      TestSupport.check("inductive Bool : Type\n | same : Bool\n | same : Bool\n")
    }
  }

  test("mutual inductive formation sees every provisional family") {
    val span = Span(0, 1)
    val left = CoreAst.Decl.InductiveDecl(
      CoreAst.InductiveHeader("Left", Vector.empty, Vector.empty, CoreAst.Term.GlobalRef("Type", span), span),
      Vector(CoreAst.ConstructorDecl("Left.l", "l", Vector.empty, CoreAst.Term.GlobalRef("Left", span), span)),
      span
    )
    val right = CoreAst.Decl.InductiveDecl(
      CoreAst.InductiveHeader("Right", Vector.empty, Vector.empty, CoreAst.Term.GlobalRef("Type", span), span),
      Vector(
        CoreAst.ConstructorDecl(
          "Right.r",
          "r",
          Vector(CoreAst.Binder(CoreAst.LocalRef(2, "left"), CoreAst.Term.GlobalRef("Left", span), span)),
          CoreAst.Term.GlobalRef("Right", span),
          span
        )
      ),
      span
    )
    val (env, _) =
      TypeChecker.checkProgram(CoreAst.Program(Vector(CoreAst.Decl.InductiveBlock(Vector(left, right), span)), None))
    assert(env.globals.contains("Left"))
    assert(env.globals.contains("Right"))
  }

  test("mutual inductives reject non-uniform parameter telescopes") {
    val span = Span(0, 1)
    val binder = CoreAst.Binder(CoreAst.LocalRef(1, "A"), CoreAst.Term.GlobalRef("Type", span), span)
    val left = CoreAst.Decl.InductiveDecl(
      CoreAst.InductiveHeader("Left", Vector(binder), Vector.empty, CoreAst.Term.GlobalRef("Type", span), span),
      Vector(
        CoreAst.ConstructorDecl(
          "Left.l",
          "l",
          Vector.empty,
          CoreAst.Term
            .App(CoreAst.Term.GlobalRef("Left", span), Vector(CoreAst.Term.LocalRef(binder.localRef, span)), span),
          span
        )
      ),
      span
    )
    val right = CoreAst.Decl.InductiveDecl(
      CoreAst.InductiveHeader("Right", Vector.empty, Vector.empty, CoreAst.Term.GlobalRef("Type", span), span),
      Vector(CoreAst.ConstructorDecl("Right.r", "r", Vector.empty, CoreAst.Term.GlobalRef("Right", span), span)),
      span
    )
    intercept[WTF] {
      TypeChecker.checkProgram(CoreAst.Program(Vector(CoreAst.Decl.InductiveBlock(Vector(left, right), span)), None))
    }
  }

  test("constructors must return their declared parameter") {
    val span = Span(0, 1)
    val param = CoreAst.Binder(CoreAst.LocalRef(40, "A"), CoreAst.Term.GlobalRef("Type", span), span)
    val wrongResult = CoreAst.Term.App(
      CoreAst.Term.GlobalRef("Box", span),
      Vector(CoreAst.Term.GlobalRef("Type", span)),
      span
    )
    val decl = CoreAst.Decl.InductiveDecl(
      CoreAst.InductiveHeader("Box", Vector(param), Vector.empty, CoreAst.Term.GlobalRef("Type", span), span),
      Vector(CoreAst.ConstructorDecl("Box.mk", "mk", Vector.empty, wrongResult, span)),
      span
    )
    intercept[WTF] {
      TypeChecker.checkProgram(CoreAst.Program(Vector(decl), None))
    }
  }

  test("mutual families accept alpha-equivalent dependent parameters") {
    val span = Span(0, 1)
    def family(name: String, aId: Int, bId: Int, ctorName: String): CoreAst.Decl.InductiveDecl = {
      val a = CoreAst.Binder(CoreAst.LocalRef(aId, "A"), CoreAst.Term.GlobalRef("Type", span), span)
      val b = CoreAst.Binder(CoreAst.LocalRef(bId, "B"), CoreAst.Term.LocalRef(a.localRef, span), span)
      val result = CoreAst.Term.App(
        CoreAst.Term.GlobalRef(name, span),
        Vector(CoreAst.Term.LocalRef(a.localRef, span), CoreAst.Term.LocalRef(b.localRef, span)),
        span
      )
      CoreAst.Decl.InductiveDecl(
        CoreAst.InductiveHeader(name, Vector(a, b), Vector.empty, CoreAst.Term.GlobalRef("Type", span), span),
        Vector(CoreAst.ConstructorDecl(s"$name.$ctorName", ctorName, Vector.empty, result, span)),
        span
      )
    }
    val (env, _) = TypeChecker.checkProgram(
      CoreAst.Program(
        Vector(CoreAst.Decl.InductiveBlock(Vector(family("Left", 60, 61, "l"), family("Right", 70, 71, "r")), span)),
        None
      )
    )
    assert(env.globals.contains("Left"))
    assert(env.globals.contains("Right"))
  }

  test("indexed constructors may compute their result index from fields") {
    val span = Span(0, 1)
    val a = CoreAst.Binder(CoreAst.LocalRef(80, "A"), CoreAst.Term.GlobalRef("Type", span), span)
    val x = CoreAst.Binder(CoreAst.LocalRef(81, "x"), CoreAst.Term.LocalRef(a.localRef, span), span)
    val y = CoreAst.Binder(CoreAst.LocalRef(82, "y"), CoreAst.Term.LocalRef(a.localRef, span), span)
    val result = CoreAst.Term.App(
      CoreAst.Term.GlobalRef("Eq", span),
      Vector(CoreAst.Term.LocalRef(a.localRef, span), CoreAst.Term.LocalRef(y.localRef, span)),
      span
    )
    val declaration = CoreAst.Decl.InductiveDecl(
      CoreAst.InductiveHeader("Eq", Vector(a), Vector(x), CoreAst.Term.GlobalRef("Type", span), span),
      Vector(CoreAst.ConstructorDecl("Eq.refl", "refl", Vector(y), result, span)),
      span
    )
    val (env, _) = TypeChecker.checkProgram(CoreAst.Program(Vector(declaration), None))
    assert(env.globals.contains("Eq.refl"))
  }

  test("indexed constructor results cannot refer to header indices as fields") {
    val span = Span(0, 1)
    val a = CoreAst.Binder(CoreAst.LocalRef(90, "A"), CoreAst.Term.GlobalRef("Type", span), span)
    val x = CoreAst.Binder(CoreAst.LocalRef(91, "x"), CoreAst.Term.LocalRef(a.localRef, span), span)
    val result = CoreAst.Term.App(
      CoreAst.Term.GlobalRef("Eq", span),
      Vector(CoreAst.Term.LocalRef(a.localRef, span), CoreAst.Term.LocalRef(x.localRef, span)),
      span
    )
    val declaration = CoreAst.Decl.InductiveDecl(
      CoreAst.InductiveHeader("Eq", Vector(a), Vector(x), CoreAst.Term.GlobalRef("Type", span), span),
      Vector(CoreAst.ConstructorDecl("Eq.bad", "bad", Vector.empty, result, span)),
      span
    )
    intercept[NotFound] {
      TypeChecker.checkProgram(CoreAst.Program(Vector(declaration), None))
    }
  }

  test("constructor parameter discipline is based on definitional equality") {
    val span = Span(0, 1)
    val a = CoreAst.Binder(CoreAst.LocalRef(100, "A"), CoreAst.Term.GlobalRef("Type", span), span)
    val b = CoreAst.LocalRef(101, "B")
    val wrapped = CoreAst.Term.Body(
      Vector(CoreAst.Let(b, None, CoreAst.Term.LocalRef(a.localRef, span), span)),
      CoreAst.Term.App(CoreAst.Term.GlobalRef("Box", span), Vector(CoreAst.Term.LocalRef(b, span)), span),
      span
    )
    val declaration = CoreAst.Decl.InductiveDecl(
      CoreAst.InductiveHeader("Box", Vector(a), Vector.empty, CoreAst.Term.GlobalRef("Type", span), span),
      Vector(CoreAst.ConstructorDecl("Box.mk", "mk", Vector.empty, wrapped, span)),
      span
    )
    val (env, _) = TypeChecker.checkProgram(CoreAst.Program(Vector(declaration), None))
    assert(env.globals.contains("Box.mk"))
  }
}
