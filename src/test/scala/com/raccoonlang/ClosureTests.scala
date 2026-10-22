package com.raccoonlang

import com.raccoonlang.{CoreAst => CA}

/** Function types retain closure-kind syntax, inference, containment, and conversion. */
class ClosureTests extends munit.FunSuite with TestSupport {
  private val token =
    """
      |inductive Tok : Type { kind = lin }
      | | mk : Tok
      |
      |def eat (t: Tok): Nat := match t returning Nat with
      | | Tok.mk => 0
      |""".stripMargin

  private def withToken(decls: String): String = token + "\n" + decls

  private def parseFailure(source: String): String =
    LanguageParser.parseProgram(source) match {
      case Failure(_, _, message) => message
      case _: Success[_]          => fail("expected a parse error")
    }

  test("a closure prefixes a function type or lambda, and only accepts kind") {
    typecheckDecls("def keep {k: Kind}{A: Type { kind = k }}(x: A): A := x\n")
    typecheckDecls("def f (g: { kind = lin } Unit -> Nat): Nat := g(Unit.unit)\n")
    typecheckDecls("def f (u: Unit): Nat := (fun { kind = lin } (v: Unit): Nat => 0)(u)\n")
    assertEquals(
      parseFailure("def f : Unit -> Nat := fun { scope = Nat.zero } (u: Unit): Nat => 0\n"),
      "Unknown field scope"
    )
    assertEquals(parseFailure("def f (g: { scope = Nat.zero } Unit -> Nat): Nat := 0\n"), "Unknown field scope")
  }

  test("closure prefixes are accepted only before a whole function type") {
    val misplaced = "A closure prefixes a whole function type; parenthesize a nested one"
    assertEquals(parseFailure("def f (g: Nat -> { kind = lin } Unit -> Nat): Nat := 0\n"), misplaced)
    assertEquals(parseFailure("def f (g: (n: Nat) -> { kind = lin } (u: Unit) -> Nat): Nat := 0\n"), misplaced)
    assertEquals(parseFailure("def f (g: { kind = lin } Nat): Nat := 0\n"), "A closure prefixes a function type")
    assertEquals(
      parseFailure("def f (g: { level = one } Unit -> Nat): Nat := 0\n"),
      "Misplaced field level: a closure has no level"
    )
    assertEquals(parseFailure("def f (g: { size = one } Unit -> Nat): Nat := 0\n"), "Unknown field size")
    assertEquals(parseFailure("def f (g: { kind = lin, kind = lin } Unit -> Nat): Nat := 0\n"), "Repeated field kind")
    assertEquals(
      parseFailure("def f : Unit -> Nat := fun { level = one } (u: Unit): Nat => 0\n"),
      "Misplaced field level: a closure has no level"
    )
  }

  test("a lambda binds one or more parameters, and empty binder groups are rejected") {
    typecheckDecls("def f : Nat -> Nat := fun (n: Nat): Nat => 0\n")
    assertEquals(parseFailure("def f : Nat -> Nat := fun : Nat => 0\n"), "A lambda binds a parameter")
    assertEquals(parseFailure("def f : Nat -> Nat := fun { kind = unr } : Nat => 0\n"), "A lambda binds a parameter")
  }

  test("closure kinds are compared exactly and named in mismatches") {
    typecheckDecls("def f (g: { kind = lin } Unit -> Nat): { kind = lin } Unit -> Nat := g\n")
    expectOnly[TypeMismatch](typecheckDecls("def f (g: { kind = lin } Unit -> Nat): Unit -> Nat := g\n"))
    val mismatch =
      expectOnly[TypeMismatch](
        typecheckDecls("def f (g: { kind = lin } Unit -> Nat): { kind = unr } Unit -> Nat := g\n")
      )
    val message = ErrorRendering.render(mismatch, None)
    assert(message.contains("closures differ in kind"), message)
  }

  test("a function type's sort contains its closure kind, while propositions reject linear closures") {
    typecheckDecls("inductive Holder : Type { kind = lin }\n | mk (f: { kind = lin } Unit -> Nat) : Holder\n")
    expectOnly[KindExceeded](
      typecheckDecls("inductive Holder : Type\n | mk (f: { kind = lin } Unit -> Nat) : Holder\n")
    )
    typecheckDecls("def f (g: Unit -> True): Nat := 0\n")
    expectOnly[KindExceeded](typecheckDecls("def f (g: { kind = lin } Unit -> True): Nat := 0\n"))
  }

  test("a lambda derives its kind from captures, and written kinds are checked") {
    typecheckDecls(withToken("def f (t: Tok): { kind = lin } Unit -> Nat := fun (u: Unit): Nat => eat(t)\n"))
    expectOnly[TypeMismatch](typecheckDecls(withToken("def f (t: Tok): Unit -> Nat := fun (u: Unit): Nat => eat(t)\n")))
    val exceeded =
      expectOnly[KindExceeded](
        typecheckDecls(
          withToken("def f (t: Tok): Nat := fun { kind = unr } (u: Unit): Nat => Nat.add(eat(t), 1)\n")
        )
      )
    assert(PartialFunction.cond(exceeded.part) { case ContainedPart.Capture("t", _) => true }, exceeded.part)
    typecheckDecls(
      withToken("def f (t: Tok): Nat := { let g := fun (u: Unit): Nat => 0\n Nat.add(g(Unit.unit), eat(t)) }\n")
    )
  }

  test("a closure-polymorphic parameter accepts captures of either kind") {
    val program = withToken(
      """
        |def app {kf: Kind}(g: { kind = kf } Unit -> Nat): Nat := g(Unit.unit)
        |def captured (t: Tok): Nat := app(fun (u: Unit): Nat => eat(t))
        |def closed : Nat := app(fun (u: Unit): Nat => 2)
        |{ Nat.add(captured(Tok.mk), closed) }
        |""".stripMargin
    )
    assert(ValueEquivalence.defEq(runProgram(program), runProgram("{ 2 }")))
    expectOnly[TypeMismatch](
      typecheckDecls(
        withToken(
          "def app (g: Unit -> Nat): Nat := g(Unit.unit)\ndef f (t: Tok): Nat := app(fun (u: Unit): Nat => eat(t))\n"
        )
      )
    )
  }

  test("a closure-kind variable is forced only by an exact closure annotation") {
    typecheckDecls("def apply {k: Kind}(g: { kind = k } Unit -> Nat): Nat := g(Unit.unit)\n")
    expectOnly[NonForcedImplicitParam](
      typecheckDecls(
        "def bad {k: Kind}(j: Kind)(g: { kind = join(k, j) } Unit -> Nat): Nat := g(Unit.unit)\n"
      )
    )
  }

  test("function-typed captures contribute their closure kind, and unrestricted functions can be lifted") {
    val source =
      "def lift (g: Unit -> Nat): { kind = lin } Unit -> Nat := " +
        "fun { kind = lin } (u: Unit): Nat => g(u)\n"
    typecheckDecls(source)
    typecheckDecls(
      withToken(
        "def use (g: { kind = lin } Nat -> Nat): { kind = lin } Unit -> Nat := " +
          "fun (u: Unit): Nat => g(0)\n"
      )
    )
    expectOnly[TypeMismatch](
      typecheckDecls(
        withToken("def use (g: { kind = lin } Nat -> Nat): Unit -> Nat := fun (u: Unit): Nat => g(0)\n")
      )
    )
  }

  test("recursive references to the definition itself are not captures") {
    val program =
      """
        |def count (n: Nat): Nat decreases structural(n) :=
        |  match n returning Nat with
        |  | Nat.zero => 0
        |  | Nat.succ m => (fun (x: Nat): Nat => Nat.succ(count(m)))(0)
        |
        |{ count(3) }
        |""".stripMargin
    assert(ValueEquivalence.defEq(runProgram(program), runProgram("{ 3 }")))
  }

  test("proof lambdas contain no linear captures, while tokens are consumed in data code") {
    typecheckDecls(
      withToken(
        "def closed (t: Tok): Unit -> Nat := " +
          "(fun (n: Nat): Unit -> Nat => fun (u: Unit): Nat => 0)(eat(t))\n"
      )
    )
    typecheckDecls(
      withToken(
        "def ok (t: Tok): Nat := {\n  let p := fun (u: Unit): True => True.intro\n  eat(t)\n}\n"
      )
    )
    expectOnly[KindExceeded](
      typecheckDecls(
        withToken(
          "def bad (t: Tok): Nat := {\n  let p := fun (u: Unit): True => " +
            "match t returning True with\n  | Tok.mk => True.intro\n  Nat.add(eat(t), 1)\n}\n"
        )
      )
    )
  }

  test("a derived closure is re-evaluated from the current capture kind") {
    val declarations = withToken(
      """
        |def delay {k: Kind}{A: Type { kind = k }}(x: A): { kind = k } Unit -> A := fun (u: Unit): A => x
        |def force {k: Kind}{A: Type { kind = k }}(f: { kind = k } Unit -> A): A := f(Unit.unit)
        |def throughToken (t: Tok): Nat := eat(force(delay(t)))
        |def throughNat (n: Nat): Nat := force(delay(n))
        |""".stripMargin
    )
    typecheckDecls(declarations)

    def closureKind(term: String): Value.Kind = {
      val core = Elaborator.elab(parseSurface(declarations + s"\n{ $term }\n"), Prelude.default)
      val env = core.decls.foldLeft(Prelude.default.checkedEnv)((env, decl) => Interpreter.evalDecl(decl, env))
      TypeChecker.checkTerm(core.body.getOrElse(fail("Expected a body")), env).value.tpe match {
        case pi: Value.VPi => pi.closureKind
        case other         => fail(s"Expected a function type, got $other")
      }
    }

    assertEquals(closureKind("delay(Tok.mk)"), Value.Kind.lin)
    assertEquals(closureKind("delay(0)"), Value.Kind.unr)
    assert(
      ValueEquivalence.defEq(
        runProgram(declarations + "{ Nat.add(throughToken(Tok.mk), throughNat(3)) }"),
        runProgram("{ 3 }")
      )
    )
  }

  private def checkInnerLambda(source: String): (Env, TypeChecker.CheckedTerm) = {
    val core = Elaborator.elab(parseSurface(source), Prelude.default)
    val env =
      core.decls.dropRight(1).foldLeft(Prelude.default.checkedEnv)((env, decl) => Interpreter.evalDecl(decl, env))
    core.decls.last match {
      case CA.Decl.ConstDecl(_, _, CA.ConstBody.TermBody(lam: CA.Term.Lam), _, _) =>
        val bodyEnv = telescope.BinderOps.checkBinders(lam.ty.binders, env, familyParams = 0, lam.ty.span).env
        (bodyEnv, TypeChecker.checkTerm(lam.body, bodyEnv))
      case other => fail(s"Expected a definition with header binders, got $other")
    }
  }

  test("a residual stores its derived closure kind and reevaluates to the checked type") {
    val (env, checked) = checkInnerLambda(
      withToken(
        "def f (n: Nat)(t: Tok): { kind = lin } Unit -> Nat :=\n" +
          "  fun (u: Unit): Nat => Nat.add(Nat.add(n, eat(t)), 1)\n"
      )
    )
    val residual = checked.residual match {
      case lam: CA.Term.Lam => lam
      case other            => fail(s"Expected a lambda residual, got $other")
    }
    residual.ty.closure match {
      case CA.Closure(CA.ClosureField.Derived(kind)) => assertEquals(kind.map(_.name), Vector("t"))
      case other                                     => fail(s"Expected a derived closure kind, got $other")
    }
    assertEquals(checked.value.tpe.toString, "{ kind = Kind.lin } (u: Unit) -> Nat")
    val reevaluated = Interpreter.evalTerm(residual, env)
    assertEquals(reevaluated.key, checked.value.key)
    assert(ValueEquivalence.defEq(reevaluated, checked.value))
  }

  test("function values differing only in closure kind are not convertible") {
    val (env, checked) = checkInnerLambda(
      withToken("def f (t: Tok): { kind = lin } Unit -> Nat := fun (u: Unit): Nat => eat(t)\n")
    )
    val linear = checked.value.tpe
    val unrestricted = Interpreter.evalTerm(
      checked.residual match {
        case lam: CA.Term.Lam =>
          lam.ty.copy(closure =
            CA.Closure(CA.ClosureField.Written(CA.Term.FormOp(CA.Form.KindUnr, Vector.empty, lam.span)))
          )
        case other => fail(s"Expected a lambda residual, got $other")
      },
      env
    )
    assert(!ValueEquivalence.defEq(linear, unrestricted))
    assert(ValueEquivalence.defEq(linear, Interpreter.evalTerm(checked.residual, env).tpe))
    intercept[InternalError](linear == unrestricted)
  }
}
