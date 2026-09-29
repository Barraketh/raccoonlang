package com.raccoonlang

import com.raccoonlang.{CoreAst => CA}

/**
 * Function-type and lambda closures (spec §1, §2.4, §2.5, §2.7, §3.3, §4.3, §8): a closure's kind and scope are part of
 * a function type's identity and its sort, are forced like a sort's fields, and a lambda's are derived from what its
 * body captures or checked against it. Each rule has an admitted program and the smallest mutation that reaches its
 * diagnostic.
 */
class ClosureTests extends munit.FunSuite with TestSupport {

  /** A family scoped by its lifetime, a linear one, and a consumer of each. */
  private val families =
    """
      |inductive V (l: Lifetime) : Type { scope = l }
      | | mk : V(l)
      |
      |inductive Tok (l: Lifetime) : Type { kind = lin, scope = l }
      | | mk : Tok(l)
      |
      |def useV {l: Lifetime}(v: V(l)): Nat := 0
      |
      |def eat {l: Lifetime}(t: Tok(l)): Nat := match t returning Nat with
      | | Tok.mk => 0
      |""".stripMargin

  private def withFamilies(decls: String): String = families + "\n" + decls

  private def parseFailure(source: String): String =
    LanguageParser.parseProgram(source) match {
      case Failure(_, _, message) => message
      case _: Success[_]          => fail("expected a parse error")
    }

  test("a closure prefixes a function type's group, or a lambda") {
    typecheckDecls(withFamilies("def f (l: Lifetime)(g: { kind = lin, scope = l } Unit -> Nat): Nat := 0\n"))
    typecheckDecls(withFamilies("def f (l: Lifetime)(g: Nat -> ({ scope = l } Unit -> Nat)): Nat := 0\n"))
    typecheckDecls(withFamilies("def f (l: Lifetime)(g: { scope = l } (u: Unit)(n: Nat) -> Nat): Nat := 0\n"))
    typecheckDecls(
      withFamilies("def f (l: Lifetime): { scope = l } Unit -> Nat := fun { scope = l } (u: Unit): Nat => 0\n")
    )
    // The token after the first name tells a closure from an implicit binder.
    typecheckDecls("def keep {kind: Kind}{A: Type { kind = kind }}(x: A): A := x\n")
  }

  test("a closure is a parse error before a later domain, as a level field is in one") {
    def program(domain: String): String = s"def f (g: $domain): Nat := 0\n"

    val misplaced = "A closure prefixes a whole function type; parenthesize a nested one"
    assertEquals(parseFailure(program("Nat -> { kind = lin } Unit -> Nat")), misplaced)
    assertEquals(parseFailure(program("(n: Nat) -> { kind = lin } (u: Unit) -> Nat")), misplaced)
    assertEquals(parseFailure(program("{ kind = lin } Nat")), "A closure prefixes a function type")
    assertEquals(parseFailure(program("{ level = one } Unit -> Nat")), "Misplaced field level: a closure has no level")
    assertEquals(parseFailure(program("{ size = one } Unit -> Nat")), "Unknown field size")
    assertEquals(parseFailure(program("{ kind = lin, kind = lin } Unit -> Nat")), "Repeated field kind")
    assertEquals(
      parseFailure("def f : Unit -> Nat := fun { level = one } (u: Unit): Nat => 0\n"),
      "Misplaced field level: a closure has no level"
    )
  }

  test("a function type's closure is part of its type, compared exactly") {
    def program(result: String): String =
      withFamilies(s"def f (l: Lifetime)(g: { scope = l } Unit -> Nat): $result := g\n")

    typecheckDecls(program("{ scope = l } Unit -> Nat"))
    expectOnly[TypeMismatch](typecheckDecls(program("Unit -> Nat")))
    expectOnly[TypeMismatch](typecheckDecls(program("{ kind = lin, scope = l } Unit -> Nat")))
    typecheckDecls("def f {k: Kind}(g: { kind = k } Unit -> Nat): { kind = k } Unit -> Nat := g\n")
    expectOnly[TypeMismatch](typecheckDecls("def f {k: Kind}(g: { kind = k } Unit -> Nat): Unit -> Nat := g\n"))
  }

  test("a function type's sort takes its closure's kind and adds its closure's scope") {
    def program(sort: String): String =
      withFamilies(
        s"inductive Holds (l: Lifetime) : $sort\n | mk (f: { kind = lin, scope = l } Unit -> Nat) : Holds(l)\n"
      )

    typecheckDecls(program("Type { kind = lin, scope = l }"))
    expectOnly[KindExceeded](typecheckDecls(program("Type { scope = l }")))
    expectOnly[ScopeExceeded](typecheckDecls(program("Type { kind = lin }")))
  }

  test("a linear closure into a proposition is LinearProp") {
    typecheckDecls("def f (g: Unit -> True): Nat := 0\n")
    expectOnly[LinearProp](typecheckDecls("def f (g: { kind = lin } Unit -> True): Nat := 0\n"))
    expectOnly[LinearProp](typecheckDecls("def f {k: Kind}(g: { kind = k } Unit -> True): Nat := 0\n"))
  }

  test("a closure field forces a variable only when it is exactly that variable") {
    def program(scope: String): String =
      withFamilies(s"def f {S: Lifetime}(l: Lifetime)(g: { scope = $scope } Unit -> Nat): Nat := g(Unit.unit)\n")

    typecheckDecls(program("S"))
    expectOnly[NonForcedImplicitParam](typecheckDecls(program("union(S, l)")))
  }

  test("a lambda's omitted closure is what its body captures") {
    def program(result: String, body: String): String =
      withFamilies(
        s"def f (l: Lifetime)(v: V(l))(t: Tok(l)): $result := fun (u: Unit): Nat => $body\n"
      )

    typecheckDecls(program("Unit -> Nat", "0"))
    typecheckDecls(program("{ scope = l } Unit -> Nat", "useV(v)"))
    typecheckDecls(program("{ kind = lin, scope = l } Unit -> Nat", "eat(t)"))
    expectOnly[TypeMismatch](typecheckDecls(program("{ scope = l } Unit -> Nat", "eat(t)")))
    expectOnly[TypeMismatch](typecheckDecls(program("Unit -> Nat", "useV(v)")))
    // Where the lambda stands never changes its type: one that captures nothing is not at scope l.
    expectOnly[TypeMismatch](typecheckDecls(program("{ scope = l } Unit -> Nat", "0")))
  }

  test("a lambda's captures are what its body mentions, not its binder types or result") {
    val indexed =
      "inductive P (l: Lifetime) indices (h: V(l)) : Type { scope = l }\n | mk : P(l, V.mk(l))\n\n"
    def program(body: String): String =
      withFamilies(indexed + s"def f (l: Lifetime)(v: V(l)): P(l, v) -> Nat := fun (p: P(l, v)): Nat => $body\n")

    typecheckDecls(program("0"))
    expectOnly[TypeMismatch](typecheckDecls(program("useV(v)")))
    // A captured type variable carries its sort's scope; a captured lifetime is not a value.
    typecheckDecls(
      "def f {S: Lifetime}(A: Type { scope = S }): { scope = S } Unit -> Type { scope = S } := " +
        "fun (u: Unit): Type { scope = S } => A\n"
    )
    typecheckDecls(withFamilies("def f (l: Lifetime): Unit -> Nat := fun (u: Unit): Nat => useV(V.mk(l))\n"))
  }

  test("a closure derived in a refined branch names a variable by any local bound to it") {
    def program(motive: String): String =
      withFamilies(
        s"""
           |inductive W (l: Lifetime) : Type
           | | mk : W(l)
           |
           |def f (l: Lifetime)(m: Lifetime)(v: V(m))(p: Eq(Type, W(l), W(m))): $motive :=
           |  match p returning $motive with
           |  | Eq.refl x => fun (u: Unit): Nat => useV(v)
           |
           |def g (l: Lifetime)(v: V(l)): Nat := f(l, l, v, Eq.refl(W(l)))(Unit.unit)
           |
           |{ g(Lifetime.empty, V.mk(Lifetime.empty)) }
           |""".stripMargin
      )

    // Refinement links `m` to `l`, so the capture `v : V(m)` is at scope `l` in the branch.
    assert(ValueEquivalence.defEq(runProgram(program("{ scope = l } Unit -> Nat")), runProgram("{ 0 }")))
    expectOnly[TypeMismatch](typecheckDecls(program("Unit -> Nat")))
  }

  test("a function-typed capture contributes its closure's kind and its type's scope") {
    def program(result: String): String =
      withFamilies(
        s"def f (l: Lifetime)(g: { kind = lin } V(l) -> Nat)(v: V(l)): $result := fun (u: Unit): Nat => g(v)\n"
      )

    typecheckDecls(program("{ kind = lin, scope = l } Unit -> Nat"))
    expectOnly[TypeMismatch](typecheckDecls(program("{ kind = lin } Unit -> Nat")))
  }

  test("a lambda that captures a linear value into a proposition is LinearProp") {
    def program(body: String): String =
      withFamilies(s"def f (l: Lifetime)(t: Tok(l)): Nat := {\n  let p := fun (u: Unit): True => $body\n  0\n}\n")

    typecheckDecls(program("True.intro"))
    expectOnly[LinearProp](typecheckDecls(program("match t returning True with\n    | Tok.mk => True.intro")))
  }

  test("a recursive definition's reference to itself is not a capture") {
    val p =
      """
        |def count {u: Level}{A: Sort { level = u }}(a: A)(n: Nat): Nat decreases structural(n) :=
        |  match n returning Nat with
        |  | Nat.zero => 0
        |  | Nat.succ m => (fun (x: Nat): Nat => Nat.succ(count(a, m)))(0)
        |
        |{ count(Nat.zero, 3) }
        |""".stripMargin
    assert(ValueEquivalence.defEq(runProgram(p), runProgram("{ 3 }")))
  }

  test("a written closure must contain what the lambda captures") {
    def program(closure: String, body: String): String =
      withFamilies(
        s"def f (l: Lifetime)(v: V(l))(t: Tok(l)): Nat := {\n  let g := fun $closure (u: Unit): Nat => $body\n  0\n}\n"
      )

    typecheckDecls(program("{ kind = lin, scope = l }", "eat(t)"))
    typecheckDecls(program("{ kind = lin, scope = l }", "0"))
    val kind = expectOnly[KindExceeded](typecheckDecls(program("{ kind = unr, scope = l }", "eat(t)")))
    assert(kind.part.contains("capture t"), kind.part)
    val scope = expectOnly[ScopeExceeded](typecheckDecls(program("{ kind = lin, scope = empty }", "eat(t)")))
    assert(scope.part.contains("capture t"), scope.part)
    expectOnly[ScopeExceeded](typecheckDecls(program("{ scope = empty }", "useV(v)")))
    // Each omitted field is derived on its own.
    typecheckDecls(program("{ kind = lin }", "eat(t)"))
    typecheckDecls(program("{ scope = l }", "eat(t)"))
  }

  test("a function value is lifted to a larger closure by a lambda") {
    val lift =
      "def lift {S: Lifetime}(l: Lifetime)(g: { scope = S } Unit -> Nat): { kind = lin, scope = union(S, l) } " +
        "Unit -> Nat :=\n  fun { kind = lin, scope = union(S, l) } (u: Unit): Nat => g(u)\n"
    typecheckDecls(lift)
    expectOnly[ScopeExceeded](
      typecheckDecls(
        "def lift {S: Lifetime}(l: Lifetime)(g: { scope = S } Unit -> Nat): { scope = l } Unit -> Nat :=\n" +
          "  fun { scope = l } (u: Unit): Nat => g(u)\n"
      )
    )
  }

  test("a closure-polymorphic parameter accepts lambdas of either kind and forces through their closures") {
    val p = withFamilies(
      """
        |def app {kf: Kind}{S: Lifetime}(g: { kind = kf, scope = S } Unit -> Nat): Nat := g(Unit.unit)
        |
        |def linear (l: Lifetime)(t: Tok(l)): Nat := app(fun (u: Unit): Nat => eat(t))
        |def scoped (l: Lifetime)(v: V(l)): Nat := app(fun (u: Unit): Nat => useV(v))
        |def closed (l: Lifetime): Nat := app(fun (u: Unit): Nat => 3)
        |
        |{ Nat.add(linear(Lifetime.empty, Tok.mk(Lifetime.empty)), closed(Lifetime.empty)) }
        |""".stripMargin
    )
    assert(ValueEquivalence.defEq(runProgram(p), runProgram("{ 3 }")))
    // Without the variables, the parameter accepts only an unrestricted, capture-free lambda.
    expectOnly[TypeMismatch](
      typecheckDecls(
        withFamilies(
          "def app (g: Unit -> Nat): Nat := g(Unit.unit)\n" +
            "def linear (l: Lifetime)(t: Tok(l)): Nat := app(fun (u: Unit): Nat => eat(t))\n"
        )
      )
    )
  }

  test("a definition's own function type is unrestricted and captures nothing") {
    def program(ty: String): String =
      withFamilies(s"def f (l: Lifetime)(t: Tok(l)): Nat := eat(t)\n\ndef g : $ty := f\n")

    typecheckDecls(program("(l: Lifetime) -> Tok(l) -> Nat"))
    expectOnly[TypeMismatch](typecheckDecls(program("{ kind = lin } (l: Lifetime) -> Tok(l) -> Nat")))
  }

  /** The header's binders checked, and the definition's body: an inner lambda, checked where it stands. */
  private def checkInnerLambda(source: String): (Env, TypeChecker.CheckedTerm) = {
    val core = Elaborator.elab(parseSurface(source), Prelude.default)
    val env =
      core.decls.dropRight(1).foldLeft(Prelude.default.checkedEnv)((env, decl) => Interpreter.evalDecl(decl, env))
    core.decls.last match {
      case CA.Decl.ConstDecl(_, _, _, CA.ConstBody.TermBody(lam: CA.Term.Lam), _) =>
        val bodyEnv = telescope.BinderOps.checkBinders(lam.ty.binders, env).env
        (bodyEnv, TypeChecker.checkTerm(lam.body, bodyEnv))
      case other => fail(s"Expected a definition with header binders, got $other")
    }
  }

  test("a residual carries a derived closure, and re-evaluating it gives the checked value") {
    val (env, checked) = checkInnerLambda(
      withFamilies(
        "def f (l: Lifetime)(v: V(l))(t: Tok(l)): { kind = lin, scope = l } Unit -> Nat :=\n" +
          "  fun (u: Unit): Nat => Nat.add(useV(v), eat(t))\n"
      )
    )
    val residual = checked.residual match {
      case lam: CA.Term.Lam => lam
      case other            => fail(s"Expected a lambda residual, got $other")
    }
    residual.ty.closure match {
      case CA.Closure(CA.ClosureField.Derived(Some(kind)), CA.ClosureField.Derived(Some(scope))) =>
        assertEquals(kind.toString, "Kind.lin")
        assertEquals(scope.toString, "l")
      case other => fail(s"Expected derived closure fields, got $other")
    }
    assert(
      checked.value.tpe.toString.matches(raw"\{ kind = Kind\.lin, scope = l#\d+ \} \(u: Unit\) -> Nat"),
      checked.value.tpe.toString
    )
    val reevaluated = Interpreter.evalTerm(residual, env)
    assertEquals(reevaluated.key, checked.value.key)
    assert(ValueEquivalence.defEq(reevaluated, checked.value))
    assert(ValueEquivalence.defEq(reevaluated.tpe, checked.value.tpe))
  }

  test("re-evaluating a derived closure that disagrees with the captures is an internal error") {
    val (env, checked) = checkInnerLambda(
      withFamilies("def f (l: Lifetime)(v: V(l)): { scope = l } Unit -> Nat := fun (u: Unit): Nat => useV(v)\n")
    )
    val tampered = checked.residual match {
      case lam: CA.Term.Lam =>
        val empty = CA.Term.FormOp(CA.Form.LifetimeEmpty, Vector.empty, lam.span)
        lam.copy(ty = lam.ty.copy(closure = lam.ty.closure.copy(scope = CA.ClosureField.Derived(Some(empty)))))
      case other => fail(s"Expected a lambda residual, got $other")
    }
    intercept[InternalError](Interpreter.evalTerm(tampered, env))
  }

  test("function types differing only in their closures are not convertible") {
    val (env, checked) = checkInnerLambda(
      withFamilies("def f (l: Lifetime)(v: V(l)): { scope = l } Unit -> Nat := fun (u: Unit): Nat => useV(v)\n")
    )
    val scoped = checked.value.tpe
    val closed = Interpreter.evalTerm(
      checked.residual match {
        case lam: CA.Term.Lam =>
          val empty = CA.Term.FormOp(CA.Form.LifetimeEmpty, Vector.empty, lam.span)
          lam.ty.copy(closure = lam.ty.closure.copy(scope = CA.ClosureField.Written(empty)))
        case other => fail(s"Expected a lambda residual, got $other")
      },
      env
    )
    assert(!ValueEquivalence.defEq(scoped, closed))
    assert(ValueEquivalence.defEq(scoped, Interpreter.evalTerm(checked.residual, env).tpe))
    intercept[InternalError](scoped == closed)
  }
}
