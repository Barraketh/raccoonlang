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
    typecheckDecls(withFamilies("def f (l: Lifetime)(g: { kind = lin, scope = l } Unit -> Nat): Nat := g(Unit.unit)\n"))
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

  test("a lambda binds a parameter, so one with none is a parse error") {
    typecheckDecls("def f : Nat -> Nat := fun (n: Nat): Nat => 0\n")
    assertEquals(parseFailure("def f : Nat -> Nat := fun : Nat => 0\n"), "A lambda binds a parameter")
    assertEquals(parseFailure("def f : Nat -> Nat := fun { kind = unr } : Nat => 0\n"), "A lambda binds a parameter")
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

  test("a mismatch between function types that differ in their closures names the closure fields that differ") {
    def rendered(source: String): String = ErrorRendering.render(expectOnly[TypeMismatch](typecheckDecls(source)))

    assertEquals(
      rendered("def f (l: Lifetime)(g: { scope = l } Unit -> Nat): { kind = lin } Unit -> Nat := g\n"),
      "type mismatch\n  expected: { kind = Kind.lin } Unit -> Nat\n  actual:   { scope = l } Unit -> Nat\n" +
        "  closures differ in kind Kind.lin  vs  Kind.unr\n  closures differ in scope Lifetime.empty  vs  l"
    )
    // Inside a family instance, at the function types rather than at the instances' sorts.
    assertEquals(
      rendered("def f (l: Lifetime)(xs: List(({ scope = l } Unit -> Nat))): List((Unit -> Nat)) := xs\n"),
      "type mismatch\n  expected: List(Unit -> Nat)\n  actual:   List({ scope = l } Unit -> Nat)\n" +
        "  differ at: Unit -> Nat  vs  { scope = l } Unit -> Nat\n  closures differ in scope Lifetime.empty  vs  l"
    )
    // An implicit forced both by a closure and by a sort is read off the sort, so a lambda written without the closure
    // its parameter declares is itself the mismatch, rather than the sort of whatever else the implicit governs.
    assertEquals(
      rendered("def f {S: Lifetime}(A: Type { scope = S }): BEq(A) := BEq.mk(fun (a: A)(b: A): Bool => Bool.true)\n"),
      "type mismatch\n  expected: { scope = S } A -> A -> Bool\n  actual:   (a: A) -> (b: A) -> Bool\n" +
        "  closures differ in scope S  vs  Lifetime.empty"
    )
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
    def program(capture: String, result: String, body: String): String =
      withFamilies(s"def f (l: Lifetime)$capture: $result := fun (u: Unit): Nat => $body\n")

    typecheckDecls(program("", "Unit -> Nat", "0"))
    typecheckDecls(program("(v: V(l))", "{ scope = l } Unit -> Nat", "useV(v)"))
    typecheckDecls(program("(t: Tok(l))", "{ kind = lin, scope = l } Unit -> Nat", "eat(t)"))
    expectOnly[TypeMismatch](typecheckDecls(program("(t: Tok(l))", "{ scope = l } Unit -> Nat", "eat(t)")))
    expectOnly[TypeMismatch](typecheckDecls(program("(v: V(l))", "Unit -> Nat", "useV(v)")))
    // Where the lambda stands never changes its type: one that captures nothing is not at scope l.
    expectOnly[TypeMismatch](typecheckDecls(program("", "{ scope = l } Unit -> Nat", "0")))
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
      withFamilies(s"def f (l: Lifetime)(t: Tok(l)): Nat := {\n  let p := fun (u: Unit): True => $body\n  eat(t)\n}\n")

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
    // The block applies `g` once, and consumes the token itself when `g` does not.
    def program(closure: String, body: String, result: String): String =
      withFamilies(
        s"def f (l: Lifetime)(v: V(l))(t: Tok(l)): Nat := {\n  let g := fun $closure (u: Unit): Nat => $body\n  $result\n}\n"
      )

    typecheckDecls(program("{ kind = lin, scope = l }", "eat(t)", "g(Unit.unit)"))
    typecheckDecls(program("{ kind = lin, scope = l }", "0", "Nat.add(g(Unit.unit), eat(t))"))
    val kind = expectOnly[KindExceeded](typecheckDecls(program("{ kind = unr, scope = l }", "eat(t)", "g(Unit.unit)")))
    assert(kind.part.contains("capture t"), kind.part)
    val scope =
      expectOnly[ScopeExceeded](typecheckDecls(program("{ kind = lin, scope = empty }", "eat(t)", "g(Unit.unit)")))
    assert(scope.part.contains("capture t"), scope.part)
    expectOnly[ScopeExceeded](typecheckDecls(program("{ scope = empty }", "useV(v)", "Nat.add(g(Unit.unit), eat(t))")))
    // Each omitted field is derived on its own.
    typecheckDecls(program("{ kind = lin }", "eat(t)", "g(Unit.unit)"))
    typecheckDecls(program("{ scope = l }", "eat(t)", "g(Unit.unit)"))
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
      withFamilies(
        s"def f (l: Lifetime)(t: Tok(l)): Nat := eat(t)\n\n" +
          s"def h (l: Lifetime)(t: Tok(l)): Nat := {\n  let g : $ty := f\n  g(l, t)\n}\n"
      )

    typecheckDecls(program("(l: Lifetime) -> Tok(l) -> Nat"))
    expectOnly[TypeMismatch](typecheckDecls(program("{ kind = lin } (l: Lifetime) -> Tok(l) -> Nat")))
  }

  /** The header's binders checked, and the definition's body: an inner lambda, checked where it stands. */
  private def checkInnerLambda(source: String): (Env, TypeChecker.CheckedTerm) = {
    val core = Elaborator.elab(parseSurface(source), Prelude.default)
    val env =
      core.decls.dropRight(1).foldLeft(Prelude.default.checkedEnv)((env, decl) => Interpreter.evalDecl(decl, env))
    core.decls.last match {
      case CA.Decl.ConstDecl(_, _, _, CA.ConstBody.TermBody(lam: CA.Term.Lam), _, _) =>
        val bodyEnv = telescope.BinderOps.checkBinders(lam.ty.binders, env, familyParams = 0, lam.ty.span).env
        (bodyEnv, TypeChecker.checkTerm(lam.body, bodyEnv))
      case other => fail(s"Expected a definition with header binders, got $other")
    }
  }

  test("a residual carries a derived closure as its captures, and re-evaluating it gives the checked value") {
    val (env, checked) = checkInnerLambda(
      withFamilies(
        "def f (l: Lifetime)(n: Nat)(v: V(l))(t: Tok(l)): { kind = lin, scope = l } Unit -> Nat :=\n" +
          "  fun (u: Unit): Nat => Nat.add(Nat.add(n, useV(v)), eat(t))\n"
      )
    )
    val residual = checked.residual match {
      case lam: CA.Term.Lam => lam
      case other            => fail(s"Expected a lambda residual, got $other")
    }
    // Each field carries the captures that contribute to it: `n` contributes to neither, and `v` to the scope alone.
    residual.ty.closure match {
      case CA.Closure(CA.ClosureField.Derived(kind), CA.ClosureField.Derived(scope)) =>
        assertEquals(kind.map(_.name), Vector("t"))
        assertEquals(scope.map(_.name), Vector("v", "t"))
      case other => fail(s"Expected derived closure fields, got $other")
    }
    // The residual prints its derived fields as omitted, as written; the value's type shows the closure.
    assert(residual.toString.startsWith("fun (u: Unit): Nat => "), residual.toString)
    assertEquals(checked.value.tpe.toString, "{ kind = Kind.lin, scope = l } (u: Unit) -> Nat")
    val reevaluated = Interpreter.evalTerm(residual, env)
    assertEquals(reevaluated.key, checked.value.key)
    assert(ValueEquivalence.defEq(reevaluated, checked.value))
    assert(ValueEquivalence.defEq(reevaluated.tpe, checked.value.tpe))
  }

  test("a derived closure is derived again from its captures wherever its residual is evaluated") {
    val delay = withFamilies(
      """
        |def delay {k: Kind}{S: Lifetime}{A: Type { kind = k, scope = S }}(x: A): { kind = k, scope = S } Unit -> A :=
        |  fun (u: Unit): A => x
        |
        |def force {kf: Kind}{Sf: Lifetime}{k: Kind}{S: Lifetime}{A: Type { kind = k, scope = S }}
        |    (g: { kind = kf, scope = Sf } Unit -> A): A := g(Unit.unit)
        |""".stripMargin
    )
    def closure(result: String): (Value.Kind, Value.Lifetime) =
      runProgram(delay + s"\n{ $result }\n").tpe match {
        case pi: Value.VPi => (pi.closureKind, pi.closureScope)
        case other         => fail(s"Expected a function type, got $other")
      }

    // One residual, evaluated at a linear and at an unrestricted capture.
    assertEquals(closure("delay(Tok.mk(Lifetime.empty))"), (Value.Kind.lin, Value.Lifetime.empty))
    assertEquals(closure("delay(Nat.zero)"), (Value.Kind.unr, Value.Lifetime.empty))
    // Forcing reads the closure where the residual was evaluated: at `Tok(l)` it is linear and scoped by `l`.
    val p = delay +
      """
        |def viaTok (l: Lifetime)(t: Tok(l)): Nat := eat(force(delay(t)))
        |def viaV (l: Lifetime)(v: V(l)): Nat := useV(force(delay(v)))
        |def viaNat (n: Nat): Nat := force(delay(n))
        |
        |{ Nat.add(Nat.add(viaTok(Lifetime.empty, Tok.mk(Lifetime.empty)), viaV(Lifetime.empty, V.mk(Lifetime.empty))), viaNat(3)) }
        |""".stripMargin
    assert(ValueEquivalence.defEq(runProgram(p), runProgram("{ 3 }")))
    // The evaluated lambda's type is the declared result under the instantiation, and nothing else.
    def program(result: String): String = delay + s"\ndef g (l: Lifetime)(t: Tok(l)): $result := delay(t)\n"
    typecheckDecls(program("{ kind = lin, scope = l } Unit -> Tok(l)"))
    expectOnly[TypeMismatch](typecheckDecls(program("{ scope = l } Unit -> Tok(l)")))
    expectOnly[TypeMismatch](typecheckDecls(program("{ kind = lin } Unit -> Tok(l)")))
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
