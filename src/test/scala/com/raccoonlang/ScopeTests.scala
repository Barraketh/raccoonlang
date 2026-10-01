package com.raccoonlang

import com.raccoonlang.{CoreAst => CA}

/**
 * `scope l => e` and atoms (spec §1, §4.1, §4.2, §6.2, §8): a `scope` term opens one atom, named by the term's node
 * identity in checking and evaluation alike, and a type whose sort's scope names it outside the scope is
 * `LifetimeEscapes`. Each rule has an admitted program and the smallest mutation that reaches its diagnostic.
 */
class ScopeTests extends munit.FunSuite with TestSupport {

  /**
   * A family scoped by its lifetime, a linear one, one holding the first, one scoped by two lifetimes, and consumers.
   */
  private val families =
    """
      |inductive V (l: Lifetime) : Type { scope = l }
      | | mk : V(l)
      |
      |inductive Tok (l: Lifetime) : Type { kind = lin, scope = l }
      | | mk : Tok(l)
      |
      |inductive H (l: Lifetime) : Type { scope = l }
      | | mk (v: V(l)) : H(l)
      |
      |inductive Two (l: Lifetime)(m: Lifetime) : Type { scope = union(l, m) }
      | | mk : Two(l, m)
      |
      |def useV {l: Lifetime}(v: V(l)): Nat := 0
      |
      |def same {l: Lifetime}(a: V(l))(b: V(l)): Nat := 1
      |
      |def burn {l: Lifetime}(t: Tok(l)): Nat := match t returning Nat with
      | | .mk => 1
      |
      |def keep {S: Lifetime}{A: Type { scope = S }}(x: A): A := x
      |
      |def constNat {S: Lifetime}(A: Type { scope = S }): Nat := 0
      |
      |inductive Box (n: Nat) : Type
      | | mk : Box(n)
      |""".stripMargin

  private def withFamilies(decls: String): String = families + "\n" + decls

  private def parseFailure(source: String): String =
    LanguageParser.parseProgram(source) match {
      case Failure(_, _, message) => message
      case _: Success[_]          => fail("expected a parse error")
    }

  test("scope is a keyword at the start of a term and a field name in a field list") {
    // The body extends as far to the right as a lambda body does, so `useV(...)` is the body, not an argument.
    assert(
      ValueEquivalence.defEq(
        runProgram(withFamilies("def n : Nat := scope l => useV(V.mk(l))\n\n{ n }")),
        runProgram("{ 0 }")
      )
    )
    typecheckDecls("def keep {S: Lifetime}{A: Type { scope = S }}(x: A): A := x\n")
    parseFailure("def scope : Nat := 0\n")
    parseFailure("def keep {scope: Lifetime}{A: Type { scope = scope }}(x: A): A := x\n")
  }

  test("a scope denotes its body's value, with its binder denoting the atom") {
    val program = withFamilies(
      """
        |def n : Nat := scope l => {
        |  let v := V.mk(l)
        |  same(v, V.mk(l))
        |}
        |
        |{ n }
        |""".stripMargin
    )
    assert(ValueEquivalence.defEq(runProgram(program), runProgram("{ 1 }")))
  }

  test("a type whose sort names the atom outside its scope is LifetimeEscapes") {
    def program(body: String): String = withFamilies(s"def n : Nat := $body\n")

    typecheckDecls(program("scope l => useV(V.mk(l))"))
    val escaped = expectOnly[LifetimeEscapes](typecheckDecls(program("useV(scope l => V.mk(l))")))
    assertEquals(escaped.lifetime, "l")
    assertEquals(escaped.tpe.toString, "V(l)")
    // The type's sort counts too.
    typecheckDecls("def s : Sort { level = succ(one) } := scope l => Type\n")
    expectOnly[LifetimeEscapes](typecheckDecls("def s : Sort { level = succ(one) } := scope l => Type { scope = l }\n"))
  }

  /** docs/SCOPE_CONTAINMENT.md §2's table: rows 1, 6 and 7 are admitted, and rows 2 to 5 are each one's mutation. */
  test("once a scope closes, no value that belongs to it is held, created or used") {
    def result(tpe: String, body: String): String = withFamilies(s"def r : $tpe := $body\n")
    def run(body: String): Value = runProgram(withFamilies(s"def r : Nat := $body\n\n{ r }"))
    val leased = "{\n  let h := V.mk(l)\n  "
    // 1 and its mutation 2.
    assert(ValueEquivalence.defEq(run("scope l => useV(V.mk(l))"), runProgram("{ 0 }")))
    expectOnly[LifetimeEscapes](typecheckDecls(result("Nat", "useV(scope l => V.mk(l))")))
    // 3, whose admitted form uses the list inside the scope.
    typecheckDecls(result("Nat", "scope l => List.length(List.cons(V.mk(l), List.nil(V(l))))"))
    expectOnly[LifetimeEscapes](
      typecheckDecls(result("Nat", "List.length(scope l => List.cons(V.mk(l), List.nil(V(l))))"))
    )
    // 6: the functions of 4 and 5 applied inside the scope; 4 and 5: each as the result.
    for (function <- Vector(leased + "fun (u: Unit): Nat => useV(h)\n}", "fun (u: Unit): Nat => useV(V.mk(l))")) {
      assert(ValueEquivalence.defEq(run(s"scope l => ($function)(Unit.unit)"), runProgram("{ 0 }")), function)
      expectOnly[LifetimeEscapes](typecheckDecls(result("Unit -> Nat", s"scope l => $function")))
    }
    // 7: a function that neither captures nor mentions the scope's lifetime leaves it; 5 is its mutation.
    typecheckDecls(result("Unit -> Nat", "scope l => fun (u: Unit): Nat => 3"))
    // §3's function type, whose codomain is code that builds a value of the scope.
    typecheckDecls(result("Type", "scope l => (x: Nat) -> Box(Nat.add(useV(V.mk(Lifetime.empty)), x))"))
    expectOnly[LifetimeEscapes](typecheckDecls(result("Type", "scope l => (x: Nat) -> Box(Nat.add(useV(V.mk(l)), x))")))
  }

  test("a function type belongs to the scopes its code captures, which are part of its identity") {
    def result(tpe: String, body: String): String = withFamilies(s"def r : $tpe := $body\n")
    // Its own lifetime binders, curried or grouped, are supplied by whoever instantiates it.
    for (telescope <- Vector("(m: Lifetime) -> (x: Nat) ->", "(m: Lifetime)(x: Nat) ->")) {
      typecheckDecls(result("Type", s"scope l => $telescope Box(useV(V.mk(m)))"))
      expectOnly[LifetimeEscapes](typecheckDecls(result("Type", s"scope l => $telescope Box(useV(V.mk(l)))")))
    }
    // A residual function type re-evaluated at a lifetime argument counts it there.
    def instance(declared: String): String =
      withFamilies(s"def P (m: Lifetime): $declared := (x: Nat) -> Box(useV(V.mk(m)))\n")
    typecheckDecls(instance("Type { scope = m }") + "def a : Type := P(Lifetime.empty)\n")
    expectOnly[LifetimeEscapes](typecheckDecls(instance("Type { scope = m }") + "def b : Type := scope l => P(l)\n"))
    expectOnly[TypeMismatch](typecheckDecls(instance("Type")))
    // Two function types whose code captures different scopes are different types, though their instances agree.
    def converting(result: String): String =
      withFamilies(
        "def P (m: Lifetime): Type := (x: Nat) -> Box(7)\n" +
          "def Q (m: Lifetime): Type { scope = m } := (x: Nat) -> Box(useV(V.mk(m)))\n" +
          s"def coerce (m: Lifetime)(f: Q(m)): $result := f\n"
      )
    typecheckDecls(converting("Q(m)"))
    expectOnly[TypeMismatch](typecheckDecls(converting("P(m)")))
    // So a lambda whose result type's code names `m` is not at a function type that does not.
    def lambda(resultType: String): String =
      withFamilies(s"def x (m: Lifetime): (u: Unit) -> Box(7) := fun (u: Unit): $resultType => Box.mk(7)\n")
    typecheckDecls(lambda("Box(7)"))
    expectOnly[TypeMismatch](typecheckDecls(lambda("Box(useV(V.mk(m)))")))
  }

  test("an opaque application's arguments are not projection positions") {
    // An implicit read out of an opaque application could recover a lifetime, or a value of a scope, that the type
    // holding the application does not count.
    def program(binders: String, opaque: String): String =
      withFamilies(s"opaque def o {l: Lifetime}(v: V(l)): Nat := 0\n\ndef g $binders(t: Box($opaque)): Nat := 0\n")
    typecheckDecls(program("{n: Nat}", "n"))
    expectOnly[NonForcedImplicitParam](typecheckDecls(program("{l: Lifetime}{v: V(l)}", "o(v)")))
    expectOnly[NonForcedImplicitParam](
      typecheckDecls(
        withFamilies("opaque def f (l: Lifetime): Nat := 0\n\ndef g {l: Lifetime}(t: Box(f(l))): Nat := 0\n")
      )
    )
  }

  test("a type-former axiom names its lifetime parameters, and only its and families' arguments are projected") {
    def assuming(axioms: String): Prelude.Config =
      TestSupport.preludeAssuming(TestSupport.bundledPreludeSource, axioms)
    // A proposition former that does not name its lifetime would let an implicit read it off a proof's type.
    val exceeded = interceptError[ScopeExceeded](assuming("axiom PAx (l: Lifetime): Prop\n").checkedEnv)
    assertEquals(exceeded.part, ContainedPart.LifetimeParameter("l"))
    // Across its binder groups, wherever the lifetime is bound and however the sort is reached.
    Vector(
      "a later binder" -> "axiom F (n: Nat)(l: Lifetime): Type\n",
      "an implicit forced by a family" ->
        "inductive PV (l: Lifetime) : Type { scope = l }\n | mk : PV(l)\naxiom F {l: Lifetime}(v: PV(l)): Type\n",
      "after a level binder" -> "axiom F (u: Level)(l: Lifetime): Sort { level = u }\n",
      "a curried codomain" -> "axiom F (l: Lifetime): (n: Nat) -> Type\n",
      "a closure on the codomain" -> "axiom F (l: Lifetime): { scope = l } (n: Nat) -> Type\n",
      "a sort through a definition" -> "def MyT : Sort { level = succ(one) } := Type\naxiom F (l: Lifetime): MyT\n",
      "the whole type through a definition" ->
        "def TF : Sort { level = succ(one) } := (l: Lifetime) -> Type\naxiom F : TF\n"
    ).foreach { case (what, axiom) =>
      assertEquals(
        interceptError[ScopeExceeded](assuming(axiom).checkedEnv).part,
        ContainedPart.LifetimeParameter("l"),
        what
      )
    }
    val prelude = assuming(
      "axiom PAx (l: Lifetime): Prop { scope = l }\naxiom pfAx (l: Lifetime): PAx(l)\naxiom NAx (l: Lifetime): Nat\n"
    )
    def program(decls: String): String = withFamilies(decls)
    typecheckDecls(program("def g {l: Lifetime}(p: PAx(l)): V(l) := V.mk(l)\n"), prelude)
    // So a proof of it belongs to the lifetime, and a lambda that captures one cannot leave the scope.
    val leak =
      "def g {l: Lifetime}(p: PAx(l)): V(l) := V.mk(l)\n" +
        "def leak : Unit -> Nat := scope l => {\n  let t := pfAx(l)\n  fun (u: Unit): Nat => useV(g(t))\n}\n"
    expectOnly[LifetimeEscapes](typecheckDecls(program(leak), prelude))
    // A data axiom's application is blocked: its arguments are not projected.
    expectOnly[NonForcedImplicitParam](
      typecheckDecls(program("def g {l: Lifetime}(t: Box(NAx(l))): V(l) := V.mk(l)\n"), prelude)
    )
    // `Quot` is a type former, whose arguments are projected.
    val quot =
      "def rel (a: Nat)(b: Nat): Prop := Eq(Nat, a, b)\n" +
        "def g {u: Level}{S: Lifetime}{Sr: Lifetime}{Sq: Lifetime}{A: Sort { level = u, scope = S }}" +
        "{r: { scope = Sr } A -> A -> Prop { scope = Sq }}(q: Quot(A, r)): Nat := 3\n\n{ g(Quot.mk(rel, 4)) }\n"
    assert(ValueEquivalence.defEq(runProgram(quot), runProgram("{ 3 }")))
  }

  test("a mismatch between function types whose code captures differ names the scopes") {
    val mismatch = expectOnly[TypeMismatch](
      typecheckDecls(
        withFamilies(
          "def asB (f: (u: Unit) -> Box(0)): Nat := 0\n" +
            "def x (m: Lifetime): Nat := asB(fun (u: Unit): Box(useV(V.mk(m))) => Box.mk(0))\n"
        )
      )
    )
    val rendered = ErrorRendering.render(mismatch, None)
    assert(rendered.contains("their code captures differ in scope Lifetime.empty  vs  m"), rendered)
  }

  test("a lambda's own lifetime binders and its level and kind variables are not captures, its lifetimes are") {
    // The caller supplies a lambda's own lifetime, so it may leave the scope.
    def own(lifetime: String): String =
      withFamilies(
        s"def f : (m: Lifetime)(u: Unit) -> Nat := scope l => fun (m: Lifetime)(u: Unit): Nat => useV(V.mk($lifetime))\n"
      )
    typecheckDecls(own("m"))
    expectOnly[LifetimeEscapes](typecheckDecls(own("l")))
    // A variable of `Level` or `Kind` contributes nothing; one of `Lifetime`, mentioned only in a type in the body,
    // contributes the lifetime it holds, and is named by the written closure that omits it.
    def mentions(written: String, sort: String): String =
      s"def f (u: Level)(k: Kind)(m: Lifetime): Unit -> Nat := fun $written(x: Unit): Nat => " +
        s"List.length(List.nil($sort))\n"
    typecheckDecls(mentions("", "Sort { level = succ(u), kind = k }"))
    expectOnly[TypeMismatch](typecheckDecls(mentions("", "Type { scope = m }")))
    val exceeded =
      expectOnly[ScopeExceeded](typecheckDecls(mentions("{ scope = Lifetime.empty } ", "Type { scope = m }")))
    assert(PartialFunction.cond(exceeded.part) { case ContainedPart.Capture("m", _) => true }, exceeded.part)
    // A mention in a term counts as one in a type does.
    def inTerm(written: String): String =
      withFamilies(s"def f (m: Lifetime): { scope = m } Unit -> Nat := fun $written(x: Unit): Nat => useV(V.mk(m))\n")
    typecheckDecls(inTerm("{ scope = m } "))
    val inTermExceeded = expectOnly[ScopeExceeded](typecheckDecls(inTerm("{ scope = Lifetime.empty } ")))
    assert(
      PartialFunction.cond(inTermExceeded.part) { case ContainedPart.Capture("m", _) => true },
      inTermExceeded.part
    )
  }

  /**
   * Confinement reads only the sort's scope, so it rests on each rule that computes one (spec §2.4, §4.3, §5.1). Each
   * value below is bound in the scope and leaves it, and its type's sort names the atom exactly when the value is built
   * at `l` rather than at `Lifetime.empty`.
   */
  test("each rule that computes a sort's scope counts the atom") {
    def leaving(value: String): String = withFamilies(s"def n : Nat := {\n  let x := scope l => $value\n  0\n}\n")
    val values = Vector(
      "a lease" -> "V.mk(@)",
      "a family holding a lease, through its declared scope (§5.1)" -> "H.mk(V.mk(@))",
      "a family's type argument" -> "List.nil(V(@))",
      "a closure capturing a lease, through its derived closure (§4.3)" ->
        "{\n    let v := V.mk(@)\n    fun (u: Unit): Nat => useV(v)\n  }",
      "a lambda with a written closure" -> "fun { scope = @ } (u: Unit): Nat => 0",
      "a lambda whose code mentions the lifetime, through its derived closure (§4.3)" ->
        "fun (u: Unit): Nat => useV(V.mk(@))",
      "a lambda that mentions the lifetime only in a type written in its body" ->
        "fun (u: Unit): Nat => List.length(List.nil(V(@)))",
      "a function type's domain" -> "fun (v: V(@)): Nat => 0",
      "a function type's codomain" -> "fun (u: Unit): V(@) => V.mk(@)",
      "a function type whose domain mentions the lifetime" -> "(b: Box(useV(V.mk(@)))) -> Nat",
      "a lambda whose binder type alone mentions the lifetime, through its type's code" ->
        "fun (b: Box(useV(V.mk(@)))): Nat => 3",
      "a function type whose codomain mentions the lifetime" -> "(x: Nat) -> Box(Nat.add(useV(V.mk(@)), x))",
      "a function type whose codomain captures a lease" ->
        "{\n    let h := V.mk(@)\n    (x: Nat) -> Box(Nat.add(useV(h), x))\n  }",
      "a function type whose codomain captures a type" ->
        "{\n    let A := V(@)\n    (x: Nat) -> Box(Nat.add(constNat(A), x))\n  }",
      "a sort, at its own scope" -> "Type { scope = @ }",
      "a type variable, instantiated exactly" -> "keep(V.mk(@))",
      "a proof of an equation between leases" -> "Eq.refl(V.mk(@))",
      "a match's pattern field" -> "(match H.mk(V.mk(@)) returning V(@) with\n    | .mk v => v\n    )"
    )
    values.foreach { case (what, value) =>
      typecheckDecls(leaving(value.replace("@", "Lifetime.empty")))
      val escaped = expectOnly[LifetimeEscapes](typecheckDecls(leaving(value.replace("@", "l"))))
      assertEquals(escaped.lifetime, "l", what)
    }
    // A token is consumed where it is bound, so it leaves through its consumer.
    typecheckDecls(withFamilies("def n : Nat := scope l => burn(Tok.mk(l))\n"))
    expectOnly[LifetimeEscapes](typecheckDecls(withFamilies("def n : Nat := burn(scope l => Tok.mk(l))\n")))
  }

  test("a closure that captures or mentions the atom cannot leave its scope; a blocked computation may") {
    def program(body: String): String =
      withFamilies(s"def leave : Unit -> Nat := scope l => {\n  let v := V.mk(l)\n  fun (u: Unit): Nat => $body\n}\n")

    val leave = program("useV(V.mk(Lifetime.empty))")
    assert(ValueEquivalence.defEq(runProgram(leave + "\n{ leave(Unit.unit) }"), runProgram("{ 0 }")))
    // Capturing `v : V(l)` puts the atom in the closure's scope, and so does mentioning `l`.
    expectOnly[LifetimeEscapes](typecheckDecls(program("useV(v)")))
    expectOnly[LifetimeEscapes](typecheckDecls(program("useV(V.mk(l))")))
    // A type about the closure is at the closure type's scope.
    typecheckDecls(leave + "def refl : Eq(Unit -> Nat, leave, leave) := Eq.refl(leave)\n")
    // A computation blocked on a parameter holds the atom, and its type does not name it.
    typecheckDecls(
      withFamilies(
        """
          |def pick {l: Lifetime}(n: Nat)(v: V(l)): Nat := match n returning Nat with
          | | .zero => useV(v)
          | | .succ _ => 1
          |
          |def count (n: Nat): Nat := scope l => pick(n, V.mk(l))
          |
          |def lemma (n: Nat): Eq(Nat, count(n), count(n)) := Eq.refl(count(n))
          |""".stripMargin
      )
    )
  }

  test("nested scopes open distinct atoms") {
    def program(second: String): String =
      withFamilies(s"def n : Nat := scope l => scope m => same(V.mk(l), V.mk($second))\n")

    typecheckDecls(program("l"))
    expectOnly[TypeMismatch](typecheckDecls(program("m")))
  }

  // spec §6.2: a lifetime equation arises only between instances that share a scope, as `Two(a, b)` and `Two(b, a)` do.
  test("refinement links a lifetime variable to an atom but never links an atom") {
    def program(binders: String, a: String, b: String): String =
      withFamilies(
        s"""
           |def n : Nat := scope l => scope m => {
           |  let f := fun $binders(p: Eq(Type { scope = union($a, $b) }, Two($a, $b), Two($b, $a)))(w: Two($a, $b))
           |      : Two($b, $a) =>
           |    (match p returning Two($b, $a) with
           |    | Eq.refl x => w
           |    )
           |  0
           |}
           |""".stripMargin
      )

    typecheckDecls(program("(a: Lifetime)(b: Lifetime)", "a", "b"))
    typecheckDecls(program("(a: Lifetime)", "a", "m"))
    typecheckDecls(program("(b: Lifetime)", "l", "b"))
    // Two atoms: the equation is stuck, so the branch learns nothing.
    expectOnly[TypeMismatch](typecheckDecls(program("", "l", "m")))
  }

  // A type computed under a scope names the atom exactly when its sort does, so it cannot leave as a definition's value.
  test("a type computed under a scope is confined where the scope stands") {
    typecheckDecls(withFamilies("def T : Type := scope l => V(Lifetime.empty)\n"))
    val escaped = expectOnly[LifetimeEscapes](typecheckDecls(withFamilies("def T : Type := scope l => V(l)\n")))
    assertEquals(escaped.tpe.toString, "Type { scope = l }")
  }

  /**
   * A type naming the atom may stand at a local's binder, as an argument at a binder whose type is a sort, and as a
   * type a term is checked against, all inside the scope. Outside it only a `scope` term can name the atom, and that
   * term's own type, a sort that names it, is refused where the term stands.
   */
  test("a type at a binder, as an argument or as an expected type is confined") {
    typecheckDecls(
      withFamilies("def k : Nat := scope l => {\n  let x : V(l) := V.mk(l)\n  constNat(V(l))\n}\n")
    )
    typecheckDecls(withFamilies("def k : Nat := constNat(scope l => V(Lifetime.empty))\n"))
    val escaped =
      expectOnly[LifetimeEscapes](typecheckDecls(withFamilies("def k : Nat := constNat(scope l => V(l))\n")))
    assertEquals(escaped.tpe.toString, "Type { scope = l }")
  }

  test("a recursive call re-enters the same atom") {
    val program = withFamilies(
      """
        |def count (n: Nat): Nat decreases structural(n) := scope l =>
        |  match n returning Nat with
        |  | Nat.zero => same(V.mk(l), V.mk(l))
        |  | Nat.succ m => Nat.add(count(m), useV(V.mk(l)))
        |
        |{ count(3) }
        |""".stripMargin
    )
    assert(ValueEquivalence.defEq(runProgram(program), runProgram("{ 1 }")))
  }

  test("a closure derived inside a scope is at the atom, and its residual derives it again from the capture") {
    def program(annotation: String): String =
      withFamilies(
        s"def n : Nat := scope l => {\n  let v := V.mk(l)\n  let f$annotation := fun (u: Unit): Nat => useV(v)\n" +
          "  f(Unit.unit)\n}\n"
      )
    typecheckDecls(program(" : { scope = l } Unit -> Nat"))
    expectOnly[TypeMismatch](typecheckDecls(program(" : Unit -> Nat")))
    val (env, _, checked) = checkBody(program(""))
    // The residual carries the capture, and prints the derived field as omitted, as written.
    assert(checked.residual.toString.contains("fun (u: Unit): Nat"), checked.residual.toString)
    assert(ValueEquivalence.defEq(Interpreter.evalTerm(checked.residual, env), checked.value))
  }

  test("one scope term is one atom in checking and evaluation, and its residual keeps its node identity") {
    // A computation blocked on an opaque definition holds the atom, and may leave, since its type does not name it.
    val program =
      withFamilies("opaque def hold {l: Lifetime}(v: V(l)): Nat := 0\n\ndef f : Nat := scope l => hold(V.mk(l))\n")
    val (env, sourceTerm, checked) = checkBody(program)
    val (source, residual) = (sourceTerm, checked.residual) match {
      case (source: CA.Term.Scope, residual: CA.Term.Scope) => (source, residual)
      case other                                            => fail(s"Expected scope terms, got $other")
    }
    assertEquals(residual.id, source.id)
    assertEquals(Atoms.of(residual), Atoms.of(source))
    val first = Interpreter.evalTerm(residual, env)
    val second = Interpreter.evalTerm(residual, env)
    assertEquals(first.key, checked.value.key)
    assert(ValueEquivalence.defEq(first, checked.value))
    assert(ValueEquivalence.defEq(first, second))
    // A second scope term, however alike, opens another atom.
    val (_, otherTerm, _) = checkBody(program)
    otherTerm match {
      case other: CA.Term.Scope => assertNotEquals(Atoms.of(other), Atoms.of(source))
      case other                => fail(s"Expected a scope term, got $other")
    }
  }

  /** The declarations before the last one published, and the last definition's body checked where it stands. */
  private def checkBody(source: String): (Env, CA.Term, TypeChecker.CheckedTerm) = {
    val core = Elaborator.elab(parseSurface(source), Prelude.default)
    val env =
      core.decls.dropRight(1).foldLeft(Prelude.default.checkedEnv)((env, decl) => Interpreter.evalDecl(decl, env))
    core.decls.last match {
      case CA.Decl.ConstDecl(_, _, _, CA.ConstBody.TermBody(body), _, _) =>
        (env, body, TypeChecker.checkTerm(body, env))
      case other => fail(s"Expected a definition, got $other")
    }
  }
}
