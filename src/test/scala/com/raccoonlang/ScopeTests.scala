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
      "a function type's domain" -> "fun (v: V(@)): Nat => 0",
      "a function type's codomain" -> "fun (u: Unit): V(@) => V.mk(@)",
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

  test("a value whose type's sort does not name the atom may leave its scope, even when it holds the atom") {
    def program(result: String, body: String): String =
      withFamilies(s"def leave : $result := scope l => {\n  let v := V.mk(l)\n  fun (u: Unit): Nat => $body\n}\n")

    val leave = program("Unit -> Nat", "useV(V.mk(l))")
    assert(ValueEquivalence.defEq(runProgram(leave + "\n{ leave(Unit.unit) }"), runProgram("{ 0 }")))
    // Capturing `v : V(l)` puts the atom in the closure's scope, so its type names it.
    expectOnly[LifetimeEscapes](typecheckDecls(program("Unit -> Nat", "useV(v)")))
    // A type about the closure is at the closure type's scope, not at the atoms its value holds.
    typecheckDecls(leave + "def refl : Eq(Unit -> Nat, leave, leave) := Eq.refl(leave)\n")
    // So is a stuck computation that holds the atom.
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
    // The closure holds the atom and may leave, since its type does not name it.
    val program = withFamilies("def f : Unit -> Nat := scope l => fun (u: Unit): Nat => List.length(List.nil(V(l)))\n")
    val (env, sourceTerm, checked) = checkBody(program)
    val (source, residual) = (sourceTerm, checked.residual) match {
      case (source: CA.Term.Scope, residual: CA.Term.Scope) => (source, residual)
      case other                                            => fail(s"Expected scope terms, got $other")
    }
    assertEquals(residual.nodeId, source.nodeId)
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
