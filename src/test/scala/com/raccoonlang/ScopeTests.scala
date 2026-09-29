package com.raccoonlang

import com.raccoonlang.{CoreAst => CA}

/**
 * `scope l => e` and atoms (spec §1, §4.1, §4.2, §6.2, §8): a `scope` term opens one atom, named by the term's node
 * identity in checking and evaluation alike, and a type that names it outside the scope is `LifetimeEscapes`. Each rule
 * has an admitted program and the smallest mutation that reaches its diagnostic.
 */
class ScopeTests extends munit.FunSuite with TestSupport {

  /** A family scoped by its lifetime, an unscoped one, and consumers of both. */
  private val families =
    """
      |inductive V (l: Lifetime) : Type { scope = l }
      | | mk : V(l)
      |
      |inductive W (l: Lifetime) : Type
      | | mk : W(l)
      |
      |def useV {l: Lifetime}(v: V(l)): Nat := 0
      |
      |def same {l: Lifetime}(a: W(l))(b: W(l)): Nat := 1
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
        |  same(W.mk(l), W.mk(l))
        |}
        |
        |{ n }
        |""".stripMargin
    )
    assert(ValueEquivalence.defEq(runProgram(program), runProgram("{ 1 }")))
  }

  test("a type that names the atom outside its scope is LifetimeEscapes") {
    def program(body: String): String = withFamilies(s"def n : Nat := $body\n")

    typecheckDecls(program("scope l => useV(V.mk(l))"))
    val escaped = expectOnly[LifetimeEscapes](typecheckDecls(program("useV(scope l => V.mk(l))")))
    assertEquals(escaped.lifetime, "l")
    assertEquals(escaped.tpe.toString, "V(l)")
    // An unscoped family names the atom in its value alone.
    expectOnly[LifetimeEscapes](
      typecheckDecls(withFamilies("def w : Nat := same(scope l => W.mk(l), W.mk(Lifetime.empty))\n"))
    )
    // The type's sort counts too.
    typecheckDecls("def s : Sort { level = succ(one) } := scope l => Type\n")
    expectOnly[LifetimeEscapes](typecheckDecls("def s : Sort { level = succ(one) } := scope l => Type { scope = l }\n"))
  }

  test("a closure whose code names the atom but captures nothing scoped may leave its scope") {
    def program(result: String, body: String): String =
      withFamilies(s"def leave : $result := scope l => {\n  let v := V.mk(l)\n  fun (u: Unit): Nat => $body\n}\n")

    val leave = program("Unit -> Nat", "useV(V.mk(l))")
    assert(ValueEquivalence.defEq(runProgram(leave + "\n{ leave(Unit.unit) }"), runProgram("{ 0 }")))
    // Capturing `v : V(l)` puts the atom in the closure's scope, so its type names it.
    expectOnly[LifetimeEscapes](typecheckDecls(program("Unit -> Nat", "useV(v)")))
  }

  test("nested scopes open distinct atoms") {
    def program(second: String): String =
      withFamilies(s"def n : Nat := scope l => scope m => same(W.mk(l), W.mk($second))\n")

    typecheckDecls(program("l"))
    expectOnly[TypeMismatch](typecheckDecls(program("m")))
  }

  test("refinement links a lifetime variable to an atom but never links an atom") {
    def program(binders: String, a: String, b: String): String =
      withFamilies(
        s"""
           |def n : Nat := scope l => scope m => {
           |  let f := fun $binders(p: Eq(Type, W($a), W($b)))(w: W($a)): W($b) =>
           |    (match p returning W($b) with
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

  /**
   * A definition whose type is a sort may compute a type naming an atom: its own type does not name it. Every use of it
   * as a type is confined.
   */
  private val computed = withFamilies("def T : Type := scope l => W(l)\n\ndef constNat (A: Type): Nat := 0\n")

  test("a local's type at its binder is confined") {
    typecheckDecls(computed + "def f (x: W(Lifetime.empty)): Nat := 0\n")
    expectOnly[LifetimeEscapes](typecheckDecls(computed + "def f (x: T): Nat := 0\n"))
  }

  test("an argument at a binder whose type is a sort is confined") {
    typecheckDecls(computed + "def k : Nat := constNat(W(Lifetime.empty))\n")
    expectOnly[LifetimeEscapes](typecheckDecls(computed + "def k : Nat := constNat(T)\n"))
  }

  test("a type a term is checked against is confined") {
    typecheckDecls(computed + "def t : Nat := 0\n")
    expectOnly[LifetimeEscapes](typecheckDecls(computed + "def t : T := 0\n"))
  }

  test("a recursive call re-enters the same atom") {
    val program = withFamilies(
      """
        |def count (n: Nat): Nat decreases structural(n) := scope l =>
        |  match n returning Nat with
        |  | Nat.zero => same(W.mk(l), W.mk(l))
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
    val (env, sourceTerm, checked) = checkBody(withFamilies("def T : Type := scope l => W(l)\n"))
    val (source, residual) = (sourceTerm, checked.residual) match {
      case (source: CA.Term.Scope, residual: CA.Term.Scope) => (source, residual)
      case other                                            => fail(s"Expected scope terms, got $other")
    }
    assertEquals(residual.nodeId, source.nodeId)
    assertEquals(Atoms.of(residual), Atoms.of(source))
    assertEquals(checked.value.toString, "W(l)")
    val first = Interpreter.evalTerm(residual, env)
    val second = Interpreter.evalTerm(residual, env)
    assertEquals(first.key, checked.value.key)
    assert(ValueEquivalence.defEq(first, checked.value))
    assert(ValueEquivalence.defEq(first, second))
    // A second scope term, however alike, opens another atom.
    val (_, _, other) = checkBody(withFamilies("def T : Type := scope l => W(l)\n"))
    assert(!ValueEquivalence.defEq(other.value, checked.value))
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
