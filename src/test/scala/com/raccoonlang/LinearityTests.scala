package com.raccoonlang

/**
 * Anonymous locals and the ledger (spec §1, §3.1-§3.5, §6.1): each local of linear type is used exactly once along
 * every path through its binder's extent, a lambda's body lying on those paths at the lambda's position, and no global
 * is linear. Each rule has an admitted program and the smallest mutation that reaches its diagnostic.
 */
class LinearityTests extends munit.FunSuite with TestSupport {

  /** A linear token, a linear pair of them, a linear chain, and a consumer of a token. */
  private val families =
    """
      |inductive Tok (l: Lifetime) : Type { kind = lin, scope = l }
      | | mk : Tok(l)
      |
      |inductive Two (l: Lifetime) : Type { kind = lin, scope = l }
      | | mk (a: Tok(l)) (b: Tok(l)) : Two(l)
      |
      |inductive Chain (l: Lifetime) : Type { kind = lin, scope = l }
      | | done : Chain(l)
      | | next (rest: Chain(l)) : Chain(l)
      |
      |def eat {l: Lifetime}(t: Tok(l)): Nat := match t returning Nat with
      | | Tok.mk => 0
      |""".stripMargin

  private def withFamilies(decls: String): String = families + "\n" + decls

  private def evaluatesTo(source: String, expected: String): Unit =
    assert(ValueEquivalence.defEq(runProgram(withFamilies(source)), runProgram(expected)))

  test("a linear parameter is used exactly once") {
    def program(body: String): String = withFamilies(s"def f {l: Lifetime}(t: Tok(l)): Nat := $body\n")

    typecheckDecls(program("eat(t)"))
    assertEquals(expectOnly[LinearUnused](typecheckDecls(program("0"))), LinearUnused("t"))
    assertEquals(expectOnly[LinearReused](typecheckDecls(program("Nat.add(eat(t), eat(t))"))), LinearReused("t"))
    // An unrestricted local is not tracked.
    typecheckDecls(withFamilies("def f (n: Nat): Nat := Nat.add(n, n)\ndef g (n: Nat): Nat := 0\n"))
  }

  test("a second use is reported where it stands, and no use at the binder") {
    val reused = withFamilies("def f {l: Lifetime}(t: Tok(l)): Nat := Nat.add(eat(t), eat(t))\n")
    assertEquals(interceptDiagnostic(typecheckDecls(reused)).span.map(_.start), Some(reused.lastIndexOf("t))")))
    val unused = withFamilies("def f {l: Lifetime}(t: Tok(l)): Nat := 0\n")
    assertEquals(interceptDiagnostic(typecheckDecls(unused)).span.map(_.start), Some(unused.lastIndexOf("(t: Tok(l))")))
  }

  test("uses are counted along each path that takes one branch at every match") {
    def program(onTrue: String, onFalse: String): String =
      withFamilies(
        s"def f {l: Lifetime}(b: Bool)(t: Tok(l)): Nat := match b returning Nat with\n" +
          s" | Bool.true => $onTrue\n | Bool.false => $onFalse\n"
      )

    typecheckDecls(program("eat(t)", "Nat.succ(eat(t))"))
    assertEquals(expectOnly[LinearUnused](typecheckDecls(program("eat(t)", "0"))), LinearUnused("t"))
    // Reused on one path and unused on another is the reuse (G8).
    assertEquals(
      expectOnly[LinearReused](typecheckDecls(program("Nat.add(eat(t), eat(t))", "0"))),
      LinearReused("t")
    )
    // A use before the match lies on every path through it.
    val before =
      withFamilies(
        "def f {l: Lifetime}(b: Bool)(t: Tok(l)): Nat := {\n  let n := eat(t)\n  match b returning Nat with\n" +
          "  | Bool.true => eat(t)\n  | Bool.false => n\n}\n"
      )
    expectOnly[LinearReused](typecheckDecls(before))
  }

  test("a let binds a tracked local, and `let _` an anonymous one") {
    def program(lets: String, result: String): String =
      withFamilies(s"def f {l: Lifetime}(t: Tok(l)): Nat := {\n$lets\n  $result\n}\n")

    typecheckDecls(program("  let u := t", "eat(u)"))
    typecheckDecls(program("  let _ := eat(t)", "0"))
    assertEquals(expectOnly[LinearUnused](typecheckDecls(program("  let u := t", "0"))), LinearUnused("u"))
    assertEquals(expectOnly[LinearUnused](typecheckDecls(program("  let _ := t", "0"))), LinearUnused("_"))
    assertEquals(
      expectOnly[LinearReused](typecheckDecls(program("  let u := t", "Nat.add(eat(u), eat(t))"))),
      LinearReused("t")
    )
  }

  test("`_` binds an anonymous local wherever a local is bound") {
    typecheckDecls("def f (n: Nat): Nat := {\n  let _ := n\n  scope _ => (fun (_: Nat): Nat => n)(0)\n}\n")
    // No name resolves to it: `_` is not a term.
    assert(LanguageParser.parseProgram("def f (n: Nat): Nat := {\n  let _ := n\n  _\n}\n").isInstanceOf[Failure])
  }

  test("matching a linear scrutinee consumes it and releases its fields to the ledger") {
    def program(pattern: String, body: String): String =
      withFamilies(s"def f {l: Lifetime}(w: Two(l)): Nat := match w returning Nat with\n | Two.mk $pattern => $body\n")

    typecheckDecls(program("a b", "Nat.add(eat(a), eat(b))"))
    assertEquals(expectOnly[LinearUnused](typecheckDecls(program("a b", "eat(a)"))), LinearUnused("b"))
    // A wildcard over a linear field binds an anonymous local, which is never used.
    assertEquals(expectOnly[LinearUnused](typecheckDecls(program("a _", "eat(a)"))), LinearUnused("_"))
    val consumed =
      withFamilies("def f {l: Lifetime}(t: Tok(l)): Nat := match t returning Nat with\n | Tok.mk => eat(t)\n")
    assertEquals(expectOnly[LinearReused](typecheckDecls(consumed)), LinearReused("t"))
  }

  test("a match with no branch uses every linear local live at it") {
    typecheckDecls(withFamilies("def f {l: Lifetime}(t: Tok(l))(h: False): Nat := match h returning Nat with\n"))
    // Through a global the branchless match is not in the extent.
    expectOnly[LinearUnused](
      typecheckDecls(withFamilies("def f {l: Lifetime}(t: Tok(l))(h: False): Nat := False.elim(h, Nat)\n"))
    )
    // A path the match ends still counts the uses before it.
    expectOnly[LinearReused](
      typecheckDecls(
        withFamilies(
          "def f {l: Lifetime}(t: Tok(l))(h: False): Nat := {\n  let n := Nat.add(eat(t), eat(t))\n" +
            "  match h returning Nat with\n}\n"
        )
      )
    )
  }

  test("a local whose type's kind is a variable is tracked") {
    typecheckDecls("def keep {k: Kind}{A: Type { kind = k }}(x: A): A := x\n")
    typecheckDecls("def drop {A: Type}(x: A): Nat := 0\n")
    assertEquals(
      expectOnly[LinearUnused](typecheckDecls("def drop {k: Kind}{A: Type { kind = k }}(x: A): Nat := 0\n")),
      LinearUnused("x")
    )
    expectOnly[LinearReused](
      typecheckDecls("def dup {k: Kind}{A: Type { kind = k }}(x: A)(f: A -> A -> Nat): Nat := f(x, x)\n")
    )
  }

  test("a closure that uses a captured linear local uses it on every path through its body") {
    def program(onFalse: String): String =
      withFamilies(
        "def f (l: Lifetime)(t: Tok(l)): { kind = lin, scope = l } Bool -> Nat :=\n" +
          s"  fun (b: Bool): Nat => match b returning Nat with\n | Bool.true => eat(t)\n | Bool.false => $onFalse\n"
      )

    typecheckDecls(program("eat(t)"))
    assertEquals(expectOnly[LinearUnused](typecheckDecls(program("0"))), LinearUnused("t"))
  }

  test("a use inside a lambda is one use, by the lambda, at its position") {
    def program(result: String): String =
      withFamilies(
        s"def f (l: Lifetime)(t: Tok(l)): Nat := {\n  let g := fun (u: Unit): Nat => eat(t)\n  $result\n}\n"
      )

    typecheckDecls(program("g(Unit.unit)"))
    assertEquals(expectOnly[LinearReused](typecheckDecls(program("Nat.add(g(Unit.unit), eat(t))"))), LinearReused("t"))
    // The lambda captures the token, so it is linear itself.
    assertEquals(expectOnly[LinearUnused](typecheckDecls(program("0"))), LinearUnused("g"))
    assertEquals(
      expectOnly[LinearReused](typecheckDecls(program("Nat.add(g(Unit.unit), g(Unit.unit))"))),
      LinearReused("g")
    )
  }

  test("a linear closure is tracked, and applying it is its use") {
    def program(body: String): String = s"def f (g: { kind = lin } Unit -> Nat): Nat := $body\n"

    typecheckDecls(program("g(Unit.unit)"))
    assertEquals(
      expectOnly[LinearReused](typecheckDecls(program("Nat.add(g(Unit.unit), g(Unit.unit))"))),
      LinearReused("g")
    )
    assertEquals(expectOnly[LinearUnused](typecheckDecls(program("0"))), LinearUnused("g"))
    typecheckDecls("def f (g: Unit -> Nat): Nat := Nat.add(g(Unit.unit), g(Unit.unit))\n")
  }

  test("a decreases clause is not a use") {
    evaluatesTo(
      """
        |def drain {l: Lifetime}(c: Chain(l)): Nat decreases structural(c) := match c returning Nat with
        | | Chain.done => 0
        | | Chain.next rest => Nat.succ(drain(rest))
        |
        |{ drain(Chain.next(Chain.next(Chain.done(Lifetime.empty)))) }
        |""".stripMargin,
      "{ 2 }"
    )
  }

  test("a struct selector applied to a linear value consumes it") {
    val box =
      "struct Box (l: Lifetime) : Type { kind = lin, scope = l }\n | mk (t: Tok(l)) : Box(l)\n\n"
    typecheckDecls(withFamilies(box + "def f {l: Lifetime}(b: Box(l)): Nat := eat(b.t)\n"))
    assertEquals(
      expectOnly[LinearReused](
        typecheckDecls(withFamilies(box + "def f {l: Lifetime}(b: Box(l)): Nat := Nat.add(eat(b.t), eat(b.t))\n"))
      ),
      LinearReused("b")
    )
  }

  test("a global is never tracked, so a definition of linear type is LinearGlobal") {
    typecheckDecls(withFamilies("def mint (l: Lifetime): Tok(l) := Tok.mk(l)\n"))
    val global =
      expectOnly[LinearGlobal](typecheckDecls(withFamilies("def t : Tok(Lifetime.empty) := Tok.mk(Lifetime.empty)\n")))
    assertEquals(global.name, "t")
    expectOnly[LinearGlobal](
      typecheckDecls(withFamilies("opaque def t : Tok(Lifetime.empty) := Tok.mk(Lifetime.empty)\n"))
    )
    expectOnly[LinearGlobal](
      typecheckDecls("def g : { kind = lin } Unit -> Nat := fun { kind = lin } (u: Unit): Nat => 0\n")
    )
  }

  test("one kind-polymorphic definition serves linear and unrestricted instantiations") {
    val program =
      """
        |def pass {k: Kind}{S: Lifetime}{A: Type { kind = k, scope = S }}(x: A): A := x
        |
        |def app {kf: Kind}{Sf: Lifetime}(f: { kind = kf, scope = Sf } Unit -> Nat): Nat := f(Unit.unit)
        |
        |def viaPass (l: Lifetime)(t: Tok(l)): Nat := Nat.add(eat(pass(t)), pass(3))
        |
        |def viaApp (l: Lifetime)(t: Tok(l)): Nat := Nat.add(app(fun (u: Unit): Nat => eat(t)), app(fun (u: Unit): Nat => 2))
        |
        |{ Nat.add(viaPass(Lifetime.empty, Tok.mk(Lifetime.empty)), viaApp(Lifetime.empty, Tok.mk(Lifetime.empty))) }
        |""".stripMargin
    evaluatesTo(program, "{ 5 }")
    // A definition that drops its argument exists only at `Kind.unr`.
    expectOnly[TypeMismatch](
      typecheckDecls(
        withFamilies("def drop {A: Type}(x: A): Nat := 0\n\ndef f (l: Lifetime)(t: Tok(l)): Nat := drop(t)\n")
      )
    )
  }
}
