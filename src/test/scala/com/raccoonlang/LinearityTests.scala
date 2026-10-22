package com.raccoonlang

/**
 * Anonymous locals and the ledger (spec §1, §3.1-§3.5, §6.1): each local of linear type is used exactly once along
 * every path through its binder's extent, a lambda being one use at its position with paths of its own, and no global
 * is linear; and tokens stay out of types (spec §3.2, §3.5): no type or proof contains a subterm of linear type. Each
 * rule has an admitted program and the smallest mutation that reaches its diagnostic.
 */
class LinearityTests extends munit.FunSuite with TestSupport {

  /**
   * A linear token, a linear pair of them, a linear chain, a consumer of a token, and a proposition about a value of
   * any kind.
   */
  private val families =
    """
      |inductive Tok : Type { kind = lin }
      | | mk : Tok
      |
      |inductive Two : Type { kind = lin }
      | | mk (a: Tok) (b: Tok) : Two
      |
      |inductive Chain : Type { kind = lin }
      | | done : Chain
      | | next (rest: Chain) : Chain
      |
      |def eat (t: Tok): Nat := match t returning Nat with
      | | Tok.mk => 0
      |
      |inductive Fact {k: Kind}{A: Type { kind = k }}(x: A) : Prop
      |""".stripMargin

  private def withFamilies(decls: String): String = families + "\n" + decls

  private def evaluatesTo(source: String, expected: String): Unit =
    assert(ValueEquivalence.defEq(runProgram(withFamilies(source)), runProgram(expected)))

  test("a linear parameter is used exactly once") {
    def program(body: String): String = withFamilies(s"def f (t: Tok): Nat := $body\n")

    typecheckDecls(program("eat(t)"))
    assertEquals(expectOnly[LinearUnused](typecheckDecls(program("0"))), LinearUnused("t"))
    assertEquals(expectOnly[LinearReused](typecheckDecls(program("Nat.add(eat(t), eat(t))"))), LinearReused("t"))
    // An unrestricted local is not tracked.
    typecheckDecls(withFamilies("def f (n: Nat): Nat := Nat.add(n, n)\ndef g (n: Nat): Nat := 0\n"))
  }

  test("a second use is reported where it stands, and no use at the binder") {
    val reused = withFamilies("def f (t: Tok): Nat := Nat.add(eat(t), eat(t))\n")
    assertEquals(interceptDiagnostic(typecheckDecls(reused)).span.map(_.start), Some(reused.lastIndexOf("t))")))
    val unused = withFamilies("def f (t: Tok): Nat := 0\n")
    assertEquals(interceptDiagnostic(typecheckDecls(unused)).span.map(_.start), Some(unused.lastIndexOf("(t: Tok)")))
  }

  test("uses are counted along each path that takes one branch at every match") {
    def program(onTrue: String, onFalse: String): String =
      withFamilies(
        s"def f (b: Bool)(t: Tok): Nat := match b returning Nat with\n" +
          s" | Bool.true => $onTrue\n | Bool.false => $onFalse\n"
      )

    typecheckDecls(program("eat(t)", "Nat.succ(eat(t))"))
    assertEquals(expectOnly[LinearUnused](typecheckDecls(program("eat(t)", "0"))), LinearUnused("t"))
    // Reused on one path and unused on another is the reuse.
    assertEquals(
      expectOnly[LinearReused](typecheckDecls(program("Nat.add(eat(t), eat(t))", "0"))),
      LinearReused("t")
    )
    // A use before the match lies on every path through it.
    val before =
      withFamilies(
        "def f (b: Bool)(t: Tok): Nat := {\n  let n := eat(t)\n  match b returning Nat with\n" +
          "  | Bool.true => eat(t)\n  | Bool.false => n\n}\n"
      )
    expectOnly[LinearReused](typecheckDecls(before))
  }

  test("a let binds a tracked local, and `let _` an anonymous one") {
    def program(lets: String, result: String): String =
      withFamilies(s"def f (t: Tok): Nat := {\n$lets\n  $result\n}\n")

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
    typecheckDecls("def f (n: Nat): Nat := {\n  let _ := n\n  (fun (_: Nat): Nat => n)(0)\n}\n")
    // No name resolves to it: `_` is not a term.
    assert(LanguageParser.parseProgram("def f (n: Nat): Nat := {\n  let _ := n\n  _\n}\n").isInstanceOf[Failure])
  }

  test("matching a linear scrutinee consumes it and releases its fields to the ledger") {
    def program(pattern: String, body: String): String =
      withFamilies(s"def f (w: Two): Nat := match w returning Nat with\n | Two.mk $pattern => $body\n")

    typecheckDecls(program("a b", "Nat.add(eat(a), eat(b))"))
    assertEquals(expectOnly[LinearUnused](typecheckDecls(program("a b", "eat(a)"))), LinearUnused("b"))
    // A wildcard over a linear field binds an anonymous local, which is never used.
    assertEquals(expectOnly[LinearUnused](typecheckDecls(program("a _", "eat(a)"))), LinearUnused("_"))
    val consumed =
      withFamilies("def f (t: Tok): Nat := match t returning Nat with\n | Tok.mk => eat(t)\n")
    assertEquals(expectOnly[LinearReused](typecheckDecls(consumed)), LinearReused("t"))
  }

  test("an unused pattern field is reported at its pattern variable, a wildcard at its `_`") {
    def program(pattern: String, body: String): String =
      withFamilies(s"def f (w: Two): Nat := match w returning Nat with\n | Two.mk $pattern => $body\n")
    def reported(source: String): Option[(Int, String)] =
      interceptDiagnostic(typecheckDecls(source)).span.map(span => (span.start, source.substring(span.start, span.end)))

    val unusedB = program("a b", "eat(a)")
    assertEquals(reported(unusedB), Some((unusedB.lastIndexOf("b =>"), "b")))
    val unusedA = program("a b", "eat(b)")
    assertEquals(reported(unusedA), Some((unusedA.lastIndexOf("a b =>"), "a")))
    val wildcard = program("a _", "eat(a)")
    assertEquals(reported(wildcard), Some((wildcard.lastIndexOf("_ =>"), "_")))
  }

  test("a match with no branch uses every linear local live at it") {
    typecheckDecls(withFamilies("def f (t: Tok)(h: False): Nat := match h returning Nat with\n"))
    // Through a global the branchless match is not in the extent.
    expectOnly[LinearUnused](
      typecheckDecls(withFamilies("def f (t: Tok)(h: False): Nat := False.elim(h, Nat)\n"))
    )
    // A path the match ends still counts the uses before it.
    expectOnly[LinearReused](
      typecheckDecls(
        withFamilies(
          "def f (t: Tok)(h: False): Nat := {\n  let n := Nat.add(eat(t), eat(t))\n" +
            "  match h returning Nat with\n}\n"
        )
      )
    )
    // What follows it lies on no path.
    typecheckDecls(
      withFamilies(
        "def f (t: Tok)(h: False): Nat := {\n  let n := match h returning Nat with\n\n" +
          "  Nat.add(eat(t), eat(t))\n}\n"
      )
    )
  }

  test("a use on a path a branchless match ends is not a use on the paths that continue") {
    def program(onTrue: String, onFalse: String): String =
      withFamilies(
        "def toEmpty (t: Tok)(e: Empty): Empty := {\n  let _ := eat(t)\n  e\n}\n" +
          "def f (t: Tok)(b: Bool)(e: Empty): Nat := {\n  let first := match b returning Nat with\n" +
          s"    | .true => $onTrue\n    | .false => $onFalse\n  Nat.add(first, eat(t))\n}\n"
      )

    typecheckDecls(program("{\n      let n := eat(t)\n      match e returning Nat with\n    }", "0"))
    // The use in the ended path is its scrutinee's.
    typecheckDecls(program("{\n      match toEmpty(t, e) returning Nat with\n    }", "0"))
    // A path that uses it and continues still meets the use after the match.
    expectOnly[LinearReused](typecheckDecls(program("{\n      match e returning Nat with\n    }", "eat(t)")))
  }

  test("a path a lambda's body ends does not end the enclosing path") {
    val absurd = "fun (e: Empty): Nat => match e returning Nat with\n"
    def dropped(decls: String): LinearUnused = expectOnly[LinearUnused](typecheckDecls(withFamilies(decls)))

    // A parameter, a let and a pattern field, each dropped beside an absurd lambda.
    assertEquals(
      dropped(s"def f (t: Tok): Nat := {\n  let g := $absurd  7\n}\n"),
      LinearUnused("t")
    )
    assertEquals(
      dropped(s"def f (t: Tok): Nat := {\n  let u := t\n  let g := $absurd  7\n}\n"),
      LinearUnused("u")
    )
    assertEquals(
      dropped(
        "def f (w: Two): Nat := match w returning Nat with\n" +
          s" | Two.mk a b => {\n  let g := $absurd  eat(a)\n}\n"
      ),
      LinearUnused("b")
    )
    // An absurd lambda as an argument, and an inline proof of a negation.
    assertEquals(
      dropped(s"def ignore (f: Empty -> Nat): Nat := 7\ndef f (t: Tok): Nat := ignore($absurd)\n"),
      LinearUnused("t")
    )
    assertEquals(
      dropped(
        "def ignore (p: Not(False)): Nat := 7\n" +
          "def f (t: Tok): Nat := ignore(fun (h: False): False => match h returning False with\n)\n"
      ),
      LinearUnused("t")
    )
    // Inside a closure's body: its own parameter, and a captured local on one of its paths.
    assertEquals(
      dropped(
        "def f : Tok -> Nat :=\n" +
          s"  fun (t: Tok): Nat => {\n  let g := $absurd  7\n}\n"
      ),
      LinearUnused("t")
    )
    assertEquals(
      dropped(
        "def f (t: Tok): { kind = lin } Bool -> Nat :=\n" +
          "  fun (b: Bool): Nat => match b returning Nat with\n | Bool.true => eat(t)\n" +
          s" | Bool.false => {\n  let g := $absurd  0\n}\n"
      ),
      LinearUnused("t")
    )
  }

  test("a sealed module's client cannot drop an issued token beside an absurd proof") {
    val module = TestSupport.tokenModule
    def client(body: String): String =
      "def leak : Nat := {\n  let t := issue(Unit.unit)\n" +
        s"  let n : Not(False) := fun (h: False): False => match h returning False with\n\n  $body\n}\n"

    outside(module, client("burn(t)"))
    assertEquals(expectOnly[LinearUnused](outside(module, client("0"))), LinearUnused("t"))
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
        "def f (t: Tok): { kind = lin } Bool -> Nat :=\n" +
          s"  fun (b: Bool): Nat => match b returning Nat with\n | Bool.true => eat(t)\n | Bool.false => $onFalse\n"
      )

    typecheckDecls(program("eat(t)"))
    assertEquals(expectOnly[LinearUnused](typecheckDecls(program("0"))), LinearUnused("t"))
    assertEquals(
      expectOnly[LinearReused](typecheckDecls(program("Nat.add(eat(t), eat(t))"))),
      LinearReused("t")
    )
    // A path through the body that a branchless match ends needs no use of its own.
    typecheckDecls(
      withFamilies(
        "def f (t: Tok)(e: Empty): { kind = lin } Bool -> Nat :=\n" +
          "  fun (b: Bool): Nat => match b returning Nat with\n | Bool.true => eat(t)\n" +
          " | Bool.false => {\n  match e returning Nat with\n}\n"
      )
    )
  }

  test("a use inside a lambda is one use, by the lambda, at its position") {
    def program(result: String): String =
      withFamilies(
        s"def f (t: Tok): Nat := {\n  let g := fun (u: Unit): Nat => eat(t)\n  $result\n}\n"
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
        |def drain (c: Chain): Nat decreases structural(c) := match c returning Nat with
        | | Chain.done => 0
        | | Chain.next rest => Nat.succ(drain(rest))
        |
        |{ drain(Chain.next(Chain.next(Chain.done))) }
        |""".stripMargin,
      "{ 2 }"
    )
  }

  test("a struct selector applied to a linear value consumes it") {
    val box =
      "struct Box  : Type { kind = lin }\n | mk (t: Tok) : Box\n\n"
    typecheckDecls(withFamilies(box + "def f (b: Box): Nat := eat(b.t)\n"))
    assertEquals(
      expectOnly[LinearReused](
        typecheckDecls(withFamilies(box + "def f (b: Box): Nat := Nat.add(eat(b.t), eat(b.t))\n"))
      ),
      LinearReused("b")
    )
  }

  test("a global is never tracked, so a definition of linear type is LinearGlobal") {
    typecheckDecls(withFamilies("def mint (u: Unit): Tok := Tok.mk\n"))
    val global =
      expectOnly[LinearGlobal](typecheckDecls(withFamilies("def t : Tok := Tok.mk\n")))
    assertEquals(global.definition, Some("t"))
    expectOnly[LinearGlobal](
      typecheckDecls("def g : { kind = lin } Unit -> Nat := fun { kind = lin } (u: Unit): Nat => 0\n")
    )
  }

  test("the program's result is outside every binder, so a linear one is LinearGlobal") {
    // A module whose protocol is that every handle it opens is closed.
    val file =
      """
        |sealed inductive Handle : Type { kind = lin }
        | | mk : Handle
        |
        |def openFile (u: Unit): Handle := Handle.mk
        |
        |def closeFile (h: Handle): Nat := match h returning Nat with
        | | .mk => 0
        |""".stripMargin

    def evaluatesTo(client: String, expected: String): Unit =
      assert(outside(file, client).exists(ValueEquivalence.defEq(_, runProgram(expected))))

    evaluatesTo("{ closeFile(openFile(Unit.unit)) }", "{ 0 }")
    // Built from a token it consumed, the result is unrestricted.
    evaluatesTo("{\n  let h := openFile(Unit.unit)\n  Nat.succ(closeFile(h))\n}", "{ 1 }")
    val handle = expectOnly[LinearGlobal](outside(file, "{ openFile(Unit.unit) }"))
    assertEquals(handle.definition, None)
    // A linear closure that would close the handle, never applied.
    val closure = "{\n  let h := openFile(Unit.unit)\n  fun (u: Unit): Nat => closeFile(h)\n}"
    val diagnostic = interceptDiagnostic(outside(file, closure))
    assert(diagnostic.error.isInstanceOf[LinearGlobal], diagnostic)
    assertEquals(diagnostic.span.map(_.start), Some("import Module\n".length + closure.indexOf("fun")))
  }

  test("one kind-polymorphic definition serves linear and unrestricted instantiations") {
    val program =
      """
        |def pass {k: Kind}{A: Type { kind = k }}(x: A): A := x
        |
        |def app {kf: Kind}(f: { kind = kf } Unit -> Nat): Nat := f(Unit.unit)
        |
        |def viaPass (t: Tok): Nat := Nat.add(eat(pass(t)), pass(3))
        |
        |def viaApp (t: Tok): Nat := Nat.add(app(fun (u: Unit): Nat => eat(t)), app(fun (u: Unit): Nat => 2))
        |
        |{ Nat.add(viaPass(Tok.mk), viaApp(Tok.mk)) }
        |""".stripMargin
    evaluatesTo(program, "{ 5 }")
    // A definition that drops its argument exists only at `Kind.unr`.
    expectOnly[TypeMismatch](
      typecheckDecls(
        withFamilies("def drop {A: Type}(x: A): Nat := 0\n\ndef f (t: Tok): Nat := drop(t)\n")
      )
    )
  }

  test("a type in a type position contains no subterm of linear type") {
    def program(factType: String): String =
      withFamilies(s"def f (t: Tok)(n: Nat)(p: $factType): Nat := eat(t)\n")

    typecheckDecls(program("Fact(n)"))
    val inType = program("Fact(t)")
    val diagnostic = interceptDiagnostic(typecheckDecls(inType))
    assertEquals(PrettyPrinter.printTerm(expectOnly[LinearInType](typecheckDecls(inType)).term), "t")
    // Located at the linear subterm, and reported before the ledger would count it as a use.
    assertEquals(diagnostic.span.map(_.start), Some(inType.indexOf("Fact(t)") + "Fact(".length))
    // The subterm need not be the type's own argument: here it is inside one.
    expectOnly[LinearInType](typecheckDecls(program("Eq(Nat, eat(t), 0)")))
    // A kind-polymorphic local is linear, so it stays out of types too. `Eq` takes a type at `Kind.unr`, so there the
    // application is ill-typed first.
    typecheckDecls("def f {A: Type}{x: A}(p: Eq(A, x, x)): Nat := 0\n")
    expectOnly[TypeMismatch](
      typecheckDecls("def f {k: Kind}{A: Type { kind = k }}{x: A}(p: Eq(A, x, x)): Nat := 0\n")
    )
    expectOnly[LinearInType](
      typecheckDecls(
        withFamilies("def f {k: Kind}{A: Type { kind = k }}{x: A}(p: Fact(x)): Nat := 0\n")
      )
    )
    // A linear function value is a token like any other.
    typecheckDecls("def h : Prop := Eq(Nat, (fun (n: Nat): Nat => n)(0), 0)\n")
    expectOnly[LinearInType](typecheckDecls("def h : Prop := Eq(Nat, (fun { kind = lin } (n: Nat): Nat => n)(0), 0)\n"))
  }

  test("a type computed as a value, and a returning motive, contain no token") {
    typecheckDecls("def T (b: Bool): Type := match b returning Type with\n | Bool.true => Nat\n | Bool.false => Unit\n")
    expectOnly[LinearInType](
      typecheckDecls(
        withFamilies("def T (t: Tok): Type := match t returning Type with\n | Tok.mk => Nat\n")
      )
    )
    def program(motive: String): String =
      withFamilies(
        s"def f (n: Nat)(t: Tok)(u: Tok): Nat := match u returning $motive with\n | Tok.mk => eat(t)\n"
      )
    typecheckDecls(program("Nat"))
    expectOnly[LinearInType](typecheckDecls(program("Fact(t)")))
  }

  test("a proof holds no token, so no proof takes or consumes one") {
    def program(result: String, body: String): String =
      withFamilies(
        s"def burn (t: Tok): $result := match t returning $result with\n | Tok.mk => $body\n"
      )

    typecheckDecls(program("Nat", "0"))
    expectOnly[LinearInType](typecheckDecls(program("True", "True.intro")))
    // A proof that leaves the token alone must still use it.
    assertEquals(
      expectOnly[LinearUnused](typecheckDecls(withFamilies("def keep (t: Tok): True := True.intro\n"))),
      LinearUnused("t")
    )
    // A linear function into a proposition is refused at its type, before anything holds it.
    expectOnly[KindExceeded](
      typecheckDecls("def f : Unit -> True := fun { kind = lin } (u: Unit): True => True.intro\n")
    )
  }

  test("a lambda inside a type that consumes its own linear parameter is refused; a named one is not") {
    def program(argument: String): String =
      withFamilies(
        "def g (f: Tok -> Nat): Prop := True\n\n" +
          "def eatIn : Tok -> Nat := fun (t: Tok): Nat => eat(t)\n\n" +
          s"def h : Prop := g($argument)\n"
      )

    typecheckDecls(program("eatIn"))
    assertEquals(
      PrettyPrinter.printTerm(expectOnly[LinearInType](typecheckDecls(program("fun (t: Tok): Nat => eat(t)"))).term),
      "t"
    )
  }

  test("an implicit of linear type is never forced") {
    typecheckDecls(withFamilies("def f (t: Tok)(n: Nat): Nat := eat(t)\n"))
    assertEquals(
      expectOnly[NonForcedImplicitParam](
        typecheckDecls(withFamilies("def f {t: Tok}(n: Nat): Nat := eat(t)\n"))
      ),
      NonForcedImplicitParam("t", isProposition = false)
    )
    // Only a type could force it, and no type may name it.
    expectOnly[LinearInType](
      typecheckDecls(withFamilies("def f {t: Tok}(p: Fact(t)): Nat := eat(t)\n"))
    )
  }

  test("facts about a token are stated about its indices") {
    val coin =
      """
        |inductive Coin  indices (n: Nat) : Type { kind = lin }
        | | mk (n: Nat) : Coin(n)
        |""".stripMargin
    def program(fact: String): String =
      coin +
        s"\ndef spend {n: Nat}(c: Coin(n))(p: $fact): Nat := match c returning Nat with\n" +
        " | Coin.mk m => m\n"

    evaluatesTo(program("Eq(Nat, n, 1)") + "\n{ spend(Coin.mk(1), Eq.refl(1)) }\n", "{ 1 }")
    expectOnly[LinearInType](typecheckDecls(withFamilies(program("Fact(c)"))))
  }

  test("a linear struct's selector is rejected when another field is linear or its field is dependent") {
    // A selector binds every field and returns one, so another linear field is unused (spec §3.5).
    val couple = withFamilies(
      "struct Couple  : Type { kind = lin }\n | mk (a: Tok) (b: Tok) : Couple\n"
    )
    assertEquals(
      interceptDiagnostics(typecheckDecls(couple)).map(_.error),
      Vector(LinearUnused("b"), LinearUnused("a"))
    )
    // A dependent field's selector names the earlier field's selector applied to the struct value in its result type.
    // The family is still published, as are the other selectors.
    def sized(fieldType: String): String =
      "inductive Tag (n: Nat) : Type\n | mk : Tag(n)\n\n" +
        s"struct Sized : Type { kind = lin }\n | mk (n: Nat) (t: $fieldType) : Sized\n\n" +
        "def size (s: Sized): Nat := s.n\n"
    typecheckDecls(sized("Tag(0)"))
    val dependent = sized("Tag(n)")
    val diagnostic = interceptDiagnostic(typecheckDecls(dependent))
    val inType = expectOnly[LinearInType](typecheckDecls(dependent))
    assertEquals((PrettyPrinter.printTerm(inType.term), inType.tpe.toString), ("self", "Sized"))
    assertEquals(diagnostic.span.map(_.start), Some(dependent.lastIndexOf("Tag(n)") + "Tag(".length))
    assertEquals(diagnostic.frames, Vector(Frame.InDefinition("Sized.t")))
    // A proof field's selector is a proof that consumes the struct value (spec §3.2).
    expectOnly[LinearInType](
      typecheckDecls(sized("Tag(0)") + "\nstruct Proved : Type { kind = lin }\n | mk (p: True) : Proved\n")
    )
  }
}
