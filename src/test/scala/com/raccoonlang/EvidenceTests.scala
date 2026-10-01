package com.raccoonlang

/**
 * Evidence arguments discharged by rule 1 (docs/PROOF_BY_EVALUATION.md §1.1–1.7): an evidence binder `[h: P]` in a
 * definition's, a lambda's or a function type's telescope, discharged at each application by evaluating `P` there and
 * applying a constructor whose fields its result type determines, or supplied in a bracket group `f(x)[p]`. Each rule
 * has an admitted program and the smallest mutation that reaches its diagnostic.
 *
 * `Same` is an equality whose constructor is fieldless, `IsTrue` a proposition that checks a decision procedure's
 * result, and `SameP` an equality between proofs.
 */
class EvidenceTests extends munit.FunSuite with TestSupport {

  private def evaluatesTo(source: String, expected: String)(implicit loc: munit.Location): Unit =
    evaluatesTo(source, expected, suitePrelude)

  private def evaluatesTo(source: String, expected: String, prelude: Prelude.Config)(implicit
      loc: munit.Location
  ): Unit =
    assertEquals(PrettyPrinter.print(runProgram(source, prelude)), expected)

  /** The failure an application reports, for the evidence binder `binder` of `callee`. */
  private def notDischarged(source: String, binder: String, callee: String)(implicit
      loc: munit.Location
  ): EvidenceNotDischarged = {
    val failure = expectOnly[EvidenceNotDischarged](typecheckDecls(source))
    assertEquals((failure.binder, failure.callee), (binder, callee))
    failure
  }

  /** The proposition an application failed to discharge because no constructor fits, printed. */
  private def noConstructor(source: String, binder: String, callee: String)(implicit loc: munit.Location): String = {
    val failure = notDischarged(source, binder, callee)
    assertEquals(failure.reason, EvidenceNotDischarged.NoConstructor)
    PrettyPrinter.print(failure.proposition)
  }

  private val families =
    "inductive Same {A: Type}(a: A) indices (b: A) : Prop\n | refl : Same(a, a)\n\n" +
      "inductive IsTrue indices (b: Bool) : Prop\n | yes : IsTrue(Bool.true)\n\n" +
      "inductive SameP {A: Prop}(a: A) indices (b: A) : Prop\n | refl : SameP(a, a)\n\n"

  /** `def need [h: P]: Nat := 1`, whose proposition is closed. */
  private def needing(proposition: String): String = families + s"def need [h: $proposition]: Nat := 1\n\n"

  private val three = families + "def three (n: Nat)[h: Eq(Nat, n, 3)]: Nat := n\n\n"

  test("an evidence argument is discharged by evaluating its proposition where the application stands") {
    evaluatesTo(three + "{ three(3) }", "3")
    evaluatesTo(three + "{ three(Nat.add(1, 2)) }", "3")
    assertEquals(noConstructor(three + "{ three(4) }", "h", "three"), "Eq(Nat, 4, 3)")
    // The proposition is evaluated with the call's arguments, so a decision procedure in it runs.
    val positive = families + "def pred (n: Nat)[h: Eq(Bool, Nat.blt(0, n), Bool.true)]: Nat := Nat.sub(n, 1)\n\n"
    evaluatesTo(positive + "{ pred(5) }", "4")
    assertEquals(noConstructor(positive + "{ pred(0) }", "h", "pred"), "Eq(Bool, Bool.false, Bool.true)")
  }

  test("a constructor discharges when its fields are read off the proposition, and never by inventing one") {
    evaluatesTo(needing("True") + "{ need() }", "1")
    // `Eq.refl`'s field is the argument its result type repeats, so it is read off the proposition.
    evaluatesTo(needing("Eq(Nat, Nat.mul(2, 3), 6)") + "{ need() }", "1")
    evaluatesTo(needing("Same(Nat.mul(2, 3), 6)") + "{ need() }", "1")
    evaluatesTo(needing("IsTrue(Nat.blt(2, 3))") + "{ need() }", "1")
    assertEquals(noConstructor(needing("False") + "{ need() }", "h", "need"), "False")
    assertEquals(noConstructor(needing("Eq(Nat, 2, 3)") + "{ need() }", "h", "need"), "Eq(Nat, 2, 3)")
    // A field its result type does not determine would have to be invented, though here one could be proved.
    assertEquals(noConstructor(needing("And(True, True)") + "{ need() }", "h", "need"), "And(True, True)")
    assertEquals(noConstructor(needing("Or(True, False)") + "{ need() }", "h", "need"), "Or(True, False)")
    noConstructor(
      families + "def isZero (n: Nat): Prop := Eq(Nat, n, 0)\n\ndef need [h: Exists(Nat, isZero)]: Nat := 1\n\n{ need() }",
      "h",
      "need"
    )
    // A field inside an argument of the result type cannot be read back.
    val succ = "inductive Succ indices (n: Nat) : Prop\n | mk (m: Nat) : Succ(Nat.succ(m))\n\n"
    assertEquals(noConstructor(succ + needing("Succ(4)") + "{ need() }", "h", "need"), "Succ(4)")
    // A proof field is read off the proposition as a data field is.
    val holds = "inductive Holds indices (p: True) : Prop\n | mk (h: True) : Holds(h)\n\n"
    evaluatesTo(holds + needing("Holds(True.intro)") + "{ need() }", "1")
    // The constructors are tried in declaration order, and the first that fits is taken.
    val le =
      "inductive Le (n: Nat) indices (m: Nat) : Prop\n | refl : Le(n, n)\n | step (m: Nat)(h: Le(n, m)) : " +
        "Le(n, Nat.succ(m))\n\n"
    evaluatesTo(le + needing("Le(3, 3)") + "{ need() }", "1")
    assertEquals(noConstructor(le + needing("Le(3, 4)") + "{ need() }", "h", "need"), "Le(3, 4)")
    val two = "inductive B indices (b: Bool) : Prop\n | t : B(Bool.true)\n | f : B(Bool.false)\n\n"
    evaluatesTo(two + needing("B(Bool.false)") + "{ need() }", "1")
  }

  test("a proposition that stays neutral is not discharged, and one whose sides convert is") {
    // Generic code knows no concrete argument, so its proposition stays neutral.
    assertEquals(noConstructor(three + "def g (n: Nat): Nat := three(n)\n", "h", "three"), "Eq(Nat, n, 3)")
    assertEquals(
      noConstructor("def any (P: Prop)[h: P]: Nat := 1\n\ndef g (Q: Prop): Nat := any(Q)\n", "h", "any"),
      "Q"
    )
    // An instance whose sides convert is discharged, neutral or not.
    evaluatesTo(
      "def same (a: Nat)(b: Nat)[h: Eq(Nat, a, b)]: Nat := b\n\ndef g (n: Nat): Nat := same(n, n)\n\n{ g(7) }",
      "7"
    )
  }

  test("generic code forwards the evidence it has, and its callers discharge theirs") {
    val forward = three + "def g (n: Nat)[h: Eq(Nat, n, 3)]: Nat := Nat.add(three(n)[h], 1)\n\n"
    evaluatesTo(forward + "{ g(3) }", "4")
    assertEquals(noConstructor(forward + "{ g(2) }", "h", "g"), "Eq(Nat, 2, 3)")
    // Any proof of the proposition is supplied the same way, one rule 1 would not find included.
    evaluatesTo(three + "{ three(3)[Eq.refl(3)] }", "3")
    evaluatesTo(needing("And(True, True)") + "{ need()[And.intro(True.intro, True.intro)] }", "1")
  }

  test("a supplied proof is checked against the evaluated proposition, one proof per evidence binder") {
    val mismatch = expectOnly[TypeMismatch](typecheckDecls(three + "{ three(3)[Eq.refl(4)] }"))
    assertEquals(PrettyPrinter.print(mismatch.expected), "Eq(Nat, 3, 3)")
    assertEquals(
      expectOnly[ArityMismatch](typecheckDecls(three + "{ three(3)[Eq.refl(3), Eq.refl(3)] }")),
      ArityMismatch(1, 2, ArityMismatch.Evidence)
    )
    assertEquals(
      expectOnly[ArityMismatch](typecheckDecls("def same (n: Nat): Nat := n\n\n{ same(3)[True.intro] }")),
      ArityMismatch(0, 1, ArityMismatch.Evidence)
    )
    // Proofs hold no tokens, a supplied one included.
    val tokens =
      "inductive Tok (l: Lifetime) : Type { kind = lin, scope = l }\n | mk : Tok(l)\n\n" +
        "def eat {l: Lifetime}(t: Tok(l)): Nat := match t returning Nat with\n | Tok.mk => 3\n\n"
    expectOnly[LinearInType](
      typecheckDecls(tokens + three + "def g {l: Lifetime}(t: Tok(l)): Nat := three(3)[Eq.refl(eat(t))]\n")
    )
  }

  test("evidence mixes with implicit and explicit binders in any order, each proposition over earlier binders") {
    val mixed =
      families + "def m {A: Type}(x: A)[h1: Eq(A, x, x)](n: Nat)[h2: IsTrue(Nat.beq(n, 2))]{B: Type}(b: B): B := b\n\n"
    evaluatesTo(mixed + "{ m(Bool.false, 2, 5) }", "5")
    assertEquals(noConstructor(mixed + "{ m(Bool.false, 3, 5) }", "h2", "m"), "IsTrue(Bool.false)")
    evaluatesTo(mixed + "{ m(Bool.false, 2, 5)[Eq.refl(Bool.false), IsTrue.yes] }", "5")
    assertEquals(
      expectOnly[ArityMismatch](typecheckDecls(mixed + "{ m(Bool.false, 2, 5)[Eq.refl(Bool.false)] }")),
      ArityMismatch(2, 1, ArityMismatch.Evidence)
    )
    // Evidence first, then an explicit binder, which its proposition cannot mention.
    evaluatesTo("def first [h: True](n: Nat): Nat := n\n\n{ first(4) }", "4")
    assertEquals(
      expectOnly[NotFound](typecheckDecls("def later [h: Eq(Nat, n, 3)](n: Nat): Nat := n\n")),
      NotFound("n")
    )
    // A proposition over an earlier evidence binder.
    evaluatesTo(families + "def two [h1: True][h2: SameP(h1, True.intro)]: Nat := 5\n\n{ two() }", "5")
  }

  test("a definition whose only parameters are evidence is applied to no arguments, in a type as anywhere") {
    evaluatesTo(needing("True") + "{ need() }", "1")
    // Named alone it is the function, whose type keeps its evidence binder.
    evaluatesTo(needing("True") + "def f : [h: True] -> Nat := need\n\n{ f() }", "1")
    expectOnly[TypeMismatch](typecheckDecls(needing("True") + "def f : Nat := need\n"))
    val typed = "def g [h: True]: Type := Nat\n\n"
    evaluatesTo(typed + "def k (x: g()): Nat := x\n\n{ k(3) }", "3")
    evaluatesTo(typed + "{\n  let x : g() := 4\n  x\n}", "4")
    evaluatesTo(typed + "def k : (g()) -> Nat := fun (x: Nat): Nat => x\n\n{ k(5) }", "5")
  }

  test("a lambda binds evidence, applied directly and through a function type") {
    evaluatesTo("{ (fun (x: Nat)[h: Eq(Nat, x, 3)]: Nat => Nat.add(x, 1))(3) }", "4")
    evaluatesTo("{ (fun [h: True]: Nat => 5)() }", "5")
    assertEquals(
      noConstructor("def v : Nat := (fun (x: Nat)[h: Eq(Nat, x, 3)]: Nat => x)(4)\n", "h", "function"),
      "Eq(Nat, 4, 3)"
    )
    val typed = "def viaType : (x: Nat) -> [h: Eq(Nat, x, 3)] -> Nat := fun (x: Nat)[h: Eq(Nat, x, 3)]: Nat => x\n\n"
    evaluatesTo(typed + "{ viaType(3) }", "3")
    assertEquals(noConstructor(typed + "{ viaType(5) }", "h", "viaType"), "Eq(Nat, 5, 3)")
  }

  test("the evidence mode is part of a function type's identity, and a higher-order argument keeps it") {
    val takes = "def takes (f: (x: Nat) -> [h: Eq(Nat, x, 3)] -> Nat): Nat := f(3)\n\n"
    evaluatesTo(takes + "{ takes(fun (x: Nat)[h: Eq(Nat, x, 3)]: Nat => Nat.add(x, 4)) }", "7")
    expectOnly[TypeMismatch](typecheckDecls(takes + "{ takes(fun (x: Nat)(h: Eq(Nat, x, 3)): Nat => x) }"))
    expectOnly[TypeMismatch](
      typecheckDecls(
        "def takes (f: (x: Nat) -> (h: Eq(Nat, x, 3)) -> Nat): Nat := f(3, Eq.refl(3))\n\n" +
          "{ takes(fun (x: Nat)[h: Eq(Nat, x, 3)]: Nat => x) }"
      )
    )
    // Applied inside the higher-order function, the parameter's evidence is discharged from its type there.
    assertEquals(
      noConstructor("def takes (f: (x: Nat) -> [h: Eq(Nat, x, 3)] -> Nat): Nat := f(2)\n", "h", "f"),
      "Eq(Nat, 2, 3)"
    )
    // A proposition over the higher-order function's own parameter, neutral but with convertible sides.
    evaluatesTo(
      "def at (n: Nat)(f: (x: Nat) -> [h: Eq(Nat, x, n)] -> Nat): Nat := f(n)\n\n" +
        "{ at(6, fun (x: Nat)[h: Eq(Nat, x, 6)]: Nat => x) }",
      "6"
    )
  }

  test("a function type's key tells its binders' modes apart, as conversion does") {
    val explicit = runProgram("{ (h: True) -> Nat }") match {
      case pi: Value.VPi => pi
      case other         => fail(s"expected a function type, got $other")
    }
    // The same node and captures at another mode: only the key's own mix of the modes can tell them apart.
    val evidence = explicit.copy(binders = explicit.binders.map(_.copy(mode = BinderMode.Evidence)))
    assertNotEquals(explicit.key, evidence.key)
    assert(!ValueEquivalence.defEq(explicit, evidence))
    assert(ValueEquivalence.defEq(evidence, evidence.copy()))
  }

  test("a bracket group follows an application's arguments, with no space, and is not empty") {
    def parseError(source: String): String =
      LanguageParser.parseProgram(source) match {
        case Failure(_, _, message) => message
        case _: Success[_]          => fail(s"expected a parse error in:\n$source")
      }
    val spaced = "Evidence follows the arguments with no space: write f(a)[h]"
    val misplaced = "An evidence group follows an application's arguments: write f(a)[h]"
    assertEquals(parseError(three + "{ three(3) [Eq.refl(3)] }"), spaced)
    assertEquals(parseError(three + "def k (p: Eq(Nat, three(3) [Eq.refl(3)], 3)): Nat := 0\n"), spaced)
    assertEquals(parseError(three + "{ three[Eq.refl(3)] }"), misplaced)
    assertEquals(parseError(three + "{ three(3)[] }"), "An evidence group supplies at least one proof")
    assertEquals(parseError(three + "{ three(3)[Eq.refl(3)][Eq.refl(3)] }"), misplaced)
    assertEquals(parseError(three + "{ (1, 2)[True.intro] }"), misplaced)
    assertEquals(parseError("inductive F [h: True] : Type\n"), "A family's parameters and indices are not evidence")
    assertEquals(
      parseError("inductive F indices [h: True] : Type\n"),
      "A family's parameters and indices are not evidence"
    )
    // A bracket group applies in a type as anywhere, and its result may be applied again.
    evaluatesTo(three + "def t (p: Eq(Nat, three(3)[Eq.refl(3)], 3)): Nat := 0\n\n{ t(Eq.refl(3)) }", "0")
    evaluatesTo(
      "def k (n: Nat)[h: Eq(Nat, n, 1)]: Nat -> Nat := fun (m: Nat): Nat => Nat.add(n, m)\n\n{ k(1)[Eq.refl(1)](2) }",
      "3"
    )
    // A function type's binder group may be spaced, and so may an evidence binder in it.
    evaluatesTo(
      "def f (g: (x: Nat) [h: Eq(Nat, x, 1)] -> Nat): Nat := g(1)\n\n{ f(fun (x: Nat)[h: Eq(Nat, x, 1)]: Nat => x) }",
      "1"
    )
  }

  test("a function type prints its evidence binders as written") {
    assertEquals(PrettyPrinter.print(runProgram(three + "{ three }").tpe), "(n: Nat) -> [h: Eq(Nat, n, 3)] -> Nat")
    assertEquals(PrettyPrinter.print(runProgram("{ fun [h: True]: Nat => 5 }").tpe), "[h: True] -> Nat")
  }

  test("an evidence binder is never a source for forcing, supplied or not") {
    assertEquals(
      expectOnly[NonForcedImplicitParam](typecheckDecls("def f {n: Nat}[h: Eq(Nat, n, 3)]: Nat := n\n")),
      NonForcedImplicitParam("n", isProposition = false)
    )
    // An unforced implicit proposition is refused as any unforced implicit is, and its message points to evidence.
    val failure = interceptDiagnostic(typecheckDecls("def f {h: True}(n: Nat): Nat := n\n"))
    assertEquals(failure.error, NonForcedImplicitParam("h", isProposition = true))
    assert(failure.getMessage.contains("[h: …]"), failure.getMessage)
  }

  test("an evidence binder's type is a proposition") {
    assertEquals(expectOnly[NotAProposition](typecheckDecls("def f [h: Nat]: Nat := 0\n")).binder, "h")
    expectOnly[NotAProposition](typecheckDecls("def f (n: Nat): Nat := (fun [h: Bool]: Nat => n)()\n"))
    expectOnly[NotAProposition](typecheckDecls("def f (g: [l: Lifetime] -> Nat): Nat := 0\n"))
    expectOnly[NotAProposition](typecheckDecls("def f {u: Level}(P: Sort { level = u })[h: P]: Nat := 0\n"))
    // A proposition a definition computes is one.
    evaluatesTo(
      "def isThree (n: Nat): Prop := Eq(Nat, n, 3)\n\ndef f (n: Nat)[h: isThree(n)]: Nat := n\n\n{ f(3) }",
      "3"
    )
  }

  test("a sealed family's constructor discharges evidence only in its module") {
    val module = "sealed inductive Permit : Prop\n | mk : Permit\n\ndef need [p: Permit]: Nat := 1\n"
    assertEquals(inside(module, "{ need() }").map(PrettyPrinter.print), Some("1"))
    assertEquals(expectOnly[EvidenceNotDischarged](outside(module, "{ need() }")).reason, EvidenceNotDischarged.Sealed)
    // A proof the module hands out is forwarded as any proof is.
    val exporting = module + "def permit : Permit := Permit.mk\n"
    assertEquals(outside(exporting, "{ need()[permit] }").map(PrettyPrinter.print), Some("1"))
  }

  test("a family whose constructors are not yet declared discharges nothing") {
    val failure = notDischarged(
      families + "def need (P: Prop)[h: P]: Nat := 1\n\ninductive U : Prop\n | mk (x: Same(need(U), 1)) : U\n",
      "h",
      "need"
    )
    assertEquals(failure.reason, EvidenceNotDischarged.Undeclared)
  }

  test("running a program evaluates no proposition, even where a head stores its evidence") {
    // `spin(k)` makes 2^k calls, and is Bool.true; a proposition that calls it would dominate the run.
    val spin =
      families + "def spin (n: Nat): Bool decreases structural(n) := match n returning Bool with\n" +
        " | Nat.zero => Bool.true\n | Nat.succ k => Bool.and(spin(k), spin(k))\n\n"
    // A prelude has no literals of its own, so the proposition names 10 as `ten`.
    val ten = "def ten : Nat := " + "Nat.succ(" * 10 + "Nat.zero" + ")" * 10 + "\n\n"
    val guarded = "guarded (x: Nat)[h: IsTrue(spin(ten))]: Nat"
    def loop(step: String): String =
      "def loop (n: Nat): Nat decreases structural(n) := match n returning Nat with\n" +
        s" | Nat.zero => 0\n | Nat.succ k => $step\n\n"
    // The same `guarded` assumed, so that its applications are blocked.
    val assumed = TestSupport.preludeAssuming(TestSupport.bundledPreludeSource, spin + ten + s"axiom $guarded\n")
    // Checking `loop` discharges the proposition once; each of the 200 calls then binds an erased proof, a lambda's
    // parameter to it and an axiom's stored argument alike.
    val counting = loop("{\n    let u := guarded(1)\n    Nat.add(1, loop(k))\n  }")
    val transparent = spin + ten + s"def $guarded := x\n\n" + counting
    typecheckDecls(transparent)
    typecheckDecls(counting, assumed)
    assertEquals(forcings(evaluatesTo(transparent + "{ loop(200) }", "200")), 0L)
    assertEquals(forcings(evaluatesTo(counting + "{ loop(200) }", "200", assumed)), 0L)
    // An axiom's applications kept in the result, and printed, which reads only their explicit arguments.
    val kept = loop("Nat.add(guarded(1), loop(k))")
    typecheckDecls(kept, assumed)
    assertEquals(forcings(evaluatesTo(kept + "{ loop(2) }", "Nat.add(guarded(1), guarded(1))", assumed)), 0L)
    // Publishing them, where the environment assertions check that a global is closed, reads their dependencies, which
    // leave their evidence out.
    assert(sys.props.getOrElse("raccoon.envAssertions", "true").toBoolean)
    assertEquals(forcings(typecheckDecls(kept + "def r : Nat := loop(2)\n", assumed)), 0L)
    // So do their keys and conversion: two built alike are equal by key, and the key assertion's recheck skips the
    // evidence too, as conversion does.
    assert(ValueEquivalence.keyAssertionsEnabled)
    assertEquals(
      forcings {
        val (left, right) = (runProgram(kept + "{ loop(3) }", assumed), runProgram(kept + "{ loop(3) }", assumed))
        assertEquals(left.key, right.key)
        assert(left.synDeps.isEmpty)
        assert(ValueEquivalence.defEq(left, right))
        assert(!ValueEquivalence.defEq(left, runProgram(kept + "{ loop(2) }", assumed)))
        assumed.checkedEnv.putGlobal("r", left)
      },
      0L
    )
  }

  test("an application's evidence is determined by the rest, so its dependencies, key and conversion skip it") {
    val pi = runProgram(three + "{ three }").tpe match {
      case pi: Value.VPi => pi
      case other         => fail(s"expected a function type, got $other")
    }
    val proposition = runProgram("{ Eq(Nat, 3, 3) }")
    val nat = Prelude.default.checkedEnv("Nat")
    val head = Value.VConst("three", Value.Symbol, pi)
    val unforceable = new Value.DeferredEvidence(() => fail("the evidence was forced"))
    val checked = Value.canonicalizeProof(Value.VProof(proposition))
    val three3 = Value.VPacked.nat(3, nat)
    // One application as checking builds it, with the proof bound, and one as evaluation does, with deferred evidence.
    val bound = Value.VApp(head, Vector(three3, checked), nat, DepSet.empty)
    val deferred = Value.VApp(head, Vector(three3, unforceable), nat, DepSet.empty)
    assertEquals(deferred.key, bound.key)
    assert(deferred.synDeps.isEmpty)
    assert(!deferred.needsStructuralDefEq)
    assert(ValueEquivalence.defEq(deferred, bound))
    Prelude.default.checkedEnv.putGlobal("deferred", deferred)

    // Materializing rebuilds the application and keeps its evidence deferred, at the proposition materialized.
    val x = FreshVar.freshVar("x", nat)
    val propositionAtX =
      Interpreter.evalTerm(pi.binders(1).ty, telescope.BinderOps.instantiateFull(pi.binders.take(1), pi.env, Vector(x)))
    val atX = Value.VApp(head, Vector(x, new Value.DeferredEvidence(() => propositionAtX)), nat, DepSet.empty)
    assertEquals(atX.synDeps, DepSet(x.id))
    val solved = EqStore.empty.allow(DepSet(x.id)).addLink(x.id, three3)
    var materialized: Value = null
    assertEquals(forcings { materialized = ValueOps.materialize(atX, solved) }, 0L)
    assertEquals(materialized.key, bound.key)
    materialized match {
      case app: Value.VApp =>
        assertEquals(forcings(assert(ValueEquivalence.defEq(app.args(1).tpe, proposition))), 1L)
      case other => fail(s"expected an application, got $other")
    }
  }

  test("an application reapplied at the head its blocker was solved to has its evidence deferred at that head") {
    val nat = Prelude.default.checkedEnv("Nat")
    val three = Value.VPacked.nat(3, nat)
    // `f(3)` where `f : (x: Nat) -> [h: Eq(Nat, x, n)] -> Nat` for an unknown `n`, as evaluation stores it.
    val atN = runProgram("def mk (m: Nat): Type := (x: Nat) -> [h: Eq(Nat, x, m)] -> Nat\n\n{ mk }")
    val n = FreshVar.freshVar("n", nat)
    val piAtN = Interpreter.evalApply(atN, Vector(n)) match {
      case pi: Value.VPi => pi
      case other         => fail(s"expected a function type, got $other")
    }
    val f = FreshVar.freshVar("f", piAtN)
    val propositionAtN =
      Interpreter.evalTerm(
        piAtN.binders(1).ty,
        telescope.BinderOps.instantiateFull(piAtN.binders.take(1), piAtN.env, Vector(three))
      )
    val app = Value.VBlockedApp(f, Vector(three, new Value.DeferredEvidence(() => propositionAtN)), nat, DepSet(f.id))
    assertEquals(app.synDeps, DepSet(f.id, n.id))
    // `f` is solved to `k(3)`, blocked on `k`, whose type states the proposition at 3, and `n` to 3.
    val k = FreshVar.freshVar("k", runProgram("{ (b: Nat) -> ((x: Nat) -> [h: Eq(Nat, x, 3)] -> Nat) }"))
    val solved = EqStore.empty
      .allow(DepSet(f.id, n.id))
      .addLink(n.id, three)
      .addLink(f.id, Interpreter.evalApply(k, Vector(three)))
    Interpreter.resolveInEqStore(app, solved) match {
      case resolved: Value.VApp =>
        assertEquals(resolved.synDeps, DepSet(k.id))
        // The evidence is determined by the new head: its proposition no longer mentions `n`.
        val evidence = resolved.args(1)
        assert(evidence.synDeps.isEmpty, evidence.synDeps)
        assert(ValueEquivalence.defEq(evidence.tpe, runProgram("{ Eq(Nat, 3, 3) }")))
      case other => fail(s"expected an application, got $other")
    }
  }

  test("a callee that looks at its evidence sees the proof checking bound") {
    // Matching on it into data forces it, once per call, and reduces as the canonical proof does.
    val matching =
      "def three (n: Nat)[h: Eq(Nat, n, 3)]: Nat := match h returning Nat with\n | Eq.refl z => Nat.add(z, 10)\n\n"
    assertEquals(forcings(evaluatesTo(matching + "def g (u: Nat): Nat := three(3)\n\n{ g(0) }", "13")), 1L)
    // Equally from a lambda that captures it.
    evaluatesTo(
      "def mk (n: Nat)[h: Eq(Nat, n, 3)]: Nat -> Nat := fun (m: Nat): Nat => match h returning Nat with\n" +
        " | Eq.refl z => Nat.add(z, m)\n\n{ mk(3)(4) }",
      "7"
    )
    // A proof of a function type is applied.
    evaluatesTo(
      families + "def f [h: (x: Nat) -> Same(x, x)]: Nat := match h(3) returning Nat with\n | Same.refl => 1\n\n" +
        "{ f()[fun (x: Nat): Same(x, x) => Same.refl(x)] }",
      "1"
    )
    // A lambda with evidence stored in a pair and taken back out.
    evaluatesTo(
      "def body (x: Nat)[h: Eq(Nat, x, 3)]: Nat := match h returning Nat with\n | Eq.refl z => Nat.add(z, 1)\n\n" +
        "def p : Pair((x: Nat) -> [h: Eq(Nat, x, 3)] -> Nat, Nat) := (fun (x: Nat)[h: Eq(Nat, x, 3)]: Nat => body(x)[h], 1)\n\n" +
        "def use (q: Pair((x: Nat) -> [h: Eq(Nat, x, 3)] -> Nat, Nat)): Nat := {\n  let (f, n) := q\n  f(3)\n}\n\n{ use(p) }",
      "4"
    )
    // Recursion that forwards its evidence, and a proposition over a recursive call's argument.
    evaluatesTo(
      "def r (n: Nat)[h: True]: Nat decreases structural(n) := match n returning Nat with\n" +
        " | Nat.zero => 0\n | Nat.succ k => Nat.add(1, r(k)[h])\n\n" +
        "def z (n: Nat)[h: Eq(Nat, n, n)]: Nat := match h returning Nat with\n | Eq.refl m => m\n\n" +
        "def r3 (n: Nat)[h: Eq(Nat, n, n)]: Nat decreases structural(n) := match n returning Nat with\n" +
        " | Nat.zero => z(n)[h]\n | Nat.succ k => Nat.add(1, r3(k))\n\n{ (r(5), r3(5)) }",
      "Pair.mk(5, 5)"
    )
    // A measure that looks at its evidence.
    evaluatesTo(
      "def m (n: Nat)[h: Eq(Nat, n, n)]: Nat := match h returning Nat with\n | Eq.refl k => k\n\n" +
        "def r (n: Nat)[h: Eq(Nat, n, n)]: Nat decreases measure(m(n)[h]) := match n returning Nat with\n" +
        " | Nat.zero => 0\n | Nat.succ k => r(k)\n\n{ r(3) }",
      "0"
    )
  }
}
