package com.raccoonlang

/**
 * Evidence arguments discharged by the fieldless rule (docs/PROOF_BY_EVALUATION.md §1.1–1.7): an evidence binder
 * `[h: P]` in a definition's, a lambda's or a function type's telescope, discharged at each application by evaluating
 * `P` there, or supplied in a bracket group `f(x)[p]`. Each rule has an admitted program and the smallest mutation that
 * reaches its diagnostic.
 *
 * The bundled prelude's `Eq.refl` stores its field, so the fieldless rule never discharges `Eq`; `Same` is the equality
 * whose one constructor is fieldless, and `IsTrue` a proposition a decision procedure's result is checked by.
 */
class EvidenceTests extends munit.FunSuite with TestSupport {

  private def evaluatesTo(source: String, expected: String)(implicit loc: munit.Location): Unit =
    assertEquals(PrettyPrinter.print(runProgram(source)), expected)

  /** The proposition an application failed to discharge, printed, for the evidence binder `binder` of `callee`. */
  private def notDischarged(source: String, binder: String, callee: String)(implicit loc: munit.Location): String = {
    val failure = expectOnly[EvidenceNotDischarged](typecheckDecls(source))
    assertEquals((failure.binder, failure.callee), (binder, callee))
    PrettyPrinter.print(failure.proposition)
  }

  private val families =
    "inductive Same {A: Type}(a: A) indices (b: A) : Prop\n | refl : Same(a, a)\n\n" +
      "inductive IsTrue indices (b: Bool) : Prop\n | yes : IsTrue(Bool.true)\n\n"

  /** `def need [h: P]: Nat := 1`, whose proposition is closed. */
  private def needing(proposition: String): String = families + s"def need [h: $proposition]: Nat := 1\n\n"

  private val three = families + "def three (n: Nat)[h: Same(n, 3)]: Nat := n\n\n"

  test("an evidence argument is discharged by evaluating its proposition where the application stands") {
    evaluatesTo(three + "{ three(3) }", "3")
    evaluatesTo(three + "{ three(Nat.add(1, 2)) }", "3")
    assertEquals(notDischarged(three + "{ three(4) }", "h", "three"), "Same(4, 3)")
    // The proposition is evaluated with the call's arguments, so a decision procedure in it runs.
    val positive = families + "def pred (n: Nat)[h: IsTrue(Nat.blt(0, n))]: Nat := Nat.sub(n, 1)\n\n"
    evaluatesTo(positive + "{ pred(5) }", "4")
    assertEquals(notDischarged(positive + "{ pred(0) }", "h", "pred"), "IsTrue(Bool.false)")
  }

  test("only a fieldless constructor whose type is the proposition discharges it") {
    evaluatesTo(needing("True") + "{ need() }", "1")
    evaluatesTo(needing("Same(Nat.mul(2, 3), 6)") + "{ need() }", "1")
    assertEquals(notDischarged(needing("False") + "{ need() }", "h", "need"), "False")
    assertEquals(notDischarged(needing("Same(2, 3)") + "{ need() }", "h", "need"), "Same(2, 3)")
    // A constructor with fields is never applied, though its fields could be proved: they would have to be invented.
    assertEquals(notDischarged(needing("And(True, True)") + "{ need() }", "h", "need"), "And(True, True)")
    assertEquals(notDischarged(needing("Or(True, False)") + "{ need() }", "h", "need"), "Or(True, False)")
    notDischarged(
      families + "def isZero (n: Nat): Prop := Same(n, 0)\n\n" + "def need [h: Exists(Nat, isZero)]: Nat := 1\n\n{ need() }",
      "h",
      "need"
    )
    // The prelude's `Eq.refl (x: A)` stores `x`, so it is not fieldless, and `Eq` is never discharged.
    assertEquals(notDischarged(needing("Eq(Nat, 3, 3)") + "{ need() }", "h", "need"), "Eq(Nat, 3, 3)")
    // Of a fieldless constructor and one with fields, only the fieldless one is tried.
    val le =
      "inductive Le (n: Nat) indices (m: Nat) : Prop\n | refl : Le(n, n)\n | step (m: Nat)(h: Le(n, m)) : " +
        "Le(n, Nat.succ(m))\n\n"
    evaluatesTo(le + needing("Le(3, 3)") + "{ need() }", "1")
    assertEquals(notDischarged(le + needing("Le(3, 4)") + "{ need() }", "h", "need"), "Le(3, 4)")
  }

  test("a proposition that stays neutral is not discharged, and one whose sides convert is") {
    // Generic code knows no concrete argument, so its proposition stays neutral.
    assertEquals(notDischarged(three + "def g (n: Nat): Nat := three(n)\n", "h", "three"), "Same(n, 3)")
    assertEquals(
      notDischarged("def any (P: Prop)[h: P]: Nat := 1\n\ndef g (Q: Prop): Nat := any(Q)\n", "h", "any"),
      "Q"
    )
    // An instance whose sides convert is discharged, neutral or not.
    evaluatesTo(
      families + "def same (a: Nat)(b: Nat)[h: Same(a, b)]: Nat := b\n\ndef g (n: Nat): Nat := same(n, n)\n\n{ g(7) }",
      "7"
    )
  }

  test("generic code forwards the evidence it has, and its callers discharge theirs") {
    val forward = three + "def g (n: Nat)[h: Same(n, 3)]: Nat := Nat.add(three(n)[h], 1)\n\n"
    evaluatesTo(forward + "{ g(3) }", "4")
    assertEquals(notDischarged(forward + "{ g(2) }", "h", "g"), "Same(2, 3)")
    // Any proof of the proposition is supplied the same way, one the fieldless rule would not find included.
    evaluatesTo(three + "{ three(3)[Same.refl(3)] }", "3")
    evaluatesTo(needing("And(True, True)") + "{ need()[And.intro(True.intro, True.intro)] }", "1")
    evaluatesTo(needing("Eq(Nat, 3, 3)") + "{ need()[Eq.refl(3)] }", "1")
  }

  test("a supplied proof is checked against the evaluated proposition, one proof per evidence binder") {
    val mismatch = expectOnly[TypeMismatch](typecheckDecls(three + "{ three(3)[Same.refl(4)] }"))
    assertEquals(PrettyPrinter.print(mismatch.expected), "Same(3, 3)")
    assertEquals(
      expectOnly[ArityMismatch](typecheckDecls(three + "{ three(3)[Same.refl(3), Same.refl(3)] }")),
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
      typecheckDecls(tokens + three + "def g {l: Lifetime}(t: Tok(l)): Nat := three(3)[Same.refl(eat(t))]\n")
    )
  }

  test("evidence mixes with implicit and explicit binders in any order, each proposition over earlier binders") {
    val mixed =
      families + "def m {A: Type}(x: A)[h1: Same(x, x)](n: Nat)[h2: IsTrue(Nat.beq(n, 2))]{B: Type}(b: B): B := b\n\n"
    evaluatesTo(mixed + "{ m(Bool.false, 2, 5) }", "5")
    assertEquals(notDischarged(mixed + "{ m(Bool.false, 3, 5) }", "h2", "m"), "IsTrue(Bool.false)")
    evaluatesTo(mixed + "{ m(Bool.false, 2, 5)[Same.refl(Bool.false), IsTrue.yes] }", "5")
    assertEquals(
      expectOnly[ArityMismatch](typecheckDecls(mixed + "{ m(Bool.false, 2, 5)[Same.refl(Bool.false)] }")),
      ArityMismatch(2, 1, ArityMismatch.Evidence)
    )
    // Evidence first, then an explicit binder, which its proposition cannot mention.
    evaluatesTo("def first [h: True](n: Nat): Nat := n\n\n{ first(4) }", "4")
    assertEquals(
      expectOnly[NotFound](typecheckDecls(families + "def later [h: Same(n, 3)](n: Nat): Nat := n\n")),
      NotFound("n")
    )
  }

  test("a definition whose only parameters are evidence is applied to no arguments") {
    evaluatesTo(needing("True") + "{ need() }", "1")
    // Named alone it is the function, whose type keeps its evidence binder.
    evaluatesTo(needing("True") + "def f : [h: True] -> Nat := need\n\n{ f() }", "1")
    expectOnly[TypeMismatch](typecheckDecls(needing("True") + "def f : Nat := need\n"))
  }

  test("a lambda binds evidence, applied directly and through a function type") {
    evaluatesTo(families + "{ (fun (x: Nat)[h: Same(x, 3)]: Nat => Nat.add(x, 1))(3) }", "4")
    evaluatesTo("{ (fun [h: True]: Nat => 5)() }", "5")
    assertEquals(
      notDischarged(families + "def v : Nat := (fun (x: Nat)[h: Same(x, 3)]: Nat => x)(4)\n", "h", "function"),
      "Same(4, 3)"
    )
    val typed =
      families + "def viaType : (x: Nat) -> [h: Same(x, 3)] -> Nat := fun (x: Nat)[h: Same(x, 3)]: Nat => x\n\n"
    evaluatesTo(typed + "{ viaType(3) }", "3")
    assertEquals(notDischarged(typed + "{ viaType(5) }", "h", "viaType"), "Same(5, 3)")
  }

  test("the evidence mode is part of a function type's identity, and a higher-order argument keeps it") {
    val takes = families + "def takes (f: (x: Nat) -> [h: Same(x, 3)] -> Nat): Nat := f(3)\n\n"
    evaluatesTo(takes + "{ takes(fun (x: Nat)[h: Same(x, 3)]: Nat => Nat.add(x, 4)) }", "7")
    expectOnly[TypeMismatch](typecheckDecls(takes + "{ takes(fun (x: Nat)(h: Same(x, 3)): Nat => x) }"))
    expectOnly[TypeMismatch](
      typecheckDecls(
        families + "def takes (f: (x: Nat) -> (h: Same(x, 3)) -> Nat): Nat := f(3, Same.refl(3))\n\n" +
          "{ takes(fun (x: Nat)[h: Same(x, 3)]: Nat => x) }"
      )
    )
    // Applied inside the higher-order function, the parameter's evidence is discharged from its type there.
    assertEquals(
      notDischarged(families + "def takes (f: (x: Nat) -> [h: Same(x, 3)] -> Nat): Nat := f(2)\n", "h", "f"),
      "Same(2, 3)"
    )
    // A proposition over the higher-order function's own parameter, neutral but with convertible sides.
    evaluatesTo(
      families + "def at (n: Nat)(f: (x: Nat) -> [h: Same(x, n)] -> Nat): Nat := f(n)\n\n" +
        "{ at(6, fun (x: Nat)[h: Same(x, 6)]: Nat => x) }",
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
    val defs = families + "def three (n: Nat)[h: Same(n, 3)]: Nat := n\n\n"
    assertEquals(
      parseError(defs + "{ three(3) [Same.refl(3)] }"),
      "Evidence follows the arguments with no space: write f(a)[h]"
    )
    assertEquals(
      parseError(defs + "{ three[Same.refl(3)] }"),
      "An evidence group follows an application's arguments: write f(a)[h]"
    )
    assertEquals(parseError(defs + "{ three(3)[] }"), "An evidence group supplies at least one proof")
    assertEquals(
      parseError(defs + "{ three(3)[Same.refl(3)][Same.refl(3)] }"),
      "An evidence group follows an application's arguments: write f(a)[h]"
    )
    assertEquals(
      parseError(defs + "{ (1, 2)[True.intro] }"),
      "An evidence group follows an application's arguments: write f(a)[h]"
    )
    assertEquals(parseError("inductive F [h: True] : Type\n"), "A family's parameters and indices are not evidence")
    assertEquals(
      parseError("inductive F indices [h: True] : Type\n"),
      "A family's parameters and indices are not evidence"
    )
    // A bracket group applies in a type as anywhere, and its result may be applied again.
    evaluatesTo(defs + "def t (p: Same(three(3)[Same.refl(3)], 3)): Nat := 0\n\n{ t(Same.refl(3)) }", "0")
    evaluatesTo(
      families + "def k (n: Nat)[h: Same(n, 1)]: Nat -> Nat := fun (m: Nat): Nat => Nat.add(n, m)\n\n{ k(1)[Same.refl(1)](2) }",
      "3"
    )
  }

  test("a function type prints its evidence binders as written") {
    assertEquals(PrettyPrinter.print(runProgram(three + "{ three }").tpe), "(n: Nat) -> [h: Same(n, 3)] -> Nat")
    assertEquals(PrettyPrinter.print(runProgram("{ fun [h: True]: Nat => 5 }").tpe), "[h: True] -> Nat")
  }

  test("an evidence binder is never a source for forcing, supplied or not") {
    assertEquals(
      expectOnly[NonForcedImplicitParam](typecheckDecls(families + "def f {n: Nat}[h: Same(n, 3)]: Nat := n\n")),
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
      families + "def isThree (n: Nat): Prop := Same(n, 3)\n\ndef f (n: Nat)[h: isThree(n)]: Nat := n\n\n{ f(3) }",
      "3"
    )
  }

  test("a constructor's evidence field is not yet supported") {
    assertEquals(
      expectOnly[EvidenceFieldUnsupported](
        typecheckDecls("struct Box (n: Nat) : Type\n | mk (i: Nat)[h: True] : Box(n)\n")
      ),
      EvidenceFieldUnsupported("Box.mk", "h")
    )
  }

  test("a sealed family's constructor discharges evidence only in its module") {
    val module = "sealed inductive Permit : Prop\n | mk : Permit\n\ndef need [p: Permit]: Nat := 1\n"
    assertEquals(inside(module, "{ need() }").map(PrettyPrinter.print), Some("1"))
    expectOnly[EvidenceNotDischarged](outside(module, "{ need() }"))
    // A proof the module hands out is forwarded as any proof is.
    val exporting = module + "def permit : Permit := Permit.mk\n"
    assertEquals(outside(exporting, "{ need()[permit] }").map(PrettyPrinter.print), Some("1"))
  }

  test("running a program binds evidence without evaluating its proposition") {
    // `spin(k)` makes 2^k calls, and is Bool.true.
    val spin =
      families + "def spin (n: Nat): Bool decreases structural(n) := match n returning Bool with\n" +
        " | Nat.zero => Bool.true\n | Nat.succ k => Bool.and(spin(k), spin(k))\n\n" +
        "def guarded (x: Nat)[h: IsTrue(spin(15))]: Nat := x\n\n" +
        "def loop (n: Nat): Nat decreases structural(n) := match n returning Nat with\n" +
        " | Nat.zero => 0\n | Nat.succ k => Nat.add(guarded(1), loop(k))\n\n"
    def timed(body: String): (String, Long) = {
      val start = System.nanoTime()
      val result = PrettyPrinter.print(runProgram(spin + body))
      (result, System.nanoTime() - start)
    }
    // Checking `loop` discharges the proposition once, and each of the program's 200 calls binds an erased proof. Were
    // the proposition evaluated at each call, the run would take some 100 to 200 times what one call takes. The first
    // run warms the evaluator up, so that the two measured ones compare evaluation alone.
    timed("{ loop(1) }")
    val (once, onceTime) = timed("{ loop(1) }")
    val (many, manyTime) = timed("{ loop(200) }")
    assertEquals((once, many), ("1", "200"))
    assert(manyTime < onceTime * 5, s"200 calls took ${manyTime / 1000000} ms, one took ${onceTime / 1000000} ms")
  }
}
