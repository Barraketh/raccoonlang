package com.raccoonlang

/**
 * Evidence fields and discharge through them (docs/implemented/PROOF_BY_EVALUATION.md §1.8, §1.9): a constructor's
 * evidence binder is a stored proof field, discharged or supplied at a construction as any evidence argument is, and an
 * instance of an evidence-eligible family is discharged by discharging its fields in turn, to a bound on the nesting.
 *
 * `Fin` is a bounded natural, `Both` a conjunction whose fields are evidence, and `GemmShape` a proposition over data.
 */
class EvidenceFieldTests extends munit.FunSuite with TestSupport {

  private def evaluatesTo(source: String, expected: String)(implicit loc: munit.Location): Unit =
    evaluatesTo(source, expected, suitePrelude)

  private def evaluatesTo(source: String, expected: String, prelude: Prelude.Config)(implicit
      loc: munit.Location
  ): Unit =
    assertEquals(PrettyPrinter.print(runProgram(source, prelude)), expected)

  /** Where discharge failed, for the evidence binder `binder` of `callee`: the path, the proposition, and why. */
  private def notDischarged(source: String, binder: String, callee: String)(implicit
      loc: munit.Location
  ): (String, EvidenceNotDischarged.Reason) = {
    val failure = expectOnly[EvidenceNotDischarged](typecheckDecls(source))
    assertEquals((failure.binder, failure.callee), (binder, callee))
    val at = (failure.path :+ PrettyPrinter.print(failure.proposition)).mkString(": ")
    (at, failure.reason)
  }

  private val fin = "struct Fin (n: Nat) : Type\n | mk (i: Nat)[h: Nat.lt(i, n)] : Fin(n)\n\n"

  private val both = "struct Both (a: Prop)(b: Prop) : Prop\n | mk [x: a][y: b] : Both(a, b)\n\n"

  /** `def need [h: P]: Nat := 1`, after `Both`. */
  private def needing(proposition: String): String = both + s"def need [h: $proposition]: Nat := 1\n\n"

  test("a construction discharges its evidence field, or is refused, as an application is") {
    // `n` is forced by no field, so it is an explicit argument of the constructor (docs/language.md).
    evaluatesTo(fin + "{ Fin.mk(5, 3) }", "Fin.mk(3)")
    assertEquals(
      notDischarged(fin + "{ Fin.mk(2, 3) }", "h", "Fin.mk"),
      ("Eq(Bool, Bool.false, Bool.true)", EvidenceNotDischarged.NoConstructor)
    )
    // Supplied, one proof per evidence field.
    evaluatesTo(fin + "{ Fin.mk(5, 3)[Eq.refl(Bool.true)] }", "Fin.mk(3)")
    assertEquals(
      expectOnly[ArityMismatch](typecheckDecls(fin + "{ Fin.mk(5, 3)[Eq.refl(Bool.true), Eq.refl(Bool.true)] }")),
      ArityMismatch(1, 2, ArityMismatch.Evidence)
    )
    expectOnly[TypeMismatch](typecheckDecls(fin + "{ Fin.mk(5, 3)[Eq.refl(Bool.false)] }"))
    // Generic code forwards the proof it has.
    val generic = fin + "def mk (i: Nat)[h: Nat.lt(i, 5)]: Fin(5) := Fin.mk(5, i)[h]\n\n"
    evaluatesTo(generic + "{ mk(4) }", "Fin.mk(4)")
    assertEquals(
      notDischarged(fin + "def mk (i: Nat): Fin(5) := Fin.mk(5, i)\n", "h", "Fin.mk")._2,
      EvidenceNotDischarged.NoConstructor
    )
  }

  test("an evidence field is a stored proof field: a match, a destructuring and a selector bind it") {
    // Each forwards the bound proof to a construction that needs it.
    val matched =
      fin + "def again (x: Fin(5)): Fin(5) := match x returning Fin(5) with\n | Fin.mk i h => Fin.mk(5, i)[h]\n\n"
    evaluatesTo(matched + "{ again(Fin.mk(5, 2)) }", "Fin.mk(2)")
    val destructured = fin + "def again (x: Fin(5)): Fin(5) := {\n  let (i, h) := x\n  Fin.mk(5, i)[h]\n}\n\n"
    evaluatesTo(destructured + "{ again(Fin.mk(5, 2)) }", "Fin.mk(2)")
    val selected = fin + "def again (x: Fin(5)): Fin(5) := Fin.mk(5, x.i)[x.h]\n\n"
    evaluatesTo(selected + "{ again(Fin.mk(5, 2)) }", "Fin.mk(2)")
    evaluatesTo(fin + "def bound (x: Fin(5)): Nat.lt(x.i, 5) := x.h\n\n{ Fin.mk(5, 1).i }", "1")
    // Checking destructures a value evaluation built, whose evidence field is deferred, and checks a match after it.
    evaluatesTo(
      fin + "def mk (i: Nat)[h: Nat.lt(i, 5)]: Fin(5) := Fin.mk(5, i)[h]\n\n" +
        "def t (x: Nat): Nat := {\n  let (i, h) := mk(3)\n  match x returning Nat with\n   | Nat.zero => i\n" +
        "   | Nat.succ k => Fin.mk(5, i)[h].i\n}\n\n{ Nat.add(t(0), t(1)) }",
      "6"
    )
    // A pattern binds every stored field, the evidence field included.
    assertEquals(
      expectOnly[ArityMismatch](
        typecheckDecls(fin + "def f (x: Fin(5)): Nat := match x returning Nat with\n | Fin.mk i => i\n")
      ),
      ArityMismatch(2, 1, ArityMismatch.Fields)
    )
  }

  test("two values that differ only in an evidence field are equal") {
    val generic = fin + "def mk (i: Nat)[h: Nat.lt(i, 5)]: Fin(5) := Fin.mk(5, i)[h]\n\n"
    evaluatesTo(generic + "def same : Eq(Fin(5), Fin.mk(5, 3), mk(3)) := Eq.refl(Fin.mk(5, 3))\n\n{ 0 }", "0")
    evaluatesTo(
      generic + "def same (a: Nat.lt(3, 5))(b: Nat.lt(3, 5)): Eq(Fin(5), Fin.mk(5, 3)[a], Fin.mk(5, 3)[b]) := " +
        "Eq.refl(Fin.mk(5, 3))\n\n{ 0 }",
      "0"
    )
    expectOnly[TypeMismatch](typecheckDecls(generic + "def same : Eq(Fin(5), Fin.mk(5, 3), mk(2)) := Eq.refl(mk(3))\n"))
    // Structure eta: a value is its constructor applied to its fields, whatever proof the evidence field holds.
    evaluatesTo(generic + "def same (x: Fin(5)): Eq(Fin(5), x, mk(x.i)[x.h]) := Eq.refl(x)\n\n{ 0 }", "0")
    // A structure whose fields are all evidence has one value up to them, so any two of its values are equal.
    val only = "struct S (n: Nat) : Type\n | mk [h: Eq(Nat, n, 3)] : S(n)\n\n"
    evaluatesTo(only + "def viaMk (x: S(3)): Eq(S(3), x, S.mk(3)) := Eq.refl(x)\n\n{ 0 }", "0")
    evaluatesTo(only + "def any (x: S(3))(y: S(3)): Eq(S(3), x, y) := Eq.refl(x)\n\n{ 0 }", "0")
  }

  test("structure eta skips an evidence field, and forces no deferred proof in one") {
    val finType = runProgram(fin + "{ Fin(5) }")
    val finMk = runProgram(fin + "{ Fin.mk }") match {
      case head: Value.ConstructorHead => head
      case other                       => fail(s"expected a constructor, got $other")
    }
    val (instance, info) = StructEta.eligibleInstance(finType).getOrElse(fail("Fin is eta-eligible"))
    val x = FreshVar.freshVar("x", finType)
    val unforceable = new Value.DeferredEvidence(() => fail("the evidence was forced"))
    val i = StructEta.fieldProjection(x, instance, info, 0)
    val three = Value.VPacked.nat(3, Prelude.default.checkedEnv("Nat"))
    assertEquals(
      forcings {
        assert(ValueEquivalence.defEq(x, Value.VCtor(finMk, Vector(i, unforceable), finType)))
        assert(ValueEquivalence.defEq(Value.VCtor(finMk, Vector(i, unforceable), finType), x))
        assert(!ValueEquivalence.defEq(x, Value.VCtor(finMk, Vector(three, unforceable), finType)))
      },
      0L
    )
  }

  test("an evidence field's type is checked as any field's, and a constructor's implicits must still be forced") {
    assertEquals(
      expectOnly[NotAProposition](typecheckDecls("struct Box : Type\n | mk [h: Nat] : Box\n")).binder,
      "h"
    )
    expectOnly[NonStrictlyPositive](typecheckDecls("inductive Bad : Prop\n | mk [h: (b: Bad) -> False] : Bad\n"))
    // It may mention the family's parameters and earlier fields.
    evaluatesTo(
      "struct Pair2 (n: Nat) : Type\n | mk (a: Nat)[ha: Eq(Nat, a, n)](b: Nat)[hb: Eq(Nat, b, a)] : Pair2(n)\n\n" +
        "{ Pair2.mk(2, 2, 2) }",
      "Pair2.mk(2, 2)"
    )
    assertEquals(
      expectOnly[NonForcedImplicitParam](typecheckDecls("inductive T : Type\n | mk {n: Nat}[h: Eq(Nat, n, 3)] : T\n")),
      NonForcedImplicitParam("n", isProposition = false)
    )
  }

  test("a construction stores an erased proof, and running or printing it evaluates no proposition") {
    // `spin(k)` makes 2^k calls; a proposition that calls it would dominate the run.
    val spin =
      "def spin (n: Nat): Bool decreases structural(n) := match n returning Bool with\n" +
        " | Nat.zero => Bool.true\n | Nat.succ k => Bool.and(spin(k), spin(k))\n\n"
    val checked =
      "struct Checked (n: Nat) : Type\n | mk (i: Nat)[h: Eq(Bool, spin(n), Bool.true)] : Checked(n)\n\n" +
        "def get (c: Checked(10)): Nat := match c returning Nat with\n | Checked.mk i h => i\n\n" +
        "def loop (n: Nat): Nat decreases structural(n) := match n returning Nat with\n" +
        " | Nat.zero => 0\n | Nat.succ k => {\n    let c := Checked.mk(10, 1)\n" +
        "    let (i, h) := c\n    Nat.add(Nat.add(get(c), Nat.sub(c.i, i)), loop(k))\n  }\n\n"
    val source = spin + checked
    typecheckDecls(source)
    assertEquals(forcings(evaluatesTo(source + "{ loop(200) }", "200")), 0L)
    assertEquals(forcings(evaluatesTo(source + "{ (Checked.mk(10, 7), 1) }", "Pair.mk(Checked.mk(7), 1)")), 0L)
    // Each call projects an implicit through a stored constructor field, and one through a family's argument that is an
    // axiom's application, each read alone, beside evidence that is not read. A blocked application's own arguments
    // are not projection positions. A prelude has no literals of its own, so the axiom names 10 as `ten`.
    val assumed = TestSupport.preludeAssuming(
      TestSupport.bundledPreludeSource,
      spin + "def ten : Nat := " + "Nat.succ(" * 10 + "Nat.zero" + ")" * 10 + "\n\n" +
        "axiom tag (n: Nat)[h: Eq(Bool, spin(ten), Bool.true)]: Nat\n"
    )
    val projecting =
      checked + "struct Tagged (t: Nat) : Type\n | mk : Tagged(t)\n\n" +
        "def untag {t: Nat}(x: Tagged(t)): Nat := 1\n\n" +
        "def at {i: Nat}(c: Checked(10))(p: Eq(Checked(10), c, Checked.mk(10, i))): Nat := i\n\n" +
        "def again (n: Nat): Nat decreases structural(n) := match n returning Nat with\n" +
        " | Nat.zero => 0\n | Nat.succ k => {\n    let c := Checked.mk(10, 1)\n" +
        "    Nat.add(Nat.add(untag(Tagged.mk(tag(1))), Nat.sub(at(c, Eq.refl(c)), 1)), again(k))\n  }\n\n"
    // Checking alone, with no iteration run, is the baseline.
    typecheckDecls(projecting, assumed)
    val checking = forcings(typecheckDecls(projecting + "{ again(0) }", assumed))
    assertEquals(forcings(evaluatesTo(projecting + "{ again(200) }", "200", assumed)) - checking, 0L)
  }

  test("an eligible proposition is discharged through its evidence fields") {
    evaluatesTo(needing("Both(True, Eq(Nat, 2, 2))") + "{ need() }", "1")
    evaluatesTo(needing("Both(Both(True, Eq(Nat, 2, 2)), Both(True, True))") + "{ need() }", "1")
    // A field that duplicates a parameter.
    val twice = both + "struct Twice (p: Prop) : Prop\n | mk [a: Both(p, p)] : Twice(p)\n\n"
    evaluatesTo(twice + "def need [h: Twice(Eq(Nat, 3, 3))]: Nat := 1\n\n{ need() }", "1")
    // A field's proposition over the family's arguments and an earlier field's proof.
    val gemm =
      "struct GemmShape (m: Nat)(n: Nat) : Prop\n" +
        " | mk [mOk: Eq(Nat, Nat.mul(m, 2), 256)][nOk: Eq(Nat, n, 128)][same: Eq(Eq(Nat, n, 128), nOk, nOk)] : " +
        "GemmShape(m, n)\n\n"
    evaluatesTo(gemm + "def need [h: GemmShape(128, 128)]: Nat := 1\n\n{ need() }", "1")
    // Rule 1 still takes a fieldless instance of an eligible family.
    evaluatesTo(both + "struct Unit2 : Prop\n | mk : Unit2\n\ndef need [h: Unit2]: Nat := 1\n\n{ need() }", "1")
  }

  test("a failing field is reported with its path, depth first in field order") {
    val gemm =
      both + "struct GemmShape (m: Nat)(n: Nat) : Prop\n" +
        " | mk [mOk: Eq(Nat, m, 128)][nOk: Eq(Nat, n, 128)] : GemmShape(m, n)\n\n"
    assertEquals(
      notDischarged(gemm + "def need [h: GemmShape(128, 192)]: Nat := 1\n\n{ need() }", "h", "need"),
      ("GemmShape.nOk: Eq(Nat, 192, 128)", EvidenceNotDischarged.NoConstructor)
    )
    assertEquals(
      notDischarged(gemm + "def need [h: Both(True, GemmShape(128, 192))]: Nat := 1\n\n{ need() }", "h", "need"),
      ("Both.y: GemmShape.nOk: Eq(Nat, 192, 128)", EvidenceNotDischarged.NoConstructor)
    )
    // Both fields fail; the first is reported.
    assertEquals(
      notDischarged(gemm + "def need [h: Both(GemmShape(1, 2), False)]: Nat := 1\n\n{ need() }", "h", "need"),
      ("Both.x: GemmShape.mOk: Eq(Nat, 1, 128)", EvidenceNotDischarged.NoConstructor)
    )
  }

  test("a recursive family and a family of several constructors are not recursed into") {
    assertEquals(
      notDischarged(
        "inductive Loop : Prop\n | mk [h: Loop] : Loop\n\ndef need [h: Loop]: Nat := 1\n\n{ need() }",
        "h",
        "need"
      ),
      ("Loop", EvidenceNotDischarged.NoConstructor)
    )
    // A mutual block's families mention each other.
    val mutualLoop =
      "mutual {\n  inductive Ping : Prop\n   | mk [h: Pong] : Ping\n  inductive Pong : Prop\n   | mk [h: Ping] : Pong\n}\n\n"
    assertEquals(
      notDischarged(mutualLoop + "def need [h: Ping]: Nat := 1\n\n{ need() }", "h", "need"),
      ("Ping", EvidenceNotDischarged.NoConstructor)
    )
    val two = "inductive Two : Prop\n | a [h: True] : Two\n | b [h: True] : Two\n\n"
    assertEquals(
      notDischarged(two + "def need [h: Two]: Nat := 1\n\n{ need() }", "h", "need"),
      ("Two", EvidenceNotDischarged.NoConstructor)
    )
    // A family that is a proposition only at one level is not declared in Prop.
    val poly = "struct Poly (u: Level) : Sort { level = u }\n | mk [h: True] : Poly(u)\n\n"
    assertEquals(
      notDischarged(poly + "def need [h: Poly(Level.zero)]: Nat := 1\n\n{ need() }", "h", "need")._2,
      EvidenceNotDischarged.NoConstructor
    )
    // A field that is not evidence.
    val data = "struct Data : Prop\n | mk (h: True) : Data\n\n"
    assertEquals(
      notDischarged(data + "def need [h: Data]: Nat := 1\n\n{ need() }", "h", "need"),
      ("Data", EvidenceNotDischarged.NoConstructor)
    )
  }

  test("rule 2 takes any arguments: open ones, stuck ones, and ones that hold functions") {
    val over = both + "def need (n: Nat)[h: Both(Eq(Nat, n, n), True)]: Nat := n\n\n"
    evaluatesTo(over + "def g (n: Nat): Nat := need(n)\n\n{ g(4) }", "4")
    evaluatesTo(
      both + "def need [h: Both(Eq(Nat, five, five), True)]: Nat := 1\n\n{ need() }",
      "1",
      TestSupport.preludeAssuming(TestSupport.bundledPreludeSource, "axiom five : Nat\n")
    )
    val app =
      both + "struct App (f: Nat -> Prop)(n: Nat) : Prop\n | mk [a: f(n)] : App(f, n)\n\n" +
        "def isFour (n: Nat): Prop := Eq(Nat, n, 4)\n\n"
    evaluatesTo(app + "def need [h: App(isFour, 4)]: Nat := 1\n\n{ need() }", "1")
    assertEquals(
      notDischarged(app + "def need [h: App(isFour, 3)]: Nat := 1\n\n{ need() }", "h", "need"),
      ("App.a: Eq(Nat, 3, 4)", EvidenceNotDischarged.NoConstructor)
    )
    // A proposition argument that holds a function.
    evaluatesTo(app + "def need [h: Both(App(isFour, 4), True)]: Nat := 1\n\n{ need() }", "1")
  }

  test("the constructions that broke the ordering proof are checked promptly") {
    // These once broke the recursive path ordering argument for termination (PROOF_BY_EVALUATION §5.3): the field `r`
    // views `p` at the type `Wrap(c)` through `e`, and inference reads the function out of `p`'s own proposition, `A`,
    // so `c2`, declared after `F`, runs, and the field's proposition unfolds `later`, declared after `F` too. Termination
    // now rests on the depth bound, and both are discharged.
    val common =
      "struct U : Type\n | mk : U\n\nstruct PU : Type\n | mk (u: U) : PU\n\n" +
        "struct Wrap (f: Nat -> PU) : Prop\n | mk : Wrap(f)\n\nstruct Holds (x: PU) : Prop\n | mk : Holds(x)\n\n" +
        "def peek {f: Nat -> PU}(w: Wrap(f)): PU := f(0)\n\ndef c (n: Nat): PU := PU.mk(U.mk)\n\n" +
        "def third (A: Prop)(p: A)(e: Eq(Prop, A, Wrap(c))): Prop := {\n" +
        "  let q := match e returning Wrap(c) with\n    | Eq.refl x => p\n  Holds(peek(q))\n}\n\n" +
        "struct F (A: Prop) : Prop\n | mk [p: A][e: Eq(Prop, A, Wrap(c))][r: third(A, p, e)] : F(A)\n\n" +
        "def later : U := U.mk\n\ndef c2 (n: Nat): PU := PU.mk(later)\n\n"
    evaluatesTo(common + "{ third(Wrap(c2), Wrap.mk(c2), Eq.refl(Wrap(c2))) }", "Holds(PU.mk(U.mk))")
    evaluatesTo(common + "def need [h: F(Wrap(c2))]: Nat := 1\n\n{ need() }", "1")
    // The same with data beside it, where the ordering itself failed to decrease.
    val withData =
      "struct U : Type\n | mk : U\n\nstruct Box (T: Type) : Type\n | mk (t: T) : Box(T)\n\n" +
        "struct PU2 (T: Type) : Type\n | mk (b: Box(T))(u: U) : PU2(T)\n\n" +
        "struct Wrap (f: (T: Type) -> Box(T) -> PU2(T)) : Prop\n | mk : Wrap(f)\n\n" +
        "struct Holds {T: Type}(x: PU2(T)) : Prop\n | mk : Holds(x)\n\n" +
        "def peek {f: (T: Type) -> Box(T) -> PU2(T)}(w: Wrap(f))(T: Type)(b: Box(T)): PU2(T) := f(T, b)\n\n" +
        "def c (T: Type)(b: Box(T)): PU2(T) := PU2.mk(b, U.mk)\n\n" +
        "def third (A: Prop)(X: Type)(d: Box(X))(p: A)(e: Eq(Prop, A, Wrap(c))): Prop := {\n" +
        "  let q := match e returning Wrap(c) with\n    | Eq.refl x => p\n  Holds(peek(q, X, d))\n}\n\n" +
        "struct F (A: Prop)(X: Type)(d: Box(X)) : Prop\n" +
        " | mk [p: A][e: Eq(Prop, A, Wrap(c))][r: third(A, X, d, p, e)] : F(A, X, d)\n\n" +
        "def laterU (T: Type)(b: Box(T)): U := U.mk\n\n" +
        "def c2 (T: Type)(b: Box(T)): PU2(T) := PU2.mk(b, laterU(T, b))\n\ninductive E : Type\n | e : E\n\n"
    evaluatesTo(withData + "def need [h: F(Wrap(c2), E, Box.mk(E.e))]: Nat := 1\n\n{ need() }", "1")
  }

  test("a sealed eligible family is discharged through its fields only in its module") {
    val module = both.replace("struct Both", "sealed struct Both") + "def need [h: Both(True, True)]: Nat := 1\n"
    assertEquals(inside(module, "{ need() }").map(PrettyPrinter.print), Some("1"))
    assertEquals(expectOnly[EvidenceNotDischarged](outside(module, "{ need() }")).reason, EvidenceNotDischarged.Sealed)
    // Reached through a field of a family that is not sealed.
    val nested =
      "sealed struct Inner : Prop\n | mk [h: True] : Inner\n\n" + both + "def need [h: Both(True, Inner)]: Nat := 1\n"
    val failure = expectOnly[EvidenceNotDischarged](outside(nested, "{ need() }"))
    assertEquals((failure.path, failure.reason), (Vector("Both.y"), EvidenceNotDischarged.Sealed))
  }

  test("discharge takes at most the bound of rule-2 steps on a path") {
    // `wraps(k)` is `True` wrapped `k` times, and discharging it takes a rule-2 step for each `Wrap`.
    val wraps =
      "struct Wrap (p: Prop) : Prop\n | mk [h: p] : Wrap(p)\n\n" +
        "def wraps (k: Nat): Prop decreases structural(k) := match k returning Prop with\n" +
        " | Nat.zero => True\n | Nat.succ j => Wrap(wraps(j))\n\n" +
        "def need (k: Nat)[h: wraps(k)]: Nat := k\n\n"
    val bound = Discharge.DepthBound
    // Each step is host recursion, so the chain is checked on the fixtures' stack rather than the test thread's.
    Execution.onStack(TestSupport.FixtureStack)(evaluatesTo(wraps + s"{ need($bound) }", s"$bound"))
    val failure = expectOnly[EvidenceNotDischarged](
      Execution.onStack(TestSupport.FixtureStack)(typecheckDecls(wraps + s"{ need(${bound + 1}) }"))
    )
    assertEquals(
      (failure.path, PrettyPrinter.print(failure.proposition), failure.reason),
      (Vector.fill(bound)("Wrap.h"), "Wrap(True)", EvidenceNotDischarged.TooDeep)
    )
  }

  test("an application's proposition is evaluated once, and each field's once") {
    // Evaluating a proposition that calls `look` forces `look`'s own evidence once, so the forcings count evaluations.
    val look =
      both + "def look (n: Nat)[h: Eq(Nat, n, n)]: Nat := match h returning Nat with\n" +
        " | Eq.refl z => Nat.add(z, 10)\n\n"
    val one = look + "def f (n: Nat)[e: Eq(Nat, look(n), 13)]: Nat := n\n\n"
    assertEquals(forcings(typecheckDecls(one + "def t : Nat := f(3)\n")) - forcings(typecheckDecls(one)), 1L)
    val two = look + "def f (n: Nat)[e: Both(Eq(Nat, look(n), 13), Eq(Nat, look(n), 13))]: Nat := n\n\n"
    assertEquals(forcings(typecheckDecls(two + "def t : Nat := f(3)\n")) - forcings(typecheckDecls(two)), 2L)
  }

  test("a builtin's own binders are never evidence") {
    val base = TestSupport.bundledPreludeSource
    val lift = "def lift {u: Level}"
    assert(base.contains(lift))
    val prelude = Prelude.fromSource("evidence-builtin", base.replace(lift, "def lift [ok: True]{u: Level}"))
    val failure = interceptDiagnostic(prelude.checkedEnv)
    assertEquals(failure.error, BuiltinEvidence("Quot.lift", "ok"))
  }
}
