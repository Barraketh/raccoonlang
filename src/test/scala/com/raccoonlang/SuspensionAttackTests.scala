package com.raccoonlang

import com.raccoonlang.ErrorReporter.Source
import com.raccoonlang.ProgramFixtures.Programs

/**
 * Adversarial review of proof suspension (EVALUATION_AND_PORTS §2.1, 5c87dec3; docs/kernel.md, "Proof calls"): a call
 * to a checked lambda whose function type is a proposition is a `VProofCall`, run only when something reads its form.
 * Each test names what it attacks. Every program was also run on a build that never suspends, eager evaluation, and its
 * outcome is the same there unless the test says otherwise.
 *
 * An attack passes when the kernel refuses the program with the expected error; an ACCEPT of one would be a break.
 * CONTROL tests are sound programs the kernel must accept. LIMIT tests pin an outcome worth knowing that differs from
 * eager evaluation by design. FIXED tests pin a defect this review found and fixed. OVER-REJECTION tests pin a sound
 * program the kernel refuses today, where eager evaluation accepted it.
 */
class SuspensionAttackTests extends munit.FunSuite {
  private val programs = new Programs(Prelude.default, allowUserAxioms = false)
  private val withAxioms = new Programs(Prelude.default, allowUserAxioms = true)
  import programs.{result, runChecked}

  private def describe(t: Throwable, src: String): String =
    t match {
      case te: TypeError => s"${te.getClass.getSimpleName}: " + ErrorReporter.pretty(te, Source(src)).take(500)
      case other         => s"${other.getClass.getSimpleName}: ${String.valueOf(other.getMessage).take(300)}"
    }

  /** The program checks and runs. */
  private def accepts(src: String, with_ : Programs = programs)(implicit loc: munit.Location): Unit =
    try { with_.runChecked(src); () }
    catch { case t: TypeError => fail("REJECTED (should accept): " + describe(t, src)) }

  /** The program is refused with `T`; an acceptance is a break, any other refusal a misdiagnosis. */
  private def rejectsWith[T <: TypeError](src: String, with_ : Programs = programs)(implicit
      loc: munit.Location,
      ct: reflect.ClassTag[T]
  ): T =
    try {
      with_.runChecked(src)
      fail(s"ACCEPTED (BREAK: should be rejected with ${ct.runtimeClass.getSimpleName})")
    } catch {
      case t: T         => t
      case t: TypeError => fail(s"rejected, but not with ${ct.runtimeClass.getSimpleName}: ${describe(t, src)}")
    }

  private def onSmallStack[A](body: => A): A = Execution.onStack(4L << 20)(body)

  /** A proof by recursion on proofs, `idp` a proof call that returns its argument, and helpers through data. */
  private val acc =
    """
      |inductive Acc2 : Prop
      | | step (h: Acc2) : Acc2
      |
      |def idp (p: Prop)(h: p) : p := h
      |
      |// A new proof of a field's proposition.
      |def rebuild (h: Acc2) : Acc2 := {
      |  match h returning Acc2 with
      |  | Acc2.step k => Acc2.step(k)
      |}
      |
      |// The field of a proof, found by a match in the call's own body.
      |def down (h: Acc2) : Acc2 := {
      |  match h returning Acc2 with
      |  | Acc2.step k => k
      |}
      |
      |// A proof out of data.
      |def unfact (f: Fact(Acc2)) : Acc2 := {
      |  match f returning Acc2 with
      |  | Fact.mk p => p
      |}
      |
      |""".stripMargin

  /** `deep(n)` runs `n` calls deep; nothing demands it unless a test does. */
  private val deep =
    """
      |def deep (n: Nat) : True decreases structural(n) := {
      |  match n returning True with
      |  | Nat.zero => True.intro
      |  | Nat.succ k => {
      |    let h := deep(k)
      |    h
      |  }
      |}
      |
      |""".stripMargin

  /** `big(n)` computes `2^n`, which is `NatValueTooLarge` beyond an Int exponent, then proves `True`. */
  private val big =
    """
      |def big (n: Nat) : True := {
      |  let x := Nat.pow(2, n)
      |  True.intro
      |}
      |
      |""".stripMargin

  // ------------------------------------------------------------------------------------------------------------------
  // 1. Termination: a recursive call inside a suspended proof call is still checked, where its lambda is checked.
  // ------------------------------------------------------------------------------------------------------------------

  test("term-1 a non-decreasing call inside an applied local lambda whose result is a proof") {
    rejectsWith[NonDecreasingRecursiveCall](
      acc +
        """
          |def walk (h: Acc2) : True decreases structural(h) := {
          |  let g := fun (u: Unit) : True => walk(h)
          |  g(Unit.unit)
          |}
          |""".stripMargin
    )
  }

  test("term-2 CONTROL a decreasing call inside an applied local lambda, in a branch") {
    accepts(
      acc +
        """
          |def walk (h: Acc2) : True decreases structural(h) := {
          |  match h returning True with
          |  | Acc2.step h1 => {
          |    let g := fun (u: Unit) : True => walk(h1)
          |    g(Unit.unit)
          |  }
          |}
          |""".stripMargin
    )
  }

  test("term-3 a call on a lambda parameter is checked on the parameter, not on the argument it is applied to") {
    // Eager evaluation re-ran the check at walk(h1), where it holds; the check on the parameter k does not.
    rejectsWith[NonDecreasingRecursiveCall](
      acc +
        """
          |def walk (h: Acc2) : True decreases structural(h) := {
          |  match h returning True with
          |  | Acc2.step h1 => {
          |    let g := fun (k: Acc2) : True => walk(k)
          |    g(h1)
          |  }
          |}
          |""".stripMargin
    )
  }

  test("term-4 a loop through a lambda handed to a global whose result is a proof") {
    rejectsWith[NonDecreasingRecursiveCall](
      """
        |def app (P: Prop)(f: Unit -> P) : P := f(Unit.unit)
        |def loop (n: Nat) : True decreases structural(n) := app(True, fun (u: Unit) : True => loop(n))
        |def t : True := loop(3)
        |""".stripMargin
    )
  }

  test("term-5 a recursive call as the argument of a suspended call, and in a let of an undemanded proof") {
    rejectsWith[NonDecreasingRecursiveCall](
      acc + "def walk (h: Acc2) : True decreases structural(h) := idp(True, walk(h))\n"
    )
    rejectsWith[NonDecreasingRecursiveCall](
      acc +
        """
          |def app (P: Prop)(f: Unit -> P) : P := f(Unit.unit)
          |def walk (h: Acc2) : True decreases structural(h) := {
          |  let t := app(True, fun (u: Unit) : True => { let x := walk(h) x })
          |  True.intro
          |}
          |""".stripMargin
    )
  }

  test("term-6 a mutual block whose call to a peer sits in an applied local lambda") {
    rejectsWith[NonDecreasingRecursiveCall](
      acc +
        """
          |mutual {
          |  def f (h: Acc2) : True decreases structural(h) := {
          |    let k := fun (u: Unit) : True => g(h)
          |    k(Unit.unit)
          |  }
          |  def g (h: Acc2) : True decreases structural(h) := f(h)
          |}
          |""".stripMargin
    )
  }

  test("term-7 the termination checker forces a candidate whose run makes another recursive call") {
    // CONTROL: forcing g(h1) inside the comparison runs walk(h1), whose own check holds, and returns h1.
    accepts(
      acc +
        """
          |def walk (h: Acc2) : True decreases structural(h) := {
          |  match h returning True with
          |  | Acc2.step h1 => {
          |    let g := fun (k: Acc2) : Acc2 => { let t := walk(h1) k }
          |    walk(g(h1))
          |  }
          |}
          |""".stripMargin
    )
    // The inner call does not decrease; it is refused where g is checked, before anything forces g(h1).
    rejectsWith[NonDecreasingRecursiveCall](
      acc +
        """
          |def walk (h: Acc2) : True decreases structural(h) := {
          |  match h returning True with
          |  | Acc2.step h1 => {
          |    let g := fun (k: Acc2) : Acc2 => { let t := walk(h) k }
          |    walk(g(h1))
          |  }
          |}
          |""".stripMargin
    )
  }

  test("term-8 a root passed back through suspended calls and data is unchanged, so does not decrease") {
    rejectsWith[NonDecreasingRecursiveCall](
      acc + "def walk (h: Acc2) : True decreases structural(h) := walk(idp(Acc2, idp(Acc2, h)))\n"
    )
    rejectsWith[NonDecreasingRecursiveCall](
      acc + "def walk (h: Acc2) : True decreases structural(h) := walk(unfact(Fact.mk(h)))\n"
    )
  }

  test("term-9 a suspended call that rebuilds a field: its forced value is a new proof, which does not decrease") {
    rejectsWith[NonDecreasingRecursiveCall](
      acc +
        """
          |def walk (h: Acc2) : True decreases structural(h) := {
          |  match h returning True with
          |  | Acc2.step h1 => walk(rebuild(h1))
          |}
          |""".stripMargin
    )
  }

  test("term-10 CONTROL a field through two suspended calls and a fact, and a field a call's own match finds") {
    accepts(
      acc +
        """
          |def walk (h: Acc2) : True decreases structural(h) := {
          |  match h returning True with
          |  | Acc2.step h1 => walk(idp(Acc2, unfact(Fact.mk(idp(Acc2, h1)))))
          |}
          |
          |// down(h) forces to h1 only because the branch links h to step(h1): the forced value is read in the branch.
          |def walk2 (h: Acc2) : True decreases structural(h) := {
          |  match h returning True with
          |  | Acc2.step h1 => walk2(down(h))
          |}
          |""".stripMargin
    )
    // Outside the branch down(h) is stuck, a proof that is no field of h.
    rejectsWith[NonDecreasingRecursiveCall](
      acc + "def walk (h: Acc2) : True decreases structural(h) := walk(down(h))\n"
    )
  }

  test("term-11 a lexicographic proof component kept by a suspended call, and a later component that must decrease") {
    accepts(
      acc +
        """
          |def walk (h: Acc2)(n: Nat) : True decreases lexicographic(h, n) := {
          |  match n returning True with
          |  | Nat.zero => True.intro
          |  | Nat.succ k => walk(idp(Acc2, h), k)
          |}
          |""".stripMargin
    )
    rejectsWith[NonDecreasingRecursiveCall](
      acc + "def walk (h: Acc2)(n: Nat) : True decreases lexicographic(h, n) := walk(idp(Acc2, h), n)\n"
    )
  }

  test("term-12 ranks in a mutual proof block whose calls pass suspended calls from local lambdas") {
    // CONTROL: f to g passes a field, g to f keeps h from rank 1 to rank 0.
    accepts(
      acc +
        """
          |mutual {
          |  def f (h: Acc2) : True decreases lexicographic(h, measure(0)) := {
          |    match h returning True with
          |    | Acc2.step h1 => {
          |      let k := fun (u: Unit) : True => g(idp(Acc2, h1))
          |      k(Unit.unit)
          |    }
          |  }
          |  def g (h: Acc2) : True decreases lexicographic(h, measure(1)) := {
          |    let k := fun (u: Unit) : True => f(idp(Acc2, h))
          |    k(Unit.unit)
          |  }
          |}
          |""".stripMargin
    )
    // Equal ranks around the cycle.
    rejectsWith[NonDecreasingRecursiveCall](
      acc +
        """
          |mutual {
          |  def f (h: Acc2) : True decreases lexicographic(h, measure(0)) := {
          |    let k := fun (u: Unit) : True => g(idp(Acc2, h))
          |    k(Unit.unit)
          |  }
          |  def g (h: Acc2) : True decreases lexicographic(h, measure(0)) := f(idp(Acc2, h))
          |}
          |""".stripMargin
    )
  }

  test("term-13 a Nat measure read through a subsingleton elimination of a proof call") {
    val viaProof =
      """
        |def lemE (n: Nat) : Eq(Nat, n, n) := Eq.refl(n)
        |def viaProof (n: Nat) : Nat := {
        |  match lemE(n) returning Nat with
        |  | Eq.refl z => z
        |}
        |""".stripMargin
    assertEquals(
      result(
        viaProof +
          """
            |def f (n: Nat) : Nat decreases measure(viaProof(n)) := {
            |  match n returning Nat with
            |  | Nat.zero => 0
            |  | Nat.succ k => f(k)
            |}
            |f(5)
            |""".stripMargin
      ),
      "0"
    )
    rejectsWith[NonDecreasingRecursiveCall](
      viaProof + "def g (n: Nat) : Nat decreases measure(viaProof(n)) := g(n)\n"
    )
  }

  test("term-14 a candidate whose forcing for the key test is NatValueTooLarge is refused with it") {
    // The comparison forces the candidate, which eager evaluation ran as the call's argument.
    rejectsWith[NatValueTooLarge](
      acc +
        """
          |def bigAcc (n: Nat)(h: Acc2) : Acc2 := {
          |  let x := Nat.pow(2, n)
          |  h
          |}
          |def walk (h: Acc2) : True decreases structural(h) := {
          |  match h returning True with
          |  | Acc2.step h1 => walk(bigAcc(4294967296, h1))
          |}
          |""".stripMargin
    )
  }

  // ------------------------------------------------------------------------------------------------------------------
  // 2. Hidden failures: what an undemanded proof's run would raise. Only exhausting a resource is skipped.
  // ------------------------------------------------------------------------------------------------------------------

  test("hid-1 LIMIT an undemanded proof whose run is NatValueTooLarge checks; demanded, it is refused") {
    // Eager evaluation refused the first two programs with NatValueTooLarge: the accepted resource change. A match into
    // a proposition does not demand its scrutinee (changed by proof match suspension); a large elimination does.
    assertEquals(result(big + "def t : True := big(4294967296)\n\nNat.zero\n"), "0")
    assertEquals(
      result(
        big +
          """
            |def t : True := {
            |  match big(4294967296) returning True with
            |  | True.intro => True.intro
            |}
            |
            |Nat.zero
            |""".stripMargin
      ),
      "0"
    )
    rejectsWith[NatValueTooLarge](
      big +
        """
          |def t : Nat := {
          |  match big(4294967296) returning Nat with
          |  | True.intro => 0
          |}
          |""".stripMargin
    )
  }

  test("hid-2 FIXED a program's result that holds a proof whose run fails reports the failure") {
    // Printing the result runs big(2^32). It printed `VApp` and the CLI exited 0, where eager evaluation reported
    // NatValueTooLarge: the printer's fallback for values it cannot open swallowed the run's error.
    val src = big + "Prod.mk(Nat, Fact(True), 3, Fact.mk(big(4294967296)))\n"
    val value = programs.runProgram(src)
    intercept[NatValueTooLarge](PrettyPrinter.printResult(value))
    intercept[NatValueTooLarge](Interpreter.show(value, Span(0, 0)))
    intercept[NatValueTooLarge](result(src))
    // A diagnostic still prints, showing the call.
    assertEquals(PrettyPrinter.print(value), "Prod.mk(3, Fact.mk(big(4294967296)))")
  }

  test("hid-3 FIXED a diagnostic that would force a proof too deep for the stack prints the call") {
    // The type annotation is no type; its message printed the proof call by forcing it, outside every evaluation
    // boundary, so the CLI died with a StackOverflowError. Eager evaluation reported EvaluationTooDeep.
    onSmallStack {
      val error = rejectsWith[NotAType](deep + "def bad : Fact.mk(deep(100000)) := 3\n")
      assertEquals(error.getMessage, "Fact.mk(deep(100000)) is not a type")
    }
  }

  test("hid-4 a demanded proof too deep for the stack is EvaluationTooDeep, an undemanded one checks") {
    onSmallStack {
      rejectsWith[EvaluationTooDeep](
        deep +
          """
            |def t : Nat := {
            |  match deep(100000) returning Nat with
            |  | True.intro => 0
            |}
            |""".stripMargin
      )
      accepts(deep + "def t : True := deep(100000)\n")
      // A match into a proposition does not demand it (changed by proof match suspension).
      accepts(
        deep +
          """
            |def t : True := {
            |  match deep(100000) returning True with
            |  | True.intro => True.intro
            |}
            |""".stripMargin
      )
    }
  }

  // ------------------------------------------------------------------------------------------------------------------
  // 3. Conversion and keys: a proof call against another proof, a constructor and an axiom.
  // ------------------------------------------------------------------------------------------------------------------

  private val proofIndexed =
    """
      |inductive Foo (h: Eq(Nat, 1, 1)) : Type
      | | mk {h: Eq(Nat, 1, 1)} : Foo(h)
      |
      |def lem (u: Unit) : Eq(Nat, 1, 1) := Eq.refl(1)
      |
      |""".stripMargin

  test("conv-1 CONTROL a proof call converts with an axiom and with a constructor of its proposition") {
    accepts(
      proofIndexed +
        """
          |axiom ax : Eq(Nat, 1, 1)
          |def f (x: Foo(ax)) : Foo(lem(Unit.unit)) := x
          |def g (x: Foo(Eq.refl(1))) : Foo(lem(Unit.unit)) := x
          |f(Foo.mk(ax))
          |""".stripMargin,
      withAxioms
    )
  }

  test("conv-2 CONTROL proof calls with different forced values convert at one proposition") {
    accepts(
      """
        |inductive Bar (h: Or(True, True)) : Type
        | | mk {h: Or(True, True)} : Bar(h)
        |
        |def lemL (n: Nat) : Or(True, True) := Or.inl(True, True.intro)
        |def lemR (n: Nat) : Or(True, True) := Or.inr(True, True.intro)
        |def f (x: Bar(lemL(0))) : Bar(lemR(0)) := x
        |""".stripMargin
    )
  }

  test("conv-3 proof calls of propositions that do not convert do not convert") {
    rejectsWith[TypeMismatch](
      """
        |inductive Box2 (P: Prop)(h: P) : Type
        | | mk {P: Prop}{h: P} : Box2(P, h)
        |
        |def lemT (n: Nat) : True := True.intro
        |def lemE (n: Nat) : Eq(Nat, n, n) := Eq.refl(n)
        |def f (x: Box2(True, lemT(0))) : Box2(Eq(Nat, 0, 0), lemE(0)) := x
        |""".stripMargin
    )
  }

  test("conv-4 CONTROL unification across a proof-call index whose proposition differs in form") {
    assertEquals(
      result(
        """
          |inductive P indices (n: Nat) : Prop
          | | z : P(0)
          | | s (n: Nat)(h: P(n)) : P(Nat.succ(n))
          |inductive W indices (n: Nat)(h: P(n)) : Type
          | | mk (n: Nat)(h: P(n)) : W(n, h)
          |def lemP (n: Nat)(h: P(n)) : P(Nat.add(n, 0)) := h
          |def f (n: Nat)(h: P(n))(w: W(n, lemP(n, h))) : Nat := {
          |  match w returning Nat with
          |  | W.mk m q => m
          |}
          |f(1, P.s(0, P.z), W.mk(1, P.s(0, P.z)))
          |""".stripMargin
      ),
      "1"
    )
  }

  test("conv-5 CONTROL a capture read off a proof call's proposition, and a projection of a proof call") {
    assertEquals(
      result(
        """
          |def lemEq (n: Nat) : Eq(Nat, Nat.add(n, 0), n) := Eq.refl(n)
          |def useEq (h: Eq(Nat, $a, $b)) : Eq(Nat, b, a) := Eq.symm(h)
          |def t (m: Nat) : Eq(Nat, m, m) := useEq(lemEq(m))
          |t(4)
          |""".stripMargin
      ),
      "Eq.refl(4)"
    )
    assertEquals(
      result(
        """
          |def MyAnd (a: Prop)(b: Prop) : Prop := And(a, b)
          |def lemA (n: Nat) : MyAnd(Eq(Nat, n, n), True) := And.intro(Eq(Nat, n, n), True, Eq.refl(n), True.intro)
          |def t (n: Nat) : Eq(Nat, n, n) := (lemA(n)).left
          |t(2)
          |""".stripMargin
      ),
      "Eq.refl(2)"
    )
  }

  test("conv-6 CONTROL an instance that is a proof call is found by its proposition") {
    assertEquals(
      result(
        """
          |def lemNE (n: Nat) : Nonempty(Nat) := Nonempty.intro(n)
          |def instance neNat : Nonempty(Nat) := lemNE(0)
          |def needs (B: Type)[h: Nonempty(B)] : Nonempty(B) := h
          |def t : Nonempty(Nat) := needs(Nat, derive[Nonempty(Nat)])
          |derive[Nonempty(Nat)]
          |""".stripMargin
      ),
      "Nonempty.intro(0)"
    )
  }

  // ------------------------------------------------------------------------------------------------------------------
  // 4. Large elimination and matches: the match sees the forced value, and refuted cases stay refuted.
  // ------------------------------------------------------------------------------------------------------------------

  test("elim-1 CONTROL transport along a proof call's equation of types, and a subsingleton elimination of True") {
    assertEquals(
      result(
        """
          |def lemE (n: Nat) : Eq(Type, Nat, Nat) := Eq.refl(Nat)
          |def cast (n: Nat)(x: Nat) : Nat := Eq.subst(lemE(n), Kind.copy, Level.zero, fun (T: Type): Type => T, x)
          |cast(3, 7)
          |""".stripMargin
      ),
      "7"
    )
    assertEquals(
      result(
        """
          |def lemT (n: Nat) : True := True.intro
          |def three (n: Nat) : Nat := {
          |  match lemT(n) returning Nat with
          |  | True.intro => 3
          |}
          |three(0)
          |""".stripMargin
      ),
      "3"
    )
  }

  test("elim-2 False.elim on a proof call stuck on an axiom stays stuck") {
    accepts(
      """
        |axiom bot : (n: Nat) -> False
        |def lemF (n: Nat) : False := bot(n)
        |def h (n: Nat) : Nat := False.elim(lemF(n), Nat)
        |""".stripMargin,
      withAxioms
    )
  }

  private val pick =
    """
      |def lemB (b: Bool) : Or(Eq(Bool, b, Bool.true), Eq(Bool, b, Bool.false)) := {
      |  match b returning Or(Eq(Bool, b, Bool.true), Eq(Bool, b, Bool.false)) with
      |  | Bool.true => Or.inl(Eq(Bool, Bool.true, Bool.false), Eq.refl(Bool.true))
      |  | Bool.false => Or.inr(Eq(Bool, Bool.false, Bool.true), Eq.refl(Bool.false))
      |}
      |
      |""".stripMargin

  test("elim-3 a proof call forced to a known constructor gives no large elimination of a disjunction") {
    rejectsWith[PropEliminationRestricted](
      pick +
        """
          |def n : Nat := {
          |  match lemB(Bool.true) returning Nat with
          |  | Or.inl e => 1
          |}
          |""".stripMargin
    )
  }

  test("elim-4 a match into a proposition needs every case its type allows, at a known argument and in a branch") {
    // Changed by proof match suspension: the forced value's other case, `Or.inr`, was UnreachableCase in both programs,
    // which needed `Or.inl` alone. The call is no constructor value, so the match is checked by type.
    accepts(
      pick +
        """
          |def t : True := {
          |  match lemB(Bool.true) returning True with
          |  | Or.inl e => True.intro
          |  | Or.inr e => True.intro
          |}
          |""".stripMargin
    )
    rejectsWith[MissingCase](
      pick +
        """
          |def t : True := {
          |  match lemB(Bool.true) returning True with
          |  | Or.inl e => True.intro
          |}
          |""".stripMargin
    )
    accepts(
      pick +
        """
          |def f (b: Bool) : True := {
          |  let h := lemB(b)
          |  match b returning True with
          |  | Bool.true => {
          |    match h returning True with
          |    | Or.inl e => True.intro
          |    | Or.inr e => True.intro
          |  }
          |  | Bool.false => True.intro
          |}
          |""".stripMargin
    )
  }

  // ------------------------------------------------------------------------------------------------------------------
  // 5. Linearity: a suspended proof that reads a linear value.
  // ------------------------------------------------------------------------------------------------------------------

  /** A protocol whose packets are released, and `observes`, a proof that reads a packet by observing it. */
  private val tokens =
    ProgramFixtures.packets +
      """
        |def l0 : List(Nat) := List.nil(Nat)
        |def l1 (a: Nat) : List(Nat) := List.cons(a, List.nil(Nat))
        |def l2 (a: Nat)(b: Nat) : List(Nat) := List.cons(a, List.cons(b, List.nil(Nat)))
        |
        |inductive Shares indices (consumed: List(Nat))(produced: List(Nat)) : Prop
        | | split (q: Nat)(r: Nat) : Shares(l1(Nat.add(Nat.succ(q), Nat.succ(r))), l2(Nat.succ(q), Nat.succ(r)))
        | | join (q: Nat)(r: Nat) : Shares(l2(q, r), l1(Nat.add(q, r)))
        | | release (q: Nat) : Shares(l1(q), l0)
        |
        |def releaseOne (init: List(Nat))(s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), init))(a: Nat)
        |    (toks: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), init, s, l1(a))) : Protocol.Toks(Protocol.Proto.mk(Nat, Shares), init, s, l0) :=
        |  Protocol.step(Protocol.Proto.mk(Nat, Shares), init, s, l1(a), l0, Shares.release(a), toks)
        |
        |def releaseTwo (init: List(Nat))(s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), init))(q: Nat)(r: Nat)
        |    (toks: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), init, s, l2(q, r))) : Protocol.Toks(Protocol.Proto.mk(Nat, Shares), init, s, l0) := {
        |  let whole := Protocol.step(Protocol.Proto.mk(Nat, Shares), init, s, l2(q, r), l1(Nat.add(q, r)), Shares.join(q, r), toks)
        |  releaseOne(init, s, Nat.add(q, r), whole)
        |}
        |
        |def done (init: List(Nat))(s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), init))(toks: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), init, s, l0))
        |    (R: Type)(x: R) : R := {
        |  match toks with
        |  | Protocol.Toks.nil => x
        |}
        |
        |def observes (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(C: List(Nat))
        |    (toks: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, C)) : True := {
        |  match Protocol.observe(Protocol.Proto.mk(Nat, Shares), l1(2), s, C, toks) with
        |  | Protocol.Observed.mk seen v => True.intro
        |}
        |
        |""".stripMargin

  /** An entry that splits a packet of 2 into `halves`, then runs `rest`, which must consume `halves`. */
  private def entry(resultType: String, rest: String): String =
    tokens +
      s"""
         |fun (sup: Protocol.Supply): $resultType => {
         |  let (next, s, toks) := Protocol.new(Protocol.Proto.mk(Nat, Shares), l1(2), sup)
         |  let halves := Protocol.step(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2), l2(1, 1), Shares.split(0, 0), toks)
         |""".stripMargin + rest + "}\n"

  test("lin-1 CONTROL a suspended observation outlives its packet's consumption and is demanded after it") {
    assertEquals(
      result(
        entry(
          "Nat",
          """  let seen : True := observes(s, l2(1, 1), halves)
            |  let n := done(l1(2), s, releaseTwo(l1(2), s, 1, 1, halves), Nat, 5)
            |  let later : True := {
            |    match seen returning True with
            |    | True.intro => True.intro
            |  }
            |  n
            |""".stripMargin
        )
      ),
      "5"
    )
  }

  test("lin-2 CONTROL the entry's result holds a suspended observation of a consumed packet, which printing runs") {
    assertEquals(
      result(
        entry(
          "Fact(True)",
          """  let seen : True := observes(s, l2(1, 1), halves)
            |  done(l1(2), s, releaseTwo(l1(2), s, 1, 1, halves), Fact(True), Fact.mk(seen))
            |""".stripMargin
        )
      ),
      "Fact.mk(True.intro)"
    )
  }

  test("lin-3 an undemanded proof observing a packet joined with itself is LinearReusedInType") {
    rejectsWith[LinearReusedInType](
      tokens +
        """
          |def bad (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(t: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2))) : Nat := {
          |  let never : True := observes(s, List.append(l1(2), l1(2)), joinToks(Nat, Shares, l1(2), s, l1(2), l1(2), t, t))
          |  done(l1(2), s, releaseOne(l1(2), s, 2, t), Nat, 0)
          |}
          |""".stripMargin
    )
  }

  test("lin-4 an undemanded proof over a consumed packet and its successor is LinearReusedInType") {
    rejectsWith[LinearReusedInType](
      tokens +
        """
          |def bad (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(halves: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l2(1, 1))) : Nat := {
          |  let whole := Protocol.step(Protocol.Proto.mk(Nat, Shares), l1(2), s, l2(1, 1), l1(2), Shares.join(1, 1), halves)
          |  let never : True := observes(s, List.append(l2(1, 1), l1(2)), joinToks(Nat, Shares, l1(2), s, l2(1, 1), l1(2), halves, whole))
          |  done(l1(2), s, releaseOne(l1(2), s, 2, whole), Nat, 0)
          |}
          |""".stripMargin
    )
  }

  test("lin-5 suspended proof calls are reads, not uses: the packet is consumed once after two of them") {
    def twice(consumptions: String) =
      tokens +
        """
          |def keep (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(halves: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l2(1, 1))) : Nat := {
          |  let b1 : True := observes(s, l2(1, 1), halves)
          |  let b2 : True := observes(s, l2(1, 1), halves)
          |""".stripMargin + consumptions + "}\n"
    accepts(twice("  done(l1(2), s, releaseTwo(l1(2), s, 1, 1, halves), Nat, 0)\n"))
    rejectsWith[LinearReused](
      twice(
        """  let n := done(l1(2), s, releaseTwo(l1(2), s, 1, 1, halves), Nat, 0)
          |  done(l1(2), s, releaseTwo(l1(2), s, 1, 1, halves), Nat, n)
          |""".stripMargin
      )
    )
  }

  // ------------------------------------------------------------------------------------------------------------------
  // 6–7. Refinement and memoization: a call forced in one context and read in another.
  // ------------------------------------------------------------------------------------------------------------------

  test("memo-1 CONTROL one let-bound call, materialized in each branch, forces to that branch's constructor") {
    // Changed by proof match suspension: each branch's match read its materialized call's forced value and needed that
    // branch's case alone. Now each needs both; running f(false) forces the call materialized at false, `Or.inr`,
    // whose case refutes its equation `Eq(Bool, false, true)` only if it is the one taken.
    def program(f: String) =
      pick +
        """
          |def f (b: Bool) : True := {
          |  let h := lemB(b)
          |  match b returning True with
          |  | Bool.true => {
          |    match h returning True with
          |    | Or.inl e => True.intro
          |    | Or.inr e => True.intro
          |  }
          |  | Bool.false => {
          |    match h returning True with
          |    | Or.inl e => True.intro
          |    | Or.inr e => True.intro
          |  }
          |}
          |""".stripMargin + f
    assertEquals(result(program("f(Bool.false)\n")), "True.intro")
    rejectsWith[MissingCase](
      pick +
        """
          |def f (b: Bool) : True := {
          |  let h := lemB(b)
          |  match b returning True with
          |  | Bool.true => {
          |    match h returning True with
          |    | Or.inl e => True.intro
          |  }
          |  | Bool.false => True.intro
          |}
          |""".stripMargin
    )
  }

  test("memo-2 a call forced before the branch, stuck, is checked by type in each branch, as one never forced") {
    // Changed by proof match suspension: `early` forced h, stuck on b, and each branch's match read h's forced value,
    // materialized, needing that branch's case alone. Now `early` 's match does not force h, the inferred type of
    // `forcedEarly` does (quotation), and neither changes how a later match on h checks: by type, with both cases.
    def program(forcing: String, caseInTrue: String) =
      pick +
        """
          |def f (b: Bool) : True := {
          |  let h := lemB(b)
          |  let early : True := {
          |    match h returning True with
          |    | Or.inl e => True.intro
          |    | Or.inr e => True.intro
          |  }
          |""".stripMargin + forcing +
        """
          |  match b returning True with
          |  | Bool.true => {
          |    match h returning True with
          |""".stripMargin + caseInTrue +
        """
          |  }
          |  | Bool.false => early
          |}
          |f(Bool.true)
          |""".stripMargin
    val forcing = "  let forcedEarly := {\n    match Bool.true with\n    | Bool.true => h\n  }\n"
    val both = "    | Or.inl e => early\n    | Or.inr e => early\n"
    val one = "    | Or.inl e => early\n"
    assertEquals(result(program(forcing, both)), "True.intro")
    assertEquals(result(program("", both)), "True.intro")
    rejectsWith[MissingCase](program(forcing, one))
    rejectsWith[MissingCase](program("", one))
  }

  test("memo-3 a call forced in a branch is not refined outside it, where its match needs every case") {
    rejectsWith[MissingCase](
      pick +
        """
          |def f (b: Bool) : True := {
          |  let h := lemB(b)
          |  let inBranch : True := {
          |    match b returning True with
          |    | Bool.true => {
          |      match h returning True with
          |      | Or.inl e => True.intro
          |    }
          |    | Bool.false => True.intro
          |  }
          |  match h returning True with
          |  | Or.inl e => inBranch
          |}
          |""".stripMargin
    )
  }

  test("memo-4 a demanded run that fails leaves no forcing behind: later proof calls are suspended again") {
    // The global count of running forced calls is restored however a run ends, so the next program's undemanded
    // proof, too deep for the stack, is not run.
    onSmallStack {
      rejectsWith[NatValueTooLarge](
        big +
          """
            |def t : Nat := {
            |  match big(4294967296) returning Nat with
            |  | True.intro => 0
            |}
            |""".stripMargin
      )
      accepts(deep + "def t : True := deep(100000)\n")
    }
  }

  test("ref-2 FIXED an eta projection's type holds no template variable that only a proof call's argument mentions") {
    // R's field type mentions its capture n only as constN's argument, and constN's forced value does not, so eta
    // eligibility, confirmed through forced values, holds. The projection of a neutral R kept constN(n) suspended in
    // its type, over the eta template's own variable n, so the closed global g held a free variable: the kernel died
    // with an AssertionError where eager evaluation printed the projection.
    val src =
      """
        |def constN (n: Nat) : Exists(Nat, fun (k: Nat): Prop => True) :=
        |  Exists.intro(Nat, fun (k: Nat): Prop => True, 0, True.intro)
        |
        |inductive Q (h: Exists(Nat, fun (k: Nat): Prop => True)) : Type
        | | mk {h: Exists(Nat, fun (k: Nat): Prop => True)} : Q(h)
        |
        |// n is read by position off the forced proof, so it is 0 whatever the field.
        |inductive R : Type
        | | mk (x: Q(constN($n))) : R
        |
        |def built : R := R.mk(Q.mk(Exists.intro(Nat, fun (k: Nat): Prop => True, 5, True.intro)))
        |
        |// A closed R that is no constructor: a transport along the prelude's builtin proof `Nat.expand_eq`, which never
        |// reduces, so the transport is stuck.
        |def r : R := Eq.subst(Nat.expand_eq(5), Kind.copy, Level.zero, fun (k: Nat): Type => R, built)
        |
        |def g : Q(constN(7)) := {
        |  match r returning Q(constN(7)) with
        |  | R.mk x => x
        |}
        |
        |g
        |""".stripMargin
    assertEquals(
      result(src),
      "(match Nat.expand_eq(5) returning (fun (k: Nat) => R)(5) with | Eq.refl z => R.mk(Q.mk)).x"
    )
    val g = programs.declsEnv(src).apply("g")
    assert(g.synDeps.isEmpty && g.tpe.synDeps.isEmpty, PrettyPrinter.print(g.tpe))
  }

  test("ref-1 CONTROL an equation links the call's argument through another variable, and the call sees it") {
    // Changed by proof match suspension: the inner match read the call materialized through the link, forced to
    // `Or.inl`, and needed that case alone; now it is checked by type and needs both. Printing the result runs the
    // match on the call, which reaches `Or.inl`.
    def program(cases: String) =
      pick +
        """
          |def f (b: Bool)(c: Bool)(e: Eq(Bool, b, c)) : Or(True, True) := {
          |  let h := lemB(b)
          |  match c returning Or(True, True) with
          |  | Bool.true => {
          |    match e returning Or(True, True) with
          |    | Eq.refl z => {
          |      match h returning Or(True, True) with
          |""".stripMargin + cases +
        """
          |    }
          |  }
          |  | Bool.false => Or.inr(True, True.intro)
          |}
          |f(Bool.true, Bool.true, Eq.refl(Bool.true))
          |""".stripMargin
    val inl = "      | Or.inl q => Or.inl(True, True.intro)\n"
    assertEquals(result(program(inl + "      | Or.inr q => Or.inr(True, True.intro)\n")), "Or.inl(True.intro)")
    rejectsWith[MissingCase](program(inl))
  }

  // ------------------------------------------------------------------------------------------------------------------
  // 8. The other ports: tail loops, memoized materialization and EvaluationTooDeep, meeting suspended proofs.
  // ------------------------------------------------------------------------------------------------------------------

  /**
   * A tail loop of `n` steps whose accumulator holds a proof built from the previous one's, through data, and `t`, a
   * match on the last one into a proposition, or with `demand` a large elimination of it.
   */
  private def chain(n: Int, demand: Boolean = false): String = {
    val (motive, result) = if (demand) ("Nat", "0") else ("True", "a")
    s"""
       |def step (h: And(True, True)) : And(True, True) := {
       |  match h returning And(True, True) with
       |  | And.intro a b => And.intro(True, True, a, b)
       |}
       |
       |def unfactAnd (f: Fact(And(True, True))) : And(True, True) := {
       |  match f returning And(True, True) with
       |  | Fact.mk p => p
       |}
       |
       |def go (n: Nat)(acc: Fact(And(True, True))) : Fact(And(True, True)) decreases structural(n) := {
       |  match n returning Fact(And(True, True)) with
       |  | Nat.zero => acc
       |  | Nat.succ k => go(k, Fact.mk(step(unfactAnd(acc))))
       |}
       |
       |def chain : Fact(And(True, True)) := go($n, Fact.mk(And.intro(True, True, True.intro, True.intro)))
       |
       |def t : $motive := {
       |  match unfactAnd(chain) returning $motive with
       |  | And.intro a b => $result
       |}
       |""".stripMargin
  }

  test("port-1 CONTROL a tail loop accumulates suspended proofs, and a match demands the last one") {
    // A large elimination, since a match into a proposition no longer demands it (changed by proof match suspension).
    onSmallStack(accepts(chain(1000, demand = true)))
  }

  test("port-2 FIXED a long chain of suspended proofs through data checks on the stack eager evaluation kept") {
    // Each step of the loop suspends step(unfactAnd(acc)), whose argument holds the previous step's call, so the chain
    // is as long as the loop. Eager evaluation ran each call as it was made, on a value already in normal form, and
    // checked this program on the same 4 MiB stack. The build before proof match suspension refused a chain of 5000
    // with EvaluationTooDeep, and the CLI's 256 MiB stack one of 1000000: forcing it, which t's match demanded, and its
    // dependencies, which the closedness check of the globals computes, recursed once per step. t's match is into a
    // proposition, so nothing forces the chain now, and dependencies are computed in a loop.
    onSmallStack(accepts(chain(1000000)))
  }

  test("port-2b LIMIT a demanded chain of suspended proofs through data still forces one step inside the next") {
    // A large elimination demands the chain: each step's run forces the previous one where its match needs it, as
    // eager evaluation never had to.
    onSmallStack(rejectsWith[EvaluationTooDeep](chain(100000, demand = true)))
  }

  test("port-3 CONTROL a long chain of proof calls that each return the next forces in a loop, without stack") {
    // Each idp returns its argument, unfactTrue's field, which is the previous step's call: forcing follows the chain.
    val src =
      """
        |def idp (p: Prop)(h: p) : p := h
        |
        |def unfactTrue (f: Fact(True)) : True := {
        |  match f returning True with
        |  | Fact.mk p => p
        |}
        |
        |def go (n: Nat)(acc: Fact(True)) : Fact(True) decreases structural(n) := {
        |  match n returning Fact(True) with
        |  | Nat.zero => acc
        |  | Nat.succ k => go(k, Fact.mk(idp(True, unfactTrue(acc))))
        |}
        |
        |{
        |  match unfactTrue(go(100000, Fact.mk(True.intro))) returning Nat with
        |  | True.intro => 7
        |}
        |""".stripMargin
    onSmallStack(assertEquals(result(src), "7"))
  }

  // ------------------------------------------------------------------------------------------------------------------
  // 9. Proof matches (EVALUATION_AND_PORTS §2 item 4): a match from a suspended proof into a proposition is itself
  //    suspended, and the checker reads its scrutinee by its proposition. Eager evaluation's outcome is the same unless
  //    a test says otherwise.
  // ------------------------------------------------------------------------------------------------------------------

  test("pm-1 a suspended match whose cases the scrutinee's type refutes, or whose result is false, is refused") {
    val le =
      """
        |inductive Le indices (n: Nat) : Prop
        | | z : Le(0)
        | | s (n: Nat)(h: Le(n)) : Le(Nat.succ(n))
        |def lemZ (u: Unit) : Le(0) := Le.z
        |""".stripMargin
    rejectsWith[UnreachableCase](
      le +
        """
          |def t : True := {
          |  match lemZ(Unit.unit) returning True with
          |  | Le.z => True.intro
          |  | Le.s m h => True.intro
          |}
          |""".stripMargin
    )
    // The case the forced value takes cannot prove the false motive, and the other case has nothing to prove it from.
    rejectsWith[TypeMismatch](
      pick +
        """
          |def bad : Eq(Bool, Bool.true, Bool.false) := {
          |  match lemB(Bool.true) returning Eq(Bool, Bool.true, Bool.false) with
          |  | Or.inl e => e
          |  | Or.inr f => f
          |}
          |""".stripMargin
    )
    // CONTROL: a proof of False by an axiom, matched into False with no case, stays suspended; printing forces it to
    // a match stuck on the call's forced value, the axiom's application, which prints as its syntax.
    assertEquals(
      withAxioms.result(
        """
          |axiom bot : (n: Nat) -> False
          |def lemF (n: Nat) : False := bot(n)
          |def t : False := {
          |  match lemF(0) returning False with
          |}
          |t
          |""".stripMargin
      ),
      "match lemF(0) returning False with "
    )
  }

  test("pm-2 a suspended match whose proposition depends on its scrutinee") {
    // CONTROL: the motive names the let-bound scrutinee, a proof call, which no branch refines; the branch's proof of
    // Wit(True.intro) converts with Wit(h) by proof irrelevance.
    accepts(
      """
        |inductive Wit (h: True) : Prop
        | | mk {h: True} : Wit(h)
        |def lemT (n: Nat) : True := True.intro
        |def t (n: Nat) : Wit(lemT(n)) := {
        |  let h := lemT(n)
        |  match h returning Wit(h) with
        |  | True.intro => Wit.mk(True.intro)
        |}
        |""".stripMargin
    )
    // The motive large-eliminates the scrutinee, which reading the motive demands, as eager evaluation ran it.
    rejectsWith[NatValueTooLarge](
      big +
        """
          |def M (h: True) : Prop := {
          |  match h returning Prop with
          |  | True.intro => True
          |}
          |def t : True := {
          |  let h := big(4294967296)
          |  match h returning M(h) with
          |  | True.intro => True.intro
          |}
          |""".stripMargin
    )
    // CONTROL: a motive over a variable index that the case's refinement solves; outside, the motive is unrefined.
    accepts(
      """
        |inductive Is indices (b: Bool) : Prop
        | | yes : Is(Bool.true)
        |def idp (p: Prop)(h: p) : p := h
        |def f (b: Bool)(h: Is(b)) : Eq(Bool, b, Bool.true) := {
        |  match idp(Is(b), h) returning Eq(Bool, b, Bool.true) with
        |  | Is.yes => Eq.refl(Bool.true)
        |}
        |""".stripMargin
    )
    rejectsWith[TypeMismatch](
      """
        |inductive Is indices (b: Bool) : Prop
        | | yes : Is(Bool.true)
        |def idp (p: Prop)(h: p) : p := h
        |def f (b: Bool)(h: Is(b)) : Eq(Bool, b, Bool.false) := {
        |  match idp(Is(b), h) returning Eq(Bool, b, Bool.false) with
        |  | Is.yes => Eq.refl(Bool.true)
        |}
        |""".stripMargin
    )
  }

  test("pm-3 linear values read inside a suspended match: reads, checked by the read rules, run after consumption") {
    val idp = "def idp (p: Prop)(h: p) : p := h\n"
    // CONTROL: the match observes the packet in its case; it is demanded by printing, after the packet is consumed.
    assertEquals(
      result(
        idp + entry(
          "Fact(True)",
          """  let seen : True := {
            |    match idp(True, True.intro) returning True with
            |    | True.intro => observes(s, l2(1, 1), halves)
            |  }
            |  done(l1(2), s, releaseTwo(l1(2), s, 1, 1, halves), Fact(True), Fact.mk(seen))
            |""".stripMargin
        )
      ),
      "Fact.mk(True.intro)"
    )
    // A packet joined with itself, read in an undemanded case, is still refused.
    rejectsWith[LinearReusedInType](
      idp + tokens +
        """
          |def bad (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(t: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2))) : Nat := {
          |  let never : True := {
          |    match idp(True, True.intro) returning True with
          |    | True.intro => observes(s, List.append(l1(2), l1(2)), joinToks(Nat, Shares, l1(2), s, l1(2), l1(2), t, t))
          |  }
          |  done(l1(2), s, releaseOne(l1(2), s, 2, t), Nat, 0)
          |}
          |""".stripMargin
    )
    // Two suspended matches only read the packet: one consumption checks, a second is refused.
    def twice(consumptions: String) =
      idp + tokens +
        """
          |def keep (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(halves: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l2(1, 1))) : Nat := {
          |  let b1 : True := {
          |    match idp(True, True.intro) returning True with
          |    | True.intro => observes(s, l2(1, 1), halves)
          |  }
          |  let b2 : True := {
          |    match idp(True, True.intro) returning True with
          |    | True.intro => observes(s, l2(1, 1), halves)
          |  }
          |""".stripMargin + consumptions + "}\n"
    accepts(twice("  done(l1(2), s, releaseTwo(l1(2), s, 1, 1, halves), Nat, 0)\n"))
    rejectsWith[LinearReused](
      twice(
        """  let n := done(l1(2), s, releaseTwo(l1(2), s, 1, 1, halves), Nat, 0)
          |  done(l1(2), s, releaseTwo(l1(2), s, 1, 1, halves), Nat, n)
          |""".stripMargin
      )
    )
  }

  test("pm-4 a suspended match as a termination candidate is compared by its forced value's key") {
    // CONTROL: in the branch, the match forces to h1, a field of the root.
    accepts(
      acc +
        """
          |def walk (h: Acc2) : True decreases structural(h) := {
          |  match h returning True with
          |  | Acc2.step h1 => {
          |    let c : Acc2 := {
          |      match idp(Acc2, h) returning Acc2 with
          |      | Acc2.step k => k
          |    }
          |    walk(c)
          |  }
          |}
          |""".stripMargin
    )
    // The root itself, through a suspended match, is unchanged.
    rejectsWith[NonDecreasingRecursiveCall](
      acc +
        """
          |def walk (h: Acc2) : True decreases structural(h) := {
          |  match h returning True with
          |  | Acc2.step h1 => {
          |    let c : Acc2 := {
          |      match idp(Acc2, h) returning Acc2 with
          |      | Acc2.step k => h
          |    }
          |    walk(c)
          |  }
          |}
          |""".stripMargin
    )
    // Outside a branch the match is stuck on the root: no field of it.
    rejectsWith[NonDecreasingRecursiveCall](
      acc +
        """
          |def walk (h: Acc2) : True decreases structural(h) := {
          |  let c : Acc2 := {
          |    match idp(Acc2, h) returning Acc2 with
          |    | Acc2.step k => k
          |  }
          |  walk(c)
          |}
          |""".stripMargin
    )
    // A rebuilt proof of a field's proposition is a new proof.
    rejectsWith[NonDecreasingRecursiveCall](
      acc +
        """
          |def walk (h: Acc2) : True decreases structural(h) := {
          |  match h returning True with
          |  | Acc2.step h1 => {
          |    let c : Acc2 := {
          |      match idp(Acc2, h1) returning Acc2 with
          |      | Acc2.step k => Acc2.step(k)
          |    }
          |    walk(c)
          |  }
          |}
          |""".stripMargin
    )
    // The key test forces the candidate, so a failing run is refused with its error, as eager evaluation ran it.
    rejectsWith[NatValueTooLarge](
      acc +
        """
          |def bigAcc (n: Nat)(h: Acc2) : Acc2 := {
          |  let x := Nat.pow(2, n)
          |  h
          |}
          |def walk (h: Acc2) : True decreases structural(h) := {
          |  match h returning True with
          |  | Acc2.step h1 => {
          |    let c : Acc2 := {
          |      match bigAcc(4294967296, h) returning Acc2 with
          |      | Acc2.step k => k
          |    }
          |    walk(c)
          |  }
          |}
          |""".stripMargin
    )
  }

  test("pm-5 OVER-REJECTION a field of a matched proof call is no field of the root, where its forced variable was") {
    // Eager evaluation, and the build before proof match suspension, forced idp(Acc2, h1) to h1, a variable, so the
    // match linked h1 to Acc2.step(k), and k was a field of a field of the root. The suspended scrutinee is linked to
    // nothing: k is a fresh proof. The match into a proposition reads the call by its proposition, so this is the cost
    // of not forcing it. Matching on h1 itself still links it.
    rejectsWith[NonDecreasingRecursiveCall](
      acc +
        """
          |def walk (h: Acc2) : True decreases structural(h) := {
          |  match h returning True with
          |  | Acc2.step h1 => {
          |    match idp(Acc2, h1) returning True with
          |    | Acc2.step k => walk(k)
          |  }
          |}
          |""".stripMargin
    )
    accepts(
      acc +
        """
          |def walk (h: Acc2) : True decreases structural(h) := {
          |  match h returning True with
          |  | Acc2.step h1 => {
          |    match h1 returning True with
          |    | Acc2.step k => walk(k)
          |  }
          |}
          |""".stripMargin
    )
  }

  test("pm-6 a suspended match is compared by its proposition, and by its forced value's key") {
    // CONTROL: suspended matches with different forced values convert at one proposition.
    accepts(
      """
        |inductive Bar (h: Or(True, True)) : Type
        | | mk {h: Or(True, True)} : Bar(h)
        |def lemL (n: Nat) : Or(True, True) := Or.inl(True, True.intro)
        |def swap (n: Nat) : Or(True, True) := {
        |  match lemL(n) returning Or(True, True) with
        |  | Or.inl a => Or.inr(True, a)
        |  | Or.inr a => Or.inl(True, a)
        |}
        |def f (x: Bar(swap(0))) : Bar(lemL(0)) := x
        |""".stripMargin
    )
    // Suspended matches of propositions that do not convert do not convert.
    rejectsWith[TypeMismatch](
      """
        |inductive Box2 (P: Prop)(h: P) : Type
        | | mk {P: Prop}{h: P} : Box2(P, h)
        |def lemT (n: Nat) : True := True.intro
        |def lemE (n: Nat) : Eq(Nat, n, n) := Eq.refl(n)
        |def mT : True := {
        |  match lemT(0) returning True with
        |  | True.intro => True.intro
        |}
        |def mE : Eq(Nat, 0, 0) := {
        |  match lemE(0) returning Eq(Nat, 0, 0) with
        |  | Eq.refl z => Eq.refl(0)
        |}
        |def f (x: Box2(True, mT)) : Box2(Eq(Nat, 0, 0), mE) := x
        |""".stripMargin
    )
    // A suspended match keys as its forced value, so equal forced values have equal keys and different ones differ.
    val env = programs.declsEnv(
      """
        |def lemL (n: Nat) : Or(True, True) := Or.inl(True, True.intro)
        |def same : Or(True, True) := {
        |  match lemL(0) returning Or(True, True) with
        |  | Or.inl a => Or.inl(True, a)
        |  | Or.inr a => Or.inr(True, a)
        |}
        |def swap : Or(True, True) := {
        |  match lemL(0) returning Or(True, True) with
        |  | Or.inl a => Or.inr(True, a)
        |  | Or.inr a => Or.inl(True, a)
        |}
        |def direct : Or(True, True) := Or.inl(True, True.intro)
        |""".stripMargin
    )
    assert(env("same").isInstanceOf[Value.VProofMatch] && env("swap").isInstanceOf[Value.VProofMatch])
    assertEquals(env("same").key, env("direct").key)
    assertNotEquals(env("swap").key, env("direct").key)
  }
}
