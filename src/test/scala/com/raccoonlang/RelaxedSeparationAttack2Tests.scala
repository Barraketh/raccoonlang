package com.raccoonlang

import com.raccoonlang.ErrorReporter.Source
import com.raccoonlang.ProgramFixtures.Programs
import com.raccoonlang.Value._

/**
 * Second-round adversarial review of the S1 relaxation (branch `relaxed-separation`). The first attacker broke
 * `let a := t; let b := t`; it was fixed by making lets alias their value's provenance. This suite probes the remaining
 * laundering surface: function results built from some/none of their inputs, higher-order and stored functions,
 * `Eq.subst` transports into linear motives, selectors, recursion, matches on constructed/non-exact scrutinees, deep
 * nested fields, exactness, erased binders, joint liveness with mid-body Pi binders, escapes and conversion.
 *
 * The canonical target is `Valid(Shares, [2], [2, 2])`, refuted by `heldCoverage` /`pairBound` to an absurd `Le(4, 2)`
 * / `Eq(Nat, 2, 0)`, and then `False`. A test that ACCEPTS a forgery, or accepts a program deriving `False` /a false
 * `Valid` with no user axioms, is a break. A test labelled OVER-REJECTION flags a sound program the language rejects.
 */
class RelaxedSeparationAttack2Tests extends munit.FunSuite {
  private val programs = new Programs(Prelude.default, allowUserAxioms = false)
  import programs.runChecked

  /** Accept: the program checks and runs with no user axioms. */
  private def accepts(src: String): Unit =
    try { runChecked(src); () }
    catch { case t: TypeError => fail("REJECTED (should accept): " + ErrorReporter.pretty(t, Source(src))) }

  /** The program is rejected by some TypeError; a pass means no break here. An ACCEPT is a break. */
  private def rejects(src: String): TypeError =
    try {
      runChecked(src)
      fail("ACCEPTED (BREAK: should be rejected)")
    } catch { case t: TypeError => t }

  private def rejectsWith[T <: TypeError](src: String)(implicit ct: reflect.ClassTag[T]): T = {
    val t = rejects(src)
    t match {
      case ct(e) => e
      case other =>
        fail(s"rejected by ${other.getClass.getSimpleName} (${other.getMessage}), not ${ct.runtimeClass.getSimpleName}")
    }
  }

  // ------------------------------------------------------------------------------------------------------------------
  // Shared prelude, copied from RelaxedSeparationAttackTests: Shares, pairBound/heldCoverage, packet ops, releases,
  // the observing bundle, and eqFalse.
  // ------------------------------------------------------------------------------------------------------------------

  private val shares =
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
      |def total (xs: List(Nat)) : Nat decreases structural(xs) := {
      |  match xs with
      |  | List.nil => 0
      |  | List.cons x rest => Nat.add(x, total(rest))
      |}
      |
      |inductive Le (a: Nat)(b: Nat) : Prop
      | | mk {a: Nat}{b: Nat} (k: Nat)(e: Eq(Nat, Nat.add(a, k), b)) : Le(a, b)
      |
      |def addZero (q: Nat)(k: Nat)(h: Eq(Nat, Nat.add(q, k), 0)) : Eq(Nat, q, 0) := {
      |  match q returning Eq(Nat, q, 0) with
      |  | Nat.zero => Eq.refl(0)
      |  | Nat.succ q1 => {
      |    match h returning Eq(Nat, Nat.succ(q1), 0) with
      |  }
      |}
      |
      |def permTotal (xs: List(Nat))(ys: List(Nat))(p: List.Perm(Nat, xs, ys))
      |    : Eq(Nat, total(xs), total(ys)) decreases structural(p) := {
      |  match p returning Eq(Nat, total(xs), total(ys)) with
      |  | List.Perm.nil => Eq.refl(0)
      |  | List.Perm.cons x xs1 ys1 q =>
      |      congrArg(permTotal(xs1, ys1, q), Nat, fun (m: Nat): Nat => Nat.add(x, m))
      |  | List.Perm.swap x y zs => Eq.refl(total(List.cons(y, List.cons(x, zs))))
      |  | List.Perm.trans as1 bs1 cs1 q r => Eq.trans(permTotal(as1, bs1, q), permTotal(bs1, cs1, r))
      |}
      |
      |def reachBound (n: Nat)(C: List(Nat))(r: Protocol.Reach(Protocol.Proto.mk(Nat, Shares), l1(n), C))
      |    : Le(total(C), n) decreases structural(r) := {
      |  match r returning Le(total(C), n) with
      |  | Protocol.Reach.initial => Le.mk(total(l1(n)), n, 0, Eq.refl(n))
      |  | Protocol.Reach.step A B frame h prev => {
      |    match h returning Le(total(List.append(B, frame)), n) with
      |    | Shares.split q r1 => reachBound(n, List.append(A, frame), prev)
      |    | Shares.join q r1 => reachBound(n, List.append(A, frame), prev)
      |    | Shares.release q => {
      |      match reachBound(n, List.append(A, frame), prev) returning Le(total(frame), n) with
      |      | Le.mk k e => Le.mk(total(frame), n, Nat.add(q, k), e)
      |    }
      |  }
      |  | Protocol.Reach.perm C1 D1 prev p =>
      |      Eq.substProp(permTotal(C1, D1, p), fun (x: Nat): Prop => Le(x, n), reachBound(n, C1, prev))
      |}
      |
      |def pairBound (n: Nat)(q: Nat)(r: Nat)(v: Protocol.Valid(Protocol.Proto.mk(Nat, Shares), l1(n), l2(q, r))) : Le(Nat.add(q, r), n) := {
      |  match v returning Le(Nat.add(q, r), n) with
      |  | Protocol.Valid.mk C rest r1 => {
      |    match reachBound(n, List.append(C, rest), r1) returning Le(Nat.add(q, r), n) with
      |    | Le.mk k e => Le.mk(Nat.add(q, r), n, Nat.add(total(rest), k), e)
      |  }
      |}
      |
      |def heldCoverage (n: Nat)(q: Nat)(v: Protocol.Valid(Protocol.Proto.mk(Nat, Shares), l1(n), l2(n, q))) : Eq(Nat, q, 0) := {
      |  match pairBound(n, n, q, v) returning Eq(Nat, q, 0) with
      |  | Le.mk k e => addZero(q, k, congrArg(e, Nat, fun (x: Nat): Nat => Nat.sub(x, n)))
      |}
      |
      |def eqFalse (h: Eq(Nat, 2, 0)) : False := {
      |  match h returning False with
      |}
      |
      |""".stripMargin

  private val releases =
    shares +
      """
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
        |""".stripMargin

  private val packets = ProgramFixtures.packets

  private val observing =
    releases + packets +
      """
        |def observedBound (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(q: Nat)(r: Nat)
        |    (both: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l2(q, r))) : Le(Nat.add(q, r), 2) := {
        |  match Protocol.observe(Protocol.Proto.mk(Nat, Shares), l1(2), s, l2(q, r), both) with
        |  | Protocol.Observed.mk seen v => pairBound(2, q, r, v)
        |}
        |
        |""".stripMargin

  // ==================================================================================================================
  // Vector 1: laundering through function calls whose result is built from some/none of their inputs.
  // ==================================================================================================================

  // A function that releases its token and then tries to mint a fresh [2,2] packet: there is no Shares rule from nil,
  // so there is no closed source for [2,2], and the body cannot be written. This records that the "mint from a
  // zero-input step" door is closed for a no-duplication protocol.
  test("V1 mint-from-nothing: no Shares rule consumes nil, so [2] cannot be forged by a zero-input step") {
    rejects(
      observing +
        """
          |def forge (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(t: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2)))
          |    : Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2)) := {
          |  let gone := releaseOne(l1(2), s, 2, t)
          |  Protocol.step(Protocol.Proto.mk(Nat, Shares), l1(2), s, l0, l1(2), Shares.release(2), gone)
          |}
          |""".stripMargin
    )
  }

  // A function that returns a packet built from only ONE of its two linear inputs still carries BOTH inputs' regions
  // in its result provenance (Provenance.union over all linear inputs). So feeding it `t` twice through two such
  // functions cannot disjoin the regions. `keepFirst` genuinely drops `b` (releasing it) and returns `a`.
  test("V1 project-one-of-two: a result keeps every input's region, even a dropped one") {
    rejectsWith[LinearReusedInType](
      observing +
        """
          |def keepFirst (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(a: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2)))
          |    (b: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2))) : Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2)) := {
          |  let gone := releaseOne(l1(2), s, 2, b)
          |  match gone with
          |  | Protocol.Toks.nil => a
          |}
          |
          |def forge (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(t: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2)))
          |    : Le(Nat.add(2, 2), 2) := {
          |  match Protocol.observe(Protocol.Proto.mk(Nat, Shares), l1(2), s, l2(2, 2),
          |      joinToks(Nat, Shares, l1(2), s, l1(2), l1(2), keepFirst(s, t, t), t)) with
          |  | Protocol.Observed.mk seen v => pairBound(2, 2, 2, v)
          |}
          |""".stripMargin
    )
  }

  // ==================================================================================================================
  // Vector 2: Eq.subst into a linear motive, and transports.
  // ==================================================================================================================

  // Transport t along Eq(List, l1(2), l1(2)) (reflexive) to a copy b. Eq.subst's result unions its linear input's
  // region, so b carries {t}; joining a := t and b overlaps.
  test("V2 subst-launder: transport t along a reflexive Eq, then join with t") {
    rejectsWith[LinearReusedInType](
      observing +
        """
          |def forge (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(t: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2)))
          |    : Le(Nat.add(2, 2), 2) := {
          |  let a := t
          |  let b := Eq.subst(Eq.refl(l1(2)), Kind.lin, Level.zero,
          |    fun (c: List(Nat)): Lin(Level.zero) => Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, c), t)
          |  match Protocol.observe(Protocol.Proto.mk(Nat, Shares), l1(2), s, l2(2, 2), joinToks(Nat, Shares, l1(2), s, l1(2), l1(2), a, b)) with
          |  | Protocol.Observed.mk seen v => pairBound(2, 2, 2, v)
          |}
          |""".stripMargin
    )
  }

  // ==================================================================================================================
  // Vector 3: stored copyable functions in a linear family (L9) cannot be a duplication channel.
  // ==================================================================================================================

  // A linear family stores a copyable function field. The function cannot capture a token (F5), and a function taking
  // a token and returning join(x, x) is rejected inside its own body (x used twice, body not a read). So a stored
  // function offers no duplication channel. Here the attempt is caught at the lambda that builds the stored function.
  test("V3 stored-function: a function field that would duplicate its own token argument is rejected") {
    rejects(
      observing +
        """
          |inductive Dup : Lin(Level.zero)
          | | mk (f: (x: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2))) ->
          |        Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l2(2, 2)))(s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2))) : Dup
          |
          |def make (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2))) : Dup :=
          |  Dup.mk(fun (x: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2))): Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l2(2, 2)) =>
          |    joinToks(Nat, Shares, l1(2), s, l1(2), l1(2), x, x), s)
          |""".stripMargin
    )
  }

  // ==================================================================================================================
  // Vector 4: recursion.
  // ==================================================================================================================

  // A recursive function that in a proof body reads its token twice via the recursive call plus a direct observe.
  // The recursion self is app-head only; the body is a proof (read extent). Any call combining t with a t-derived
  // value is separation-checked.
  test("V4 recursion-launder: a proof recursing on a token cannot read it beside its own result") {
    rejects(
      observing +
        """
          |def bad (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(a: Nat)(t: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(a)))
          |    : Le(Nat.add(2, 2), 2) decreases structural(a) := {
          |  match a returning Le(Nat.add(2, 2), 2) with
          |  | Nat.zero => {
          |    match Protocol.observe(Protocol.Proto.mk(Nat, Shares), l1(2), s, l2(2, 2),
          |        joinToks(Nat, Shares, l1(2), s, l1(2), l1(2), t, t)) with
          |    | Protocol.Observed.mk seen v => pairBound(2, 2, 2, v)
          |  }
          |  | Nat.succ k => bad(s, 2, t)
          |}
          |""".stripMargin
    )
  }

  // ==================================================================================================================
  // Vector 5: matches on constructed / non-exact scrutinees.
  // ==================================================================================================================

  // Reconstruct a packet from t's fields (legit), then match THAT reconstructed packet: it is a call result, so its
  // fields get the whole non-exact provenance, and splitting it again cannot disjoin.
  test("V5 rematch-constructed: fields of a constructed packet get its whole provenance, so cannot be disjoined") {
    rejectsWith[LinearReusedInType](
      observing +
        """
          |def single (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(a: Nat)(tok: Protocol.Tok(Protocol.Proto.mk(Nat, Shares), l1(2), s, a))
          |    : Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(a)) :=
          |  Protocol.Toks.cons(Protocol.Proto.mk(Nat, Shares), l1(2), s, a, tok, l0, Protocol.Toks.nil(Protocol.Proto.mk(Nat, Shares), l1(2), s))
          |
          |def forge (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(t: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2)))
          |    : Le(Nat.add(2, 2), 2) := {
          |  match t with
          |  | Protocol.Toks.cons a tok C rest => {
          |    let built := joinToks(Nat, Shares, l1(2), s, l1(a), C, single(s, a, tok), rest)
          |    match built with
          |    | Protocol.Toks.cons a2 tok2 C2 rest2 => {
          |      match Protocol.observe(Protocol.Proto.mk(Nat, Shares), l1(2), s, l2(2, 2),
          |          joinToks(Nat, Shares, l1(2), s, l1(2), l1(2), single(s, a2, tok2), built)) with
          |      | Protocol.Observed.mk seen v => pairBound(2, 2, 2, v)
          |    }
          |  }
          |}
          |""".stripMargin
    )
  }

  // ==================================================================================================================
  // Vector 6: deep nested fields -- a field of a field against a field.
  // ==================================================================================================================

  // t : l2(2,2) has two tokens. Match t to get tok (field 1) and rest (field 3). Match rest to get tok2 (rest's
  // field 1). tok and tok2 are genuinely different tokens, so joining single(tok) with single(tok2) is the legit
  // recombination of t -- Valid([2],[2,2]) here is TRUE for an honest [2,2] packet, so no contradiction arises.
  // This must be ACCEPTED: rejecting it would be an over-rejection.
  test("V6 deep-fields-honest: two distinct deep tokens recombine into their own true packet (accept)") {
    accepts(
      observing +
        """
          |def single (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(a: Nat)(tok: Protocol.Tok(Protocol.Proto.mk(Nat, Shares), l1(2), s, a))
          |    : Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(a)) :=
          |  Protocol.Toks.cons(Protocol.Proto.mk(Nat, Shares), l1(2), s, a, tok, l0, Protocol.Toks.nil(Protocol.Proto.mk(Nat, Shares), l1(2), s))
          |
          |def honest (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(t: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l2(2, 2))) : Nat := {
          |  match t with
          |  | Protocol.Toks.cons a tok C rest => {
          |    match rest with
          |    | Protocol.Toks.cons a2 tok2 C2 rest2 => {
          |      let rebuilt := joinToks(Nat, Shares, l1(2), s, l1(a), l1(a2), single(s, a, tok),
          |        Protocol.Toks.cons(Protocol.Proto.mk(Nat, Shares), l1(2), s, a2, tok2, C2, rest2))
          |      match Protocol.observe(Protocol.Proto.mk(Nat, Shares), l1(2), s, List.append(l1(a), l1(a2)), rebuilt) with
          |      | Protocol.Observed.mk seen v =>
          |          done(l1(2), s, releaseTwo(l1(2), s, a, a2, seen), Nat, 0)
          |    }
          |  }
          |}
          |""".stripMargin
    )
  }

  // The dishonest version: a deep token tok2 (rest's field 1) joined with the WHOLE t overlaps, since t's region is a
  // prefix of tok2's path. Must be rejected.
  test("V6 deep-fields-dishonest: a deep token joined with its whole packet overlaps") {
    rejectsWith[LinearReusedInType](
      observing +
        """
          |def single (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(a: Nat)(tok: Protocol.Tok(Protocol.Proto.mk(Nat, Shares), l1(2), s, a))
          |    : Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(a)) :=
          |  Protocol.Toks.cons(Protocol.Proto.mk(Nat, Shares), l1(2), s, a, tok, l0, Protocol.Toks.nil(Protocol.Proto.mk(Nat, Shares), l1(2), s))
          |
          |def forge (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(t: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2)))
          |    : Le(Nat.add(2, 2), 2) := {
          |  match t with
          |  | Protocol.Toks.cons a tok C rest => {
          |    match Protocol.observe(Protocol.Proto.mk(Nat, Shares), l1(2), s, List.append(l1(a), l1(2)),
          |        joinToks(Nat, Shares, l1(2), s, l1(a), l1(2), single(s, a, tok), t)) with
          |    | Protocol.Observed.mk seen v => pairBound(2, 2, 2, v)
          |  }
          |}
          |""".stripMargin
    )
  }

  // ==================================================================================================================
  // Vector 7: joint liveness with a mid-body Pi binder, and with an erased binder.
  // ==================================================================================================================

  // Consume t at term level, then form a Pi type whose binder u is read together with the (consumed) t. Not jointly
  // live.
  test("V7 consume-then-form-Pi: a Pi binder bound after t is consumed cannot combine with t") {
    rejectsWith[LinearNotJointlyLive](
      observing +
        """
          |def Seen (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(C: List(Nat))(t: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, C)) : Prop :=
          |  True
          |
          |def bad (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(t: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2))) : Nat := {
          |  let gone := releaseOne(l1(2), s, 2, t)
          |  let T : Prop := (u: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2))) ->
          |    Seen(s, l2(2, 2), joinToks(Nat, Shares, l1(2), s, l1(2), l1(2), u, t))
          |  done(l1(2), s, gone, Nat, 0)
          |}
          |""".stripMargin
    )
  }

  // ==================================================================================================================
  // Vector 8: escape -- a linear value leaving a read into a term.
  // ==================================================================================================================

  // `observe` returns an Observed (a linear family), so its `seen` packet is a real token leaving the observation.
  // Trying to observe twice to get two seen packets and join them: the second observe's input t overlaps the first.
  test("V8 double-observe: two observations of t give two seen packets that overlap at t") {
    rejects(
      observing +
        """
          |def forge (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(t: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2)))
          |    : Le(Nat.add(2, 2), 2) := {
          |  match Protocol.observe(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2), t) with
          |  | Protocol.Observed.mk seen1 v1 => {
          |    match Protocol.observe(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2), t) with
          |    | Protocol.Observed.mk seen2 v2 => {
          |      match Protocol.observe(Protocol.Proto.mk(Nat, Shares), l1(2), s, l2(2, 2),
          |          joinToks(Nat, Shares, l1(2), s, l1(2), l1(2), seen1, seen2)) with
          |      | Protocol.Observed.mk seen v => pairBound(2, 2, 2, v)
          |    }
          |  }
          |}
          |""".stripMargin
    )
  }

  // ==================================================================================================================
  // Positive controls / over-rejection probes: the relaxation must still accept these sound programs.
  // ==================================================================================================================

  // Honest split/observe/join/release round trip, held in a proof that reads the tokens, then consumes them.
  test("POSITIVE: observe held halves in a proof, then consume them (R2)") {
    accepts(
      observing +
        """
          |def keep (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(halves: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l2(1, 1))) : Nat := {
          |  let bound : Le(Nat.add(1, 1), 2) := observedBound(s, 1, 1, halves)
          |  done(l1(2), s, releaseTwo(l1(2), s, 1, 1, halves), Nat, 0)
          |}
          |""".stripMargin
    )
  }

  // ==================================================================================================================
  // Vector 9: joint liveness -- can slot order (used to pick the "latest" root) ever invert path order?
  // ==================================================================================================================

  // Two nested Pi binders u, w in one type, read together with the parameter t that was consumed before the type was
  // formed. The roots are {t, u, w}. t was consumed at term level; u, w bound (during checking) afterwards, so both
  // record t as dead-before, and the max-slot root (w) also records it. Rejected.
  test("V9 nested-Pi after consume: t consumed, then read with two fresh binders, not jointly live") {
    rejectsWith[LinearNotJointlyLive](
      observing +
        """
          |def Seen3 (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(C: List(Nat))
          |    (t: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, C)) : Prop := True
          |
          |def bad (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(t: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2))) : Nat := {
          |  let gone := releaseOne(l1(2), s, 2, t)
          |  let T : Prop := (u: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2))) ->
          |    (w: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2))) ->
          |    Seen3(s, List.append(l1(2), l2(2, 2)),
          |      joinToks(Nat, Shares, l1(2), s, l1(2), l2(2, 2), t,
          |        joinToks(Nat, Shares, l1(2), s, l1(2), l1(2), u, w)))
          |  done(l1(2), s, gone, Nat, 0)
          |}
          |""".stripMargin
    )
  }

  // The joint-liveness POSITIVE: two fresh nested Pi binders read together (never consumed) -- sound, must be accepted.
  test("V9 POSITIVE: two fresh nested Pi binders may be read together") {
    accepts(
      observing +
        """
          |def Seen (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(C: List(Nat))
          |    (t: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, C)) : Prop := True
          |
          |def ok (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2))) : Prop :=
          |  (u: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2))) ->
          |  (w: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2))) ->
          |  Seen(s, l2(2, 2), joinToks(Nat, Shares, l1(2), s, l1(2), l1(2), u, w))
          |""".stripMargin
    )
  }

  // ==================================================================================================================
  // Vector 10: a match consumes the scrutinee's root at term level -- does it poison a field held in the branch?
  // Probe for over-rejection: destructure t, then in a proof read a field beside a FRESH Pi binder.
  // ==================================================================================================================

  // Per the model (R7), a field is recomputed from its root, so reading a field of a term-consumed scrutinee together
  // with a fresh binder needs the root live. The match marked t's root dead, so this is rejected. Documented as a
  // conservative (model-faithful) rejection rather than a soundness break: the field's region shares root t, and the
  // model treats it as recomputed from t.
  test("V10 field-after-match: a field of a consumed scrutinee read with a fresh binder (conservative reject)") {
    val src =
      observing +
        """
          |def single (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(a: Nat)(tok: Protocol.Tok(Protocol.Proto.mk(Nat, Shares), l1(2), s, a))
          |    : Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(a)) :=
          |  Protocol.Toks.cons(Protocol.Proto.mk(Nat, Shares), l1(2), s, a, tok, l0, Protocol.Toks.nil(Protocol.Proto.mk(Nat, Shares), l1(2), s))
          |
          |def Seen (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(C: List(Nat))
          |    (t: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, C)) : Prop := True
          |
          |def probe (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(t: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2))) : Nat := {
          |  match t with
          |  | Protocol.Toks.cons a tok C rest => {
          |    let T : Prop := (u: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2))) ->
          |      Seen(s, List.append(l1(a), l1(2)),
          |        joinToks(Nat, Shares, l1(2), s, l1(a), l1(2), single(s, a, tok), u))
          |    done(l1(2), s, single(s, a, tok), Nat, 0)
          |  }
          |}
          |""".stripMargin
    // Record whichever way it goes; both are documented. A plain reject (not an accept) means no break.
    rejects(src)
  }

  // ==================================================================================================================
  // Vector 11: relaxed L3 -- a later field's TYPE reads an earlier linear field twice in one call.
  // ==================================================================================================================

  // A linear family whose second field's type duplicates the first (linear) field in one call. Field types are read
  // extents, so separation applies: LinearReusedInType.
  test("V11 L3-field-type: a field type duplicating an earlier linear field is LinearReusedInType") {
    rejectsWith[LinearReusedInType](
      observing +
        """
          |def seenProp (inst: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(C: List(Nat))
          |    (t: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), inst, C)) : Prop := True
          |
          |inductive Dep (inst: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2))) : Lin(Level.zero)
          | | mk {inst: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2))} (p: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), inst, l1(2)))
          |      (e: seenProp(inst, l2(2, 2),
          |        joinToks(Nat, Shares, l1(2), inst, l1(2), l1(2), p, p))) : Dep(inst)
          |""".stripMargin
    )
  }

  // ==================================================================================================================
  // Vector 12: nested linear family (L9), kids: List(Tree)-style recursion, cannot smuggle a duplicate.
  // ==================================================================================================================

  // A linear tree storing a token and a list of children. Reading a stored token twice in a proof (via two matches of
  // the same tree) overlaps at the tree's root.
  test("V12 nested-family: matching one linear tree twice to read a stored token twice overlaps") {
    rejects(
      observing +
        """
          |inductive Tree : Lin(Level.zero)
          | | leaf (p: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2)))(s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2))) : Tree
          |
          |def forge (tr: Tree) : Nat := {
          |  match tr with
          |  | Tree.leaf p1 s => {
          |    match tr with
          |    | Tree.leaf p2 s2 => {
          |      match Protocol.observe(Protocol.Proto.mk(Nat, Shares), l1(2), s, l2(2, 2),
          |          joinToks(Nat, Shares, l1(2), s, l1(2), l1(2), p1, p2)) with
          |      | Protocol.Observed.mk seen v => done(l1(2), s, releaseTwo(l1(2), s, 2, 2, seen), Nat, 0)
          |    }
          |  }
          |}
          |""".stripMargin
    )
  }

  // ==================================================================================================================
  // Vector 13: conversion -- two proofs unified so a duplicate laundered through type equality.
  // ==================================================================================================================

  // Build a Fact(Le(...)) from an honest observation of halves, and try to coerce it to Fact(Le(4,2)) via an Eq of
  // propositions. The Eq.mp is a proof call; its argument (a Fact carrying a proof) has no linear provenance, and the
  // equation would itself have to be proven. No linear value is duplicated; the attack collapses to needing a false
  // Eq of props, which cannot be produced.
  test("V13 conversion: a Fact cannot be coerced across a false proposition equality") {
    rejects(
      observing +
        """
          |def bad (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(halves: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l2(1, 1)))
          |    (e: Eq(Prop, Le(Nat.add(1, 1), 2), Le(Nat.add(2, 2), 2))) : False := {
          |  let bound : Le(Nat.add(1, 1), 2) := observedBound(s, 1, 1, halves)
          |  let bad2 : Le(Nat.add(2, 2), 2) := Eq.mp(e, bound)
          |  match bad2 returning False with
          |  | Le.mk k eqk => eqFalse(congrArg(eqk, Nat, fun (x: Nat): Nat => Nat.sub(x, 2)))
          |}
          |""".stripMargin
    )
  }

  // ==================================================================================================================
  // Vector 14: an erased constructor binder of linear type is still a tracked occurrence, not a drop channel.
  // ==================================================================================================================

  // An erased linear binder that names no family parameter drops its argument (caught at the ledger).
  test("V14 erased-binder: an erased linear constructor binder drops its token argument") {
    rejects(
      observing +
        """
          |inductive Sink : Type
          | | mk {p: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2))}{s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2))} : Sink
          |
          |def drop (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(t: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2))) : Sink :=
          |  Sink.mk(t, s)
          |""".stripMargin
    )
  }

  // ==================================================================================================================
  // Vector 15: the Fresh / let-pattern destructure keeps the supply's region on its parts.
  // ==================================================================================================================

  // A full honest entry that creates, splits, observes, joins and releases -- must be accepted. This also
  // exercises the `let (next, s, toks) := Protocol.new(...)` destructure, whose fields carry the supply's provenance.
  test("V15 POSITIVE: a full entry round-trip through new/step/observe/release") {
    accepts(
      shares +
        """
          |fun (sup: Protocol.Supply): Nat => {
          |  let (next, s, toks) := Protocol.new(Protocol.Proto.mk(Nat, Shares), l1(2), sup)
          |  let halves := Protocol.step(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2), l2(1, 1), Shares.split(0, 0), toks)
          |  let (seen, valid) := Protocol.observe(Protocol.Proto.mk(Nat, Shares), l1(2), s, l2(1, 1), halves)
          |  let bound : Le(Nat.add(1, 1), 2) := pairBound(2, 1, 1, valid)
          |  let whole := Protocol.step(Protocol.Proto.mk(Nat, Shares), l1(2), s, l2(1, 1), l1(2), Shares.join(1, 1), seen)
          |  match whole with
          |  | Protocol.Toks.cons a t C rest => {
          |    let gone := Protocol.step(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(a), l0, Shares.release(a),
          |      Protocol.Toks.cons(Protocol.Proto.mk(Nat, Shares), l1(2), s, a, t, C, rest))
          |    match gone with
          |    | Protocol.Toks.nil => a
          |  }
          |}
          |""".stripMargin
    )
  }

  // ==================================================================================================================
  // Vector 16: higher-order functions cannot smuggle a duplicate through an unrestricted function argument.
  // ==================================================================================================================

  // A higher-order function `applyTwice` takes a function and a token and applies the function twice -- but it can
  // only type-check if its token parameter is used once. Here the body duplicates `x`, caught in applyTwice itself.
  test("V16 higher-order: a combinator applying its token twice is rejected in its own body") {
    rejects(
      observing +
        """
          |def applyTwice (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))
          |    (f: (a: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2)))
          |        -> (b: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2))) -> Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l2(2, 2)))
          |    (x: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2))) : Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l2(2, 2)) :=
          |  f(x, x)
          |""".stripMargin
    )
  }

  // A combinator that genuinely passes a token to a callback once is fine; feeding it a duplicating callback is still
  // blocked because the callback's body (join(a,a)) is rejected. Positive: the honest combinator checks.
  test("V16 POSITIVE: a combinator passing its token to a callback exactly once checks") {
    accepts(
      observing +
        """
          |def withToken (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))
          |    (f: (a: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2))) -> Nat)
          |    (x: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2))) : Nat := f(x)
          |
          |def useTok (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(t: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2))) : Nat :=
          |  withToken(s, fun (a: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2))): Nat =>
          |    done(l1(2), s, releaseOne(l1(2), s, 2, a), Nat, 0), t)
          |""".stripMargin
    )
  }

  // ==================================================================================================================
  // Vector 17: a type-valued selector reads its struct; using it must not drop/duplicate the stored token.
  // ==================================================================================================================

  // A linear struct storing a token and a Nat index. A selector returning the Nat consumes the struct and drops the
  // linear token (L5), which affine use allows.
  test("V17 selector-drops-token: a data selector of a struct with a linear field is accepted") {
    accepts(
      observing +
        """
          |inductive Held (inst: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2))) : Lin(Level.zero)
          | | mk {inst: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2))} (n: Nat)
          |      (p: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), inst, l1(2))) : Held(inst)
          |
          |def bad (inst: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(h: Held(inst)) : Nat := h.n
          |""".stripMargin
    )
  }

  // ==================================================================================================================
  // Vector 18: refinement rewriting a scrutinee's index does not detach a field's provenance from its root.
  // ==================================================================================================================

  // Eq.subst rewrites t's index from l1(2) to l1(2) (reflexive), binding a fresh local b that still aliases {t}. Then
  // matching b (a let aliasing a call result -> non-exact {t}) and joining a field with t overlaps.
  test("V18 refinement-index: a packet transported to a new index still overlaps its source") {
    rejectsWith[LinearReusedInType](
      observing +
        """
          |def single (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(a: Nat)(tok: Protocol.Tok(Protocol.Proto.mk(Nat, Shares), l1(2), s, a))
          |    : Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(a)) :=
          |  Protocol.Toks.cons(Protocol.Proto.mk(Nat, Shares), l1(2), s, a, tok, l0, Protocol.Toks.nil(Protocol.Proto.mk(Nat, Shares), l1(2), s))
          |
          |def forge (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(t: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2)))
          |    : Le(Nat.add(2, 2), 2) := {
          |  let b := Eq.subst(Eq.refl(l1(2)), Kind.lin, Level.zero,
          |    fun (c: List(Nat)): Lin(Level.zero) => Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, c), t)
          |  match b with
          |  | Protocol.Toks.cons a tok C rest => {
          |    match Protocol.observe(Protocol.Proto.mk(Nat, Shares), l1(2), s, l2(2, 2),
          |        joinToks(Nat, Shares, l1(2), s, l1(2), l1(2), single(s, a, tok), t)) with
          |    | Protocol.Observed.mk seen v => pairBound(2, 2, 2, v)
          |  }
          |}
          |""".stripMargin
    )
  }

  // ==================================================================================================================
  // Vector 19: the argument-order seam -- a call's own joint-liveness uses the call-start env.
  // ==================================================================================================================

  // g's proof argument reads the whole packet append(xs, ys); its two linear args xs, ys are both live at the call
  // start. Must be accepted (R7, documented): the arguments of one application see the locals live at its start.
  test("V19 POSITIVE: g(xs, ys, proof over append(xs,ys)) -- args see the call-start liveness") {
    accepts(
      observing +
        """
          |def Seen (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(C: List(Nat))
          |    (t: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, C)) : Prop := True
          |
          |def joinAndRelease (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))
          |    (a: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(1)))(b: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(1)))
          |    : Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l0) :=
          |  releaseTwo(l1(2), s, 1, 1, joinToks(Nat, Shares, l1(2), s, l1(1), l1(1), a, b))
          |
          |def g (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(a: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(1)))
          |    (b: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(1)))
          |    (h: Seen(s, l2(1, 1), joinToks(Nat, Shares, l1(2), s, l1(1), l1(1), a, b))) : Nat :=
          |  done(l1(2), s, joinAndRelease(s, a, b), Nat, 0)
          |
          |def ok (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(a: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(1)))
          |    (b: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(1))) : Nat :=
          |  g(s, a, b, True.intro)
          |""".stripMargin
    )
  }

  // ==================================================================================================================
  // Over-rejection probe: two provably-disjoint halves from splitToks cannot be combined in ONE read, because the
  // splitToks result is a call (non-exact union {t}), so both halves alias the whole {t} and overlap.
  // Documented in kernel.md as a kept-conservative simplification ("the fields of a constructed value ... overlap"),
  // not a soundness break. Term-level use of each half once is still fine (the halves are tracked separately there).
  // ==================================================================================================================

  test("OVER-REJECTION (conservative, by design): split halves cannot be read together in one call") {
    // This is REJECTED. It is sound to accept (left and right are disjoint halves of t), but the implementation makes
    // the splitToks result non-exact, so the two halves conservatively overlap inside the read.
    rejectsWith[LinearReusedInType](
      observing +
        """
          |def Seen (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(C: List(Nat))
          |    (t: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, C)) : Prop := True
          |
          |def probe (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(halves: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l2(1, 1))) : Nat := {
          |  let (left, right) := splitToks(Nat, Shares, l1(2), s, l1(1), l1(1), halves)
          |  let h : Seen(s, l2(1, 1), joinToks(Nat, Shares, l1(2), s, l1(1), l1(1), left, right)) := True.intro
          |  done(l1(2), s, releaseTwo(l1(2), s, 1, 1, joinToks(Nat, Shares, l1(2), s, l1(1), l1(1), left, right)), Nat, 0)
          |}
          |""".stripMargin
    )
  }

  // Control: the SAME split halves used separately at term level (not combined in one read) check fine.
  test("OVER-REJECTION control: split halves used once each at term level are fine") {
    accepts(
      observing +
        """
          |def probe (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(halves: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l2(1, 1))) : Nat := {
          |  let (left, right) := splitToks(Nat, Shares, l1(2), s, l1(1), l1(1), halves)
          |  done(l1(2), s, releaseTwo(l1(2), s, 1, 1, joinToks(Nat, Shares, l1(2), s, l1(1), l1(1), left, right)), Nat, 0)
          |}
          |""".stripMargin
    )
  }

  // ==================================================================================================================
  // Vector 20: the end-to-end forgery that round 1 fixed, re-expressed through a function boundary, stays blocked.
  // ==================================================================================================================

  // A helper `dupThrough` that takes t and returns join(t, aliasOf(t)) where aliasOf is identity: the body itself
  // duplicates t across the join, caught inside dupThrough (its result is linear, not a read).
  test("V20 end-to-end: a helper that joins a token with its own alias is rejected in its body") {
    rejects(
      observing +
        """
          |def aliasOf (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(t: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2)))
          |    : Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2)) := t
          |
          |def dupThrough (s: Protocol.Inst(Protocol.Proto.mk(Nat, Shares), l1(2)))(t: Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2)))
          |    : Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l2(2, 2)) :=
          |  joinToks(Nat, Shares, l1(2), s, l1(2), l1(2), t, aliasOf(s, t))
          |""".stripMargin
    )
  }
}
