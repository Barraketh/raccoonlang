package com.raccoonlang

import com.raccoonlang.ErrorReporter.Source
import com.raccoonlang.ProgramFixtures.Programs

/**
 * Adversarial review of three soundness-critical changes on `relaxed-separation`: affine use (3b904093), no universe
 * cumulativity (9bbc7ba3) and kinds (ff28aa0e). A test labelled BREAK is a program those commits accepted that
 * duplicates a linear value or derives a false `Valid` /`False` with no user axioms, through a capture under a pattern
 * head that computes; the checker now refuses each (kernel.md, "Type patterns"). A test labelled LIMIT or
 * OVER-REJECTION is a sound program the checker refuses; every other test is a held attack (the checker refuses it) or
 * a sound control (it accepts).
 */
class KindsAttackTests extends munit.FunSuite {
  private val programs = new Programs(Prelude.default, allowUserAxioms = false)
  import programs.runChecked

  private def accepts(src: String)(implicit loc: munit.Location): Unit =
    try { runChecked(src); () }
    catch { case t: TypeError => fail("REJECTED (should accept): " + ErrorReporter.pretty(t, Source(src))) }

  private def rejects(src: String)(implicit loc: munit.Location): TypeError =
    try {
      runChecked(src)
      fail("ACCEPTED (BREAK: should be rejected)")
    } catch {
      case t: TypeError =>
        println(
          s"HELD-BY ${t.getClass.getSimpleName}: ${t.getMessage.linesIterator.nextOption().getOrElse("").take(160)}"
        )
        t
    }

  private def rejectsWith[T <: TypeError](src: String)(implicit ct: reflect.ClassTag[T], loc: munit.Location): T =
    rejects(src) match {
      case ct(e) => e
      case other =>
        fail(s"rejected by ${other.getClass.getSimpleName} (${other.getMessage}), not ${ct.runtimeClass.getSimpleName}")
    }

  /** A BREAK that also runs: fails, with the value the run produced, while the program is accepted. */
  private def refusedNotRun(src: String)(implicit loc: munit.Location): Unit =
    (try Right(runChecked(src))
    catch { case t: TypeError => Left(t) }) match {
      case Right(res) =>
        fail("ACCEPTED (BREAK), and the run gives " + res.map(PrettyPrinter.print).getOrElse("<no value>"))
      case Left(t) => println(s"HELD-BY ${t.getClass.getSimpleName}: ${t.getMessage.take(160)}")
    }

  /** A linear supply pair: two supplies from one is a duplication. */
  private val base =
    ProgramFixtures.lnats + ProgramFixtures.both +
      """
        |def Sup : Lin(Level.zero) := Protocol.Supply
        |""".stripMargin

  // ==================================================================================================================
  // 1. Aliases: a pattern whose head is a function, not a family.
  // ==================================================================================================================

  private val alias =
    base +
      """
        |def SList (A: Sort($u)) : Sort(u) := List(A)
        |
        |def dupS (xs: SList($A)) : List(A) decreases structural(xs) := {
        |  match xs with
        |  | List.nil => List.nil(A)
        |  | List.cons h t => List.cons(h, List.cons(h, dupS(t)))
        |}
        |""".stripMargin

  test("alias-1 a Sort alias of the kind-polymorphic List as a pattern head: its capture is copyable in the body") {
    accepts(alias + "def ok : Nat := List.length(dupS(List.cons(1, List.nil(Nat))))\n")
  }

  test("alias-2 the alias pattern at a linear list: does the call site check the alias's parameter type?") {
    rejects(alias + "def bad (xs: List(Protocol.Supply)) : List(Protocol.Supply) := dupS(xs)\n")
  }

  test("alias-3 BREAK higher-order: a binder pattern headed by a local F, instantiated at the alias") {
    rejects(
      base +
        """
          |def dupF (F: (A: Sort($u)) -> Sort(u))(xs: F($A)) : Prod(F(A), F(A)) := Prod.mk(F(A), F(A), xs, xs)
          |def SList (A: Sort($u)) : Sort(u) := List(A)
          |def bad (xs: List(Protocol.Supply)) : Prod(List(Protocol.Supply), List(Protocol.Supply)) := dupF(SList, xs)
          |""".stripMargin
    )
  }

  test("alias-4 a Sort alias of Prod: destructure and keep both copies of a linear component") {
    rejects(
      base +
        """
          |def SPair (A: Sort($u))(B: Sort($v)) : Sort(Level.max(u, v)) := Prod(A, B)
          |def dupFst (p: SPair($A, $B)) : Prod(A, A) := {
          |  let (a, b) := p
          |  Prod.mk(A, A, a, a)
          |}
          |def bad (s: Protocol.Supply) : Prod(Protocol.Supply, Protocol.Supply) :=
          |  dupFst(Prod.mk(Protocol.Supply, Nat, s, 0))
          |""".stripMargin
    )
  }

  test("alias-5 BREAK run: dupS returns two supplies from the root supply") {
    val src =
      alias +
        """
          |fun (sup: Protocol.Supply): Nat => List.length(dupS(List.cons(sup, List.nil(Protocol.Supply))))
          |""".stripMargin
    refusedNotRun(src)
  }

  /** Shares, its bound lemmas, and packet join, as in RelaxedSeparationAttack2Tests. */
  private val shares =
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
        |def SPair (A: Sort($u))(B: Sort($v)) : Sort(Level.max(u, v)) := Prod(A, B)
        |
        |def dupFst (p: SPair($A, $B)) : Prod(A, A) := {
        |  let (a, b) := p
        |  Prod.mk(A, A, a, a)
        |}
        |
        |""".stripMargin

  test("alias-6 BREAK: a duplicated packet observed whole gives Valid(Shares, [2], [2, 2]) and so Fact(False)") {
    val src =
      shares +
        """
          |fun (sup: Protocol.Supply): Fact(False) => {
          |  let (next, s, toks) := Protocol.new(Protocol.Proto.mk(Nat, Shares), l1(2), sup)
          |  let (t1, t2) := dupFst(Prod.mk(Protocol.Toks(Protocol.Proto.mk(Nat, Shares), l1(2), s, l1(2)), Nat, toks, 0))
          |  let both := joinToks(Nat, Shares, l1(2), s, l1(2), l1(2), t1, t2)
          |  let (seen, v) := Protocol.observe(Protocol.Proto.mk(Nat, Shares), l1(2), s, l2(2, 2), both)
          |  Fact.mk(eqFalse(heldCoverage(2, 2, v)))
          |}
          |""".stripMargin
    refusedNotRun(src)
  }

  test("alias-7 BREAK: the same with an Option alias") {
    rejects(
      base +
        """
          |def SOpt (A: Sort($u)) : Sort(u) := Option(A)
          |def dupO (o: SOpt($A)) : Prod(SOpt(A), SOpt(A)) := Prod.mk(SOpt(A), SOpt(A), o, o)
          |def bad (s: Protocol.Supply) : Prod(Option(Protocol.Supply), Option(Protocol.Supply)) :=
          |  dupO(Option.some(s))
          |""".stripMargin
    )
  }

  test("alias-8 the alias with a constrained capture is checked at the call (control for the fix)") {
    rejects(
      alias +
        """
          |def dupC (xs: SList($A in Sort($u))) : List(A) := List.append(xs, xs)
          |def bad (xs: List(Protocol.Supply)) : List(Protocol.Supply) := dupC(xs)
          |""".stripMargin
    )
  }

  test("alias-9 a level alias: the body assumes a level the argument does not have (no-cumulativity probe)") {
    // Big($A) states A : Sort(1); a List(Nat) gives A := Nat, of Sort(0).
    rejects(
      base +
        """
          |def Big (A: Sort(Level.one)) : Sort(Level.one) := List(A)
          |def big (xs: Big($A)) : Nat := 0
          |def bad : Nat := big(List.nil(Nat))
          |""".stripMargin
    )
  }

  private val wFamily =
    base +
      """
        |def SList (A: Sort($u)) : Sort(u) := List(A)
        |
        |inductive W (A: Univ($k, $u)) : Univ(k, u)
        | | mk (x: SList($A)) : W(A)
        |
        |def noW (w: W(Protocol.Supply)) : False := {
        |  match w returning False with
        |}
        |
        |def mkW (n: Nat) : W(Protocol.Supply) := W.mk(List.nil(Protocol.Supply))
        |
        |def pick (b: Bool)(w: W(Protocol.Supply)) : W(Protocol.Supply) := {
        |  match b returning W(Protocol.Supply) with
        |  | Bool.true => w
        |  | Bool.false => w
        |}
        |""".stripMargin

  // W.mk's capture A has the alias's parameter type Sort(u), so a W(Supply) has no branch (Sort(u) is apart from
  // Lin(0)); but the call site never checks the projected capture against Sort(u), so W.mk(List.nil(Supply)) checks.
  test("alias-9b BREAK (levels): a level alias types Eq.refl(Type) at Eq(Type, Type, Type)") {
    // The same flaw at levels: the body assumes A : Type, and a List(Type) argument instantiates it at A := Type.
    rejects(
      base +
        """
          |def Small (A: Sort(Level.zero)) : Sort(Level.zero) := List(A)
          |def smallRefl (xs: Small($A)) : Eq(Type, A, A) := Eq.refl(A)
          |def bad (n: Nat) : Nat := {
          |  let e := smallRefl(List.nil(Type))
          |  0
          |}
          |""".stripMargin
    )
  }

  test("alias-10 BREAK: W(Supply) is both inhabited and refuted, so a function from Bool to False checks") {
    rejects(wFamily + "def contra (b: Bool) : False := noW(pick(b, mkW(0)))\n")
  }

  test("alias-10b BREAK evidence: applying it is a well-typed term the evaluator cannot reduce") {
    // The checker evaluates applications, so it runs noW on the known W.mk and finds no case for it: today the only
    // refusal is this evaluation failure, UnknownConstructor. A fixed checker refuses W.mk(List.nil(Supply)) instead.
    rejectsWith[TypeMismatch](
      wFamily + "def contra (b: Bool) : False := noW(pick(b, mkW(0)))\ndef boom : False := contra(Bool.true)\n"
    )
  }

  test("alias-10c BREAK: matching any W(A) solves A's kind as copy, so a kind-polymorphic body copies an A") {
    rejects(
      wFamily +
        """
          |def dupW (w: W($A))(x: A) : Prod(A, A) := {
          |  match w returning Prod(A, A) with
          |  | W.mk xs => {
          |    let y := x
          |    Prod.mk(A, A, y, y)
          |  }
          |}
          |def bad (s: Protocol.Supply) : Prod(Protocol.Supply, Protocol.Supply) := dupW(mkW(0), s)
          |""".stripMargin
    )
  }

  test("alias-11 function-type equality: (xs: SList($A)) -> R converts with (xs: List($A)) -> R") {
    rejects(
      alias +
        """
          |def ho (f: (xs: List($A)) -> List(A))(ys: List(Protocol.Supply)) : List(Protocol.Supply) := f(ys)
          |def bad (ys: List(Protocol.Supply)) : List(Protocol.Supply) := ho(dupS, ys)
          |""".stripMargin
    )
  }

  test("alias-12 instance search opens the alias by unification, so it refuses a linear goal (held)") {
    rejectsWith[NoInstanceFound](
      base +
        """
          |def SList (A: Sort($u)) : Sort(u) := List(A)
          |
          |inductive N (A: Univ($k, $u)) : Sort(u)
          | | mk {A: Univ($k, $u)} (n: Nat) : N(A)
          |
          |inductive D (A: Univ($k, $u)) : Sort(u)
          | | mk {A: Univ($k, $u)} (f: (x: A) -> Prod(A, A)) : D(A)
          |
          |def instance nl : N(List(Protocol.Supply)) := N.mk(List(Protocol.Supply), 0)
          |def instance dl [n: N(SList($A))] : D(SList(A)) :=
          |  D.mk(SList(A), fun (x: SList(A)): Prod(SList(A), SList(A)) => Prod.mk(SList(A), SList(A), x, x))
          |def bad (n: Nat) : D(List(Protocol.Supply)) := derive[D(List(Protocol.Supply))]
          |""".stripMargin
    )
  }

  test("alias-0 BREAK minimal: a Sort alias of List as a binder pattern, and List.append(xs, xs) in its body") {
    val src =
      base +
        """
          |def SList (A: Sort($u)) : Sort(u) := List(A)
          |def dup (xs: SList($A)) : List(A) := List.append(xs, xs)
          |fun (sup: Protocol.Supply): Nat => List.length(dup(List.cons(sup, List.nil(Protocol.Supply))))
          |""".stripMargin
    refusedNotRun(src)
  }

  test("alias-13 BREAK: the alias argument order need not match the family's") {
    rejects(
      base +
        """
          |def Swap (A: Sort($u))(B: Sort($v)) : Sort(Level.max(u, v)) := Prod(B, A)
          |def dupSw (p: Swap($A, $B)) : Prod(Prod(B, A), Prod(B, A)) := Prod.mk(Prod(B, A), Prod(B, A), p, p)
          |def bad (p: Prod(Protocol.Supply, Protocol.Supply)) : Nat := {
          |  let q := dupSw(p)
          |  0
          |}
          |""".stripMargin
    )
  }

  // The fix (TypePatternOps.checkOpenedPattern): at each application above a capture, the values opened from the
  // actual type are checked as the head's arguments, and the type they rebuild must convert with the actual type.
  // Aliases still work at well-typed arguments.

  test("alias-14 an alias pattern at a copyable list runs (sound control)") {
    assertEquals(programs.result(alias + "List.length(dupS(List.cons(1, List.cons(2, List.nil(Nat)))))\n"), "4")
  }

  test("alias-15 a Prod alias destructured at copyable components (sound control)") {
    accepts(
      base +
        """
          |def SPair (A: Sort($u))(B: Sort($v)) : Sort(Level.max(u, v)) := Prod(A, B)
          |def dupFst (p: SPair($A, $B)) : Prod(A, A) := {
          |  let (a, b) := p
          |  Prod.mk(A, A, a, a)
          |}
          |def ok : Prod(Nat, Nat) := dupFst(Prod.mk(Nat, Bool, 1, Bool.true))
          |""".stripMargin
    )
  }

  test("alias-16 a pattern headed by a local F, instantiated at the alias and a copyable list (sound control)") {
    accepts(
      base +
        """
          |def dupF (F: (A: Sort($u)) -> Sort(u))(xs: F($A)) : Prod(F(A), F(A)) := Prod.mk(F(A), F(A), xs, xs)
          |def SList (A: Sort($u)) : Sort(u) := List(A)
          |def ok (xs: List(Nat)) : Prod(List(Nat), List(Nat)) := dupF(SList, xs)
          |""".stripMargin
    )
  }

  test("alias-17 a constructor field with an alias pattern, built and matched at a copyable type (sound control)") {
    accepts(
      base +
        """
          |def SList (A: Sort($u)) : Sort(u) := List(A)
          |inductive W (A: Univ($k, $u)) : Univ(k, u)
          | | mk (x: SList($A)) : W(A)
          |
          |def len (w: W(Nat)) : Nat := {
          |  match w returning Nat with
          |  | W.mk xs => List.length(xs)
          |}
          |def ok : Nat := len(W.mk(List.cons(1, List.nil(Nat))))
          |""".stripMargin
    )
  }

  test("alias-18 instance search through an alias head at a copyable goal (sound control)") {
    accepts(
      base +
        """
          |def SList (A: Sort($u)) : Sort(u) := List(A)
          |
          |inductive N (A: Univ($k, $u)) : Sort(u)
          | | mk {A: Univ($k, $u)} (n: Nat) : N(A)
          |
          |inductive D (A: Univ($k, $u)) : Sort(u)
          | | mk {A: Univ($k, $u)} (f: (x: A) -> Prod(A, A)) : D(A)
          |
          |def instance nl : N(List(Nat)) := N.mk(List(Nat), 0)
          |def instance dl [n: N(SList($A))] : D(SList(A)) :=
          |  D.mk(SList(A), fun (x: SList(A)): Prod(SList(A), SList(A)) => Prod.mk(SList(A), SList(A), x, x))
          |def ok (n: Nat) : D(List(Nat)) := derive[D(List(Nat))]
          |""".stripMargin
    )
  }

  test("alias-19 function-type equality between two binders with the same alias head (sound control)") {
    accepts(
      alias +
        """
          |def ho (f: (xs: SList($A)) -> List(A))(ys: List(Nat)) : List(Nat) := f(ys)
          |def ok (ys: List(Nat)) : List(Nat) := ho(dupS, ys)
          |""".stripMargin
    )
  }

  test("alias-20 LIMIT: an alias capture is read by position, so Swap($A, $B) matches only where B is A") {
    // Swap(A, B) is Prod(B, A), and the captures read Prod(Nat, Bool) as A := Nat, B := Bool: Swap(Nat, Bool) is
    // Prod(Bool, Nat), which does not convert, so the sound call is refused.
    rejectsWith[TypeMismatch](
      base +
        """
          |def Swap (A: Sort($u))(B: Sort($v)) : Sort(Level.max(u, v)) := Prod(B, A)
          |def keep (p: Swap($A, $B)) : Prod(B, A) := p
          |def ok : Prod(Nat, Nat) := keep(Prod.mk(Nat, Nat, 1, 2))
          |def no : Prod(Nat, Bool) := keep(Prod.mk(Nat, Bool, 1, Bool.true))
          |""".stripMargin
    )
  }

  test(
    "alias-21 LIMIT: a kind-polymorphic function is not a function of an alias binder, though its eta-expansion is"
  ) {
    // Function types are equal only when each telescope admits the other's generic arguments, and List($A) admits a
    // linear A where SList($A) does not. Without subtyping the function is refused; the eta-expansion checks.
    val defs =
      base +
        """
          |def SList (A: Sort($u)) : Sort(u) := List(A)
          |def keepL (xs: List($A)) : List(A) := xs
          |def ho (f: (xs: SList($A)) -> List(A))(ys: List(Nat)) : List(Nat) := f(ys)
          |""".stripMargin
    rejectsWith[TypeMismatch](defs + "def no (ys: List(Nat)) : List(Nat) := ho(keepL, ys)\n")
    accepts(defs + "def ok (ys: List(Nat)) : List(Nat) := ho(fun (xs: SList($A)): List(A) => keepL(xs), ys)\n")
  }

  test("alias-22 the break predates kinds: a pure-universe alias types Eq.refl(Type) at Eq(Type, Type, Type)") {
    // Only copyable universes: Small($A) lets the body assume A : Type, and a List(Type) variable instantiates
    // A := Type. As alias-9b, at a neutral argument.
    rejectsWith[TypeMismatch](
      base +
        """
          |def Small (A: Sort(Level.zero)) : Sort(Level.zero) := List(A)
          |def smallRefl (xs: Small($A)) : Eq(Type, A, A) := Eq.refl(A)
          |def bad (xs: List(Type)) : Nat := {
          |  let e := smallRefl(xs)
          |  0
          |}
          |""".stripMargin
    )
  }

  test("alias-23 the break predates kinds: cumulativity returns through a Sort(1) alias") {
    // Big($A) lets the body assume A : Sort(1), and a List(Nat) instantiates A := Nat, of Sort(0) only.
    rejectsWith[TypeMismatch](
      base +
        """
          |def Big (A: Sort(Level.one)) : Sort(Level.one) := List(A)
          |def lift (xs: Big($A)) : Eq(Sort(Level.one), A, A) := Eq.refl(A)
          |def bad (xs: List(Nat)) : Nat := {
          |  let e := lift(xs)
          |  0
          |}
          |""".stripMargin
    )
  }

  // ==================================================================================================================
  // 2. Constrained captures.
  // ==================================================================================================================

  private val dupHeads =
    base +
      """
        |def dupHeads (xs: List($A in Sort($u))) : List(A) decreases structural(xs) := {
        |  match xs with
        |  | List.nil => List.nil(A)
        |  | List.cons h t => List.cons(h, List.cons(h, dupHeads(t)))
        |}
        |""".stripMargin

  test("cc-1 higher-order: a callback with a constrained binder applied to a linear list") {
    rejects(
      dupHeads +
        "def ho (f: (xs: List($A in Sort($u))) -> List(A))(ys: List(Protocol.Supply)) : List(Protocol.Supply) := f(ys)\n"
    )
  }

  test("cc-2 function-type equality: dupHeads where an unconstrained binder is expected") {
    rejects(
      dupHeads +
        "def ho (f: (xs: List($A)) -> List(A))(ys: List(Protocol.Supply)) : List(Protocol.Supply) := f(ys)\n" +
        "def bad (ys: List(Protocol.Supply)) : List(Protocol.Supply) := ho(dupHeads, ys)\n"
    )
  }

  test("cc-3 function-type equality: dupHeads where a monomorphic linear binder is expected") {
    rejects(
      dupHeads +
        "def ho (f: (xs: List(Protocol.Supply)) -> List(Protocol.Supply))(ys: List(Protocol.Supply)) : List(Protocol.Supply) := f(ys)\n" +
        "def bad (ys: List(Protocol.Supply)) : List(Protocol.Supply) := ho(dupHeads, ys)\n"
    )
  }

  test("cc-4 nested: List(List($A in Sort($u))) at a list of linear lists") {
    rejects(
      base +
        """
          |def dupInner (xss: List(List($A in Sort($u)))) : Nat := 0
          |def bad (xss: List(List(Protocol.Supply))) : Nat := dupInner(xss)
          |""".stripMargin
    )
  }

  test("cc-5 capture inside a capture: Option($B in List($A in Sort($u)))-style constraint chain") {
    rejects(
      base +
        """
          |def f (o: Option($B in Sort($v))) : Nat := 0
          |def bad (o: Option(List(Protocol.Supply))) : Nat := f(o)
          |""".stripMargin
    )
  }

  test("cc-6 constrained constructor field: a family whose constructor demands copyable contents") {
    // CBox(T) for linear T has no value, so the refinement in its branch is sound; this checks it cannot be built.
    rejects(
      base +
        """
          |inductive CBox (A: Univ($k, $u)) : Univ(k, u)
          | | mk (x: $A in Sort($u)) : CBox(A)
          |
          |def bad (s: Protocol.Supply) : CBox(Protocol.Supply) := CBox.mk(s)
          |""".stripMargin
    )
  }

  test("cc-7 constrained constructor field: refinement in its branch makes an outer value copyable (sound control)") {
    accepts(
      base +
        """
          |inductive CBox (A: Univ($k, $u)) : Univ(k, u)
          | | mk (x: $A in Sort($u)) : CBox(A)
          |
          |def dupWith (c: CBox($A))(y: A) : Nat := {
          |  match c with
          |  | CBox.mk x => 0
          |}
          |""".stripMargin
    )
  }

  test("cc-8 constraint at a type-pattern application inside a binder type") {
    rejects(
      base +
        """
          |def F (xs: List($A in Sort($u))) : Type := Nat
          |def g (xs: List(Protocol.Supply))(n: F(xs)) : Nat := 0
          |""".stripMargin
    )
  }

  // ==================================================================================================================
  // 3. Kind variables.
  // ==================================================================================================================

  test("kv-1 an explicit kind binder: duplicating a value of kind k") {
    rejects(base + "def dup (k: Kind)(A: Univ(k, Level.zero))(x: A) : Prod(A, A) := Prod.mk(A, A, x, x)\n")
  }

  test("kv-2 join(copy, k) is k: a value of that kind is still tracked") {
    rejects(
      base + "def dup (k: Kind)(A: Univ(Kind.join(Kind.copy, k), Level.zero))(x: A) : Prod(A, A) := Prod.mk(A, A, x, x)\n"
    )
  }

  test("kv-3 a kind read from data: Univ(b.k, 0) with b a variable") {
    rejects(
      base +
        """
          |inductive KB : Type
          | | mk (k: Kind) : KB
          |
          |def dup (b: KB)(A: Univ(b.k, Level.zero))(x: A) : Prod(A, A) := Prod.mk(A, A, x, x)
          |""".stripMargin
    )
  }

  test("kv-4 a kind computed by a match on a Bool") {
    rejects(
      base +
        """
          |def K (b: Bool) : Kind := {
          |  match b returning Kind with
          |  | Bool.true => Kind.copy
          |  | Bool.false => Kind.lin
          |}
          |def dup (b: Bool)(A: Univ(K(b), Level.zero))(x: A) : Prod(A, A) := Prod.mk(A, A, x, x)
          |""".stripMargin
    )
  }

  test("kv-5 match on a kind") {
    rejects(base + "def f (k: Kind) : Nat := {\n  match k with\n}\n")
  }

  test("kv-6 Eq(Kind, Kind.lin, Kind.copy) cannot be built") {
    rejects(base + "def e : Eq(Kind, Kind.lin, Kind.copy) := Eq.refl(Kind.lin)\n")
  }

  test("kv-7 Eq(Kind, Kind.join(k, Kind.lin), Kind.copy) cannot be built") {
    rejects(base + "def e (k: Kind) : Eq(Kind, Kind.join(k, Kind.lin), Kind.copy) := Eq.refl(Kind.copy)\n")
  }

  test("kv-8 a kind index decides the family's universe: KI(k) refined by its constructor") {
    // KI(Kind.lin) holds a supply. In the `cp` branch of a KI(k) the kind is copy, which is sound.
    accepts(
      base +
        """
          |inductive KI indices (k: Kind) : Univ(k, Level.zero)
          | | holds (s: Protocol.Supply) : KI(Kind.lin)
          | | cp : KI(Kind.copy)
          |
          |def f (k: Kind)(x: KI(k)) : Nat := {
          |  match x with
          |  | KI.holds s => 0
          |  | KI.cp => 0
          |}
          |""".stripMargin
    )
  }

  test("kv-9 a KI(Kind.lin) built from the copyable constructor") {
    rejects(
      base +
        """
          |inductive KI indices (k: Kind) : Univ(k, Level.zero)
          | | holds (s: Protocol.Supply) : KI(Kind.lin)
          | | cp : KI(Kind.copy)
          |
          |def bad (n: Nat) : KI(Kind.lin) := KI.cp
          |""".stripMargin
    )
  }

  test("kv-10 a KI(Kind.copy) value that holds a supply") {
    rejects(
      base +
        """
          |inductive KI indices (k: Kind) : Univ(k, Level.zero)
          | | holds (s: Protocol.Supply) : KI(Kind.lin)
          | | cp : KI(Kind.copy)
          |
          |def bad (s: Protocol.Supply) : KI(Kind.copy) := KI.holds(s)
          |""".stripMargin
    )
  }

  test("kv-11 a linear-kind family with a copy-kind index constructor storing a supply") {
    rejects(
      base +
        """
          |inductive KJ indices (k: Kind) : Univ(k, Level.zero)
          | | holds (s: Protocol.Supply) : KJ(Kind.copy)
          |""".stripMargin
    )
  }

  test("kv-12 refinement by an equation of universes exports a duplicator only under the equation (sound control)") {
    accepts(
      base +
        """
          |def dupIf (k: Kind)(A: Univ(k, Level.zero))(e: Eq(Sort(Level.one), Univ(k, Level.zero), Type))
          |    : (x: A) -> Prod(A, A) := {
          |  match e returning (x: A) -> Prod(A, A) with
          |  | Eq.refl U => fun (x: A): Prod(A, A) => Prod.mk(A, A, x, x)
          |}
          |""".stripMargin
    )
  }

  test("kv-13 both apartness equations at once are absurd (sound control)") {
    accepts(
      base +
        """
          |def both (k: Kind)(e1: Eq(Sort(Level.one), Univ(k, Level.zero), Type))
          |    (e2: Eq(Sort(Level.one), Univ(k, Level.zero), Lin(Level.zero))) : False := {
          |  match e1 returning False with
          |  | Eq.refl U => {
          |    match e2 returning False with
          |  }
          |}
          |""".stripMargin
    )
  }

  test("kv-14 an equation of a joined kind with copy refines nothing, so no duplication in its branch") {
    rejects(
      base +
        """
          |def dupJ (a: Kind)(b: Kind)(A: Univ(Kind.join(a, b), Level.zero))(e: Eq(Kind, Kind.join(a, b), Kind.copy))(x: A)
          |    : Prod(A, A) := {
          |  match e returning Prod(A, A) with
          |  | Eq.refl j => {
          |    let y := x
          |    Prod.mk(A, A, y, y)
          |  }
          |}
          |""".stripMargin
    )
  }

  test("kv-15 a kind variable equated with lin, then with copy, is absurd (sound control)") {
    accepts(
      base +
        """
          |def bad (k: Kind)(e1: Eq(Kind, k, Kind.lin))(e2: Eq(Kind, k, Kind.copy)) : False := {
          |  match e1 returning False with
          |  | Eq.refl j => {
          |    match e2 returning False with
          |  }
          |}
          |""".stripMargin
    )
  }

  test("kv-16 a captured kind and an explicit kind binder agree by refinement only") {
    rejects(
      base +
        """
          |def f (A: Univ($k, $u))(j: Kind)(x: A)(B: Univ(j, u))(e: Eq(Kind, j, Kind.copy)) : Prod(A, A) := {
          |  match e returning Prod(A, A) with
          |  | Eq.refl z => {
          |    let y := x
          |    Prod.mk(A, A, y, y)
          |  }
          |}
          |""".stripMargin
    )
  }

  test("kv-17 the size rule with a kind variable") {
    rejects(base + "inductive Big (k: Kind)(A: Univ(k, Level.one)) : Univ(k, Level.zero)\n")
  }

  test("kv-18 nominal injectivity of List across kinds: Eq of List(A) and List(Nat) needs A copy") {
    rejects(base + "def f (A: Univ($k, Level.zero))(e: Eq(Univ(k, Level.zero), List(A), List(Nat))) : Nat := 0\n")
  }

  // ==================================================================================================================
  // 4. Families: L1, L2, Sigma, Option, Sum, Subtype.
  // ==================================================================================================================

  test("fam-1 a Sort family with an Option(A) field of variable kind") {
    rejectsWith[LinearFieldInUnrestrictedFamily](
      base + "inductive F (A: Univ($k, $u)) : Sort(u)\n | mk {A: Univ($k, $u)} (x: Option(A)) : F(A)\n"
    )
  }

  test("fam-2 a parameter of variable kind (L2)") {
    rejectsWith[LinearFamilyArgument](base + "inductive F (A: Univ($k, $u))(x: A) : Sort(u)\n")
  }

  test("fam-3 an index of linear type (L2)") {
    rejects(base + "inductive F indices (xs: List(Protocol.Supply)) : Type\n")
  }

  test("fam-4 Sigma with a linear first component: snd then fst is a reuse") {
    rejects(
      base +
        """
          |def NatOf (x: Protocol.Supply) : Type := Nat
          |def bad (s: Sigma(Protocol.Supply, Level.zero, NatOf))
          |    : Prod(Nat, Protocol.Supply) :=
          |  Prod.mk(Nat, Protocol.Supply, s.snd, s.fst)
          |""".stripMargin
    )
  }

  test("fam-5 Subtype over a linear carrier: property is a read, val consumes once (sound control)") {
    accepts(
      base +
        """
          |def One (xs: LNats) : Prop := Eq(Nat, count(xs), 1)
          |def keep (x: Subtype(LNats, One)) : LNats := x.val
          |""".stripMargin
    )
  }

  test("fam-6 Subtype over a linear carrier: val twice") {
    rejects(
      base +
        """
          |def Any (xs: LNats) : Prop := True
          |def bad (x: Subtype(LNats, Any)) : Prod(LNats, LNats) :=
          |  Prod.mk(LNats, LNats, x.val, x.val)
          |""".stripMargin
    )
  }

  test("fam-7 Option.getD at a linear instance: returns one of the two, drops the other (sound control)") {
    accepts(base + "def f (o: Option(LNats))(d: LNats) : Nat := count(Option.getD(o, d))\n")
  }

  test("fam-8 Option at a linear instance: matched twice") {
    rejects(
      base +
        """
          |def bad (o: Option(LNats)) : Nat := {
          |  let a := Option.isSome(o)
          |  let b := Option.isSome(o)
          |  0
          |}
          |""".stripMargin
    )
  }

  test("fam-9 Sum at a linear instance: elim twice") {
    rejects(
      base +
        """
          |def bad (x: Sum(LNats, Nat)) : Nat :=
          |  Nat.add(Sum.elim(x, Nat, count, fun (n: Nat): Nat => n), Sum.elim(x, Nat, count, fun (n: Nat): Nat => n))
          |""".stripMargin
    )
  }

  test("fam-10 Option.map into a copy type from a linear one consumes the option once (sound control)") {
    accepts(base + "def f (o: Option(LNats)) : Option(Nat) := Option.map(o, Nat, count)\n")
  }

  test("fam-11 Prod selectors: fst then snd is a reuse") {
    rejects(base + "def bad (p: Prod(LNats, LNats)) : Nat := Nat.add(count(p.fst), count(p.snd))\n")
  }

  test("fam-12 Prod selectors through a let alias of the pair") {
    rejects(
      base + "def bad (p: Prod(LNats, LNats)) : Nat := {\n  let q := p\n  Nat.add(count(q.fst), count(p.snd))\n}\n"
    )
  }

  test("fam-13 Prod at a copyable and a linear component: fst twice") {
    rejects(base + "def bad (p: Prod(Nat, LNats)) : Nat := Nat.add(p.fst, p.fst)\n")
  }

  test("fam-14 a linear struct with a type field: the type selector is a read (sound control)") {
    accepts(
      base +
        """
          |inductive TP : Lin(Level.one)
          | | mk (T: Type)(s: Protocol.Supply) : TP
          |
          |def f (p: TP) : Prod(Type, Protocol.Supply) := Prod.mk(Type, Protocol.Supply, p.T, p.s)
          |""".stripMargin
    )
  }

  // ==================================================================================================================
  // 5. No cumulativity.
  // ==================================================================================================================

  test("nc-1 a Sort level capture opened on a linear type") {
    rejectsWith[TypeMismatch](
      base + "def sid (A: Sort($u))(x: A) : A := x\ndef bad (xs: LNats) : LNats := sid(LNats, xs)\n"
    )
  }

  test("nc-2 Eq.subst with the copy kind and a linear motive") {
    rejects(
      base +
        """
          |def bad (n: Nat)(e: Eq(Nat, n, 0))(xs: LNats) : LNats :=
          |  Eq.subst(e, Kind.copy, Level.zero, fun (m: Nat): Lin(Level.zero) => LNats, xs)
          |""".stripMargin
    )
  }

  test("nc-3 Eq.subst with the lin kind and a copy motive") {
    rejects(
      base +
        """
          |def bad (n: Nat)(e: Eq(Nat, n, 0)) : Nat :=
          |  Eq.subst(e, Kind.lin, Level.zero, fun (m: Nat): Type => Nat, 3)
          |""".stripMargin
    )
  }

  test("nc-4 Eq.subst with a variable kind and a motive into Univ(k, 0) (sound control)") {
    accepts(
      base +
        """
          |def tr (k: Kind)(A: Univ(k, Level.zero))(n: Nat)(e: Eq(Nat, n, 0))(x: A) : A :=
          |  Eq.subst(e, k, Level.zero, fun (m: Nat): Univ(k, Level.zero) => A, x)
          |""".stripMargin
    )
  }

  test("nc-5 a Lin binder given a copyable type") {
    rejects(base + "def f (A: Lin($u))(x: A) : Nat := 0\ndef bad : Nat := f(Nat, 3)\n")
  }

  test("nc-6 Univ(k, u) binder fixes k from the argument; a Sort result type at it") {
    rejects(base + "def f (A: Univ($k, $u)) : Sort(u) := A\n")
  }

  test("nc-7 an Eq carrier of a kind-polymorphic list") {
    rejects(base + "def f (xs: List($A))(e: Eq(List(A), xs, xs)) : Nat := 0\n")
  }

  test("nc-8 a match motive at Lin given a copyable branch") {
    rejectsWith[TypeMismatch](
      base +
        """
          |def T (b: Bool) : Lin(Level.zero) := {
          |  match b returning Lin(Level.zero) with
          |  | Bool.true => LNats
          |  | Bool.false => Nat
          |}
          |""".stripMargin
    )
  }

  test("nc-9 List.append of a copyable and a linear list") {
    rejectsWith[TypeMismatch](
      base + "def bad (xs: List(Protocol.Supply)) : Nat := List.length(List.append(List.nil(Nat), xs))\n"
    )
  }

  test("nc-10 a packed word of a supply and a Nat") {
    rejects(
      base + "def bad (s: Protocol.Supply) : Nat := List.length(List.cons(s, List.cons(1, List.nil(Nat))))\n"
    )
  }

  test("nc-11 function-type equality: a Lin-universe binder where a Sort one is expected") {
    rejectsWith[TypeMismatch](
      base +
        """
          |def ho (f: (A: Sort($u)) -> Nat) : Nat := f(Nat)
          |def g (A: Lin($u)) : Nat := 0
          |def bad : Nat := ho(g)
          |""".stripMargin
    )
  }

  test("nc-12 a Univ capture opened on Prop") {
    rejects(base + "def f (A: Univ($k, $u)) : Nat := 0\ndef bad : Nat := f(True)\n")
  }

  test("nc-13 a Univ capture with a level successor on a level-zero universe") {
    rejects(base + "def f (A: Univ($k, Level.succ($u))) : Nat := 0\ndef bad : Nat := f(LNats)\n")
  }

  test("fam-15 a family with an explicit kind parameter cannot hold a supply at that kind") {
    rejectsWith[LinearFieldInUnrestrictedFamily](
      base + "inductive G (k: Kind) : Univ(k, Level.zero)\n | mk {k: Kind} (s: Protocol.Supply) : G(k)\n"
    )
  }

  test("fam-16 explicit kind parameters joined in the family universe (sound control)") {
    accepts(
      base +
        """
          |inductive P (k1: Kind)(k2: Kind)(A: Univ(k1, Level.zero))(B: Univ(k2, Level.zero)) : Univ(Kind.join(k1, k2), Level.zero)
          | | mk {k1: Kind}{k2: Kind}{A: Univ(k1, Level.zero)}{B: Univ(k2, Level.zero)} (a: A)(b: B) : P(k1, k2, A, B)
          |
          |def dupP (p: P(Kind.copy, Kind.copy, Nat, Nat)) : Prod(P(Kind.copy, Kind.copy, Nat, Nat), P(Kind.copy, Kind.copy, Nat, Nat)) :=
          |  Prod.mk(P(Kind.copy, Kind.copy, Nat, Nat), P(Kind.copy, Kind.copy, Nat, Nat), p, p)
          |""".stripMargin
    )
  }

  test("fam-17 explicit kind parameters: a value at a join with a variable is tracked") {
    rejectsWith[LinearReused](
      base +
        """
          |inductive P (k1: Kind)(k2: Kind)(A: Univ(k1, Level.zero))(B: Univ(k2, Level.zero)) : Univ(Kind.join(k1, k2), Level.zero)
          | | mk {k1: Kind}{k2: Kind}{A: Univ(k1, Level.zero)}{B: Univ(k2, Level.zero)} (a: A)(b: B) : P(k1, k2, A, B)
          |
          |def dupP (k: Kind)(A: Univ(k, Level.zero))(p: P(Kind.copy, k, Nat, A)) : Prod(P(Kind.copy, k, Nat, A), P(Kind.copy, k, Nat, A)) :=
          |  Prod.mk(P(Kind.copy, k, Nat, A), P(Kind.copy, k, Nat, A), p, p)
          |""".stripMargin
    )
  }

  test("fam-18 Sigma's family cannot return a linear type") {
    rejects(
      base +
        """
          |def SupOf (n: Nat) : Lin(Level.zero) := Protocol.Supply
          |def bad (s: Sigma(Nat, Level.zero, SupOf)) : Nat := 0
          |""".stripMargin
    )
  }

  test("fam-19 a let pattern may drop a linear field with _ (sound control)") {
    accepts(base + "def f (p: Prod(LNats, LNats)) : Nat := {\n  let (a, _) := p\n  count(a)\n}\n")
  }

  test("over-1 Eq(Kind, Kind.copy, Kind.lin) is refuted by an empty match (sound control)") {
    // Different constant kinds are apart as Kind values, as they are as universes.
    accepts(base + "def apartK (e: Eq(Kind, Kind.copy, Kind.lin)) : False := {\n  match e returning False with\n}\n")
  }

  test("over-2 ... though it is refuted through Univ (sound control)") {
    accepts(
      base +
        """
          |def apartK (e: Eq(Kind, Kind.copy, Kind.lin)) : False := {
          |  match congrArg(e, Sort(Level.one), fun (k: Kind): Sort(Level.one) => Univ(k, Level.zero)) returning False with
          |}
          |""".stripMargin
    )
  }

  test("over-3 a kind stored as data cannot index a universe") {
    // OVER-REJECTION (implementation limit): Univ(b.k, 0) is NotAKind, since a universe holds only kind normal forms.
    rejectsWith[NotAKind](
      base +
        """
          |inductive KB : Type
          | | mk (k: Kind) : KB
          |
          |def f (b: KB)(A: Univ(b.k, Level.zero))(x: A) : A := x
          |""".stripMargin
    )
  }

  // ==================================================================================================================
  // 6. Affine use.
  // ==================================================================================================================

  test("aff-1 a reuse after an empty match counts") {
    rejects(
      base +
        """
          |def bad (xs: LNats)(e: Eq(Nat, 0, 1)) : Prod(LNats, LNats) := {
          |  let x := xs
          |  let y := xs
          |  match e returning Prod(LNats, LNats) with
          |}
          |""".stripMargin
    )
  }

  test("aff-2 let patterns: two destructurings of one linear pair") {
    rejects(
      base + "def bad (p: Prod(LNats, LNats)) : Nat := {\n  let (a, b) := p\n  let (c, d) := p\n  count(a)\n}\n"
    )
  }

  test("aff-3 two supplies from one entry supply") {
    rejects(
      base +
        """
          |fun (sup: Protocol.Supply): Nat => {
          |  let p := Both.mk(sup, sup)
          |  0
          |}
          |""".stripMargin
    )
  }

  test("aff-4 Protocol.new twice on one supply") {
    rejectsWith[LinearReused](
      base +
        """
          |def l1 (a: Nat) : List(Nat) := List.cons(a, List.nil(Nat))
          |inductive R indices (consumed: List(Nat))(produced: List(Nat)) : Prop
          |fun (sup: Protocol.Supply): Nat => {
          |  let (n1, s1, t1) := Protocol.new(Protocol.Proto.mk(Nat, R), l1(2), sup)
          |  let (n2, s2, t2) := Protocol.new(Protocol.Proto.mk(Nat, R), l1(2), sup)
          |  0
          |}
          |""".stripMargin
    )
  }

  test("aff-5 the next supply reused") {
    rejectsWith[LinearReused](
      base +
        """
          |def l1 (a: Nat) : List(Nat) := List.cons(a, List.nil(Nat))
          |inductive R indices (consumed: List(Nat))(produced: List(Nat)) : Prop
          |fun (sup: Protocol.Supply): Nat => {
          |  let (n1, s1, t1) := Protocol.new(Protocol.Proto.mk(Nat, R), l1(2), sup)
          |  let (n2, s2, t2) := Protocol.new(Protocol.Proto.mk(Nat, R), l1(2), n1)
          |  let (n3, s3, t3) := Protocol.new(Protocol.Proto.mk(Nat, R), l1(2), n1)
          |  0
          |}
          |""".stripMargin
    )
  }

  test("aff-6 kind-polymorphic keep, used twice at a linear instance through a let") {
    rejects(
      base +
        """
          |def keep (x: $A in Univ($k, $u)) : A := x
          |def bad (s: Protocol.Supply) : Prod(Protocol.Supply, Protocol.Supply) := {
          |  let a := keep(s)
          |  Prod.mk(Protocol.Supply, Protocol.Supply, a, keep(s))
          |}
          |""".stripMargin
    )
  }

  test("aff-7 a known-constructor match keeps both fields of a constructed linear pair once each (sound control)") {
    accepts(
      base +
        """
          |def f (a: LNats)(b: LNats) : Nat := {
          |  match Prod.mk(LNats, LNats, a, b) with
          |  | Prod.mk x y => Nat.add(count(x), count(y))
          |}
          |""".stripMargin
    )
  }

  test("aff-8 a known-constructor match with the field and its source both used") {
    rejects(
      base +
        """
          |def bad (a: LNats)(b: LNats) : Nat := {
          |  match Prod.mk(LNats, LNats, a, b) with
          |  | Prod.mk x y => Nat.add(count(x), count(a))
          |}
          |""".stripMargin
    )
  }

  test("aff-9 a selector through a function value and a direct selector: two uses") {
    rejectsWith[LinearReused](
      base +
        """
          |def bad (p: Prod(LNats, LNats)) : Nat := {
          |  let g := fun (q: Prod(LNats, LNats)): Nat => count(q.fst)
          |  Nat.add(g(p), count(p.snd))
          |}
          |""".stripMargin
    )
  }

  test("aff-10 a refined copy of a tracked local captured by a lambda only under its equation (sound control)") {
    accepts(
      base +
        """
          |def dupper (A: Univ($k, $u))(e: Eq(Kind, k, Kind.copy))(x: A) : (n: Nat) -> A := {
          |  match e returning (n: Nat) -> A with
          |  | Eq.refl j => {
          |    let y := x
          |    fun (n: Nat): A => y
          |  }
          |}
          |""".stripMargin
    )
  }

  test("aff-11 a recursive call given the same linear argument twice") {
    rejectsWith[LinearReused](
      base +
        """
          |def bad (n: Nat)(xs: LNats) : Nat decreases structural(n) := {
          |  match n with
          |  | Nat.zero => count(xs)
          |  | Nat.succ m => Nat.add(bad(m, xs), bad(m, xs))
          |}
          |""".stripMargin
    )
  }

  test("aff-12 S1: a value of variable kind passed twice to one call in a type is LinearReusedInType") {
    rejectsWith[LinearReusedInType](
      base +
        """
          |def two (x: $A in Univ($k, $u))(y: A) : Prop := True
          |def bad (x: $A in Univ($k, $u))(h: two(x, x)) : Nat := 0
          |""".stripMargin
    )
  }

  // ==================================================================================================================
  // 7. Natives at linear lists.
  // ==================================================================================================================

  test("nat-1 List.append(xs, xs) at a linear list") {
    rejects(base + "def bad (xs: List(Protocol.Supply)) : List(Protocol.Supply) := List.append(xs, xs)\n")
  }

  test("nat-2 List.length then reuse") {
    rejects(
      base +
        "def bad (xs: List(Protocol.Supply)) : Prod(Nat, List(Protocol.Supply)) :=\n" +
        "  Prod.mk(Nat, List(Protocol.Supply), List.length(xs), xs)\n"
    )
  }

  test("nat-3 List.length in a type, xs kept (sound control)") {
    accepts(
      base +
        """
          |inductive Tag (n: Nat) : Type
          | | mk {n: Nat} : Tag(n)
          |
          |def f (xs: List(Protocol.Supply))(t: Tag(List.length(xs))) : List(Protocol.Supply) := xs
          |""".stripMargin
    )
  }

  test("nat-4 a word of supplies matched twice") {
    rejects(
      base +
        """
          |def bad (a: Protocol.Supply)(b: Protocol.Supply) : Nat := {
          |  let xs := List.cons(a, List.cons(b, List.nil(Protocol.Supply)))
          |  Nat.add(List.length(xs), List.length(xs))
          |}
          |""".stripMargin
    )
  }

  // ==================================================================================================================
  // 7b. Level-quantified function types as universe values.
  //
  // (u: Level) -> Sort(u) is classified in Sort(succ(u#)), whose level mentions the Pi's own bound variable u#, a
  // dangling fresh variable. This is the classifier on main-clean (f10249b1) too. It is inert: the variable converts
  // with no concrete level, so the type cannot be a value of any universe, only a global's type. There is no Girard
  // path: a level-quantified type cannot be fixed to Sort(1) and passed where an ordinary type is expected.
  // ==================================================================================================================

  test("lvl-1 a level-quantified type is not Type, so it cannot be a type argument") {
    rejectsWith[TypeMismatch](base + "def U : Type := (u: Level) -> Sort(u)\nU\n")
  }

  test("lvl-2 nor Sort(1), nor any fixed level (no Girard entry)") {
    rejectsWith[TypeMismatch](base + "def U : Sort(Level.one) := (u: Level) -> Sort(u)\nU\n")
    rejectsWith[TypeMismatch](base + "def U : Sort(Level.max(Level.one, Level.one)) := (u: Level) -> Sort(u)\nU\n")
  }

  test("lvl-3 it cannot be stored as a constructor field or passed to a Sort capture") {
    rejectsWith[TypeMismatch](
      base + "def U : Type := (u: Level) -> Sort(u)\ndef b : Prod(Type, Nat) := Prod.mk(Type, Nat, U, 0)\n0\n"
    )
    rejectsWith[TypeMismatch](
      base + "def takeTy (A: Sort($w))(x: A) : Nat := 0\ndef U : Type := (u: Level) -> Sort(u)\ntakeTy(U, U)\n"
    )
  }

  test("lvl-4 the level reordered or maxed still dangles") {
    rejectsWith[TypeMismatch](base + "def U : Type := (u: Level) -> (v: Level) -> Sort(Level.max(u, v))\nU\n")
  }

  test("lvl-5 a universe-polymorphic global, whose type is a level-quantified Pi, works (sound control)") {
    accepts(base + "def constTy (u: Level)(A: Sort(u)) : Sort(u) := A\ndef z : Type := constTy(Level.zero, Nat)\nz\n")
    assertEquals(
      programs.result(base + "def constTy (u: Level)(A: Sort(u)) : Sort(u) := A\nconstTy(Level.one, Type)\n"),
      "Type"
    )
  }

  // ==================================================================================================================
  // 8. Globals, instances, indices.
  // ==================================================================================================================

  test("glob-1 a global of a linear List instance") {
    rejects(base + "def g : List(Protocol.Supply) := List.nil(Protocol.Supply)\n")
  }

  test("glob-2 an instance binder of a kind-polymorphic family") {
    rejects(base + "def f (A: Univ($k, $u))[o: Option(A)] : Nat := 0\n")
  }

  test("glob-3 a let instance of a linear list") {
    rejects(base + "def f (xs: List(Protocol.Supply)) : Nat := {\n  let instance i := xs\n  0\n}\n")
  }
}
