package com.raccoonlang

import com.raccoonlang.ErrorReporter.Source
import com.raccoonlang.ProgramFixtures.Programs

/**
 * Adversarial programs against linear types (docs/kernel.md, "Linear types"). Every test asserts that the checker
 * rejects a program that would duplicate or forge a linear value, or let one escape a type or a proof. A test that
 * fails with "ACCEPTED" is a break. Use is affine, so the programs that only drop a linear value are accepted controls.
 */
class LinearEscapeTests extends munit.FunSuite {
  private val programs = new Programs(Prelude.default, allowUserAxioms = true)

  /** The program is rejected; returns a short description of why, which the log shows. */
  private def rejects(src: String)(implicit loc: munit.Location): String = {
    val outcome =
      try {
        programs.runChecked(src)
        None
      } catch {
        case t: TypeError => Some(s"${t.getClass.getSimpleName}: ${ErrorReporter.pretty(t, Source(src)).take(400)}")
      }
    outcome match {
      case None => fail("ACCEPTED: the checker accepted a program that breaks linearity")
      case Some(why) =>
        println(s"[${loc.line}] rejected by $why".replace('\n', ' '))
        why
    }
  }

  /** The program is rejected with `T`, the error the rule names. */
  private def rejectsWith[T <: TypeError](src: String)(implicit loc: munit.Location, ct: reflect.ClassTag[T]): Unit = {
    val why = rejects(src)
    assert(why.startsWith(ct.runtimeClass.getSimpleName + ":"), s"rejected for another reason: $why")
  }

  /** The program checks; for positive controls that show an attack's variant is otherwise well-formed. */
  private def accepts(src: String)(implicit loc: munit.Location): Unit = programs.run(src)

  /** The source does not parse. */
  private def unparsable(src: String)(implicit loc: munit.Location): Unit =
    assert(LanguageParser.parseProgram(src).isInstanceOf[Failure], "the program parses")

  private val lib =
    ProgramFixtures.lnats +
      """
        |inductive LPair (A: Lin($u))(B: Lin($v)) : Lin(Level.max(u, v))
        | | mk (fst: $A in Lin($u))(snd: $B in Lin($v)) : LPair(A, B)
        |
        |inductive LVec (A: Sort($u)) indices (n: Nat) : Lin(u)
        | | nil {A: Sort($u)} : LVec(A, 0)
        | | cons (n: Nat)(head: $A in Sort($u))(tail: LVec(A, n)) : LVec(A, Nat.succ(n))
        |
        |inductive LUnit : Lin(Level.zero)
        | | unit : LUnit
        |
        |inductive Held : Lin(Level.zero)
        | | mk (fst: LNats)(snd: Nat) : Held
        |
        |inductive Tag indices (n: Nat) : Type
        | | mk (n: Nat) : Tag(n)
        |
        |inductive Box (A: Type) : Type
        | | mk {A: Type} (val: A) : Box(A)
        |
        |def lid (x: $A in Lin($u)) : A := x
        |
        |def one : Nat := count(LNats.cons(7, LNats.nil))
        |""".stripMargin

  // ------------ Erased constructor binders ------------

  test("an erased constructor binder of linear type that names no parameter drops its argument") {
    rejects(
      lib +
        """
          |inductive Sink : Type
          | | mk {xs: LNats} : Sink
          |
          |def drop (xs: LNats) : Sink := Sink.mk(xs)
          |""".stripMargin
    )
  }

  test("an erased linear binder in a linear family drops its argument") {
    rejects(
      lib +
        """
          |inductive LSink : Lin(Level.zero)
          | | mk {xs: LNats} (n: Nat) : LSink
          |
          |def drop (xs: LNats) : Nat := {
          |  match LSink.mk(xs, 3) with
          |  | LSink.mk n => n
          |}
          |""".stripMargin
    )
  }

  test("an erased linear binder used in the program body drops a linear value") {
    rejects(
      lib +
        """
          |inductive Sink : Type
          | | mk {xs: LNats} : Sink
          |
          |{
          |  let s := Sink.mk(LNats.cons(1, LNats.nil))
          |  0
          |}
          |""".stripMargin
    )
  }

  test("def binders cannot be erased: {xs: LNats} in a def header") {
    unparsable(lib + "def f {xs: LNats} : Nat := count(xs)\n")
  }

  // ------------ Axioms (S3) ------------

  // A documented S3 limit (docs/kernel.md, S3): the lint does not see a stuck codomain, here `F(n)`, which computes to a
  // minting function type. Applying the axiom's stuck result now yields a stuck application (KERNEL_FOLLOWUPS 1.3), so
  // only `--no-user-axioms`, which protocol soundness rests on, refuses the program.
  test("S3: an axiom whose codomain computes to a function type into a linear family is refused only as a user axiom") {
    val noAxioms = new Programs(Prelude.default, allowUserAxioms = false)
    intercept[UserAxiom](
      noAxioms.runChecked(
        lib +
          """
            |def F (n: Nat) : Type := {
            |  match n returning Type with
            |  | Nat.zero => (m: Nat) -> LNats
            |  | Nat.succ k => Nat
            |}
            |
            |axiom forge (n: Nat) : F(n)
            |
            |def made : Nat := {
            |  let f := forge(0)
            |  count(f(5))
            |}
            |""".stripMargin
      )
    )
  }

  test("S3 positive control: an axiom of a plain function type into a linear family is LinearAxiom") {
    rejectsWith[LinearAxiom](lib + "axiom forge : Nat -> LNats\n")
  }

  // ------------ Function types and universes ------------

  test("a Type-polymorphic duplicator does not pass where a Lin-polymorphic function is expected") {
    rejects(
      lib +
        """
          |def dupT (A: Type)(x: A) : Prod(A, A) := Prod.mk(A, A, x, x)
          |
          |def dupC (A: Type) : (x: A) -> Prod(A, A) := fun (x: A): Prod(A, A) => Prod.mk(A, A, x, x)
          |
          |def apply2 (f: (A: Lin(Level.zero)) -> (x: A) -> LPair(A, A))(xs: LNats) : LPair(LNats, LNats) := {
          |  let g := f(LNats)
          |  g(xs)
          |}
          |
          |def bad (xs: LNats) : LPair(LNats, LNats) := apply2(dupC, xs)
          |""".stripMargin
    )
  }

  test("a Sort-capture duplicator does not pass where a Lin-capture function is expected") {
    rejects(
      lib +
        """
          |def dupS (x: $A in Sort($u)) : Prod(A, A) := Prod.mk(A, A, x, x)
          |
          |def apply1 (f: (x: $A in Lin($u)) -> LPair(A, A))(xs: LNats) : LPair(LNats, LNats) := f(xs)
          |
          |def bad (xs: LNats) : LPair(LNats, LNats) := apply1(dupS, xs)
          |""".stripMargin
    )
  }

  test("a linear value does not pass where a Type-polymorphic argument is expected") {
    rejects(
      lib + "def dupT (A: Type)(x: A) : Prod(A, A) := Prod.mk(A, A, x, x)\n" +
        "def bad (xs: LNats) : Nat := {\n  let (a, b) := dupT(LNats, xs)\n  Nat.add(count(a), count(b))\n}\n"
    )
  }

  test("a linear value does not pass to prelude id, const or Bool.cond") {
    rejects(lib + "def bad (xs: LNats) : Nat := count(id(xs))\n")
    rejects(lib + "def bad (xs: LNats) : Nat := count(const(xs, 0))\n")
    rejects(lib + "def bad (xs: LNats)(ys: LNats) : Nat := count(Bool.cond(Bool.true, LNats, xs, ys))\n")
  }

  test("a level-polymorphic Sort duplicator does not take a linear type") {
    rejects(
      lib + "def dupS (u: Level)(A: Sort(u))(x: A) : Prod(A, A) := Prod.mk(A, A, x, x)\n" +
        "def bad (xs: LNats) : Nat := {\n  let (a, b) := dupS(Level.zero, LNats, xs)\n  Nat.add(count(a), count(b))\n}\n"
    )
  }

  test("partial application of a two-argument function to a linear value") {
    rejects(
      lib + "def f (xs: LNats)(n: Nat) : Nat := Nat.add(n, count(xs))\n" +
        "def bad (xs: LNats) : Nat := {\n  let g := f(xs)\n  Nat.add(g(1), g(2))\n}\n"
    )
  }

  test("a lambda in a match branch capturing a linear field") {
    rejectsWith[LinearCapture](
      lib +
        """
          |def bad (p: Held) : Nat := {
          |  match p with
          |  | Held.mk a k => {
          |    let f := fun (n: Nat): Nat => Nat.add(n, count(a))
          |    Nat.add(f(k), f(k))
          |  }
          |}
          |""".stripMargin
    )
  }

  test("a lambda returning a linear value built from a captured one") {
    rejectsWith[LinearCapture](
      lib + "def bad (xs: LNats) : Nat := {\n  let f := fun (n: Nat): LNats => LNats.cons(n, xs)\n  Nat.add(count(f(1)), count(f(2)))\n}\n"
    )
  }

  test("a lambda passed as an argument capturing a linear local") {
    rejectsWith[LinearCapture](
      lib +
        "def twice (f: Nat -> Nat) : Nat := Nat.add(f(0), f(0))\n" +
        "def bad (xs: LNats) : Nat := twice(fun (n: Nat): Nat => count(xs))\n"
    )
  }

  test("a linear let captured only by a lambda that is never called") {
    rejects(
      lib + "def bad (xs: LNats) : Nat := {\n  let ys := xs\n  let f := fun (n: Nat): Nat => count(ys)\n  0\n}\n"
    )
  }

  // ------------ Lets ------------

  test("a linear let used zero times and only in an annotation is dropped; twice is LinearReused") {
    accepts(lib + "def bad (xs: LNats) : Nat := {\n  let ys := xs\n  0\n}\n")
    rejectsWith[LinearReused](
      lib + "def bad (xs: LNats) : Nat := {\n  let ys := xs\n  Nat.add(count(ys), count(ys))\n}\n"
    )
    // An annotation only reads ys, which is then dropped (reads consume nothing).
    accepts(
      lib +
        "def bad (xs: LNats) : Nat := {\n  let ys := xs\n  let e : Eq(Nat, count(ys), count(ys)) := Eq.refl(count(ys))\n  0\n}\n"
    )
  }

  test("a let annotated with a copyable type but bound to a linear value") {
    rejects(lib + "def bad (xs: LNats) : Nat := {\n  let ys : Nat := xs\n  Nat.add(ys, ys)\n}\n")
  }

  // ------------ Matches ------------

  test("a match on a non-variable linear term whose branch drops a field is accepted") {
    accepts(
      lib + "def bad (xs: LNats) : Nat := {\n  match List.cons(LNats.cons(1, LNats.nil), List.nil(LNats)) with\n  | List.cons h t => count(xs)\n}\n"
    )
  }

  test("a known-constructor match whose branch reuses the original local") {
    rejectsWith[LinearReused](
      lib + "def bad (xs: LNats) : Nat := {\n  match Held.mk(xs, 0) with\n  | Held.mk a k => Nat.add(count(a), count(xs))\n}\n"
    )
  }

  test("a match whose scrutinee is a let bound to a constructor and which then reuses a field source") {
    rejectsWith[LinearReused](
      lib + "def bad (xs: LNats) : Nat := {\n  let p := Held.mk(xs, 1)\n  let (a, k) := p\n  Nat.add(count(a), count(xs))\n}\n"
    )
  }

  test("matching the same value twice through its refinement") {
    rejectsWith[LinearReused](
      lib +
        """
          |def bad (xs: LNats) : Nat := {
          |  match xs with
          |  | LNats.nil => 0
          |  | LNats.cons h t => {
          |    match xs with
          |    | LNats.cons h2 t2 => Nat.add(count(t), count(t2))
          |  }
          |}
          |""".stripMargin
    )
  }

  // A motive may read a linear field (L4, R1): sound, since each read is a hypothetical run that consumes nothing. A
  // field that is only read may be dropped.
  test("a returning motive that mentions a linear field") {
    val reads =
      lib +
        """
          |def bad (p: LPair(LNats, LNats)) : Nat := {
          |  match p with
          |  | LPair.mk a b => {
          |    let e := match b returning Eq(Nat, count(a), count(a)) with
          |    | LNats.nil => Eq.refl(count(a))
          |    | LNats.cons h t => Eq.refl(count(a))
          |    CONSUME
          |  }
          |}
          |""".stripMargin
    accepts(reads.replace("CONSUME", "count(b)"))
    accepts(reads.replace("CONSUME", "Nat.add(count(a), count(b))"))
  }

  // Universes whose kinds are different constants are apart (N3), so this match is absurd, and sound: no equation
  // relates a copyable type to a linear one.
  test("an absurd match on an equation of Sort and Lin universes is accepted") {
    accepts(
      lib + "def ok (h: Eq(Sort(Level.one), Type, Lin(Level.zero)))(xs: LNats) : Nat := False.elim(match h returning False with\n, Nat)\n"
    )
  }

  test("an absurd match that is not absurd: two Lin levels") {
    rejects(
      lib + "def bad (h: Eq(Sort(Level.succ(Level.one)), Lin(Level.zero), Lin(Level.one)))(xs: LNats) : Nat := False.elim(match h returning False with\n, Nat)\n"
    )
  }

  test("an absurd match on an inhabited linear family") {
    rejects(lib + "def bad (v: LVec(Nat, 0))(xs: LNats) : Nat := {\n  match v returning Nat with\n}\n")
  }

  test("an inferred motive naming a linear field") {
    rejects(
      lib +
        """
          |def bad (p: Held) : Nat := {
          |  match p with
          |  | Held.mk a k => {
          |    let t := match Bool.true with
          |    | Bool.true => Tag.mk(count(a))
          |    0
          |  }
          |}
          |""".stripMargin
    )
  }

  // R5: a proof may run a closed linear computation, here matching a constructor it builds; it has no linear input, and
  // a read extent may drop what it creates.
  test("a proof by match on a linear value") {
    accepts(
      lib +
        """
          |def ok (xs: LNats) : Nat := {
          |  let h := match LUnit.unit returning True with
          |  | LUnit.unit => True.intro
          |  count(xs)
          |}
          |""".stripMargin
    )
  }

  // ------------ Recursion ------------

  test("recursion may drop the accumulator, but not pass the tail twice") {
    accepts(
      lib +
        """
          |def bad (xs: LNats)(acc: LNats) : Nat decreases structural(xs) := {
          |  match xs with
          |  | LNats.nil => 0
          |  | LNats.cons h t => bad(t, acc)
          |}
          |""".stripMargin
    )
    rejectsWith[LinearReused](
      lib +
        """
          |def bad (xs: LNats)(acc: LNats) : Nat decreases structural(xs) := {
          |  match xs with
          |  | LNats.nil => count(acc)
          |  | LNats.cons h t => bad(t, t)
          |}
          |""".stripMargin
    )
  }

  test("a lexicographic clause over a linear parameter is not a use") {
    accepts(
      lib + "def bad (xs: LNats)(n: Nat) : Nat decreases lexicographic(xs, n) := n\n"
    )
  }

  // ------------ Globals ------------

  test("a linear global via a type alias and via a stuck type") {
    rejectsWith[LinearGlobal](lib + "def T : Lin(Level.zero) := LNats\ndef bad : T := LNats.nil\n")
    rejectsWith[LinearGlobal](
      lib + "def F (n: Nat) : Lin(Level.zero) := LNats\ndef bad : F(0) := LNats.nil\n"
    )
  }

  test("a linear instance global") {
    rejects(lib + "def instance bad : LNats := LNats.nil\n")
  }

  test("a program result of a linear family whose values are copyable") {
    rejectsWith[LinearGlobal](lib + "\nLNats.cons(1, LNats.nil)\n")
  }

  // ------------ Types and proofs ------------

  // R3: a binder type may read an earlier linear binder, consumed afterwards or not.
  test("a linear value inside a binder type, a struct field type and a family index") {
    accepts(lib + "def bad (xs: LNats)(t: Tag(count(xs))) : Nat := 0\n")
    accepts(lib + "def ok (xs: LNats)(t: Tag(count(xs))) : Nat := count(xs)\n")
  }

  // R5: a closed linear computation in a type mints from no linear input and consumes what it mints.
  test("S1: a closed linear subterm inside a constructor field's binder-type pattern is a read (R5)") {
    accepts(lib + "inductive Ok : Type\n | mk (t: Tag(count(LNats.nil))) : Ok\n")
  }

  // Lambdas in binder types do not parse (KERNEL_FOLLOWUPS 2.8); a lambda with a linear parameter in a type is allowed.
  test("a lambda inside a binder-type pattern does not parse") {
    unparsable(
      lib +
        "def apply (f: (xs: LNats) -> Nat) : Type := Nat\n" +
        "def bad (x: apply(fun (ys: LNats): Nat => count(ys))) : Nat := 0\n"
    )
  }

  // Sound under R4 (DESIGN.md §6): a proposition over a linear domain is `∀ x, Adm x → P x`. Applying such a function is a
  // proof, so its linear arguments are only read.
  test("a Prop function with a linear domain, curried, is a proposition (R4)") {
    accepts(lib + "def P : Prop := (xs: LNats) -> (n: Nat) -> Eq(Nat, n, n)\n")
    accepts(lib + "def P (A: Lin(Level.zero)) : Prop := (x: A) -> True\n")
  }

  // ------------ Instances ------------

  test("an instance binder whose type pattern resolves to a linear type") {
    rejectsWith[LinearInstance](lib + "def bad [p: LPair($A, $B)] : Nat := 0\n")
  }

  test("a linear derive result") {
    rejects(
      lib +
        "def instance mk [n: Nat] : Held := Held.mk(LNats.nil, n)\n" +
        "def instance five : Nat := 5\n" +
        "def bad : Nat := {\n  let p := derive[Held]\n  let (a, b) := p\n  Nat.add(b, b)\n}\n"
    )
  }

  // ------------ Type-pattern captures ------------

  test("a capture of a linear parameter through a Lin-capture binder of a type-valued function") {
    rejectsWith[LinearInType](
      lib +
        "def G (x: $A in Lin($u))(h: False) : Type := {\n  match h returning Type with\n}\n" +
        "def bad (y: G($x, $h)) : Nat := 0\n"
    )
  }

  test("a capture of a linear parameter nested inside another pattern") {
    rejectsWith[LinearInType](
      lib +
        "def G (xs: LNats)(h: False) : Type := {\n  match h returning Type with\n}\n" +
        "def bad (y: Box(G($xs, $h))) : Nat := 0\n"
    )
  }

  // ------------ Batch 2: reads in binder-type patterns ------------

  // Formerly S1 negatives. Each is a read (R1, R5): a closed linear computation, or one over an unrestricted local, has
  // no linear input, so it is a hypothetical run from the empty tuple, whose admissibility holds; it consumes what it
  // mints. The same reads in let annotations and codomains are accepted alike.
  test("closed linear subterms in every kind of binder-type pattern are reads (R5)") {
    accepts(lib + "def ok (t: Tag(count(LNats.nil))) : Nat := 0\n")
    accepts(lib + "def ok (n: Nat)(t: Tag(count(LNats.cons(n, LNats.nil)))) : Nat := n\n")
    accepts(lib + "def ok (h: Eq(Nat, count(LNats.nil), 0)) : Nat := 0\n")
    accepts(lib + "def ok : Nat := {\n  let f := fun (t: Tag(count(LNats.nil))): Nat => 0\n  0\n}\n")
    accepts(lib + "def T : Type := (t: Tag(count(LNats.nil))) -> Nat\n")
    accepts(lib + "def ok [t: Tag(count(LNats.nil))] : Nat := 0\n")
    accepts(lib + "inductive Ok : Lin(Level.zero)\n | mk (t: Tag(count(LNats.nil)))(xs: LNats) : Ok\n")
    accepts(lib + "def ok : Nat := {\n  let t : Tag(count(LNats.nil)) := Tag.mk(0)\n  0\n}\n")
    accepts(lib + "def ok (n: Nat) : Tag(count(LNats.nil)) := Tag.mk(0)\n")
  }

  // The duplication these controls stood near is still rejected: one call reading a local twice.
  test("one call reading a linear local twice in a binder-type pattern") {
    val pc =
      "def pc (p: LPair(LNats, LNats)) : Nat := {\n  let (a, b) := p\n  Nat.add(count(a), count(b))\n}\n"
    rejectsWith[LinearReusedInType](
      lib + pc + "def bad (xs: LNats)(t: Tag(pc(LPair.mk(xs, xs)))) : Nat := count(xs)\n"
    )
    rejectsWith[LinearReusedInType](
      lib + pc + "def bad (xs: LNats)(t: Tag(pc(LPair.mk(lid(xs), xs)))) : Nat := count(xs)\n"
    )
    // An unrestricted value computed from xs copies freely: count(xs) and xs are separate inputs.
    accepts(lib + "def ok (xs: LNats)(t: Tag(count(LNats.cons(count(xs), xs)))) : Nat := count(xs)\n")
  }

  // ------------ Batch 2: families and fields ------------

  test("L1: a Sort struct whose field's type is an earlier Lin(0) field") {
    rejectsWith[LinearFieldInUnrestrictedFamily](
      lib + "inductive Pkg : Sort(Level.one)\n | mk (T: Lin(Level.zero))(x: T) : Pkg\n"
    )
  }

  test("L1: a Sort or Prop family with a field at a Lin-polymorphic parameter") {
    rejectsWith[LinearFieldInUnrestrictedFamily](
      lib + "inductive SBox (A: Lin($u)) : Sort(u)\n | mk (a: $A in Lin($u)) : SBox(A)\n"
    )
    rejectsWith[LinearFieldInUnrestrictedFamily](
      lib + "inductive PBox (A: Lin($u)) : Prop\n | mk (a: $A in Lin($u)) : PBox(A)\n"
    )
  }

  // L3 relaxed with S1: a field type or a result index may read an earlier linear field, as a hypothetical run over the
  // field's carrier. Constructing one still needs the field type's value without a second consumption.
  test("L3: a linear field whose type mentions an earlier linear field, and a result index computed from one") {
    // A field type may be a stuck match on an earlier linear field, which positivity accepts (KERNEL_FOLLOWUPS 2.2).
    accepts(
      lib + "def F (xs: LNats) : Type := Nat\n\ninductive Dep : Lin(Level.zero)\n | mk (xs: LNats)(t: F(xs)) : Dep\n"
    )
    accepts(
      lib +
        "def G (xs: LNats) : Type := {\n  match xs returning Type with\n  | LNats.nil => Nat\n  | LNats.cons h t => Bool\n}\n\n" +
        "inductive Dep2 : Lin(Level.zero)\n | mk (xs: LNats)(t: G(xs)) : Dep2\n"
    )
    accepts(lib + "inductive Idx indices (n: Nat) : Lin(Level.zero)\n | mk (xs: LNats) : Idx(count(xs))\n")
  }

  test("an erased binder that names a parameter is checked as the parameter, with no extra linear binder") {
    rejects(
      lib +
        "inductive Sink (n: Nat) : Type\n | mk {n: Nat}{xs: LNats} : Sink(n)\n\n" +
        "def drop (xs: LNats) : Sink(0) := Sink.mk(0, xs)\n"
    )
  }

  test("L5: an LPair selector consumes the pair and drops the other field, but a second selector is LinearReused") {
    accepts(lib + "def bad (p: Held) : Nat := count(p.fst)\n")
    accepts(lib + "def bad (p: Held) : Nat := p.snd\n")
    accepts(lib + "def bad (xs: LNats) : Nat := count(LPair.mk(xs, LNats.nil).fst)\n")
    rejectsWith[LinearReused](
      lib + "def bad (p: LPair(LNats, LNats)) : Nat := Nat.add(count(p.fst), count(p.snd))\n"
    )
  }

  test("an existential linear package whose type field is copied into a binder type") {
    // Pk.T reads p in y's binder type and drops the linear field x there.
    accepts(
      lib +
        """
          |inductive Pk : Lin(Level.one)
          | | mk (T: Lin(Level.zero))(x: T) : Pk
          |
          |def bad (p: Pk)(y: (Pk.T(p))) : Nat := 0
          |""".stripMargin
    )
  }

  test("an existential linear package whose payload is dropped is accepted") {
    accepts(
      lib +
        """
          |inductive Pk : Lin(Level.one)
          | | mk (T: Lin(Level.zero))(x: T) : Pk
          |
          |def bad (p: Pk) : Nat := {
          |  match p with
          |  | Pk.mk T x => 0
          |}
          |""".stripMargin
    )
  }

  // ------------ Batch 2: shadowing and binder names ------------

  test("a let that shadows a linear parameter drops the parameter") {
    accepts(lib + "def bad (xs: LNats) : Nat := {\n  let xs := LNats.nil\n  count(xs)\n}\n")
  }

  test("a match field that shadows a linear parameter drops the parameter") {
    accepts(
      lib + "def bad (xs: LNats)(p: Held) : Nat := {\n  match p with\n  | Held.mk xs k => count(xs)\n}\n"
    )
  }

  test("a let pattern that shadows a linear parameter and reuses it on the right") {
    rejectsWith[LinearReused](
      lib + "def bad (xs: LNats) : Nat := {\n  let (xs, n) := Held.mk(xs, count(xs))\n  count(xs)\n}\n"
    )
  }

  test("a lambda parameter that shadows a linear local drops the outer one") {
    accepts(
      lib + "def bad (xs: LNats) : Nat := {\n  let f := fun (xs: LNats): Nat => count(xs)\n  0\n}\n"
    )
  }

  // ------------ Batch 2: lambdas with linear parameters ------------

  test("a lambda may drop its linear parameter, but not duplicate it") {
    accepts(
      lib + "def bad : Nat := {\n  let f := fun (xs: LNats): Nat => 0\n  f(LNats.nil)\n}\n"
    )
    rejectsWith[LinearReused](
      lib + "def bad : Nat := {\n  let f := fun (xs: LNats): Nat => Nat.add(count(xs), count(xs))\n  f(LNats.nil)\n}\n"
    )
  }

  test("a curried lambda whose inner lambda captures the outer linear parameter") {
    rejectsWith[LinearCapture](
      lib + "def bad : Nat := {\n  let f := fun (xs: LNats): (n: Nat) -> Nat => fun (n: Nat): Nat => count(xs)\n  0\n}\n"
    )
  }

  // ------------ Batch 2: proofs ------------

  // A proof may match a linear parameter, reading it; the parameter may then be dropped or consumed.
  test("a proof by match on a linear parameter") {
    val proof =
      "def bad (u: LUnit) : Nat := {\n  let h := match u returning True with\n  | LUnit.unit => True.intro\n  BODY\n}\n"
    accepts(lib + proof.replace("BODY", "0"))
    accepts(lib + proof.replace("BODY", "{\n    match u with\n    | LUnit.unit => 0\n  }"))
  }

  test("an Eq whose carrier is a function type into a linear family does not let its values be compared") {
    rejects(
      lib +
        "def bad (f: Nat -> LNats)(g: Nat -> LNats)(p: Eq(Nat -> LNats, f, g)) : Prop := Eq(LNats, f(0), g(0))\n"
    )
  }

  // ------------ Batch 2: universe level captures ------------

  test("a user alias for Lin used as a capture constraint does not open on a linear type") {
    rejects(
      lib +
        "def L (u: Level) : Sort(Level.succ(u)) := Lin(u)\n" +
        "def useL (x: $A in L($u)) : A := x\n" +
        "def bad (xs: LNats) : Nat := count(useL(xs))\n"
    )
  }

  test("a Sort-alias capture function does not pass where a Lin-alias capture function is expected") {
    rejects(
      lib +
        "def L (u: Level) : Sort(Level.succ(u)) := Lin(u)\n" +
        "def S (u: Level) : Sort(Level.succ(u)) := Sort(u)\n" +
        "def dupS (x: $A in S($u)) : Prod(A, A) := Prod.mk(A, A, x, x)\n" +
        "def apply1 (f: (x: $A in L($u)) -> LPair(A, A))(xs: LNats) : LPair(LNats, LNats) := f(xs)\n" +
        "def bad (xs: LNats) : LPair(LNats, LNats) := apply1(dupS, xs)\n"
    )
  }

  test("Lin cannot be redeclared, in the root or shadowing it in a namespace pattern") {
    rejects(lib + "def Lin (l: Level) : Type := Nat\n")
  }

  test("a namespace-local Lin alias for Sort does not turn a Lin pattern into a Sort pattern for a linear argument") {
    rejects(
      lib +
        """
          |namespace Foo {
          |  def Lin (l: Level) : Sort(Level.succ(l)) := Sort(l)
          |  def dup (x: $A in Lin($u)) : Prod(A, A) := Prod.mk(A, A, x, x)
          |}
          |
          |def bad (xs: LNats) : Nat := {
          |  let (a, b) := Foo.dup(xs)
          |  Nat.add(count(a), count(b))
          |}
          |""".stripMargin
    )
  }

  // ------------ Batch 2: no linear type equals a copyable one ------------

  // Without cumulativity a copyable type is no `Lin(u)`, so no equation makes a linear type copyable, or a copyable
  // value fill a linear slot: the refinements these programs relied on cannot be stated.
  test("an equation between a linear universe's type and a copyable type is TypeMismatch") {
    rejectsWith[TypeMismatch](
      lib +
        """
          |def twice (x: $A in Lin($u))(e: Eq(Lin(u), A, Nat)) : Nat := {
          |  match e with
          |  | Eq.refl z => {
          |    let y := x
          |    Nat.add(y, y)
          |  }
          |}
          |""".stripMargin
    )
    rejectsWith[TypeMismatch](
      lib +
        """
          |def spread (A: Lin(Level.zero))(e: Eq(Lin(Level.zero), Nat, A))(n: Nat) : LPair(A, A) := {
          |  match e returning LPair(A, A) with
          |  | Eq.refl z => LPair.mk(n, n)
          |}
          |""".stripMargin
    )
    rejectsWith[TypeMismatch](
      lib + "def absurdLin (h: Eq(Lin(Level.zero), LNats, Nat)) : False := {\n  match h returning False with\n}\n"
    )
  }

  test("refinement linking a Type variable to a linear type") {
    rejects(
      lib +
        """
          |def bad (A: Type)(e: Eq(Lin(Level.zero), A, LNats))(x: A) : LPair(A, A) := {
          |  match e returning LPair(A, A) with
          |  | Eq.refl z => LPair.mk(x, x)
          |}
          |
          |def bad2 (xs: LNats) : Nat := {
          |  let p := bad(LNats, Eq.refl(LNats), xs)
          |  0
          |}
          |""".stripMargin
    )
  }

  // ------------ Batch 2: named functions inside types ------------

  test("a named function with a linear parameter inside a type or proof is accepted, unlike the eta-equal lambda") {
    accepts(lib + "def apply (f: (xs: LNats) -> Nat) : Type := Nat\ndef ok (x: apply(count)) : Nat := 0\n")
    accepts(
      lib +
        "def applyP (f: (xs: LNats) -> Nat)(h: Eq(Nat, 0, 0)) : Eq(Nat, 0, 0) := h\n" +
        "def ok : Eq(Nat, 0, 0) := applyP(count, Eq.refl(0))\n"
    )
  }

  // ------------ Batch 2: program bodies ------------

  test("a program body may drop a linear let, but not duplicate one") {
    accepts(lib + "\n{\n  let xs := LNats.cons(1, LNats.nil)\n  0\n}\n")
    rejectsWith[LinearReused](
      lib + "\n{\n  let xs := LNats.cons(1, LNats.nil)\n  Nat.add(count(xs), count(xs))\n}\n"
    )
  }

  test("a program result that is a function holding a linear value") {
    rejects(lib + "\n{\n  let xs := LNats.cons(1, LNats.nil)\n  fun (n: Nat): Nat => Nat.add(n, count(xs))\n}\n")
  }

  // ------------ Batch 3: S3 against an opaque linear type ------------

  private val tok =
    lib +
      """
        |axiom Tok : Lin(Level.zero)
        |
        |def burnBoth (a: Tok)(b: Tok)(burn: Tok -> Nat) : Nat := Nat.add(burn(a), burn(b))
        |""".stripMargin

  test("S3 control: an opaque linear type is allowed, an axiom minting or burning it directly is not") {
    accepts(tok)
    rejectsWith[LinearAxiom](tok + "axiom mint : Nat -> Tok\n")
    rejectsWith[LinearAxiom](tok + "axiom burn : Tok -> Nat\n")
    rejectsWith[LinearAxiom](tok + "axiom t : Tok\n")
  }

  test("S3: an axiom of a Sort struct mints opaque linear tokens from nothing") {
    rejects(
      tok +
        """
          |axiom mint : Box(Nat -> Tok)
          |
          |def twoTokens (burn: Tok -> Nat) : Nat := {
          |  match mint with
          |  | Box.mk f => burnBoth(f(0), f(1), burn)
          |}
          |""".stripMargin
    )
  }

  test("S3: an axiom of a Sort struct burns an opaque linear token") {
    rejects(
      tok +
        """
          |axiom burn : Box(Tok -> Nat)
          |
          |def drop (t: Tok) : Nat := {
          |  match burn with
          |  | Box.mk f => f(t)
          |}
          |""".stripMargin
    )
  }

  test("S3: an axiom of a kernel List mints opaque linear tokens") {
    rejects(
      tok +
        """
          |axiom mints : List(Nat -> Tok)
          |
          |def twoTokens (burn: Tok -> Nat) : Nat := {
          |  match mints with
          |  | List.nil => 0
          |  | List.cons f rest => burnBoth(f(0), f(1), burn)
          |}
          |""".stripMargin
    )
  }

  test("S3: an axiom function whose codomain is a Sort struct of minting functions") {
    rejects(
      tok +
        """
          |axiom mints (n: Nat) : Box(Nat -> Tok)
          |
          |def twoTokens (burn: Tok -> Nat) : Nat := {
          |  match mints(3) with
          |  | Box.mk f => burnBoth(f(0), f(1), burn)
          |}
          |""".stripMargin
    )
  }

  // A documented S3 limit (docs/kernel.md, S3): a stuck computed codomain is not opened. Expected to fail until it is.
  test("S3: an axiom whose codomain is a stuck type that computes to a minting function type".fail) {
    rejects(
      tok +
        """
          |def F (b: Bool) : Type := {
          |  match b returning Type with
          |  | Bool.true => (m: Nat) -> Tok
          |  | Bool.false => Nat
          |}
          |
          |axiom mint (b: Bool) : F(b)
          |""".stripMargin
    )
  }

  // A documented S3 limit (docs/kernel.md, S3): the field types of a family the axiom's type names are not walked, and
  // `Gen` has no arguments. Expected to fail until they are.
  test("S3: an axiom of a Sort struct whose minted tokens fill an existential package".fail) {
    rejects(
      tok +
        """
          |inductive Gen : Sort(Level.one)
          | | mk (T: Lin(Level.zero))(f: Nat -> T) : Gen
          |
          |axiom gen : Gen
          |
          |def made (burnAny: (T: Lin(Level.zero)) -> (t: T) -> Nat) : Nat := {
          |  match gen with
          |  | Gen.mk T f => Nat.add(burnAny(T, f(0)), burnAny(T, f(1)))
          |}
          |""".stripMargin
    )
  }

  // ------------ Batch 3: S1 gap reaches only constructed values ------------

  // R5: a type may mint and burn a token through unrestricted functions in scope: the run has no linear input.
  test("a pattern-head application of an unrestricted local is a closed read (R5)") {
    accepts(tok + "def ok (g: Nat -> Tok)(burn: Tok -> Nat)(y: Tag(burn(g(0)))) : Nat := 0\n")
  }

  // R1: a binder type reads xs once, through lid, and the body consumes it.
  test("a tracked local nested in a pattern application is a read") {
    accepts(lib + "def ok (xs: LNats)(t: Tag(count(lid(xs)))) : Nat := count(xs)\n")
  }

  test("a pattern head that selects from a tracked local is not a reference") {
    rejects(
      lib +
        """
          |inductive H : Lin(Level.one)
          | | mk (F: Nat -> Type) : H
          |
          |def bad (h: H)(y: h.F(0)) : Nat := {
          |  match h with
          |  | H.mk F => 0
          |}
          |""".stripMargin
    )
  }

  // R3: y's type reads h through its selector, and the body consumes h once. Sound: the read is a hypothetical run.
  test("a tracked local selected in a parenthesized binder type") {
    accepts(
      lib +
        """
          |inductive H : Lin(Level.one)
          | | mk (F: Nat -> Type) : H
          |
          |def ok (h: H)(y: (H.F(h)(0))) : Nat := {
          |  match h with
          |  | H.mk F => 0
          |}
          |""".stripMargin
    )
  }

  // ------------ Batch 3: builtins ------------

  test("no program builtin may produce or consume a linear value") {
    rejectsWith[ProgramBuiltin](lib + "def mystery : LNats := builtin\n")
    rejectsWith[ProgramBuiltin](lib + "def mystery (xs: LNats) : Nat := builtin\n")
    rejectsWith[ProgramBuiltin](tok + "def mystery (t: Tok) : Nat := builtin\n")
  }

  // ------------ Batch 3: instance binders ------------

  test("a Lin-capture instance binder is LinearInstance") {
    rejectsWith[LinearInstance](lib + "def bad [x: $A in Lin($u)] : Nat := 0\n")
  }

  test("a local instance of a function type cannot smuggle a captured linear local") {
    rejectsWith[LinearCapture](
      lib +
        "def callIt [f: Nat -> Nat] : Nat := Nat.add(f(0), f(0))\n" +
        "def bad (xs: LNats) : Nat := {\n  let instance f := fun (n: Nat): Nat => count(xs)\n  callIt(derive[Nat -> Nat])\n}\n"
    )
  }

  // ------------ Batch 3: selectors with dependent fields ------------

  // Projecting the type component reads the struct: a type-valued selector's body is a read extent, which may drop the
  // linear field. Projecting the linear component consumes the struct, and its value may then be dropped.
  test("L5: selectors of an existential linear struct") {
    val pks =
      lib + "inductive PkS : Lin(Level.one)\n | mk (T: Lin(Level.zero))(x: T) : PkS\n\n"
    accepts(pks + "def ok (p: PkS) : Lin(Level.zero) := p.T\n")
    accepts(
      pks + "def bad (p: PkS)(burn: (T: Lin(Level.zero)) -> (t: T) -> Nat) : Nat := {\n  let x := p.x\n  0\n}\n"
    )
  }

  // ------------ Batch 3: unreachable constructors ------------

  private val vlib =
    lib +
      """
        |def vcount (v: LVec(Nat, $n)) : Nat decreases measure(n) := {
        |  match v with
        |  | LVec.nil => 0
        |  | LVec.cons k h t => Nat.add(h, vcount(t))
        |}
        |""".stripMargin

  private def consOnly(index: String): String =
    vlib +
      s"""
         |def bad (n: Nat)(m: Nat)(v: LVec(Nat, $index))(xs: LNats) : Nat := {
         |  match v with
         |  | LVec.cons k h t => Nat.add(vcount(t), count(xs))
         |}
         |""".stripMargin

  test("a cons-only match on a vector whose length may be zero is MissingCase") {
    rejectsWith[MissingCase](consOnly("Nat.sub(n, 1)"))
    rejectsWith[MissingCase](consOnly("Nat.mul(n, 2)"))
    rejectsWith[MissingCase](consOnly("Nat.pred(n)"))
    rejectsWith[MissingCase](consOnly("Nat.add(n, m)"))
    rejectsWith[MissingCase](consOnly("Nat.pow(n, 2)"))
    rejectsWith[MissingCase](consOnly("Nat.mul(n, m)"))
    rejectsWith[MissingCase](consOnly("Nat.sub(Nat.add(n, 1), m)"))
  }

  test("absurd-path control: a cons-only match on a vector of successor length is accepted") {
    accepts(consOnly("Nat.add(n, 1)"))
    accepts(consOnly("Nat.succ(Nat.add(n, m))"))
  }

  test("a branchless match on an Eq between satisfiable Nat expressions") {
    def absurd(lhs: String, rhs: String): String =
      lib +
        s"def bad (n: Nat)(m: Nat)(h: Eq(Nat, $lhs, $rhs))(xs: LNats) : Nat := False.elim(match h returning False with\n, Nat)\n"
    rejectsWith[MissingCase](absurd("Nat.mul(n, 0)", "0"))
    rejectsWith[MissingCase](absurd("Nat.sub(n, m)", "Nat.succ(m)"))
    rejectsWith[MissingCase](absurd("Nat.pow(n, m)", "0"))
    rejectsWith[MissingCase](absurd("Nat.add(n, m)", "Nat.mul(n, m)"))
    rejectsWith[MissingCase](
      lib + "def bad (n: Nat)(m: Nat)(h: Eq(Bool, Nat.beq(n, m), Bool.true))(xs: LNats) : Nat := False.elim(match h returning False with\n, Nat)\n"
    )
  }

  // ------------ Batch 3: universe-valued definitions ------------

  test("a binder universe chosen by a stuck Bool is not a type") {
    rejects(
      lib +
        "def U (b: Bool) : Sort(Level.one) := {\n  match b returning Sort(Level.one) with\n  | Bool.true => Type\n  | Bool.false => Lin(Level.zero)\n}\n" +
        "def bad (b: Bool)(T: U(b))(x: T) : LPair(T, T) := LPair.mk(x, x)\n"
    )
  }

  test("a binder universe computed to Lin tracks its values") {
    rejectsWith[LinearReused](
      lib +
        "def U (b: Bool) : Sort(Level.one) := {\n  match b returning Sort(Level.one) with\n  | Bool.true => Type\n  | Bool.false => Lin(Level.zero)\n}\n" +
        "def bad (T: U(Bool.false))(x: T) : LPair(T, T) := LPair.mk(x, x)\n"
    )
  }

  test("Lin passed as a universe-valued function is used only at its universe") {
    rejects(
      lib +
        "def useU (F: (l: Level) -> Sort(Level.succ(l)))(T: F(Level.zero))(x: T) : LPair(T, T) := LPair.mk(x, x)\n" +
        "def bad (xs: LNats) : LPair(LNats, LNats) := useU(Lin, LNats, xs)\n"
    )
  }

  // ------------ Batch 3: currying through def headers ------------

  test("a Type-polymorphic two-binder duplicator against a Lin-polymorphic two-binder type") {
    rejects(
      lib +
        """
          |def dupT (A: Type)(x: A) : Prod(A, A) := Prod.mk(A, A, x, x)
          |
          |def apply2 (f: (A: Lin(Level.zero)) -> (x: A) -> LPair(A, A))(xs: LNats) : LPair(LNats, LNats) :=
          |  f(LNats, xs)
          |
          |def bad (xs: LNats) : LPair(LNats, LNats) := apply2(dupT, xs)
          |""".stripMargin
    )
  }

  // ------------ Batch 3: dropping linear call results ------------

  test("a linear call result dropped by let _, by an unused let, or inside a type is accepted") {
    accepts(
      lib + "def mk (n: Nat) : LNats := LNats.cons(n, LNats.nil)\ndef bad : Nat := {\n  let _ := mk(1)\n  0\n}\n"
    )
    accepts(
      lib + "def mk (n: Nat) : LNats := LNats.cons(n, LNats.nil)\ndef bad (b: Bool) : Nat := {\n  let ys := mk(1)\n  match b with\n  | Bool.true => count(ys)\n  | Bool.false => 0\n}\n"
    )
  }

  test("a tracked let consumed on only one path is accepted") {
    accepts(
      lib +
        """
          |def bad (n: Nat)(xs: LNats) : Nat := {
          |  match n with
          |  | Nat.zero => 0
          |  | Nat.succ k => count(xs)
          |}
          |""".stripMargin
    )
  }
}
