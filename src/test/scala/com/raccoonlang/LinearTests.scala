package com.raccoonlang

import com.raccoonlang.ProgramFixtures._
import com.raccoonlang.Value._
import com.raccoonlang.packed.Storage.segment

/**
 * Linear types (docs/kernel.md, "Linear types"): the `Lin` sort, linear families, function types, the ledger and S1–S3.
 */
class LinearTests extends munit.FunSuite {
  private val programs = new Programs(Prelude.default, allowUserAxioms = true)
  import programs._

  private val families =
    ProgramFixtures.lnats +
      """
        |inductive LVec (A: Sort($u)) indices (n: Nat) : Lin(u)
        | | nil {A: Sort($u)} : LVec(A, 0)
        | | cons (n: Nat)(head: $A in Sort($u))(tail: LVec(A, n)) : LVec(A, Nat.succ(n))
        |
        |""".stripMargin

  // ------------ The Lin sort and linear families ------------

  test(
    "List and Prod follow their arguments' kinds, and LVec and a Lin struct with unrestricted, proof and dependent fields are linear families"
  ) {
    val env = declsEnv(
      families +
        """
          |inductive Sized : Lin(Level.zero)
          | | mk (n: Nat)(small: Nat.le(n, 3))(items: LVec(Nat, n)) : Sized
          |""".stripMargin
    )
    def universe(name: String): Value =
      env(name).tpe match {
        case pi: VPi => pi.codomain(telescope.BinderOps.freshen(pi))
        case other   => other
      }
    // A kind-polymorphic family's universe is a kind variable of its parameter.
    universe("List") match {
      case VUniv(kind, _) => assert(!kind.isCopy && !kind.lin, kind.toString)
      case other          => fail(s"List is in $other")
    }
    assertEquals(universe("Sized"), VLin(Level.zero))
    val pair = Interpreter.evalApply(env("Prod"), Vector(env("LNats"), env("Sized")))
    assertEquals(pair.tpe, VLin(Level.zero))
    assert(Linearity.isLinear(pair))
    val mixed = Interpreter.evalApply(env("Prod"), Vector(env("LNats"), Kernel.natType))
    assertEquals(mixed.tpe, VLin(Level.zero))
    val copyable = Interpreter.evalApply(env("Prod"), Vector(Kernel.natType, Kernel.natType))
    assertEquals(copyable.tpe, TypeTpe)
    assertEquals(Interpreter.evalApply(env("List"), Vector(Kernel.natType)).tpe, TypeTpe)
    assertEquals(Interpreter.evalApply(env("List"), Vector(env("LNats"))).tpe, VLin(Level.zero))
  }

  test("no cumulativity: a Sort type is no Lin(0), and a Lin capture does not open on a copyable argument") {
    val defs =
      families +
        """
          |def keep (A: Lin(Level.zero)) : Lin(Level.zero) := A
          |def lid (x: $A in Lin($u)) : A := x
          |""".stripMargin
    assertErrorAt[TypeMismatch](defs + "def bad : Lin(Level.zero) := keep(Nat)\n", "(Nat)")
    assertErrorAt[TypeMismatch](defs + "def bad : Nat := lid(5)\n", "(5)")
    assertErrorAt[TypeMismatch](defs + "def bad : Lin(Level.zero) := Nat\n", "Nat", "Nat\n")
    // A linear type, and a value of one, pass.
    run(defs + "def ok (xs: LNats) : Nat := count(lid(xs))\ndef T : Lin(Level.zero) := keep(LNats)\n")
  }

  test("Lin(u) prints, quotes and is inferred as a match motive") {
    val env = declsEnv(families)
    val lin1 = VLin(Level.one)
    assertEquals(PrettyPrinter.print(lin1), "Lin(Level(Map(), 1))")
    assertEquals(lin1.tpe, VSort(Level.const(2)))
    val quoted = ValueQuote.quoteTerm(lin1, ValueQuote.quoteContext(env), Span(0, 0))
    assertEquals(PrettyPrinter.printElabTerm(quoted), "Lin(Level.one)")
    assertEquals(Interpreter.evalTerm(quoted, env), lin1)
    // The first checked branch's (Bool.false's) result type, Lin(0), is quoted as the inferred motive.
    val res = runProgram(
      families +
        """
          |def pick (b: Bool) : Lin(Level.zero) := {
          |  let chosen := match b with
          |  | Bool.true => List(LNats)
          |  | Bool.false => LNats
          |  chosen
          |}
          |
          |{ pick(Bool.false) }
          |""".stripMargin
    )
    assertEquals(PrettyPrinter.print(res), "LNats")
    assertEquals(PrettyPrinter.print(res.tpe), "Lin(Level(Map(), 0))")
  }

  test("a linear list value is a packed word with the list storage invariants") {
    val env = declsEnv(families)
    val cons = env("LNats.cons").asInstanceOf[ConstructorHead]
    assertEquals(cons.listShape, Some(ListShape(1, 1)))
    val lnats = env("LNats")
    val nil = TypeChecker.checkTerm(parse(families + "{ LNats.nil }").body.get, env).value
    def nat(n: Int): Value = NatNormalForm.literal(BigInt(n))
    val one = ConstructorValue(cons, Vector(nat(1), nil), lnats)
    val two = ConstructorValue(cons, Vector(nat(2), one), lnats)
    assert(two.isInstanceOf[VWord])
    assert(segment(two).chunk eq segment(one).chunk)
    val checked = TypeChecker.checkTerm(
      parse(families + "{ LNats.cons(2, LNats.cons(1, LNats.nil)) }").body.get,
      env
    )
    assert(checked.value.isInstanceOf[VWord])
    assert(ValueEquivalence.defEq(checked.value, two))
    assertEquals(checked.value.key, two.key)
    assertEquals(checked.value.toString, two.toString)
    assert(Linearity.isLinear(checked.value.tpe))
  }

  test("a function type with linear domain and codomain is classified in Sort") {
    val env = declsEnv(
      families +
        """
          |def Fn : Type := (xs: LNats) -> LNats
          |def Fn1 : Sort(Level.one) := (A: Lin(Level.zero)) -> (x: A) -> A
          |""".stripMargin
    )
    assertEquals(env("Fn").tpe, TypeTpe)
    assertEquals(env("Fn1").asInstanceOf[VPi].tpe, VSort(Level.one))
  }

  test("a linear field in a Sort or Prop family is LinearFieldInUnrestrictedFamily") {
    assertErrorAt[LinearFieldInUnrestrictedFamily](
      families + "inductive Bad : Type\n | mk (xs: LNats) : Bad\n",
      "(xs: LNats)"
    )
    assertErrorAt[LinearFieldInUnrestrictedFamily](
      families + "inductive BadP : Prop\n | mk (xs: LNats) : BadP\n",
      "(xs: LNats)"
    )
  }

  test("a linear parameter or index is LinearFamilyArgument") {
    assertErrorAt[LinearFamilyArgument](
      families + "inductive BadParam (xs: LNats) : Type\n",
      "(xs: LNats)"
    )
    assertErrorAt[LinearFamilyArgument](
      families + "inductive BadIndex indices (xs: LNats) : Lin(Level.zero)\n",
      "(xs: LNats)"
    )
  }

  test("a linear family parameter that an erased constructor binder names is LinearFamilyArgument") {
    assertErrorAt[LinearFamilyArgument](
      families + "inductive Hold (xs: LNats) : Lin(Level.zero)\n | mk {xs: LNats} : Hold(xs)\n",
      "(xs: LNats)"
    )
  }

  test("a field above the linear family's level is InductiveUniverseTooSmall") {
    assertErrorAt[InductiveUniverseTooSmall](
      families + "inductive Big : Lin(Level.zero)\n | mk (A: Type) : Big\n",
      "(A: Type)"
    )
  }

  // The nominal size rule charges a record with structure eta by its fields, so a Proto, an atom type and a relation
  // into Prop, costs level 0, while a record with a large field, a family with two constructors, or a record holding a
  // large record costs its level (raccoon-formalization DESIGN.md §10).
  test("a Lin(0) family may take a record of small fields, but not one holding a large field") {
    run(
      families +
        """
          |inductive Proto : Sort(Level.one)
          | | mk (Atom: Type)(Step: (consumed: List(Atom)) -> (produced: List(Atom)) -> Prop) : Proto
          |
          |inductive Toks (P: Proto) indices (C: List(P.Atom)) : Lin(Level.zero)
          | | nil {P: Proto} : Toks(P, List.nil(P.Atom))
          |""".stripMargin
    )
    val large =
      families +
        """
          |inductive Big : Sort(Level.one)
          | | mk (F: (A: Type) -> Type) : Big
          |
          |inductive Two : Sort(Level.one)
          | | left (A: Type) : Two
          | | right (A: Type) : Two
          |
          |inductive Holds : Sort(Level.one)
          | | mk (b: Big) : Holds
          |
          |""".stripMargin
    Vector("Big", "Two", "Holds").foreach { record =>
      assertErrorAt[FamilyArgumentTooLarge](
        large + s"inductive Toks (P: $record) : Lin(Level.zero)\n | nil {P: $record} : Toks(P)\n",
        s"(P: $record)",
        s"(P: $record) :"
      )
    }
  }

  // KERNEL_FOLLOWUPS 1.1 (open question 19): matching `Tensor(Nat, Nat)`, a two-level family of `Lin` captures, left its
  // fields' types fresh. `Tensor` is gone; `Prod` has two kind and level captures, and refines its fields at copyable,
  // mixed and linear arguments alike.
  test("two-level, two-kind pairs refine their fields at every instance") {
    run(
      families +
        """
          |def sum (p: Prod(Nat, Nat)) : Nat := {
          |  match p with
          |  | Prod.mk a b => Nat.add(a, b)
          |}
          |
          |def mixed (p: Prod(LNats, Nat)) : Nat := {
          |  match p with
          |  | Prod.mk a b => Nat.add(count(a), b)
          |}
          |
          |def sizes (p: Prod(LNats, List(LNats))) : Nat := {
          |  match p with
          |  | Prod.mk a b => {
          |    match b with
          |    | List.nil => count(a)
          |    | List.cons h t => Nat.add(count(a), count(h))
          |  }
          |}
          |""".stripMargin
    )
  }

  // KERNEL_FOLLOWUPS 1.2 (open question 17): `Eq.refl(A)` returned at `Eq(Lin(0), A, A)` came back at
  // `Eq(Type, Nat, Nat)` when `A := Nat`. A value is now used at exactly its universe, so `A := Nat` is refused, and at
  // a linear instance the result has its declared type.
  test("no cumulativity: a result keeps its declared universe, since no smaller one is accepted") {
    val same =
      families +
        """
          |def same (A: Lin(Level.zero)) : Eq(Lin(Level.zero), A, A) := Eq.refl(A)
          |def sameHigh (A: Sort(Level.one)) : Eq(Sort(Level.one), A, A) := Eq.refl(A)
          |""".stripMargin
    assertErrorAt[TypeMismatch](same + "def bad : Eq(Type, Nat, Nat) := same(Nat)\n", "(Nat)", "same(Nat)")
    assertErrorAt[TypeMismatch](same + "def bad : Eq(Type, Nat, Nat) := sameHigh(Nat)\n", "(Nat)", "sameHigh(Nat)")
    run(
      same +
        "def useEq (e: Eq(Lin(Level.zero), LNats, LNats)) : Nat := 0\n" +
        "def ok : Nat := useEq(same(LNats))\n" +
        "def cast (e: Eq(Lin(Level.zero), LNats, LNats))(xs: LNats) : LNats :=\n" +
        "  Eq.subst(e, Kind.lin, Level.zero, fun (T: Lin(Level.zero)): Lin(Level.zero) => T, xs)\n" +
        "def back (xs: LNats) : Nat := count(cast(same(LNats), xs))\n"
    )
  }

  test("a Sort capture opens on a linear type, whose universe then does not fit Sort") {
    assertErrorAt[TypeMismatch](families + "def bad : Type := List(LNats)\n", "(LNats)")
    assertErrorAt[TypeMismatch](
      families + "def bad : Prop := Eq(LNats, LNats.nil, LNats.nil)\n",
      "(LNats, LNats.nil, LNats.nil)"
    )
  }

  test("linear families are nominal, and universes of different constant kinds are apart, unlike a kind variable") {
    run(
      families +
        """
          |def distinct (h: Eq(Lin(Level.zero), LNats, Prod(LNats, LNats))) : False := {
          |  match h returning False with
          |}
          |
          |def injective (h: Eq(Lin(Level.zero), List(LNats), List(List(LNats)))) : False := {
          |  match h returning False with
          |}
          |""".stripMargin
    )
    run(
      families + "def apart (h: Eq(Sort(Level.one), Type, Lin(Level.zero))) : False := {\n  match h returning False with\n}\n"
    )
    // A kind variable may be `copy`, so `Univ(k, 0)` is not apart from `Type`.
    assertErrorAt[MissingCase](
      families +
        "def notApart (k: Kind)(h: Eq(Sort(Level.one), Type, Univ(k, Level.zero))) : False := {\n  match h returning False with\n}\n",
      "match h returning False with\n"
    )
    assert(!ValueEquivalence.defEq(VSort(Level.zero), VLin(Level.zero)))
    assertNotEquals(VSort(Level.zero).key, VLin(Level.zero).key)
  }

  test("a Lin capture and a Sort capture are different capture operations") {
    assertErrorAt[TypeMismatch](
      families +
        """
          |def useLinId (f: (x: $A in Lin($u)) -> A)(xs: LNats) : Nat := count(f(xs))
          |def bad (xs: LNats) : Nat := useLinId(id, xs)
          |""".stripMargin,
      "(id, xs)"
    )
  }

  test("Nat -> Type is not Nat -> Lin(0): cumulativity does not apply under function types") {
    assertErrorAt[TypeMismatch](
      families +
        """
          |def useFamily (F: Nat -> Lin(Level.zero)) : Nat := 0
          |def bad : Nat := useFamily(fun (n: Nat): Type => Nat)
          |""".stripMargin,
      "(fun (n: Nat): Type => Nat)"
    )
  }

  test("linear families keep ordinary positivity: nested recursion, recursion under a binder, other parameters") {
    declsEnv(
      families +
        """
          |inductive Rose : Lin(Level.zero)
          | | leaf : Rose
          | | node (kids: List(Rose)) : Rose
          |
          |inductive Lim : Lin(Level.zero)
          | | stop : Lim
          | | lim (f: Nat -> Lim) : Lim
          |
          |inductive Swap (A: Lin($u)) : Lin(u)
          | | nil {A: Lin($u)} : Swap(A)
          | | wrap (t: Swap(LNats))(x: $A in Lin($u)) : Swap(A)
          |
          |inductive Handler : Lin(Level.zero)
          | | done : Handler
          | | more (f: Nat -> Nat)(g: (xs: LNats) -> Nat)(next: Handler) : Handler
          |""".stripMargin
    )
  }

  // ------------ The ledger and reads ------------

  private val library =
    families +
      """
        |def swap (p: Prod($A, $B)) : Prod(B, A) := {
        |  let (a, b) := p
        |  Prod.mk(B, A, b, a)
        |}
        |
        |def map (xs: List($A))(B: Lin($v))(f: A -> B) : List(B) decreases structural(xs) := {
        |  match xs with
        |  | List.nil => List.nil(B)
        |  | List.cons h t => List.cons(f(h), map(t, B, f))
        |}
        |
        |def append (xs: LNats)(ys: LNats) : LNats decreases structural(xs) := {
        |  match xs with
        |  | LNats.nil => ys
        |  | LNats.cons h t => LNats.cons(h, append(t, ys))
        |}
        |
        |def lengths (xs: List(LNats)) : LNats decreases structural(xs) := {
        |  match xs with
        |  | List.nil => LNats.nil
        |  | List.cons h t => LNats.cons(count(h), lengths(t))
        |}
        |
        |def lid (x: $A in Lin($u)) : A := x
        |
        |def pick (b: Bool)(xs: LNats) : Nat := {
        |  match b with
        |  | Bool.true => count(xs)
        |  | Bool.false => Nat.add(1, count(xs))
        |}
        |
        |def onlyZero (n: Nat)(h: Eq(Nat, n, 0))(xs: LNats) : Nat := {
        |  match n with
        |  | Nat.zero => count(xs)
        |  | Nat.succ k => {
        |    match Nat.succNeZero(k, h) returning Nat with
        |  }
        |}
        |
        |def castVec (v: LVec(Nat, $n))(m: Nat)(e: Eq(Nat, n, m)) : LVec(Nat, m) :=
        |  Eq.subst(e, Kind.lin, Level.zero, fun (k: Nat): Lin(Level.zero) => LVec(Nat, k), v)
        |
        |def recast (v: LVec(Nat, $n)) : LVec(Nat, n) := castVec(v, n, Eq.refl(n))
        |
        |def vcount (v: LVec(Nat, $n)) : Nat decreases measure(n) := {
        |  match v with
        |  | LVec.nil => 0
        |  | LVec.cons k h t => Nat.add(h, vcount(t))
        |}
        |
        |inductive Tagged : Lin(Level.zero)
        | | mk (tag: Nat)(payload: LNats) : Tagged
        |
        |def payloadOf (t: Tagged) : LNats := t.payload
        |""".stripMargin

  private val tags = library + "inductive Tag indices (n: Nat) : Type\n | mk (n: Nat) : Tag(n)\n\n"

  test("programs that use linear values at most once check and run") {
    val res = runProgram(
      library +
        """
          |{
          |  let p := swap(Prod.mk(LNats, LNats, LNats.cons(1, LNats.nil), LNats.cons(7, LNats.nil)))
          |  let (xs, ys) := p
          |  let nested := List.cons(LNats.cons(5, LNats.nil), List.cons(LNats.nil, List.nil(LNats)))
          |  let padded := map(nested, LNats, fun (l: LNats): LNats => append(l, LNats.cons(0, LNats.nil)))
          |  let joined := append(lengths(padded), append(lid(ys), payloadOf(Tagged.mk(3, xs))))
          |  let v := recast(LVec.cons(0, 40, LVec.nil(Nat)))
          |  Nat.add(Nat.add(count(joined), pick(Bool.false, LNats.nil)), Nat.add(vcount(v), onlyZero(0, Eq.refl(0), LNats.nil)))
          |}
          |""".stripMargin
    )
    // joined = [2, 1, 1, 7] has four elements; pick adds 1; vcount adds 40.
    assertEquals(PrettyPrinter.print(res), "45")
  }

  test("a linear local captured by a lambda is LinearCapture at the reference") {
    assertErrorAt[LinearCapture](
      library + "def bad (xs: LNats) : Nat -> Nat := fun (n: Nat): Nat => Nat.add(n, count(xs))\n",
      "xs",
      "count(xs))"
    )
    assertErrorAt[LinearCapture](
      library + "def bad (xs: LNats) : Nat := {\n  let f := fun (n: Nat): Nat => fun (m: Nat): Nat => count(xs)\n  f(0, 1)\n}\n",
      "xs",
      "count(xs)"
    )
  }

  test("L4 relaxed: a motive may read the linear scrutinee, which the match still consumes") {
    run(
      tags +
        """
          |def tagged (xs: LNats) : Tag(count(xs)) := {
          |  match xs returning Tag(count(xs)) with
          |  | LNats.nil => Tag.mk(0)
          |  | LNats.cons h t => Tag.mk(Nat.succ(count(t)))
          |}
          |""".stripMargin
    )
  }

  test("linear instance binders and instance lets are LinearInstance") {
    assertErrorAt[LinearInstance](library + "def bad [xs: LNats] : Nat := count(xs)\n", "[xs: LNats]")
    assertErrorAt[LinearInstance](
      library + "def bad (xs: LNats) : Nat := {\n  let instance ys := xs\n  count(ys)\n}\n",
      "let instance ys := xs"
    )
  }

  test("a second use is LinearReused at that use") {
    assertErrorAt[LinearReused](
      library + "def bad (xs: LNats) : Nat := Nat.add(count(xs), count(xs))\n",
      "xs",
      "xs))"
    )
    assertErrorAt[LinearReused](
      library + "def bad (xs: LNats) : Prod(LNats, LNats) := Prod.mk(LNats, LNats, xs, xs)\n",
      "xs",
      "xs)\n"
    )
  }

  test("use is affine: no use, a linear field matched by _, let _ and a dropped named field are accepted") {
    run(
      library +
        "def none (xs: LNats) : Nat := 0\n" +
        "def wild (p: Tagged) : Nat := {\n  match p with\n  | Tagged.mk n _ => n\n}\n" +
        "def pair (p: Tagged) : Nat := {\n  let (n, _) := p\n  n\n}\n" +
        "def under (xs: LNats) : Nat := {\n  let _ := xs\n  0\n}\n" +
        "def named (xs: List(LNats)) : Nat := {\n  match xs with\n  | List.nil => 0\n  | List.cons h t => 0\n}\n"
    )
    // Dropping is no copy: a dropped field's struct is still consumed once.
    assertErrorAt[LinearReused](
      library + "def bad (p: Tagged) : Nat := {\n  let (n, _) := p\n  let (m, ys) := p\n  count(ys)\n}\n",
      "p",
      "p\n  count"
    )
  }

  test("a use in one branch only is accepted, and a use in a branch and after the match is LinearReused") {
    run(
      library +
        "def one (b: Bool)(xs: LNats) : Nat := {\n  match b with\n  | Bool.true => count(xs)\n  | Bool.false => 0\n}\n"
    )
    assertErrorAt[LinearReused](
      library +
        "def bad (b: Bool)(xs: LNats) : Nat := {\n  let n := {\n    match b with\n    | Bool.true => count(xs)\n    | Bool.false => 0\n  }\n  Nat.add(n, count(xs))\n}\n",
      "xs",
      "xs))\n}"
    )
  }

  test("a use after the value was matched is LinearReused") {
    assertErrorAt[LinearReused](
      library +
        "def bad (xs: LNats) : Nat := {\n  match xs with\n  | LNats.nil => count(xs)\n  | LNats.cons h t => count(t)\n}\n",
      "xs",
      "count(xs)"
    )
  }

  test("reads in a let annotation, a proof argument or a measure are not uses") {
    run(
      library +
        "def ann (xs: LNats) : Nat := {\n  let e : Eq(Nat, count(xs), count(xs)) := Eq.refl(count(xs))\n  count(xs)\n}\n" +
        "def need (xs: LNats)(h: Eq(Nat, count(xs), count(xs))) : Nat := count(xs)\n" +
        "def arg (ys: LNats) : Nat := need(ys, Eq.refl(count(ys)))\n" +
        "def measured (xs: LNats) : Nat decreases measure(count(xs)) := count(xs)\n"
    )
    // A read is no use: a local that is only read is dropped, and one consumed after its reads is used once.
    run(
      library +
        "def ok (xs: LNats) : Nat := {\n  let e : Eq(Nat, count(xs), count(xs)) := Eq.refl(count(xs))\n  0\n}\n"
    )
  }

  test("a type-pattern capture of linear type is LinearInType at the capture") {
    // F consumes nothing on its only path, which an absurd match ends, so it checks; a capture of its linear parameter
    // would bind an untracked linear local.
    assertErrorAt[LinearInType](
      library +
        "def F (xs: LNats)(h: False) : Type := {\n  match h returning Type with\n}\n" +
        "def bad (y: F($xs, $h)) : Nat := count(xs)\n",
      "$xs"
    )
  }

  test("F3 relaxed: a codomain may read a linear binder") {
    run(tags + "def same (xs: LNats) : Tag(count(xs)) := Tag.mk(count(xs))\n")
  }

  test("R5: closed linear computations, and lambdas with linear parameters, may appear in types and proofs") {
    run(
      library +
        "def t1 : Eq(Nat, count(LNats.nil), 0) := Eq.refl(0)\n" +
        "def t2 : Eq(Nat, 0, 0) := Eq.refl(count(LNats.nil))\n" +
        "def apply (f: (xs: LNats) -> Nat)(h: Eq(Nat, 0, 0)) : Eq(Nat, 0, 0) := h\n" +
        "def t3 : Eq(Nat, 0, 0) := apply(fun (ys: LNats): Nat => count(ys), Eq.refl(0))\n"
    )
  }

  test("a type-valued function only reads its linear argument") {
    run(
      library +
        "inductive LUnit : Lin(Level.zero)\n | unit : LUnit\n\n" +
        "def F (u: LUnit) : Type := {\n  match u with\n  | LUnit.unit => Nat\n}\n"
    )
  }

  test("F2 relaxed (R4): a function returning a proposition may take linear arguments, which it only reads") {
    run(
      library +
        "def lemma (xs: LNats) : True := True.intro\n" +
        "def readFirst (xs: LNats) : Nat := {\n  let h := lemma(xs)\n  count(xs)\n}\n"
    )
    // Reading is not consuming: a linear local only read may be dropped, or consumed once afterwards.
    run(
      library + "def lemma (xs: LNats) : True := True.intro\n" +
        "def ok (ys: LNats) : Nat := {\n  let h := lemma(ys)\n  0\n}\n"
    )
  }

  test("a linear global and a linear program result are LinearGlobal") {
    assertErrorAt[LinearGlobal](library + "def bad : LNats := LNats.nil\n", "LNats", "LNats :=")
    assertErrorAt[LinearGlobal](library + "\nLNats.nil\n", "LNats.nil", "\nLNats.nil\n")
  }

  test("a selector of a linear struct consumes it and drops the other fields, or reads it for a type or proof") {
    run(library + "def tagOf (t: Tagged) : Nat := t.tag\n")
    // A selector consumes its struct, so a second selector of the same struct is a second use.
    assertErrorAt[LinearReused](
      library + "def bad (t: Tagged) : Nat := Nat.add(t.tag, count(t.payload))\n",
      "t.payload"
    )
    val sized =
      library +
        """
          |inductive Sized : Lin(Level.zero)
          | | mk (n: Nat)(small: Nat.le(n, 3))(items: LVec(Nat, n)) : Sized
          |
          |""".stripMargin
    // Destructuring is always available.
    run(sized + "def total (s: Sized) : Nat := {\n  let (n, _, items) := s\n  Nat.add(n, vcount(items))\n}\n")
    // Sized.items's result type applies Sized.n, which reads the struct.
    run(sized + "def items (s: Sized) : Nat := vcount(s.items)\n")
    // A linear struct whose fields are all unrestricted: n projects, the types of small and w depend on n, and t is a
    // proof.
    val pack =
      library +
        """
          |inductive Tag indices (n: Nat) : Type
          | | mk (n: Nat) : Tag(n)
          |
          |inductive Pack : Lin(Level.zero)
          | | mk (n: Nat)(small: Nat.le(n, 3))(w: Tag(n))(t: True) : Pack
          |
          |""".stripMargin
    run(pack + "def size (p: Pack) : Nat := p.n\n")
    // Sound since S1 was relaxed: w's selector type reads its struct (F3), and consumes it; the proof selectors read it
    // (F2), so the struct must still be consumed.
    run(pack + "def tag (p: Pack) : Nat := {\n  let w := p.w\n  0\n}\n")
    run(
      pack + "def size (p: Pack) : Nat := p.n\n" +
        "def facts (p: Pack) : Nat := {\n  let small := p.small\n  let t := p.t\n  size(p)\n}\n"
    )
    run(pack + "def onlyRead (p: Pack) : Nat := {\n  let h := p.t\n  0\n}\n")
  }

  // Without cumulativity no refinement gives a tracked local an unrestricted type: an equation between a linear
  // universe's type and a copyable type cannot be stated.
  test("no equation relates a linear type variable to a copyable type") {
    assertErrorAt[TypeMismatch](
      library + "def asNat (x: $A in Lin($u))(e: Eq(Lin(u), A, Nat)) : Nat := 0\n",
      " (x: $A in Lin($u))(e: Eq(Lin(u), A, Nat)) : Nat"
    )
  }

  test("an inferred motive cannot quote a linear value") {
    assertErrorAt[MissingReturningClause](
      library +
        """
          |inductive Tag indices (n: Nat) : Type
          | | mk (n: Nat) : Tag(n)
          |
          |def bad (b: Bool)(xs: LNats) : Nat := {
          |  let tag := match b with
          |  | Bool.true => Tag.mk(count(xs))
          |  | Bool.false => Tag.mk(count(xs))
          |  0
          |}
          |""".stripMargin,
      "match b with\n  | Bool.true => Tag.mk(count(xs))\n  | Bool.false => Tag.mk(count(xs))\n  "
    )
  }

  test("S3: an axiom that produces or consumes a linear value is LinearAxiom") {
    assertErrorAt[LinearAxiom](library + "axiom forged : LNats\n", "LNats", "LNats\n")
    assertErrorAt[LinearAxiom](
      library + "axiom drop : (xs: LNats) -> Nat\n",
      "(xs: LNats) -> Nat"
    )
    assertErrorAt[LinearAxiom](
      library + "axiom make (n: Nat) : Nat -> LNats\n",
      " (n: Nat) : Nat -> LNats"
    )
    // A linear type is not a linear value.
    run(library + "axiom Opaque : Lin(Level.zero)\naxiom useOpaque (n: Nat) : Lin(Level.zero)\n")
  }

  test("S3 finds a linear type anywhere in an axiom's evaluated type, not only in its telescope") {
    val boxes =
      library +
        """
          |inductive Box (A: Type) : Type
          | | mk {A: Type} (val: A) : Box(A)
          |
          |inductive Fam (F: Nat -> Lin(Level.zero)) : Sort(Level.one)
          | | mk {F: Nat -> Lin(Level.zero)} (f: (n: Nat) -> F(n)) : Fam(F)
          |
          |def Minting : Type := Box((n: Nat) -> LNats)
          |""".stripMargin
    // In a family argument, as a codomain or as a domain; through a kernel list, a constructor's codomain and an alias.
    assertErrorAt[LinearAxiom](
      boxes + "axiom mint : Box(Nat -> LNats)\n",
      "Box(Nat -> LNats)",
      "Box(Nat -> LNats)\n"
    )
    assertErrorAt[LinearAxiom](boxes + "axiom burn : Box(LNats -> Nat)\n", "Box(LNats -> Nat)")
    assertErrorAt[LinearAxiom](boxes + "axiom mints : List(Nat -> LNats)\n", "List(Nat -> LNats)")
    assertErrorAt[LinearAxiom](
      boxes + "axiom mints (n: Nat) : Box(Nat -> LNats)\n",
      " (n: Nat) : Box(Nat -> LNats)"
    )
    assertErrorAt[LinearAxiom](boxes + "axiom mint : Minting\n", "Minting", "Minting\n")
    // A linear type in the body of a function argument, global or local, which the family's field applies.
    assertErrorAt[LinearAxiom](
      boxes + "def Lists (n: Nat) : Lin(Level.zero) := LNats\naxiom mint : Fam(Lists)\n",
      "Fam(Lists)"
    )
    assertErrorAt[LinearAxiom](
      boxes + "def Minter : Sort(Level.one) := Fam(fun (n: Nat): Lin(Level.zero) => LNats)\naxiom mint : Minter\n",
      "Minter",
      "Minter\n"
    )
    // Data axioms, and axioms that only take linear types, still pass.
    run(
      boxes +
        "axiom magicNat : Nat\naxiom choose (A: Type)(x: A) : A\naxiom Pick : Lin(Level.zero) -> Type\n" +
        "axiom boxed : Box(Nat -> Nat)\n"
    )
  }

  test("reads keep each call's linear inputs separate, in every kind of read extent") {
    // One call receiving xs twice: in a binder type pattern, a let annotation, a codomain, a proof and a measure.
    val twice = "count(append(xs, xs))"
    assertErrorAt[LinearReusedInType](
      tags + s"def bad (xs: LNats)(t: Tag($twice)) : Nat := count(xs)\n",
      "xs",
      "xs)))"
    )
    assertErrorAt[LinearReusedInType](
      tags + s"def bad (xs: LNats) : Nat := {\n  let t : Tag($twice) := Tag.mk($twice)\n  count(xs)\n}\n",
      "xs",
      "xs))) :="
    )
    assertErrorAt[LinearReusedInType](
      tags + s"def bad (xs: LNats) : Tag($twice) := Tag.mk(count(xs))\n",
      "xs",
      "xs))) :="
    )
    assertErrorAt[LinearReusedInType](
      tags + s"def bad (xs: LNats) : Eq(Nat, $twice, $twice) := Eq.refl($twice)\n",
      "xs",
      "xs)), count"
    )
    assertErrorAt[LinearReusedInType](
      tags + s"def bad (xs: LNats) : Nat decreases measure($twice) := count(xs)\n",
      "xs",
      "xs))) :="
    )
    // Through a function that passes its input on, and through two linear parameters of one call.
    assertErrorAt[LinearReusedInType](
      tags + "def bad (xs: LNats)(t: Tag(count(append(lid(xs), lid(xs))))) : Nat := count(xs)\n",
      "lid(xs)",
      "lid(xs))))"
    )
    assertErrorAt[LinearReusedInType](
      tags +
        "def pairCount (a: LNats)(b: LNats) : Nat := Nat.add(count(a), count(b))\n" +
        "def bad (xs: LNats)(t: Tag(pairCount(xs, xs))) : Nat := count(xs)\n",
      "xs",
      "xs))) :"
    )
    // Separate calls may each read xs, and unrestricted results copy freely.
    run(
      tags +
        "def ok (xs: LNats)(e: Eq(Nat, count(xs), count(xs)))(t: Tag(Nat.add(count(xs), count(xs)))) : Nat := count(xs)\n"
    )
  }

  test("reads combine only separate regions of roots that were live together (R7)") {
    // ys aliases xs, the region its value is built from: one call may read either, but not both.
    val after =
      tags +
        "def pairCount (a: LNats)(b: LNats) : Nat := Nat.add(count(a), count(b))\n" +
        "def bad (xs: LNats) : Nat := {\n  let ys := lid(xs)\n  let t : Tag(pairCount(xs, ys)) := Tag.mk(pairCount(xs, ys))\n  0\n}\n"
    assertErrorAt[LinearReusedInType](after, "ys", "ys)) :=")
    run(
      tags +
        "def ok (xs: LNats) : Nat := {\n  let ys := lid(xs)\n" +
        "  let t : Eq(Nat, count(xs), count(xs)) := Eq.refl(count(xs))\n" +
        "  let u : Eq(Nat, count(ys), count(ys)) := Eq.refl(count(ys))\n  count(ys)\n}\n"
    )
    // A field is a region of its scrutinee.
    assertErrorAt[LinearReusedInType](
      tags +
        "def pairCount (a: LNats)(b: LNats) : Nat := Nat.add(count(a), count(b))\n" +
        "def bad (xs: LNats) : Nat := {\n  match xs with\n  | LNats.nil => 0\n" +
        "  | LNats.cons h t => {\n    let e : Tag(pairCount(t, xs)) := Tag.mk(pairCount(t, xs))\n    count(t)\n  }\n}\n",
      "xs",
      "xs)) :="
    )
    // A type formed after xs is consumed binds ys, which was never live with xs.
    val formed =
      tags +
        "def pairCount (a: LNats)(b: LNats) : Nat := Nat.add(count(a), count(b))\n" +
        "def bad (xs: LNats) : Nat := {\n  FIRST\n  SECOND\n  n\n}\n"
    val consume = "let n := count(xs)"
    val pi = "let T : Type := (ys: LNats) -> Tag(pairCount(ys, xs))"
    assertErrorAt[LinearNotJointlyLive](formed.replace("FIRST", consume).replace("SECOND", pi), "pairCount(ys, xs)")
    run(formed.replace("FIRST", pi).replace("SECOND", consume))
    // Sibling fields of one match are separate regions.
    run(
      tags +
        "def pairCount (a: LNats)(b: LNats) : Nat := Nat.add(count(a), count(b))\n" +
        "def ok (p: Prod(LNats, LNats)) : Nat := {\n  match p with\n" +
        "  | Prod.mk a b => {\n    let e : Tag(pairCount(a, b)) := Tag.mk(pairCount(a, b))\n    0\n  }\n}\n"
    )
    // The arguments of one application see the locals live at its start.
    run(
      tags +
        "def g (xs: LNats)(ys: LNats)(h: Eq(Nat, count(append(xs, ys)), count(append(xs, ys)))) : Nat :=\n" +
        "  Nat.add(count(xs), count(ys))\n" +
        "def ok (xs: LNats)(ys: LNats) : Nat := g(xs, ys, Eq.refl(count(append(xs, ys))))\n"
    )
  }

}
