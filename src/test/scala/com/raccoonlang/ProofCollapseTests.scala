package com.raccoonlang

import com.raccoonlang.ErrorReporter.Source

/** Pins the declaration-time proof representation policy (docs/proof-collapse.md). */
class ProofCollapseTests extends munit.FunSuite {
  private def parse(src: String): CoreAst.Program =
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) => Elaborator.elab(value)
      case err: Failure         => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }

  private def typecheckDecls(src: String): Unit =
    try {
      Interpreter.run(parse(src))
    } catch {
      case t: TypeError => fail(ErrorReporter.pretty(t, Source(src)))
    }

  private def runProgram(src: String): Value =
    try {
      Interpreter.run(parse(src)).getOrElse(fail("Program has no body"))
    } catch {
      case t: TypeError => fail(ErrorReporter.pretty(t, Source(src)))
    }

  private def assertTypeError[T <: TypeError](src: String)(implicit loc: munit.Location, ct: reflect.ClassTag[T]): T =
    intercept[T] {
      Interpreter.run(parse(src))
    }

  test("certified singleton proofs canonicalize to ordinary constructor form") {
    val res = runProgram(
      """
        |{
        |  Eq.refl(Nat.zero)
        |}
        |""".stripMargin
    )
    res match {
      case Value.VCtor(head, _, tpe) =>
        assertEquals(head.name, "Eq.refl")
        assertEquals(TypeChecker.inductiveFamilyOf(tpe).map(_.head.name), Some("Eq"))
      case other => fail(s"Expected a canonical Eq.refl constructor, got $other")
    }
  }

  test("unforced implicit proof params are rejected, never auto-discharged") {
    // A proof-typed implicit that no later explicit argument type forces cannot be reconstructed
    // at call sites, so the def is rejected at declaration. The residual-only proof intrinsic is
    // never available to source elaboration as a way to discharge that obligation.
    assertTypeError[NonForcedImplicitParam](
      """
        |def useProof {x: Nat}{h: Eq(Nat, x, Nat.zero)} (n: Nat): Eq(Nat, x, Nat.zero) := h
        |
        |def bad : Eq(Nat, Nat.zero, Nat.zero) := useProof(Nat.zero)
        |""".stripMargin
    )
  }

  test("a proof implicit remains forceable without storing a witness in VProof") {
    typecheckDecls(
      """
        |def choose {P: Prop}{h: P} (e: Eq(P, h, h)): P := h
        |
        |def chosen : True := choose(Eq.refl(True.intro))
        |""".stripMargin
    )
  }

  test("a proof implicit remains forceable through a structurally equal Pi proposition") {
    // The hidden binder's Pi and truthFn's separately checked Pi have distinct identity keys.
    // Projection compilation must retain structural defEq as the fallback after key bucketing.
    typecheckDecls(
      """
        |axiom truthFn (_: Nat): True
        |
        |def chooseFn {h: (x: Nat) -> True}
        |    (e: Eq((x: Nat) -> True, truthFn, truthFn)): (x: Nat) -> True := h
        |
        |def chosenFn : (x: Nat) -> True := chooseFn(Eq.refl(truthFn))
        |""".stripMargin
    )
  }

  test("fixed positive-universe families carry no proof recovery metadata") {
    val program = parse(
      """
        |inductive Box : Type
        | | mk : Box
        |""".stripMargin
    )
    val env = program.decls.foldLeft(Prelude.default.checkedEnv) { case (curEnv, decl) =>
      Interpreter.evalDecl(decl, curEnv)
    }

    env("Box") match {
      case Value.VConst(_, Value.Inductive(meta), _) =>
        assertEquals(meta.proofRecovery, None)
      case other => fail(s"Expected the Box inductive family, got $other")
    }
  }

  test("generic-universe bodies compare uncollapsed values correctly") {
    // At generic u, `x : A` with `A : Sort(u)` is not known to be a proof and stays an ordinary
    // value (irrelevance does not hold at generic u); instantiating at a proposition hands the
    // same body collapsed VProofs. Both must check.
    typecheckDecls(
      """
        |def genRefl {u: Level}{A: Sort(u)} (x: A): Eq(A, x, id(x)) := Eq.refl(x)
        |
        |def atProp (P: Prop)(h: P): Eq(P, h, id(h)) := genRefl(h)
        |""".stripMargin
    )
  }

  test("large elimination eligibility classifies polymorphic fields at the Prop instance") {
    val res = runProgram(
      """
        |inductive PolyBox {u: Level}(A: Sort(u)) : Sort(u)
        | | mk (value: A) : PolyBox(A)
        |
        |axiom boxedTrue : PolyBox(True)
        |
        |def observe (P: Prop)(box: PolyBox(P)): Nat := {
        |  match box returning Nat with
        |  | PolyBox.mk _ => Nat.zero
        |}
        |
        |{ observe(True, boxedTrue) }
        |""".stripMargin
    )
    assertEquals(PrettyPrinter.print(res), "0")
  }

  test("proof irrelevance is unchanged by constructor canonicalization") {
    typecheckDecls(
      """
        |axiom zeroEq : Eq(Nat, Nat.zero, Nat.zero)
        |
        |def mixed : Eq(
        |  Eq(Nat, Nat.zero, Nat.zero),
        |  zeroEq,
        |  Eq.refl(Nat.zero)
        |) := Eq.refl(zeroEq)
        |""".stripMargin
    )
  }

  test("casts along axiom-stuck proofs stay stuck") {
    val res = runProgram(
      """
        |axiom natIsBool : Eq(Type, Nat, Bool)
        |
        |{
        |  Eq.subst(natIsBool, Level.one, fun (A: Type): Type => A, Nat.zero)
        |}
        |""".stripMargin
    )
    res match {
      case _: Value.NeutralThunk =>
      case other                 => fail(s"Expected the cast to stay stuck, got $other")
    }
  }

  test("large-match reduction still requires the constructor result to match the exact proposition") {
    val res = runProgram(
      """
        |inductive Eq2 (A: Type) indices (left: A)(right: A) : Prop
        | | refl (value: A) : Eq2(A, value, value)
        |
        |axiom a : Nat
        |axiom b : Nat
        |axiom h : Eq2(Nat, a, b)
        |
        |def inspect (proof: Eq2(Nat, a, b)): Bool := {
        |  match proof returning Bool with
        |  | Eq2.refl _ => Bool.true
        |}
        |
        |{ inspect(h) }
        |""".stripMargin
    )
    res match {
      case _: Value.NeutralThunk =>
      case other                 => fail(s"Expected the constrained match to stay stuck, got $other")
    }
  }

  test("judgment-blocked proof matches re-fire after branch refinement") {
    typecheckDecls(
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (pred: Peano) : Peano
        |
        |inductive Eq2 indices (left: Peano)(right: Peano) : Prop
        | | refl (value: Peano) : Eq2(value, value)
        |
        |inductive IsZero indices (n: Peano) : Type
        | | mk : IsZero(Peano.zero)
        |
        |def works (n: Peano)(h: Eq2(n, Peano.zero)): Peano := {
        |  match n returning Peano with
        |  | Peano.zero => {
        |    let extracted : Peano := {
        |      match h returning Peano with
        |      | Eq2.refl v => v
        |    }
        |    let pin : IsZero(extracted) := IsZero.mk
        |    extracted
        |  }
        |  | Peano.succ _ => Peano.zero
        |}
        |
        |def frozen (n: Peano)(h: Eq2(n, Peano.zero)): Peano := {
        |  let extracted : Peano := {
        |    match h returning Peano with
        |    | Eq2.refl v => v
        |  }
        |  match n returning Peano with
        |  | Peano.zero => {
        |    let pin : IsZero(extracted) := IsZero.mk
        |    extracted
        |  }
        |  | Peano.succ _ => Peano.zero
        |}
        |""".stripMargin
    )
  }

  test("judgment blockers wake on any proposition dependency") {
    typecheckDecls(
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (pred: Peano) : Peano
        |
        |inductive Tag indices (t: Peano)(l: Peano)(r: Peano) : Prop
        | | mk (u: Peano)(v: Peano) : Tag(u, v, v)
        |
        |inductive IsZero indices (n: Peano) : Type
        | | mk : IsZero(Peano.zero)
        |
        |def wakeSecond (a: Peano)(b: Peano)(h: Tag(a, b, Peano.zero)): Peano := {
        |  let extracted : Peano := {
        |    match h returning Peano with
        |    | Tag.mk _ v => v
        |  }
        |  match b returning Peano with
        |  | Peano.zero => {
        |    let pin : IsZero(extracted) := IsZero.mk
        |    extracted
        |  }
        |  | Peano.succ _ => Peano.zero
        |}
        |""".stripMargin
    )
  }

  test("one judgment-blocked thunk re-fires under either independent dependency solve") {
    val program = parse(
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (pred: Peano) : Peano
        |
        |inductive Eq2 indices (left: Peano)(right: Peano) : Prop
        | | refl (value: Peano) : Eq2(value, value)
        |
        |def probe (a: Peano)(b: Peano)(h: Eq2(a, b)): Peano := {
        |  match h returning Peano with
        |  | Eq2.refl v => v
        |}
        |""".stripMargin
    )
    val env = program.decls.foldLeft(Prelude.default.checkedEnv) { case (current, decl) =>
      Interpreter.evalDecl(decl, current)
    }
    val peano = env("Peano")
    val a = FreshVar.freshVar("a", peano)
    val b = FreshVar.freshVar("b", peano)
    val proposition = Interpreter.evalApply(env("Eq2"), Vector(a, b))
    val h = Value.canonicalizeProof(Value.VProof(proposition))
    val thunk = Interpreter.evalApply(env("probe"), Vector(a, b, h)).asInstanceOf[Value.NeutralThunk]

    assertEquals(thunk.blockedOn, DepSet(a.id, b.id))

    val solveA = EqStore.empty.allow(DepSet(a.id)).addLink(a.id, b)
    val solveB = EqStore.empty.allow(DepSet(b.id)).addLink(b.id, a)
    val firedA = Interpreter.resolveInEqStore(thunk, solveA)
    val firedB = Interpreter.resolveInEqStore(thunk, solveB)

    assert(!firedA.isInstanceOf[Value.NeutralThunk])
    assert(!firedB.isInstanceOf[Value.NeutralThunk])
    assert(ValueEquivalence.defEq(firedA, b))
    assert(ValueEquivalence.defEq(firedB, a))
  }

  test("a judgment-blocked thunk re-sticks with only its remaining dependencies") {
    val program = parse(
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (pred: Peano) : Peano
        |
        |inductive Eq2 indices (left: Peano)(right: Peano) : Prop
        | | refl (value: Peano) : Eq2(value, value)
        |
        |def probe (a: Peano)(b: Peano)(h: Eq2(a, b)): Peano := {
        |  match h returning Peano with
        |  | Eq2.refl v => v
        |}
        |""".stripMargin
    )
    val env = program.decls.foldLeft(Prelude.default.checkedEnv) { case (current, decl) =>
      Interpreter.evalDecl(decl, current)
    }
    val peano = env("Peano")
    val a = FreshVar.freshVar("a", peano)
    val b = FreshVar.freshVar("b", peano)
    val c = FreshVar.freshVar("c", peano)
    val proposition = Interpreter.evalApply(env("Eq2"), Vector(a, b))
    val h = Value.canonicalizeProof(Value.VProof(proposition))
    val thunk = Interpreter.evalApply(env("probe"), Vector(a, b, h)).asInstanceOf[Value.NeutralThunk]
    val store = EqStore.empty.allow(DepSet(a.id)).addLink(a.id, c)

    val restuck = Interpreter.resolveInEqStore(thunk, store).asInstanceOf[Value.NeutralThunk]

    assert(!(restuck eq thunk))
    assertEquals(restuck.blockedOn, DepSet(b.id, c.id))
    assert(!restuck.blockedOn.contains(a.id))
    assert(Interpreter.resolveInEqStore(restuck, store) eq restuck)
  }

  test("a rigid-neutral match wakes when its scrutinee sort collapses to Prop") {
    val program = parse(
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (pred: Peano) : Peano
        |
        |inductive PolyUnit (u: Level) : Sort(u)
        | | mk : PolyUnit(u)
        |
        |axiom makerType (u: Level): (n: Peano) -> PolyUnit(u)
        |
        |def probe (u: Level)(x: PolyUnit(u)): Peano := {
        |  match x returning Peano with
        |  | PolyUnit.mk => Peano.zero
        |}
        |""".stripMargin
    )
    val env = program.decls.foldLeft(Prelude.default.checkedEnv) { case (current, decl) =>
      Interpreter.evalDecl(decl, current)
    }
    val u = FreshVar.freshVar("u", Value.LevelTpe)
    val polyUnitAtU = Interpreter.evalApply(env("PolyUnit"), Vector(u))
    val x = Value.VConst("x", Value.Symbol, polyUnitAtU)
    val thunk = Interpreter.evalApply(env("probe"), Vector(u, x)).asInstanceOf[Value.NeutralThunk]

    assertEquals(thunk.blockedOn, DepSet(u.id))

    val store = EqStore.empty.allow(DepSet(u.id)).addLink(u.id, Value.Level.zero)
    val fired = Interpreter.resolveInEqStore(thunk, store)
    assertEquals(PrettyPrinter.print(fired), "Peano.zero")

    val makerAtU = Interpreter.evalApply(env("makerType"), Vector(u))
    val blockedHead = FreshVar.freshVar("blockedHead", makerAtU.tpe)
    val zero = env("Peano.zero")
    // Construct the blocked application directly: ordinary creation would structure-eta-expand
    // this fieldless singleton before it can serve as a stuck scrutinee.
    val blockedScrutinee = Value.VBlockedApp(blockedHead, Vector(zero), polyUnitAtU, DepSet(blockedHead.id))
    val blockedThunk =
      Interpreter.evalApply(env("probe"), Vector(u, blockedScrutinee)).asInstanceOf[Value.NeutralThunk]

    assertEquals(blockedThunk.blockedOn, DepSet(blockedHead.id, u.id))
    val firedThroughSortCollapse = Interpreter.resolveInEqStore(blockedThunk, store)
    assertEquals(PrettyPrinter.print(firedThroughSortCollapse), "Peano.zero")
  }

  test("judgment blocker sets propagate through blocked applications") {
    typecheckDecls(
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (pred: Peano) : Peano
        |
        |inductive Eq2 indices (left: Peano)(right: Peano) : Prop
        | | refl (value: Peano) : Eq2(value, value)
        |
        |inductive IsZero indices (n: Peano) : Type
        | | mk : IsZero(Peano.zero)
        |
        |def appliedFrozen (n: Peano)(h: Eq2(n, Peano.zero)): Peano := {
        |  let f : (x: Peano) -> Peano := {
        |    match h returning (x: Peano) -> Peano with
        |    | Eq2.refl v => fun (_: Peano): Peano => v
        |  }
        |  let applied : Peano := f(Peano.zero)
        |  match n returning Peano with
        |  | Peano.zero => {
        |    let pin : IsZero(applied) := IsZero.mk
        |    applied
        |  }
        |  | Peano.succ _ => Peano.zero
        |}
        |""".stripMargin
    )
  }

  test("a diagonal equality axiom canonicalizes to refl and eliminates") {
    // Eq's declaration records that refl can be reconstructed exactly when the two endpoints
    // coincide. Runtime canonicalization follows that recipe; it does not run unification.
    val res = runProgram(
      """
        |axiom zeroEq : Eq(Nat, Nat.zero, Nat.zero)
        |
        |{
        |  Eq.subst(zeroEq, Level.one, fun (n: Nat): Type => Bool, Bool.true)
        |}
        |""".stripMargin
    )
    res match {
      case Value.VCtor(head, _, _) => assertEquals(head.name, "Bool.true")
      case other                   => fail(s"Expected the diagonal cast to reduce to Bool.true, got $other")
    }
  }

  test("a diagonal equality axiom has the same canonical constructor as refl") {
    val res = runProgram(
      """
        |axiom zeroEq : Eq(Nat, Nat.zero, Nat.zero)
        |
        |{ zeroEq }
        |""".stripMargin
    )
    res match {
      case Value.VCtor(head, fields, _) =>
        assertEquals(head.name, "Eq.refl")
        assertEquals(fields.length, 1)
        assertEquals(PrettyPrinter.print(fields.head), "0")
      case other => fail(s"Expected the canonical Eq.refl constructor, got $other")
    }
  }

  test("canonical diagonal proofs preserve congruence of execution") {
    typecheckDecls(
      """
        |axiom zeroEq : Eq(Nat, Nat.zero, Nat.zero)
        |
        |def cast (p: Eq(Nat, Nat.zero, Nat.zero)): Bool :=
        |  Eq.subst(p, Level.one, fun (_: Nat): Type => Bool, Bool.true)
        |
        |def should : Eq(Bool, cast(zeroEq), cast(Eq.refl(Nat.zero))) :=
        |  Eq.refl(cast(zeroEq))
        |""".stripMargin
    )
  }

  test("subsingleton elimination reduces through a canonical constructor") {
    val res = runProgram(
      """
        |{
        |  Eq.subst(Eq.refl(Nat.zero), Level.one, fun (n: Nat): Type => Bool, Bool.true)
        |}
        |""".stripMargin
    )
    res match {
      case Value.VCtor(head, _, _) => assertEquals(head.name, "Bool.true")
      case other                   => fail(s"Expected the refl cast to reduce to Bool.true, got $other")
    }
  }

  test("transparent singleton proof definitions canonicalize to constructor reduction") {
    val res = runProgram(
      """
        |def zeroEq : Eq(Nat, Nat.zero, Nat.zero) := Eq.refl(Nat.zero)
        |
        |{
        |  Eq.subst(zeroEq, Level.one, fun (n: Nat): Type => Bool, Bool.true)
        |}
        |""".stripMargin
    )
    res match {
      case Value.VCtor(head, _, _) => assertEquals(head.name, "Bool.true")
      case other                   => fail(s"Expected the transparent refl proof to reduce, got $other")
    }
  }

  test("canonical proof functions reconstruct constructor results") {
    typecheckDecls(
      """
        |def reflFn (n: Nat): Eq(Nat, n, n) := Eq.refl(n)
        |
        |def casted : Bool :=
        |  Eq.subst(reflFn(Nat.zero), Level.one, fun (_: Nat): Type => Bool, Bool.true)
        |
        |def shouldReduce : Eq(Bool, casted, Bool.true) := Eq.refl(casted)
        |""".stripMargin
    )
  }

  test("returned proof functions recursively reconstruct constructor results") {
    typecheckDecls(
      """
        |def makeRefl (_: Bool): (n: Nat) -> Eq(Nat, n, n) :=
        |  fun (n: Nat): Eq(Nat, n, n) => Eq.refl(n)
        |
        |def casted : Bool :=
        |  Eq.subst(makeRefl(Bool.true)(Nat.zero), Level.one, fun (_: Nat): Type => Bool, Bool.true)
        |
        |def shouldReduce : Eq(Bool, casted, Bool.true) := Eq.refl(casted)
        |""".stripMargin
    )
  }

  test("proof-valued lambdas become canonical eta-lambdas without rewriting their checked residual") {
    val core = parse(
      """
        |{
        |  fun (_: Bool): (P: Prop) -> (Q: Prop) -> P -> Or(P, Q) =>
        |    fun (P: Prop)(Q: Prop)(p: P): Or(P, Q) => Or.inl(Q, p)
        |}
        |""".stripMargin
    )
    val checked = TypeChecker.checkTerm(core.body.get, Prelude.default.checkedEnv)
    checked.value match {
      case Value.VLam(_, _, Value.LamBody.ProofEta) =>
      case other => fail(s"Expected the checked proof function to be the canonical proof eta-lambda, got $other")
    }
    val residual = checked.residual match {
      case ElabAst.Term.Body(Vector(), res, _) => res
      case other                               => other
    }
    residual match {
      case ElabAst.Term.Lam(
            _,
            ElabAst.Term.Lam(_, _: ElabAst.Term.App, _, _, _, _),
            _,
            _,
            _,
            _
          ) =>
      case other => fail(s"Expected the original constructor application in the checked residual, got $other")
    }
  }

  test("axiomatic proof functions also canonicalize to eta-lambdas") {
    val function = runProgram(
      """
        |axiom reflish (n: Nat): Eq(Nat, n, n)
        |
        |{ reflish }
        |""".stripMargin
    )
    function match {
      case Value.VLam(_, _, Value.LamBody.ProofEta) =>
      case other                                    => fail(s"Expected a canonical proof eta-lambda, got $other")
    }

    val applied = runProgram(
      """
        |axiom reflish (n: Nat): Eq(Nat, n, n)
        |
        |{
        |  Eq.subst(reflish(Nat.zero), Level.one, fun (_: Nat): Type => Bool, Bool.true)
        |}
        |""".stripMargin
    )
    applied match {
      case Value.VCtor(head, _, _) => assertEquals(head.name, "Bool.true")
      case other                   => fail(s"Expected the reconstructed equality result to reduce, got $other")
    }
  }

  test("recursive proof constructors reconstruct one finite layer at each match") {
    val res = runProgram(
      """
        |inductive Loop : Prop
        | | mk (next: Loop) : Loop
        |
        |axiom loop : Loop
        |
        |def inspectTwo (p: Loop): Bool := {
        |  match p returning Bool with
        |  | Loop.mk next => {
        |      match next returning Bool with
        |      | Loop.mk _ => Bool.true
        |    }
        |}
        |
        |{ inspectTwo(loop) }
        |""".stripMargin
    )
    res match {
      case Value.VCtor(head, _, _) => assertEquals(head.name, "Bool.true")
      case other                   => fail(s"Expected two finite constructor layers to reduce, got $other")
    }
  }

  test("erased multi-constructor proof applications do not select branches") {
    // Or is not certified for constructor preservation, so both constructors stay reachable.
    assertTypeError[MissingCase](
      """
        |def oneSided (p: Prop)(hp: p): p := {
        |  match Or.inl(p, hp) returning p with
        |  | Or.inl l => l
        |}
        |""".stripMargin
    )
  }

  test("empty elimination on a proof hypothesis stays stuck at check time and typechecks") {
    typecheckDecls(
      """
        |def fromFalse (h: False): Nat := {
        |  match h returning Nat with
        |}
        |""".stripMargin
    )
  }

  test("erased proofs quote canonically through the proof intrinsic") {
    val prop = Value.VConst("P", Value.Symbol, Value.PropTpe)
    ValueQuote.quoteTerm(Value.VProof(prop), ValueQuote.QuoteContext(Map.empty), Span(0, 0)) match {
      case ElabAst.Term.Proof(ElabAst.Term.GlobalRef("P", _), _) =>
      case other                                                 => fail(s"Expected proof(P), got $other")
    }
  }

  test("let-ascribed proof values stay collapsed through evalBody") {
    // evalBody's let ascription must go through Value.ascribe (a collapse point); the putLocal
    // collapse-invariant assertion would reject an uncollapsed prop-typed binding.
    val res = runProgram(
      """
        |axiom P : Prop
        |axiom axP : P
        |
        |{
        |  let h : P := axP
        |  h
        |}
        |""".stripMargin
    )
    res match {
      case p: Value.VProof =>
        p.tpe match {
          case Value.VConst(name, _, _) => assertEquals(name, "P")
          case other                    => fail(s"Expected the proposition P, got $other")
        }
      case other => fail(s"Expected a collapsed proof of P, got $other")
    }
  }
}
