package com.raccoonlang

import com.raccoonlang.CoreAst.{Term => CTerm}
import com.raccoonlang.Value._

class ValueOpsTests extends munit.FunSuite with DiagnosticAssertions {
  private val span = Span(0, 0)
  private val valueType: Value = Sorts.Type
  private val typeRef: CoreAst.Term = CTerm.GlobalRef("Type", span)
  private val typeToTypeClassifier: Value.VSort =
    Sorts.sort(Level.succ(Level.one), Value.Kind.unr)

  private def symbolicValue(name: String): VConst =
    VConst(name, Symbol, valueType)

  private def solve(v: Var, solution: Value): EqStore =
    EqStore.empty.allow(DepSet(v.id)).addLink(v.id, solution)

  test("materializeEnv rewrites solved locals") {
    val ref = CoreAst.LocalRef(0, "x")
    val x = FreshVar.freshVar("x", valueType)
    val solution = symbolicValue("Solved")
    val env = Env.empty.putLocal(ref, x)

    val materialized = ValueOps.materializeEnv(env, solve(x, solution))

    assertEquals(materialized(ref), solution)
    assert(!materialized(ref).synDeps.contains(x.id))
  }

  test("materialize reuses one canonical result for a shared value in a single DAG") {
    val x = FreshVar.freshVar("x", valueType)
    val solution = symbolicValue("Solved")
    var root: Value = VConst("Shared", Symbol, x)
    var depth = 0
    while (depth < 25) {
      root = VApp(symbolicValue(s"Node$depth"), Vector(root, root), valueType)
      depth += 1
    }

    val materialized = ValueOps.materialize(root, solve(x, solution)).asInstanceOf[VApp]

    var node: Value = materialized
    depth = 0
    while (depth < 25) {
      val app = node.asInstanceOf[VApp]
      assert(app.storedArgs(0) eq app.storedArgs(1))
      node = app.storedArgs(0)
      depth += 1
    }
    assert(node.asInstanceOf[VConst].tpe eq solution)
  }

  test("materialization memo is scoped to its EqStore") {
    val x = FreshVar.freshVar("x", valueType)
    val shared = VConst("Shared", Symbol, x)
    val root = VApp(symbolicValue("Root"), Vector(shared, shared), valueType)
    val leftSolution = symbolicValue("LeftSolution")
    val rightSolution = symbolicValue("RightSolution")

    val left = ValueOps.materialize(root, solve(x, leftSolution)).asInstanceOf[VApp]
    val right = ValueOps.materialize(root, solve(x, rightSolution)).asInstanceOf[VApp]

    assertEquals(left.storedArgs(0).asInstanceOf[VConst].tpe, leftSolution)
    assertEquals(right.storedArgs(0).asInstanceOf[VConst].tpe, rightSolution)
    assert(left.storedArgs(0) ne right.storedArgs(0))
  }

  test("materializeEnv leaves globals closed") {
    val ref = CoreAst.LocalRef(0, "x")
    val x = FreshVar.freshVar("x", valueType)
    val solution = symbolicValue("Solved")
    val global = symbolicValue("Global")
    val base = Env.empty
      .putGlobal("global", global)
      .putLocal(ref, x)
    val materialized = ValueOps.materializeEnv(base, solve(x, solution))

    assertEquals(materialized("global"), global)
    assertEquals(materialized(ref), solution)
  }

  test("closeForEval returns an ordinary env containing only captured locals") {
    val keptRef = CoreAst.LocalRef(0, "kept")
    val uncapturedRef = CoreAst.LocalRef(1, "uncaptured")
    val argRef = CoreAst.LocalRef(2, "arg")
    val kept = symbolicValue("Kept")
    val uncaptured = symbolicValue("Uncaptured")
    val arg = symbolicValue("Arg")
    val env = Env.empty.putLocal(keptRef, kept).putLocal(uncapturedRef, uncaptured)
    val capturedRefs = CapturedRefs.getCapturedRefs(CTerm.LocalRef(keptRef, span), env)

    val closed = env.closeForEval(capturedRefs)

    assertEquals(closed.locals.keySet, Set(keptRef))
    assertEquals(closed(keptRef), kept)
    interceptError[NotFound](closed(uncapturedRef))
    assertEquals(closed.putLocal(argRef, arg)(argRef), arg)
  }

  test("closed env omits uncaptured locals and materialization preserves that boundary") {
    val keptRef = CoreAst.LocalRef(0, "kept")
    val uncapturedRef = CoreAst.LocalRef(1, "uncaptured")
    val kept = FreshVar.freshVar("kept", valueType)
    val uncaptured = FreshVar.freshVar("uncaptured", valueType)
    val solution = symbolicValue("KeptSolution")
    val env = Env.empty.putLocal(keptRef, kept).putLocal(uncapturedRef, uncaptured)
    val capturedRefs = CapturedRefs.getCapturedRefs(CTerm.LocalRef(keptRef, span), env)

    val closed = env.closeForEval(capturedRefs)

    assertEquals(closed(keptRef), kept)
    interceptError[NotFound](closed(uncapturedRef))

    val materialized = ValueOps.materializeEnv(closed, solve(kept, solution))
    assertEquals(materialized(keptRef), solution)
    interceptError[NotFound](materialized(uncapturedRef))
  }

  test("materialize rewrites shared VLam environments and Pi types used by execution") {
    val capturedRef = CoreAst.LocalRef(0, "captured")
    val argRef = CoreAst.LocalRef(1, "arg")
    val captured = FreshVar.freshVar("captured", valueType)
    val solution = symbolicValue("CapturedSolution")
    val runtimeEnv = Env.empty.putGlobal("Type", valueType).putLocal(capturedRef, captured)

    val binder = CoreAst.Binder(argRef, typeRef, span, CoreAst.BinderSite.Function, BinderMode.Explicit)
    val pi = VPi(
      runtimeEnv,
      Vector(binder),
      _ => valueType,
      Value.Kind.unr,
      captured.synDeps,
      ValueId.LocalId(NodeId.fresh(), Vector(captured)),
      () => typeToTypeClassifier,
      isPropValued = false
    )
    val piTerm = CTerm.Pi(
      Vector(CoreAst.Binder(argRef, typeRef, span, CoreAst.BinderSite.Function, BinderMode.Explicit)),
      typeRef,
      CoreAst.Closure.unrestricted(span),
      span,
      NodeId.fresh()
    )
    val lamTerm = CTerm.Lam(
      piTerm,
      CTerm.LocalRef(capturedRef, span),
      span,
      NodeId.fresh(),
      name = None,
      recursion = None
    )
    val lam = VLam(pi, ValueId.LocalId(NodeId.fresh(), Vector(captured)), LamBody.Core(lamTerm, runtimeEnv))
    val siblingLam =
      VLam(pi, ValueId.LocalId(NodeId.fresh(), Vector(captured)), LamBody.Core(lamTerm, runtimeEnv))

    val materializedPair = ValueOps
      .materialize(VApp(symbolicValue("Pair"), Vector(lam, siblingLam, pi), valueType), solve(captured, solution))
      .asInstanceOf[VApp]
    val materialized = materializedPair.storedArgs(0).asInstanceOf[VLam]
    val materializedSibling = materializedPair.storedArgs(1).asInstanceOf[VLam]
    val materializedPiArgument = materializedPair.storedArgs(2).asInstanceOf[VPi]

    assert(materialized.tpe eq materializedSibling.tpe)
    assert(materialized.tpe eq materializedPiArgument)
    assertEquals(materialized.tpe.env(capturedRef), solution)
    val materializedBodyEnv = materialized.body match {
      case LamBody.Core(_, materializedEnv) =>
        assertEquals(materializedEnv(capturedRef), solution)
        materializedEnv
      case other => fail(s"Expected materialized core lambda body, got $other")
    }
    assert(materialized.tpe.env eq materializedBodyEnv)
    assert(!materialized.synDeps.contains(captured.id))
    assertEquals(Interpreter.evalApply(materialized, Vector(symbolicValue("Arg"))), solution)
  }

  test("materialize rewrites a function type's closure kind, which its key counts") {
    val (id, mentionedValue) = FreshVar.freshValue("k", KindTpe)
    val mentioned = mentionedValue.asInstanceOf[Kind]
    val solution = Kind.lin
    val binder =
      CoreAst.Binder(CoreAst.LocalRef(0, "x"), typeRef, span, CoreAst.BinderSite.Function, BinderMode.Explicit)
    val node = NodeId.fresh()
    def pi(kind: Kind): VPi =
      VPi(
        Env.empty.putGlobal("Type", valueType),
        Vector(binder),
        _ => valueType,
        kind,
        kind.synDeps,
        ValueId.LocalId(node, Vector.empty),
        () => typeToTypeClassifier,
        isPropValued = false
      )
    val materialized =
      ValueOps.materialize(pi(mentioned), EqStore.empty.allow(DepSet(id)).addLink(id, solution)).asInstanceOf[VPi]
    assertEquals(materialized.closureKind: Value, solution)
    assertEquals(materialized.key, pi(solution).key)
    assertNotEquals(pi(mentioned).key, pi(solution).key)
  }

  test("materialized Pi classifier stays lazy and resolves in a fresh session when forced") {
    val (levelId, levelValue) = FreshVar.freshValue("u", LevelTpe)
    val dependentSort = Sorts.sort(levelValue.asInstanceOf[Level], Kind.unr)
    val binder = CoreAst.Binder(
      CoreAst.LocalRef(0, "x"),
      typeRef,
      span,
      CoreAst.BinderSite.Function,
      BinderMode.Explicit
    )
    var classifierForces = 0
    val pi = VPi(
      Env.empty.putGlobal("Type", valueType),
      Vector(binder),
      _ => valueType,
      Kind.unr,
      dependentSort.synDeps,
      ValueId.LocalId(NodeId.fresh(), Vector.empty),
      () => {
        classifierForces += 1
        dependentSort
      },
      isPropValued = false
    )
    val store = EqStore.empty.allow(DepSet(levelId)).addLink(levelId, Level.const(4))

    val materialized = ValueOps.materialize(pi, store).asInstanceOf[VPi]

    assertEquals(classifierForces, 0)
    val classifier = materialized.tpe.asInstanceOf[VSort]
    assertEquals(classifier.level, Level.const(4))
    assertEquals(classifierForces, 1)
  }

  test("under-captured core lambda fails on uncaptured local access") {
    val capturedRef = CoreAst.LocalRef(0, "captured")
    val argRef = CoreAst.LocalRef(1, "arg")
    val captured = symbolicValue("Captured")
    val env = Env.empty.putGlobal("Type", valueType).putLocal(capturedRef, captured)
    val runtimeEnv = env.closeForEval(Set.empty)

    val binder = CoreAst.Binder(argRef, typeRef, span, CoreAst.BinderSite.Function, BinderMode.Explicit)
    val pi = VPi(
      runtimeEnv,
      Vector(binder),
      _ => valueType,
      Value.Kind.unr,
      DepSet.empty,
      ValueId.LocalId(NodeId.fresh(), Vector.empty),
      () => typeToTypeClassifier,
      isPropValued = false
    )
    val piTerm = CTerm.Pi(
      Vector(CoreAst.Binder(argRef, typeRef, span, CoreAst.BinderSite.Function, BinderMode.Explicit)),
      typeRef,
      CoreAst.Closure.unrestricted(span),
      span,
      NodeId.fresh()
    )
    val lamTerm = CTerm.Lam(
      piTerm,
      CTerm.LocalRef(capturedRef, span),
      span,
      NodeId.fresh(),
      name = None,
      recursion = None
    )
    val lam = VLam(pi, ValueId.LocalId(NodeId.fresh(), Vector.empty), LamBody.Core(lamTerm, runtimeEnv))

    interceptError[NotFound](Interpreter.evalApply(lam, Vector(symbolicValue("Arg"))))
  }

  test("core lambda execution uses the lambda body closure, not only the Pi closure") {
    val capturedRef = CoreAst.LocalRef(0, "captured")
    val argRef = CoreAst.LocalRef(1, "arg")
    val captured = symbolicValue("Captured")
    val env = Env.empty.putGlobal("Type", valueType).putLocal(capturedRef, captured)

    val piTerm = CTerm.Pi(
      Vector(CoreAst.Binder(argRef, typeRef, span, CoreAst.BinderSite.Function, BinderMode.Explicit)),
      typeRef,
      CoreAst.Closure.unrestricted(span),
      span,
      NodeId.fresh()
    )
    val vpi = Interpreter.evalPi(piTerm, env)
    val lamTerm = CTerm.Lam(
      piTerm,
      CTerm.LocalRef(capturedRef, span),
      span,
      NodeId.fresh(),
      name = None,
      recursion = None
    )
    val lam = Interpreter.evalLam(lamTerm, vpi, env).asInstanceOf[VLam]

    interceptError[NotFound](lam.tpe.env(capturedRef))
    lam.body match {
      case LamBody.Core(_, bodyEnv) => assertEquals(bodyEnv(capturedRef), captured)
      case other                    => fail(s"Expected core lambda body, got $other")
    }
    assertEquals(Interpreter.evalApply(lam, Vector(symbolicValue("Arg"))), captured)
  }

  test("materialize rewrites VNeutralThunk match environment before forcing") {
    val capturedRef = CoreAst.LocalRef(0, "captured")
    val scrutRef = CoreAst.LocalRef(1, "scrut")
    val captured = FreshVar.freshVar("captured", valueType)
    val scrut = FreshVar.freshVar("scrut", valueType)
    val solution = symbolicValue("ThunkSolution")
    val runtimeEnv = Env.empty.putLocal(capturedRef, captured).putLocal(scrutRef, scrut)
    val head = ConstructorHead("C", numErasedFamilyArgs = 0, totalArity = 0, valueType)
    val ctor = VCtor(head, Vector.empty, valueType)
    val matchTerm = CTerm.Match(
      CTerm.LocalRef(scrutRef, span),
      motive = typeRef,
      cases = Vector(
        CoreAst.Case(
          "C",
          isFullyQualified = true,
          Vector.empty,
          CTerm.LocalRef(capturedRef, span),
          span
        )
      ),
      wildcard = None,
      equation = None,
      span,
      NodeId.fresh()
    )
    val thunk = NeutralThunk(
      matchTerm,
      runtimeEnv,
      ValueId.LocalId(NodeId.fresh(), Vector(scrut, captured)),
      valueType,
      DepSet(scrut.id)
    )

    val eqCaptured = solve(captured, solution)
    val materialized = ValueOps.materialize(thunk, eqCaptured).asInstanceOf[NeutralThunk]

    assertEquals(materialized.env(capturedRef), solution)
    assertEquals(materialized.env(scrutRef), scrut)

    assert(!materialized.synDeps.contains(captured.id))
    assert(materialized.synDeps.contains(scrut.id))
    assertEquals(materialized.blockedOn, DepSet(scrut.id))

    val eqAll = eqCaptured.allow(DepSet(scrut.id)).addLink(scrut.id, ctor)
    assertEquals(Interpreter.resolveInEqStore(materialized, eqAll), solution)
  }

  test("resolveInEqStore uses the blocker set rather than all thunk dependencies") {
    val capturedRef = CoreAst.LocalRef(0, "captured")
    val scrutRef = CoreAst.LocalRef(1, "scrut")
    val captured = FreshVar.freshVar("captured", valueType)
    val scrut = FreshVar.freshVar("scrut", valueType)
    val runtimeEnv = Env.empty.putLocal(capturedRef, captured).putLocal(scrutRef, scrut)
    val matchTerm = CTerm.Match(
      CTerm.LocalRef(scrutRef, span),
      motive = typeRef,
      cases = Vector(CoreAst.Case("C", isFullyQualified = true, Vector.empty, CTerm.LocalRef(capturedRef, span), span)),
      wildcard = None,
      equation = None,
      span,
      NodeId.fresh()
    )
    val thunk = NeutralThunk(
      matchTerm,
      runtimeEnv,
      ValueId.LocalId(NodeId.fresh(), Vector(scrut, captured)),
      valueType,
      DepSet(scrut.id)
    )
    val store = solve(captured, symbolicValue("CapturedSolution"))

    assert(thunk.synDeps.contains(captured.id))
    assert(!thunk.blockedOn.contains(captured.id))
    assert(Interpreter.resolveInEqStore(thunk, store) eq thunk)
  }

  test("blocked application views preserve every blocker") {
    val first = FreshVar.freshVar("first", valueType)
    val second = FreshVar.freshVar("second", valueType)
    val blockers = DepSet(first.id, second.id)
    val app = VBlockedApp(symbolicValue("Head"), Vector(symbolicValue("Arg")), valueType, blockers)

    app match {
      case VBlockedApp(_, _, _, actual) => assertEquals(actual, blockers)
      case other                        => fail(s"Expected a blocked application, got $other")
    }
    app match {
      case Blocker(actual) => assertEquals(actual, blockers)
      case other           => fail(s"Expected the application to expose its blocker set, got $other")
    }
  }

  test("blocked match closures keep only referenced runtime locals") {
    val capturedRef = CoreAst.LocalRef(0, "captured")
    val unusedRef = CoreAst.LocalRef(1, "unused")
    val scrutRef = CoreAst.LocalRef(2, "scrut")
    val captured = symbolicValue("Captured")
    val unused = FreshVar.freshVar("unused", valueType)
    val scrut = FreshVar.freshVar("scrut", valueType)
    val env = Env.empty
      .putGlobal("Type", valueType)
      .putLocal(capturedRef, captured)
      .putLocal(unusedRef, unused)
      .putLocal(scrutRef, scrut)
    val matchTerm = CTerm.Match(
      CTerm.LocalRef(scrutRef, span),
      motive = typeRef,
      cases = Vector(
        CoreAst.Case(
          "C",
          isFullyQualified = true,
          Vector.empty,
          CTerm.LocalRef(capturedRef, span),
          span
        )
      ),
      wildcard = None,
      equation = None,
      span,
      NodeId.fresh()
    )

    val blocked = Interpreter.evalTerm(matchTerm, env).asInstanceOf[NeutralThunk]
    val closed = blocked.env

    assertEquals(closed(capturedRef), captured)
    interceptError[NotFound](closed(unusedRef))
    assertEquals(closed(scrutRef), scrut)

    assert(!blocked.synDeps.contains(unused.id))
    assert(blocked.synDeps.contains(scrut.id))
    assertEquals(blocked.blockedOn, DepSet(scrut.id))
  }

  test("constructor equality accounts for result type") {
    val head = ConstructorHead("C", numErasedFamilyArgs = 0, totalArity = 0, valueType)
    val resultA = symbolicValue("ResultA")
    val resultB = symbolicValue("ResultB")
    val ctorA = VCtor(head, Vector.empty, resultA)
    val ctorB = VCtor(head, Vector.empty, resultB)

    assertNotEquals(ctorA.key, ctorB.key)
    assert(!ValueEquivalence.defEq(ctorA, ctorB))
  }
}
