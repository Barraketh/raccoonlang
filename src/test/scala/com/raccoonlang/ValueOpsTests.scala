package com.raccoonlang

import com.raccoonlang.CoreAst.{Term => CTerm}
import com.raccoonlang.Value._

class ValueOpsTests extends munit.FunSuite {
  private val span = Span(0, 0)
  private val valueType: Value = TypeTpe
  private val typeRef: CoreAst.Term = CTerm.GlobalRef("Type", span)
  private val typeToTypeClassifier: Value.VSort = VSort(Level.succ(Level.one))

  private def nodeId(start: Int): AstNodeId = AstNodeId(None, start)

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
    intercept[NotFound](closed(uncapturedRef))
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
    intercept[NotFound](closed(uncapturedRef))

    val materialized = ValueOps.materializeEnv(closed, solve(kept, solution))
    assertEquals(materialized(keptRef), solution)
    intercept[NotFound](materialized(uncapturedRef))
  }

  test("materialize rewrites VLam core environment used by execution") {
    val capturedRef = CoreAst.LocalRef(0, "captured")
    val argRef = CoreAst.LocalRef(1, "arg")
    val captured = FreshVar.freshVar("captured", valueType)
    val solution = symbolicValue("CapturedSolution")
    val runtimeEnv = Env.empty.putGlobal("Type", valueType).putLocal(capturedRef, captured)

    val binder = CoreAst.Binder(argRef, typeRef, span)
    val pi = VPi(
      runtimeEnv,
      Vector(binder),
      _ => valueType,
      captured.synDeps,
      ValueId.LocalId(nodeId(1), Vector(captured)),
      () => typeToTypeClassifier
    )
    val piTerm = CTerm.Pi(
      Vector(CoreAst.Binder(argRef, typeRef, span)),
      typeRef,
      Span.synthetic()
    )
    val lamTerm = CTerm.Lam(
      piTerm,
      CTerm.LocalRef(capturedRef, span),
      span,
      name = None,
      recursion = None
    )
    val lam = VLam(pi, ValueId.LocalId(nodeId(2), Vector(captured)), LamBody.Core(lamTerm, runtimeEnv))

    val materialized = ValueOps.materialize(lam, solve(captured, solution)).asInstanceOf[VLam]

    assertEquals(materialized.tpe.env(capturedRef), solution)
    materialized.body match {
      case LamBody.Core(_, materializedEnv) => assertEquals(materializedEnv(capturedRef), solution)
      case other                            => fail(s"Expected materialized core lambda body, got $other")
    }
    assert(!materialized.synDeps.contains(captured.id))
    assertEquals(Interpreter.evalApply(materialized, Vector(symbolicValue("Arg"))), solution)
  }

  test("under-captured core lambda fails on uncaptured local access") {
    val capturedRef = CoreAst.LocalRef(0, "captured")
    val argRef = CoreAst.LocalRef(1, "arg")
    val captured = symbolicValue("Captured")
    val env = Env.empty.putGlobal("Type", valueType).putLocal(capturedRef, captured)
    val runtimeEnv = env.closeForEval(Set.empty)

    val binder = CoreAst.Binder(argRef, typeRef, span)
    val pi = VPi(
      runtimeEnv,
      Vector(binder),
      _ => valueType,
      DepSet.empty,
      ValueId.LocalId(nodeId(1), Vector.empty),
      () => typeToTypeClassifier
    )
    val piTerm = CTerm.Pi(
      Vector(CoreAst.Binder(argRef, typeRef, span)),
      typeRef,
      Span.synthetic()
    )
    val lamTerm = CTerm.Lam(
      piTerm,
      CTerm.LocalRef(capturedRef, span),
      span,
      name = None,
      recursion = None
    )
    val lam = VLam(pi, ValueId.LocalId(nodeId(2), Vector.empty), LamBody.Core(lamTerm, runtimeEnv))

    intercept[NotFound](Interpreter.evalApply(lam, Vector(symbolicValue("Arg"))))
  }

  test("core lambda execution uses the lambda body closure, not only the Pi closure") {
    val capturedRef = CoreAst.LocalRef(0, "captured")
    val argRef = CoreAst.LocalRef(1, "arg")
    val captured = symbolicValue("Captured")
    val env = Env.empty.putGlobal("Type", valueType).putLocal(capturedRef, captured)

    val piTerm = CTerm.Pi(
      Vector(CoreAst.Binder(argRef, typeRef, span)),
      typeRef,
      Span.synthetic()
    )
    val vpi = Interpreter.evalPi(piTerm, env)
    val lamTerm = CTerm.Lam(
      piTerm,
      CTerm.LocalRef(capturedRef, span),
      span,
      name = None,
      recursion = None
    )
    val lam = Interpreter.evalLam(lamTerm, vpi, env).asInstanceOf[VLam]

    intercept[NotFound](lam.tpe.env(capturedRef))
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
      motive = None,
      cases = Vector(
        CoreAst.Case(
          "C",
          isFullyQualified = true,
          Vector.empty,
          CTerm.LocalRef(capturedRef, span),
          span
        )
      ),
      Span.synthetic()
    )
    val thunk = NeutralThunk(
      matchTerm,
      runtimeEnv,
      ValueId.LocalId(nodeId(3), Vector(scrut, captured)),
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
      motive = None,
      cases = Vector(CoreAst.Case("C", isFullyQualified = true, Vector.empty, CTerm.LocalRef(capturedRef, span), span)),
      Span.synthetic()
    )
    val thunk = NeutralThunk(
      matchTerm,
      runtimeEnv,
      ValueId.LocalId(nodeId(4), Vector(scrut, captured)),
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
      .putLocal(capturedRef, captured)
      .putLocal(unusedRef, unused)
      .putLocal(scrutRef, scrut)
    val matchTerm = CTerm.Match(
      CTerm.LocalRef(scrutRef, span),
      motive = None,
      cases = Vector(
        CoreAst.Case(
          "C",
          isFullyQualified = true,
          Vector.empty,
          CTerm.LocalRef(capturedRef, span),
          span
        )
      ),
      Span.synthetic()
    )

    val blocked = Interpreter.evalTerm(matchTerm, env).asInstanceOf[NeutralThunk]
    val closed = blocked.env

    assertEquals(closed(capturedRef), captured)
    intercept[NotFound](closed(unusedRef))
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
