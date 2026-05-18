package com.raccoonlang

import com.raccoonlang.ElabAst.{Term => ETerm}
import com.raccoonlang.Value._

class ValueOpsTests extends munit.FunSuite {
  private val span = Span(0, 0)
  private val valueType: Value = TypeTpe
  private val typeRef: ElabAst.TypeTerm = ETerm.GlobalRef("Type", span)
  private val typeToTypeClassifier: Value.Universe = VSort(Level.succ(Level.one))

  private def binderType(term: ElabAst.TypeTerm): ElabAst.BinderType = {
    val pattern = ElabAst.TypePattern.Type(term)
    ElabAst.BinderType.TypePattern(pattern, pattern.span)
  }

  private def nodeId(start: Int): AstNodeId = AstNodeId(None, start)

  private def symbolicValue(name: String): VConst =
    VConst(name, Symbol, valueType)

  private def solve(v: Var, solution: Value): EqStore =
    EqStore.empty.allow(DepSet(v.id)).addLink(v.id, solution)

  test("materializeEnv rewrites locals without carrying local instance candidates") {
    val ref = CoreAst.LocalRef(0, "x")
    val x = FreshVar.freshVar("x", valueType)
    val solution = symbolicValue("Solved")
    val term = ETerm.LocalRef(ref, span)
    val env = TypecheckEnv.empty.putLocal(ref, x, Some("candidate"), Some(term))

    val materialized = ValueOps.materializeEnv(env, solve(x, solution))

    assertEquals(materialized(ref), solution)
    assert(materialized.isInstanceOf[RuntimeEnv])
    assert(!materialized(ref).synDeps.contains(x.id))
  }

  test("closed runtime env prunes unused locals and materialization preserves pruned slots") {
    val keptRef = CoreAst.LocalRef(0, "kept")
    val prunedRef = CoreAst.LocalRef(1, "pruned")
    val kept = FreshVar.freshVar("kept", valueType)
    val pruned = FreshVar.freshVar("pruned", valueType)
    val solution = symbolicValue("KeptSolution")
    val env = TypecheckEnv.empty.putLocal(keptRef, kept).putLocal(prunedRef, pruned)
    val capturedIndexes = CapturedIndexes.getCapturedIndexes(ETerm.LocalRef(keptRef, span), env)

    val closed = env.closeForEval(Some(capturedIndexes))

    assertEquals(closed(keptRef), kept)
    intercept[WTF](closed(prunedRef))

    val materialized = ValueOps.materializeEnv(closed, solve(kept, solution))
    assertEquals(materialized(keptRef), solution)
    intercept[WTF](materialized(prunedRef))
  }

  test("materialize rewrites VLam core environment used by execution") {
    val capturedRef = CoreAst.LocalRef(0, "captured")
    val argRef = CoreAst.LocalRef(1, "arg")
    val captured = FreshVar.freshVar("captured", valueType)
    val solution = symbolicValue("CapturedSolution")
    val env = TypecheckEnv.empty.putGlobal("Type", valueType).putLocal(capturedRef, captured)
    val runtimeEnv = RuntimeEnv(env.globals, env.locals)

    val binder = VBinder(argRef, binderType(typeRef), typeRef, Vector.empty)
    val pi = VPi(
      runtimeEnv,
      Vector(binder),
      (_, _) => valueType,
      captured.synDeps,
      ValueId.LocalId(nodeId(1), Vector(captured)),
      typeToTypeClassifier
    )
    val piTerm = ETerm.Pi(
      Vector(ElabAst.Binder(argRef, binderType(typeRef), span)),
      typeRef,
      typeToTypeClassifier,
      span
    )
    val lamTerm = ETerm.Lam(
      piTerm,
      Vector.empty,
      ETerm.LocalRef(capturedRef, span),
      span,
      name = None,
      isStable = false
    )
    val lam =
      VLam(pi, ValueId.LocalId(nodeId(2), Vector(captured)), isStable = false, LamBody.Core(lamTerm, runtimeEnv))

    val materialized = ValueOps.materialize(lam, solve(captured, solution)).asInstanceOf[VLam]

    assertEquals(materialized.tpe.env(capturedRef), solution)
    materialized.body match {
      case LamBody.Core(_, materializedEnv) => assertEquals(materializedEnv(capturedRef), solution)
      case other                            => fail(s"Expected materialized core lambda body, got $other")
    }
    assert(!materialized.synDeps.contains(captured.id))
    assertEquals(Interpreter.evalApply(materialized, Vector(symbolicValue("Arg")))(EqStore.empty), solution)
  }

  test("under-captured core lambda fails on pruned local access") {
    val capturedRef = CoreAst.LocalRef(0, "captured")
    val argRef = CoreAst.LocalRef(1, "arg")
    val captured = symbolicValue("Captured")
    val env = TypecheckEnv.empty.putGlobal("Type", valueType).putLocal(capturedRef, captured)
    val runtimeEnv = env.closeForEval()

    val binder = VBinder(argRef, binderType(typeRef), typeRef, Vector.empty)
    val pi = VPi(
      runtimeEnv,
      Vector(binder),
      (_, _) => valueType,
      DepSet.empty,
      ValueId.LocalId(nodeId(1), Vector.empty),
      typeToTypeClassifier
    )
    val piTerm = ETerm.Pi(
      Vector(ElabAst.Binder(argRef, binderType(typeRef), span)),
      typeRef,
      typeToTypeClassifier,
      span
    )
    val lamTerm = ETerm.Lam(
      piTerm,
      Vector.empty,
      ETerm.LocalRef(capturedRef, span),
      span,
      name = None,
      isStable = false
    )
    val lam = VLam(pi, ValueId.LocalId(nodeId(2), Vector.empty), isStable = false, LamBody.Core(lamTerm, runtimeEnv))

    intercept[WTF](Interpreter.evalApply(lam, Vector(symbolicValue("Arg")))(EqStore.empty))
  }

  test("core lambda execution uses the lambda body closure, not only the Pi closure") {
    implicit val eqStore: EqStore = EqStore.empty

    val capturedRef = CoreAst.LocalRef(0, "captured")
    val argRef = CoreAst.LocalRef(1, "arg")
    val captured = symbolicValue("Captured")
    val env = TypecheckEnv.empty.putGlobal("Type", valueType).putLocal(capturedRef, captured)

    val piTerm = ETerm.Pi(
      Vector(ElabAst.Binder(argRef, binderType(typeRef), span)),
      typeRef,
      typeToTypeClassifier,
      span
    )
    val vpi = Interpreter.evalPi(piTerm, env, piTerm.binders.map(com.raccoonlang.telescope.TypePatternOps.toVBinder))
    val lamTerm = ETerm.Lam(
      piTerm,
      Vector.empty,
      ETerm.LocalRef(capturedRef, span),
      span,
      name = None,
      isStable = false
    )
    val lam = Interpreter.evalLam(lamTerm, vpi, env)

    intercept[WTF](lam.tpe.env(capturedRef))
    lam.body match {
      case LamBody.Core(_, bodyEnv) => assertEquals(bodyEnv(capturedRef), captured)
      case other                    => fail(s"Expected core lambda body, got $other")
    }
    assertEquals(Interpreter.evalApply(lam, Vector(symbolicValue("Arg"))), captured)
  }

  test("materialize rewrites VBlockedThunk match environment before forcing") {
    val capturedRef = CoreAst.LocalRef(0, "captured")
    val scrutRef = CoreAst.LocalRef(1, "scrut")
    val captured = FreshVar.freshVar("captured", valueType)
    val scrut = FreshVar.freshVar("scrut", valueType)
    val solution = symbolicValue("ThunkSolution")
    val env = TypecheckEnv.empty.putLocal(capturedRef, captured).putLocal(scrutRef, scrut)
    val runtimeEnv = RuntimeEnv(env.globals, env.locals)
    val head = ConstructorHead("C", numErased = 0, totalArity = 0, valueType, isStruct = false)
    val ctor = VCtor(head, Vector.empty, valueType)
    val matchTerm = ETerm.Match(
      ETerm.LocalRef(scrutRef, span),
      motive = None,
      cases = Vector(
        ElabAst.Case(
          "C",
          Vector.empty,
          ETerm.LocalRef(capturedRef, span),
          span
        )
      ),
      span
    )
    val thunk = VBlockedThunk(
      BlockedThunkBody.Match(matchTerm, runtimeEnv),
      ValueId.LocalId(nodeId(3), Vector(scrut, captured)),
      valueType,
      scrut.id
    )

    val eqCaptured = solve(captured, solution)
    val materialized = ValueOps.materialize(thunk, eqCaptured).asInstanceOf[VBlockedThunk]

    materialized.body match {
      case BlockedThunkBody.Match(_, materializedEnv) =>
        assertEquals(materializedEnv(capturedRef), solution)
        assertEquals(materializedEnv(scrutRef), scrut)
      case other => fail(s"Expected materialized match thunk body, got $other")
    }
    assert(!materialized.synDeps.contains(captured.id))
    assert(materialized.synDeps.contains(scrut.id))

    val eqAll = eqCaptured.allow(DepSet(scrut.id)).addLink(scrut.id, ctor)
    assertEquals(Interpreter.resolveInEqStore(materialized)(eqAll).value, solution)
  }

  test("blocked match closures rewrite locals to referenced runtime slots") {
    val capturedRef = CoreAst.LocalRef(0, "captured")
    val unusedRef = CoreAst.LocalRef(1, "unused")
    val scrutRef = CoreAst.LocalRef(2, "scrut")
    val captured = symbolicValue("Captured")
    val unused = FreshVar.freshVar("unused", valueType)
    val scrut = FreshVar.freshVar("scrut", valueType)
    val env = TypecheckEnv.empty
      .putLocal(capturedRef, captured)
      .putLocal(unusedRef, unused)
      .putLocal(scrutRef, scrut)
    val matchTerm = ETerm.Match(
      ETerm.LocalRef(scrutRef, span),
      motive = None,
      cases = Vector(
        ElabAst.Case(
          "C",
          Vector.empty,
          ETerm.LocalRef(capturedRef, span),
          span
        )
      ),
      span
    )

    val blocked = Interpreter.evalTerm(matchTerm, env)(EqStore.empty).asInstanceOf[VBlockedThunk]

    blocked.body match {
      case BlockedThunkBody.Match(_, closed: RuntimeEnv) =>
        assertEquals(closed(capturedRef), captured)
        intercept[WTF](closed(unusedRef))
        assertEquals(closed(scrutRef), scrut)
      case other => fail(s"Expected closed match thunk body, got $other")
    }
    assert(!blocked.synDeps.contains(unused.id))
    assert(blocked.synDeps.contains(scrut.id))
  }

  test("constructor equality accounts for result type") {
    implicit val eqStore: EqStore = EqStore.empty
    implicit val normalizers: TypecheckContext = TypecheckContext.empty

    val head = ConstructorHead("C", numErased = 0, totalArity = 0, valueType, isStruct = false)
    val resultA = symbolicValue("ResultA")
    val resultB = symbolicValue("ResultB")
    val ctorA = VCtor(head, Vector.empty, resultA)
    val ctorB = VCtor(head, Vector.empty, resultB)

    assertNotEquals(ctorA.key, ctorB.key)
    assert(!ValueEquivalence.defEq(ctorA, ctorB))
  }
}
