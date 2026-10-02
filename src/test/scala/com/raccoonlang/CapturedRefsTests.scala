package com.raccoonlang

import com.raccoonlang.CoreAst.{Term => CTerm}

class CapturedRefsTests extends munit.FunSuite with DiagnosticAssertions {
  private val span = Span(0, 0)
  private val valueType: Value = Sorts.Type
  private val typeSort: CoreAst.Term = CoreTestTerms.sortAt(CoreAst.Form.LevelZero, span)

  private def piMentioning(refs: Vector[CoreAst.LocalRef]): CTerm.Pi = {
    val binderRef = CoreAst.LocalRef(Int.MaxValue, "binder")
    val out =
      if (refs.isEmpty) CTerm.NatLit(0, span)
      else CTerm.App(CTerm.GlobalRef("mention", span), refs.map(CTerm.LocalRef(_, span)), Vector.empty, span)
    CTerm.Pi(
      Vector(CoreAst.Binder(binderRef, typeSort, span, CoreAst.BinderSite.Function, BinderMode.Explicit)),
      out,
      CoreAst.Closure.unrestricted(span),
      span,
      NodeId.fresh()
    )
  }

  test("getCapturedRefs collects only local refs present in the current env") {
    val capturedRef = CoreAst.LocalRef(0, "captured")
    val binderRef = CoreAst.LocalRef(1, "x")
    val captured = FreshVar.freshVar("captured", valueType)
    val env = Env.empty.putLocal(capturedRef, captured)
    val term = CTerm.Pi(
      Vector(CoreAst.Binder(binderRef, typeSort, span, CoreAst.BinderSite.Function, BinderMode.Explicit)),
      CTerm.App(
        CTerm.LocalRef(binderRef, span),
        Vector(CTerm.LocalRef(capturedRef, span)),
        Vector.empty,
        span
      ),
      CoreAst.Closure.unrestricted(span),
      span,
      NodeId.fresh()
    )

    val refs = CapturedRefs.getCapturedRefs(term, env)

    assert(refs.contains(capturedRef))
    assertEquals(refs.size, 1)
    assert(ValueEquivalence.defEq(env(capturedRef), captured))
  }

  test("captured refs cannot be read from an env that does not contain them") {
    val ref = CoreAst.LocalRef(0, "x")
    val value = FreshVar.freshVar("x", valueType)
    val env = Env.empty.putLocal(ref, value)
    val refs = CapturedRefs.getCapturedRefs(CTerm.LocalRef(ref, span), env)

    intercept[InternalError](Env.empty.closeForEval(refs))
  }

  test("cached captures preserve environment order without forcing evidence") {
    val refs = Vector.tabulate(8)(index => CoreAst.LocalRef(10 + index, s"local$index"))
    val capturedRefs = Vector(refs(5), refs(1))
    val proposition = Value.VConst("P", Value.Symbol, Sorts.Prop)
    var selectedForces = 0
    var unusedForces = 0
    val selected = new Value.DeferredEvidence(() => { selectedForces += 1; proposition })
    val unused = new Value.DeferredEvidence(() => { unusedForces += 1; proposition })
    val values = refs.map {
      case ref if ref == refs(1) => selected
      case ref if ref == refs(6) => unused
      case _                     => Sorts.Type
    }
    val env = Env.empty.bindRuntimeLocals(RuntimeSlotLayout(refs), values)
    val pi = piMentioning(capturedRefs)

    val captures = CapturedRefs.getCapturedRefs(pi, env)

    assertEquals(captures, capturedRefs.toSet)
    assertEquals(selectedForces, 0)
    assertEquals(unusedForces, 0)
    val closed = env.closeForEval(captures)
    assertEquals(closed.locals.keysIterator.toVector, Vector(refs(1), refs(5)))
    assertEquals(selectedForces, 1)
    assertEquals(unusedForces, 0)
  }

  test("sparse cached Pi captures use full LocalRef identity and preserve env order") {
    val refs = Vector.tabulate(7)(index => CoreAst.LocalRef(40 + index, s"mention$index"))
    val earlierEnvRef = refs(2)
    val envRef = refs(4)
    val sameIdDifferentName = CoreAst.LocalRef(envRef.id, "unbound-alias")
    val proposition = Value.VConst("P", Value.Symbol, Sorts.Prop)
    var evidenceForces = 0
    val deferred = new Value.DeferredEvidence(() => { evidenceForces += 1; proposition })
    val earlierValue = FreshVar.freshVar("earlier", valueType)
    val env = Env.empty.bindRuntimeLocals(
      RuntimeSlotLayout(Vector(earlierEnvRef, envRef)),
      Vector(earlierValue, deferred)
    )
    val pi = piMentioning(refs.updated(5, sameIdDifferentName))

    assert(pi.refs.size > 1)
    val captures = CapturedRefs.getCapturedRefs(pi, env)
    assertEquals(captures, Set(earlierEnvRef, envRef))
    assert(!captures(sameIdDifferentName))
    assertEquals(evidenceForces, 0)
    val closed = env.closeForEval(captures)
    assertEquals(closed.locals.keysIterator.toVector, Vector(earlierEnvRef, envRef))
    assertEquals(evidenceForces, 1)
  }

  test("cached Pi capture from an empty environment is empty") {
    val ref = CoreAst.LocalRef(40, "mention")
    val emptyEnvTerm = piMentioning(Vector(ref))
    assertEquals(CapturedRefs.getCapturedRefs(emptyEnvTerm, Env.empty), Set.empty[CoreAst.LocalRef])
  }

}
