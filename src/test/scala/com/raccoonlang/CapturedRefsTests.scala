package com.raccoonlang

import com.raccoonlang.CoreAst.{Term => CTerm}
import com.raccoonlang.Value._

class CapturedRefsTests extends munit.FunSuite {
  private val span = Span(0, 0)
  private val valueType: Value = TypeTpe
  private val typeRef: CoreAst.Term = CTerm.GlobalRef("Type", span)

  test("getCapturedRefs collects only local refs present in the current env") {
    val capturedRef = CoreAst.LocalRef(0, "captured")
    val binderRef = CoreAst.LocalRef(1, "x")
    val captured = FreshVar.freshVar("captured", valueType)
    val env = Env.empty.putLocal(capturedRef, captured)
    val term = CTerm.Pi(
      Vector(CoreAst.Binder(binderRef, typeRef, span)),
      CTerm.App(
        CTerm.LocalRef(binderRef, span),
        Vector(CTerm.LocalRef(capturedRef, span)),
        span
      ),
      Span.synthetic()
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

    intercept[WTF](Env.empty.closeForEval(refs))
  }

}
