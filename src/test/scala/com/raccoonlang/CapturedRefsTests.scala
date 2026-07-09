package com.raccoonlang

import com.raccoonlang.ElabAst.{Term => ETerm}
import com.raccoonlang.Value._

class CapturedRefsTests extends munit.FunSuite {
  private val span = Span(0, 0)
  private val valueType: Value = TypeTpe
  private val typeRef: ElabAst.TypeTerm = ETerm.GlobalRef("Type", span)
  private val classifier: Value.VSort = VSort(Level.succ(Level.one))

  test("getCapturedRefs collects only local refs present in the current env") {
    val capturedRef = CoreAst.LocalRef(0, "captured")
    val binderRef = CoreAst.LocalRef(1, "x")
    val captured = FreshVar.freshVar("captured", valueType)
    val env = Env.empty[Value].putLocal(capturedRef, captured)
    val term = ETerm.Pi(
      Vector(ElabAst.Binder(binderRef, typeRef, span)),
      ETerm.App(
        ETerm.LocalRef(binderRef, span),
        Vector(ETerm.LocalRef(capturedRef, span)),
        span
      ),
      classifier,
      numLevelParams = 0,
      span,
      nodeId = AstNodeId.synthetic()
    )

    val refs = CapturedRefs.getCapturedRefs(term, env)

    assert(refs.contains(capturedRef))
    assertEquals(refs.size, 1)
    assert(ValueEquivalence.defEq(env(capturedRef), captured))
  }

  test("captured refs cannot be read from an env that does not contain them") {
    val ref = CoreAst.LocalRef(0, "x")
    val value = FreshVar.freshVar("x", valueType)
    val env = Env.empty[Value].putLocal(ref, value)
    val refs = CapturedRefs.getCapturedRefs(ETerm.LocalRef(ref, span), env)

    intercept[WTF](Env.empty[Value].closeForEval(refs))
  }

}
