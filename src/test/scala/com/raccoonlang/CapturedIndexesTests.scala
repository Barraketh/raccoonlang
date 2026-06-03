package com.raccoonlang

import com.raccoonlang.ElabAst.{Term => ETerm}
import com.raccoonlang.Value._

class CapturedIndexesTests extends munit.FunSuite {
  private val span = Span(0, 0)
  private val valueType: Value = TypeTpe
  private val typeRef: ElabAst.TypeTerm = ETerm.GlobalRef("Type", span)
  private val classifier: Value.Universe = VSort(Level.succ(Level.one))
  private val typeBinderType: ElabAst.BinderType = {
    val pattern = ElabAst.TypePattern.Type(typeRef)
    ElabAst.BinderType.TypePattern(pattern, pattern.span)
  }

  test("getCapturedIndexes collects only local indexes below the current env cutoff") {
    val capturedRef = CoreAst.LocalRef(0, "captured")
    val binderRef = CoreAst.LocalRef(1, "x")
    val captured = FreshVar.freshVar("captured", valueType)
    val env = Env.empty.putLocal(capturedRef, captured)
    val term = ETerm.Pi(
      Vector(ElabAst.Binder(binderRef, typeBinderType, span)),
      ETerm.App(
        ETerm.LocalRef(binderRef, span),
        Vector(ETerm.LocalRef(capturedRef, span)),
        span
      ),
      classifier,
      span
    )

    val indexes = CapturedIndexes.getCapturedIndexes(term, env)

    assert(indexes.contains(capturedRef.id))
    assertEquals(indexes.getCardinality, 1)
    assertEquals(env(capturedRef), captured)
  }

  test("captured indexes cannot be read from a smaller env than their cutoff") {
    val ref = CoreAst.LocalRef(0, "x")
    val value = FreshVar.freshVar("x", valueType)
    val env = Env.empty.putLocal(ref, value)
    val indexes = CapturedIndexes.getCapturedIndexes(ETerm.LocalRef(ref, span), env)

    intercept[WTF](RuntimeEnv.closeForEval(Env.empty, indexes))
  }
}
