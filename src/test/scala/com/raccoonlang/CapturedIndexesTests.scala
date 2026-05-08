package com.raccoonlang

import com.raccoonlang.CoreAst.{Term => CTerm}
import com.raccoonlang.Value._

class CapturedIndexesTests extends munit.FunSuite {
  private val span = Span(0, 0)
  private val valueType: Value = VSort(Level.zero)
  private val typeRef: CoreAst.CheckedTypeTerm = CTerm.GlobalRef[CoreAst.Checked]("Type", span)

  test("getCapturedIndexes collects only local indexes below the current env cutoff") {
    val capturedRef = CoreAst.LocalRef(0, "captured")
    val binderRef = CoreAst.LocalRef(1, "x")
    val captured = FreshVar.freshVar("captured", valueType)
    val env = TypecheckEnv.empty.putLocal(capturedRef, captured)
    val term = CTerm.Pi[CoreAst.Checked](
      Vector(CoreAst.Binder(binderRef, CoreAst.TypePattern.Type(typeRef), span)),
      CTerm.App[CoreAst.Checked](
        CTerm.LocalRef[CoreAst.Checked](binderRef, span),
        Vector(CTerm.LocalRef[CoreAst.Checked](capturedRef, span)),
        span
      ),
      span
    )

    val indexes = CapturedIndexes.getCapturedIndexes(term, env)

    assertEquals(env.getLocalsByIndexes(indexes), Vector(captured))
  }

  test("captured indexes cannot be read from a smaller env than their cutoff") {
    val ref = CoreAst.LocalRef(0, "x")
    val value = FreshVar.freshVar("x", valueType)
    val env = TypecheckEnv.empty.putLocal(ref, value)
    val indexes = CapturedIndexes.getCapturedIndexes(CTerm.LocalRef[CoreAst.Checked](ref, span), env)

    intercept[WTF](TypecheckEnv.empty.getLocalsByIndexes(indexes))
  }
}
