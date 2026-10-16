package com.raccoonlang

import com.raccoonlang.Value._

import scala.collection.immutable.VectorMap

class ValueVarsInTests extends munit.FunSuite {
  private val span = Span(0, 0)

  private def binder(ref: CoreAst.LocalRef): CoreAst.Binder =
    CoreAst.Binder(ref, CoreTestTerms.sortAt(CoreAst.Form.LevelZero, span), span, CoreAst.BinderSite.Function)

  private def localEnv(ref: CoreAst.LocalRef, value: Value): Env =
    Env.empty.copy(locals = VectorMap(ref -> value), localRefs = Set(ref))

  test("varsIn visits a shared value DAG once") {
    val target = Var("target", 40001, Sorts.Type)
    val head = VConst("f", Symbol, Sorts.Type)
    var shared: Value = target
    var depth = 0
    while (depth < 35) {
      shared = VApp(head, Vector(shared, shared), Sorts.Type)
      depth += 1
    }

    assertEquals(Value.varsIn(shared, DepSet(target.id)), Vector(target))
  }

  test("varsIn preserves order through types, closure environments, captures, and result types") {
    val typeOnly = Var("type-only", 40104, Sorts.Type)
    val piLocal = Var("pi-local", 40101, typeOnly)
    val bodyLocal = Var("body-local", 40102, Sorts.Type)
    val capture = Var("capture", 40103, Sorts.Type)
    val resultType = Var("result-type", 40105, Sorts.Type)
    val piRef = CoreAst.LocalRef(400, "pi")
    val bodyRef = CoreAst.LocalRef(401, "body")
    val piEnv = localEnv(piRef, piLocal)
    val bodyEnv = localEnv(bodyRef, bodyLocal)
    val pi = VPi(
      piEnv,
      Vector(binder(CoreAst.LocalRef(402, "x"))),
      _ => Sorts.Type,
      piLocal.synDeps,
      ValueId.LocalId(NodeId.fresh(), Vector.empty),
      () => Sorts.Type,
      isPropValued = false
    )
    val lambda = VLam(
      pi,
      ValueId.LocalId(NodeId.fresh(), Vector(capture)),
      LamBody.Native((_, _) => Sorts.Type, bodyEnv, isRawRecursive = false)
    )
    val root = VApp(VConst("f", Symbol, Sorts.Type), Vector(lambda), resultType)
    val requested = DepSet(piLocal.id, typeOnly.id, bodyLocal.id, capture.id, resultType.id)

    assertEquals(
      Value.varsIn(root, requested).map(_.id),
      Vector(piLocal.id, typeOnly.id, bodyLocal.id, capture.id, resultType.id)
    )
  }
}
