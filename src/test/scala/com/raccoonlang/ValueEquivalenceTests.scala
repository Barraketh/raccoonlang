package com.raccoonlang

import com.raccoonlang.ElabAst.{Term => ETerm}
import com.raccoonlang.Value._

class ValueEquivalenceTests extends munit.FunSuite {
  private val span = Span(0, 0)
  private val typeRef: ElabAst.TypeTerm = ETerm.GlobalRef("Type", span)
  private val binderType: ElabAst.BinderType =
    ElabAst.BinderType.TypePattern(ElabAst.TypePattern.Type(typeRef), span)
  private val binderRef = CoreAst.LocalRef(0, "x")
  private val binder = VBinder(binderRef, binderType, typeRef, Vector.empty)
  private val env = Env.empty.putGlobal("Type", TypeTpe)
  private val typeToTypeClassifier = VSort(Level.succ(Level.one))

  private def nodeId(start: Int): AstNodeId = AstNodeId(None, start)

  private def deps(values: Value*): DepSet = {
    val res = DepSet.newBuilder
    values.foreach(value => res.unionInPlace(value.synDeps))
    res.result()
  }

  private def pi(captures: Vector[Value], out: Env => Value, start: Int): VPi =
    VPi(env, Vector(binder), out, deps(captures: _*), ValueId.LocalId(nodeId(start), captures), typeToTypeClassifier)

  test("Pi unification rejects solutions that depend on fresh binder vars") {
    val hole = FreshVar.freshVar("A", TypeTpe)
    val meta = EqStore.empty.allow(DepSet(hole.id))
    val left = pi(Vector(hole), _ => hole, 1)
    val right = pi(Vector.empty, env => env(binderRef), 2)

    assert(ValueEquivalence.tryUnify(left, right, meta, Map.empty).isLeft)
  }

  test("Pi unification still allows closed solutions") {
    val hole = FreshVar.freshVar("A", TypeTpe)
    val closed = FreshVar.freshVar("B", TypeTpe)
    val meta = EqStore.empty.allow(DepSet(hole.id))
    val left = pi(Vector(hole), _ => hole, 3)
    val right = pi(Vector(closed), _ => closed, 4)

    val solved = ValueEquivalence.unify(left, right, meta, Map.empty)

    assertEquals(solved.subst(hole.id), closed)
  }
}
