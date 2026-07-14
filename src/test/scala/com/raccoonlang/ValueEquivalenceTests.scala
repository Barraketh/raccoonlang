package com.raccoonlang

import com.raccoonlang.ElabAst.{Term => ETerm}
import com.raccoonlang.Value._

class ValueEquivalenceTests extends munit.FunSuite {
  private val span = Span(0, 0)
  private val typeRef: ElabAst.TypeTerm = ETerm.GlobalRef("Type", span)
  private val binderRef = CoreAst.LocalRef(0, "x")
  private val binder = VBinder(binderRef, typeRef)
  private val env = Env.empty[Value].putGlobal("Type", TypeTpe)
  private val typeToTypeClassifier = VSort(Level.succ(Level.one))

  private def nodeId(start: Int): AstNodeId = AstNodeId(None, start)

  private def deps(values: Value*): DepSet = {
    val res = DepSet.newBuilder
    values.foreach(value => res.unionInPlace(value.synDeps))
    res.result()
  }

  private def pi(captures: Vector[Value], out: Env[Value] => Value, start: Int): VPi =
    VPi(env, Vector(binder), out, deps(captures: _*), ValueId.LocalId(nodeId(start), captures), () => typeToTypeClassifier)

  test("Pi unification rejects solutions that depend on fresh binder vars") {
    val hole = FreshVar.freshVar("A", TypeTpe)
    val meta = EqStore.empty.allow(DepSet(hole.id))
    val left = pi(Vector(hole), _ => hole, 1)
    val right = pi(Vector.empty, env => env(binderRef), 2)

    assert(ValueEquivalence.tryUnify(left, right, meta).isLeft)
  }

  test("Pi unification does not link holes beneath the Pi frame") {
    // Pi-former injectivity is not assumed, so codomain equations are not consequences of the
    // Pi equation: even a closed solution must be refused, not chosen.
    val hole = FreshVar.freshVar("A", TypeTpe)
    val closed = FreshVar.freshVar("B", TypeTpe)
    val meta = EqStore.empty.allow(DepSet(hole.id))
    val left = pi(Vector(hole), _ => hole, 3)
    val right = pi(Vector(closed), _ => closed, 4)

    assert(ValueEquivalence.tryUnify(left, right, meta).isLeft)
  }
}
