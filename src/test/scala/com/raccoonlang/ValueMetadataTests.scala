package com.raccoonlang

import com.raccoonlang.Value._

import java.util.concurrent.atomic.AtomicReference
import scala.collection.immutable.VectorMap

class ValueMetadataTests extends munit.FunSuite {
  private def onSmallStack(body: => Unit): Unit = {
    val failure = new AtomicReference[Throwable]()
    val thread = new Thread(
      null,
      new Runnable {
        override def run(): Unit =
          try body
          catch { case error: Throwable => failure.set(error) }
      },
      "deep-value-metadata",
      256L * 1024L
    )
    thread.start()
    thread.join()
    val error = failure.get()
    if (error != null) throw error
  }

  test("deep application metadata and empty-store materialization stay stack-safe") {
    onSmallStack {
      val head = VConst("f", Symbol, Sorts.Type)
      var deep: Value = VConst("leaf", Symbol, Sorts.Type)
      var index = 0
      while (index < 30000) {
        deep = VApp(head, Vector(deep), Sorts.Type)
        index += 1
      }

      assertEquals(deep.synDeps, DepSet.empty)
      assertNotEquals(deep.key, head.key)
      assert(!deep.needsStructuralDefEq)
      assert(ValueOps.materialize(deep, EqStore.empty) eq deep)
    }
  }

  test("eager keys distinguish Prop from Type") {
    assertNotEquals(Sorts.Prop.key, Sorts.Type.key)
  }

  test("materialization preserves shared value identity within one root") {
    val meta = Var("A", 40201, Sorts.Type)
    val shared = VConst("c", Symbol, meta)
    val root = VApp(VConst("f", Symbol, Sorts.Type), Vector(shared, shared), Sorts.Type)
    val store = EqStore.empty.allow(DepSet(meta.id)).addLink(meta.id, Sorts.Type)

    val materialized = ValueOps.materialize(root, store).asInstanceOf[VApp]
    assert(!(materialized.args(0) eq shared))
    assert(materialized.args(0) eq materialized.args(1))
  }

  test("materialization memos are isolated between equality stores") {
    val meta = Var("A", 40202, Sorts.Type)
    val value = VConst("c", Symbol, meta)
    val typeStore = EqStore.empty.allow(DepSet(meta.id)).addLink(meta.id, Sorts.Type)
    val propStore = EqStore.empty.allow(DepSet(meta.id)).addLink(meta.id, Sorts.Prop)

    val asType = ValueOps.materialize(value, typeStore).asInstanceOf[VConst]
    val asProp = ValueOps.materialize(value, propStore).asInstanceOf[VConst]
    assert(asType.tpe eq Sorts.Type)
    assert(asProp.tpe eq Sorts.Prop)
  }

  test("materialized Pi classifiers stay lazy and start a fresh memo session") {
    val levelMeta = Var("u", 40203, LevelTpe)
    val classifierSort = Sorts.sort(Level.mk(levelMeta.id))
    val capturedRef = CoreAst.LocalRef(420, "captured")
    val capturedEnv = Env.empty.copy(
      locals = VectorMap(capturedRef -> VConst("A", Symbol, classifierSort))
    )
    val calls = new java.util.concurrent.atomic.AtomicInteger()
    val pi = VPi(
      capturedEnv,
      Vector(
        CoreAst.Binder(
          CoreAst.LocalRef(421, "x"),
          CoreTestTerms.sortAt(CoreAst.LevelForm.LevelZero, Span(0, 0)),
          Span(0, 0),
          CoreAst.BinderSite.Function
        )
      ),
      _ => Sorts.Type,
      DepSet(levelMeta.id),
      ValueId.LocalId(NodeId.fresh(), Vector.empty),
      () => {
        calls.incrementAndGet()
        classifierSort
      },
      isPropValued = false
    )
    val store = EqStore.empty.allow(DepSet(levelMeta.id)).addLink(levelMeta.id, Level.zero)
    val materialized = ValueOps.materialize(pi, store).asInstanceOf[VPi]

    assertEquals(calls.get(), 0)
    val envClassifier = materialized.env(capturedRef).tpe.asInstanceOf[VSort]
    val forcedClassifier = materialized.tpe.asInstanceOf[VSort]
    assertEquals(calls.get(), 1)
    assertEquals(forcedClassifier.level, Level.zero)
    assert(!(forcedClassifier eq envClassifier))
  }
}
