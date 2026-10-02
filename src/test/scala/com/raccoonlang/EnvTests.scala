package com.raccoonlang

import com.raccoonlang.Value._

class EnvTests extends munit.FunSuite {
  test("group binding preserves the base env, rejects duplicate refs, and handles hash collisions") {
    val baseRef = CoreAst.LocalRef(0, "base")
    val firstRef = CoreAst.LocalRef(1, "first")
    val secondRef = CoreAst.LocalRef(1, "second")
    val base = Env.empty.putLocal(baseRef, Sorts.Type)
    val bound = base.bindLocals(Vector(firstRef, secondRef), Vector(Sorts.Type, Sorts.Prop))(identity)
    assert(bound(firstRef) eq Sorts.Type)
    assert(bound(secondRef) eq Sorts.Prop)
    assertEquals(bound.locals.keysIterator.toVector, Vector(baseRef, firstRef, secondRef))
    assertEquals(base.localRefs, Set(baseRef))
    intercept[InternalError](base.bindLocals(Vector(firstRef, firstRef), Vector(Sorts.Type, Sorts.Prop))(identity))
    intercept[InternalError](base.bindLocals(Vector(baseRef), Vector(Sorts.Type))(identity))
  }

  test("capture and materialization preserve binding order across small and large environments") {
    val refs = Vector(8, 2, 11, 0, 5, 3).map(id => CoreAst.LocalRef(id, s"x$id"))
    val values = refs.map(ref => FreshVar.freshVar(ref.name, Sorts.Type))
    val env = refs.zip(values).foldLeft(Env.empty) { case (current, (ref, value)) => current.putLocal(ref, value) }
    val kept = Set(refs(0), refs(2), refs(3), refs(4), refs(5))
    val closed = env.closeForEval(kept)
    val expectedOrder = refs.filter(kept)
    assertEquals(closed.locals.keysIterator.toVector, expectedOrder)
    assertEquals(closed.localRefs, kept)

    val replacement = VConst("Replacement", Symbol, Sorts.Type)
    val store = EqStore.empty.allow(DepSet(values(2).id)).addLink(values(2).id, replacement)
    val materialized = ValueOps.materializeEnv(closed, store)
    assertEquals(materialized.locals.keysIterator.toVector, expectedOrder)
    assertEquals(materialized.localRefs, kept)
    assert(materialized(refs(2)) eq replacement)
    assertEquals(env.locals.keysIterator.toVector, refs)
    assert(env(refs(2)) eq values(2))
  }

  test("local membership does not force evidence and closing forces only captured evidence") {
    val keptRef = CoreAst.LocalRef(0, "kept")
    val droppedRef = CoreAst.LocalRef(1, "dropped")
    val proposition = VConst("P", Symbol, Sorts.Prop)
    var keptForces = 0
    var droppedForces = 0
    val kept = new DeferredEvidence(() => { keptForces += 1; proposition })
    val dropped = new DeferredEvidence(() => { droppedForces += 1; proposition })
    val env = Env.empty.bindLocals(Vector(keptRef, droppedRef), Vector(kept, dropped))(identity)
    assertEquals(env.localRefs, Set(keptRef, droppedRef))
    assertEquals(keptForces, 0)
    assertEquals(droppedForces, 0)
    val closed = env.closeForEval(Set(keptRef))
    assert(closed(keptRef).isInstanceOf[VProof])
    assertEquals(keptForces, 1)
    assertEquals(droppedForces, 0)
    assertEquals(env.closeForEval(Set.empty).localRefs, Set.empty[CoreAst.LocalRef])
  }

  test("runtime slot groups preserve resolved refs, binding order, and frame-free captures") {
    val baseRef = CoreAst.LocalRef(20, "base")
    val argLeft = CoreAst.LocalRef(21, "left")
    val argRight =
      CoreAst.LocalRef(21, "right") // Same id, different name: full LocalRef equality still distinguishes them.
    val fieldRef = CoreAst.LocalRef(22, "field")
    val baseValue = FreshVar.freshVar("base", Sorts.Type)
    val leftValue = FreshVar.freshVar("left", Sorts.Type)
    val rightValue = FreshVar.freshVar("right", Sorts.Type)
    val fieldValue = FreshVar.freshVar("field", Sorts.Type)
    val base = Env.empty.putLocal(baseRef, baseValue)
    val call = base.bindRuntimeLocals(RuntimeSlotLayout(Vector(argLeft, argRight)), Vector(leftValue, rightValue))
    val branch = call.bindRuntimeLocals(RuntimeSlotLayout(Vector(fieldRef)), Vector(fieldValue))

    assert(branch(argLeft) eq leftValue)
    assert(branch(argRight) eq rightValue)
    assert(branch(fieldRef) eq fieldValue)
    assertEquals(branch.localRefs, Set(baseRef, argLeft, argRight, fieldRef))
    assertEquals(branch.locals.keysIterator.toVector, Vector(baseRef, argLeft, argRight, fieldRef))
    assertEquals(branch.closeForEval(Set(fieldRef, argLeft)).locals.keysIterator.toVector, Vector(argLeft, fieldRef))
    assertEquals(branch.closeForEval(Set(fieldRef)).runtimeFrames, Vector.empty)
    intercept[InternalError] {
      branch.bindRuntimeLocals(RuntimeSlotLayout(Vector(argLeft)), Vector(leftValue))
    }
    intercept[InternalError](RuntimeSlotLayout(Vector(argLeft, argLeft)))
  }

  test("runtime slot membership stays lazy and materialization owns a fresh frame") {
    val valueRef = CoreAst.LocalRef(30, "value")
    val evidenceRef = CoreAst.LocalRef(31, "evidence")
    val unusedEvidenceRef = CoreAst.LocalRef(32, "unused")
    val value = FreshVar.freshVar("value", Sorts.Type)
    val replacement = VConst("Replacement", Symbol, Sorts.Type)
    val proposition = VConst("P", Symbol, Sorts.Prop)
    var selectedForces = 0
    var unusedForces = 0
    val selected = new DeferredEvidence(() => { selectedForces += 1; proposition })
    val unused = new DeferredEvidence(() => { unusedForces += 1; proposition })
    val env = Env.empty
      .bindRuntimeLocals(RuntimeSlotLayout(Vector(valueRef)), Vector(value))
      .bindRuntimeLocals(RuntimeSlotLayout(Vector(evidenceRef, unusedEvidenceRef)), Vector(selected, unused))

    assertEquals(env.localRefs, Set(valueRef, evidenceRef, unusedEvidenceRef))
    assertEquals(selectedForces, 0)
    assertEquals(unusedForces, 0)
    val store = EqStore.empty.allow(DepSet(value.id)).addLink(value.id, replacement)
    val materialized = ValueOps.materializeEnv(env, store)
    assert(!(materialized.runtimeFrames.last eq env.runtimeFrames.last))
    assert(materialized(valueRef) eq replacement)
    assertEquals(materialized.locals.keysIterator.toVector, Vector(valueRef, evidenceRef, unusedEvidenceRef))
    assertEquals(selectedForces, 0)
    assertEquals(unusedForces, 0)

    val closed = materialized.closeForEval(Set(evidenceRef))
    assert(closed(evidenceRef).isInstanceOf[VProof])
    assertEquals(selectedForces, 1)
    assertEquals(unusedForces, 0)
    assertEquals(closed.localRefs, Set(evidenceRef))
  }

  test("deep runtime frames use the cumulative lookup index for outer reads") {
    val outerRef = CoreAst.LocalRef(100, "outer")
    val sameIdDifferentNameRef = CoreAst.LocalRef(100, "outer-alias")
    val outerValue = FreshVar.freshVar("outer", Sorts.Type)
    var env = Env.empty.bindRuntimeLocals(RuntimeSlotLayout(Vector(outerRef)), Vector(outerValue))
    val nestedRefs = sameIdDifferentNameRef +:
      Vector.tabulate(511)(index => CoreAst.LocalRef(101 + index, s"nested$index"))
    val nestedValues = nestedRefs.map(ref => FreshVar.freshVar(ref.name, Sorts.Type))

    nestedRefs.zip(nestedValues).foreach { case (ref, value) =>
      env = env.bindRuntimeLocals(RuntimeSlotLayout(Vector(ref)), Vector(value))
      assert(env(outerRef) eq outerValue)
    }

    assertEquals(env.runtimeFrames.length, nestedRefs.length + 1)
    assert(env.runtimeFrames.last.lookupIndex.exists(_.get(outerRef).contains(outerValue)))
    assert(env.containsLocal(outerRef))
    assert(env.containsLocal(sameIdDifferentNameRef))
    assert(!env.containsLocal(CoreAst.LocalRef(100, "absent")))
    assert((0 until 1000).forall(_ => env(outerRef) eq outerValue))
    assert(env.localValueOption(outerRef).contains(outerValue))
    assert(env(nestedRefs.last) eq nestedValues.last)
    assertEquals(env.locals.keysIterator.toVector, outerRef +: nestedRefs)
    intercept[InternalError] {
      env.bindRuntimeLocals(RuntimeSlotLayout(Vector(outerRef)), Vector(outerValue))
    }

    val previousLookupIndex = env.runtimeFrames.last.lookupIndex.get
    val nextRef = CoreAst.LocalRef(1000, "next")
    val extended = env.bindRuntimeLocals(
      RuntimeSlotLayout(Vector(nextRef)),
      Vector(FreshVar.freshVar("next", Sorts.Type))
    )
    assert(!previousLookupIndex.contains(nextRef))
    assert(extended.runtimeFrames.last.lookupIndex.get.contains(nextRef))
    assert(extended(outerRef) eq outerValue)
    val replacement = VConst("OuterReplacement", Symbol, Sorts.Type)
    val store = EqStore.empty.allow(DepSet(outerValue.id)).addLink(outerValue.id, replacement)
    val materialized = ValueOps.materializeEnv(extended, store)
    val materializedLookupIndex = materialized.runtimeFrames.last.lookupIndex.get
    assert(previousLookupIndex(outerRef) eq outerValue)
    assert(materializedLookupIndex(outerRef) eq replacement)
    assert(materialized.runtimeFrames.dropRight(1).forall(_.lookupIndex.isEmpty))
    assert(materialized.runtimeFrames.head.valueOrNull(outerRef) eq replacement)
    assert(materialized(outerRef) eq replacement)

    val closed = env.closeForEval(Set(outerRef, nestedRefs.last))
    assertEquals(closed.locals.keysIterator.toVector, Vector(outerRef, nestedRefs.last))
    assert(closed(outerRef) eq outerValue)
    assert(closed(nestedRefs.last) eq nestedValues.last)
    assert(!closed.containsLocal(sameIdDifferentNameRef))
  }

  test("large runtime telescope prefixes share one index and cache only requested sizes") {
    val refs = Vector.tabulate(4096)(index => CoreAst.LocalRef(1000 + index, s"arg$index"))
    val values = Vector.fill(refs.length)(Sorts.Type: Value)
    val full = RuntimeSlotLayout(refs)
    val prefixes = new RuntimeSlotPrefixCache(full)
    assertEquals(prefixes.cachedPrefixCount, 0)
    val first = prefixes(512)
    assertEquals(prefixes.cachedPrefixCount, 1)
    val second = prefixes(4095)
    assertEquals(prefixes.cachedPrefixCount, 2)

    assert(first eq prefixes(512))
    assert(second eq prefixes(4095))
    assert(first.sharesIndexTable(full))
    assert(second.sharesIndexTable(full))
    assertEquals(first.size, 512)
    assertEquals(first.indexOf(refs(511)), 511)
    assertEquals(first.indexOf(refs(512)), -1)
    assertEquals(second.indexOf(refs(4094)), 4094)
    assertEquals(second.indexOf(refs.last), -1)
    assertEquals(full.indexOf(refs.last), 4095)

    val seedRefs = Vector.tabulate(4)(index => CoreAst.LocalRef(-index - 1, s"seed$index"))
    val seedValues = Vector.fill(seedRefs.length)(Sorts.Type: Value)
    val seedEnv = seedRefs.zip(seedValues).foldLeft(Env.empty) { case (current, (ref, value)) =>
      current.bindRuntimeLocals(RuntimeSlotLayout(Vector(ref)), Vector(value))
    }
    assert(seedEnv.runtimeFrames.forall(_.lookupIndex.isEmpty))

    val env = seedEnv.bindRuntimeLocals(first, values.take(first.size))
    assert(env.runtimeFrames.last.lookupIndex.exists(_.contains(refs(511))))
    assert(!env.containsLocal(refs(512)))
    assert(env(refs(511)) eq Sorts.Type)
    assertEquals(env.locals.keysIterator.toVector, seedRefs ++ refs.take(first.size))
  }
}
