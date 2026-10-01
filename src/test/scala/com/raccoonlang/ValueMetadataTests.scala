package com.raccoonlang

import com.raccoonlang.Value._

/**
 * Value metadata at construction (docs/implemented/PROOF_BY_EVALUATION.md §2.3): a value's dependencies, key and
 * whether its key is conclusive are computed when it is built, from its children's, so publishing a global,
 * materializing and deciding an equation by key walk nothing, and the key assertion rechecks a verdict on a work stack
 * of its own. The values here are built directly, deeper than evaluation builds them, and each is used on a thread of
 * the JVM's default stack.
 */
class ValueMetadataTests extends munit.FunSuite with TestSupport {
  private val env = Prelude.default.checkedEnv
  private val nat = env("Nat")
  private val length = 1000000
  // Deep enough that a walk overflows the default stack at a hundredth of it.
  private val depth = 100000

  // A list's constructors and type, read off one that evaluation builds.
  private val (cons, nil, listOfNat) = runProgram("{ List.cons(1, List.nil(Nat)) }") match {
    case VCtor(cons, Vector(_, nil @ VCtor(_, Vector(), _)), listOfNat) => (cons, nil, listOfNat)
    case other => fail(s"Expected a one-element list, got $other")
  }

  private def number(n: BigInt): Value = VPacked.nat(n, nat)

  /** The list of `elements`, built afresh on each call: no two calls share a layer. */
  private def listOf(elements: Seq[BigInt]): Value =
    elements.reverseIterator.foldLeft(nil)((tail, element) => VCtor(cons, Vector(number(element), tail), listOfNat))

  /** `g` applied `depth` times over `bottom`, where `g` is an uninterpreted `Nat -> Nat`. */
  private def neutralChain(bottom: Value): Value = {
    val g = VConst("g", Symbol, env("Nat.succ").tpe)
    (1 to depth).foldLeft(bottom)((arg, _) => VApp(g, Vector(arg), nat, DepSet.empty))
  }

  /** A store in which a variable the values here do not mention is solved, so that materializing has work to find. */
  private def unrelatedSolution: EqStore = {
    val unrelated = FreshVar.freshVar("unrelated", nat)
    EqStore.empty.allow(DepSet(unrelated.id)).addLink(unrelated.id, number(0))
  }

  test("a million-element list is published, materialized and compared by key on the default stack") {
    assert(ValueEquivalence.keyAssertionsEnabled)
    val elements = (0 until length).map(BigInt(_))
    val (left, right) = (listOf(elements), listOf(elements))
    val lastDiffers = listOf(elements.updated(length - 1, BigInt(0)))
    onDefaultStack {
      // Publishing asserts that the global is closed, which reads its dependencies.
      env.putGlobal("big", left)
      assert(ValueOps.materialize(left, unrelatedSolution) eq left)
      assertEquals(left.key, right.key)
      assert(!left.needsStructuralDefEq)
      // Decided by key, and the assertion rechecks every layer of the verdict, the element that differs included.
      assert(ValueEquivalence.defEq(left, right))
      assertNotEquals(left.key, lastDiffers.key)
      assert(!ValueEquivalence.defEq(left, lastDiffers))
    }
  }

  test("a deep neutral application is published, materialized and compared by key on the default stack") {
    val (closed, again) = (neutralChain(number(0)), neutralChain(number(0)))
    val x = FreshVar.freshVar("x", nat)
    val (open, openAgain) = (neutralChain(x), neutralChain(x))
    onDefaultStack {
      env.putGlobal("closed", closed)
      assertEquals(open.synDeps, DepSet(x.id))
      intercept[InternalError](env.putGlobal("open", open))
      assert(ValueOps.materialize(open, unrelatedSolution) eq open)
      assertEquals(closed.key, again.key)
      assert(ValueEquivalence.defEq(closed, again))
      assert(ValueEquivalence.defEq(open, openAgain))
      assert(!ValueEquivalence.defEq(open, neutralChain(FreshVar.freshVar("y", nat))))
    }
  }

  test("a function type deep in its captures is published and keyed on the default stack") {
    val base = runProgram("{ (n: Nat) -> Nat }") match {
      case pi: VPi => pi
      case other   => fail(s"Expected a function type, got $other")
    }
    val node = base.id match {
      case ValueId.LocalId(node, _) => node
      case other                    => fail(s"Expected a local identity, got $other")
    }
    // Each layer captures the one below it, and the bottom one `bottom`. A function type's dependencies are its
    // captures', which evaluation unites when it builds one (Interpreter.evalPi).
    def captures(capture: Value): VPi =
      base.copy(id = ValueId.LocalId(node, Vector(capture)), synDeps = capture.synDeps)
    def nested(bottom: Value): VPi = (1 to depth).foldLeft(captures(bottom))((inner, _) => captures(inner))
    val (pi, again) = (nested(number(0)), nested(number(0)))
    val x = FreshVar.freshVar("x", nat)
    val open = nested(x)
    onDefaultStack {
      env.putGlobal("pi", pi)
      assertEquals(open.synDeps, DepSet(x.id))
      intercept[InternalError](env.putGlobal("open", open))
      assert(ValueOps.materialize(open, unrelatedSolution) eq open)
      // The keys differ at the bottom capture alone.
      assertEquals(pi.key, again.key)
      assertNotEquals(pi.key, nested(number(1)).key)
      assertNotEquals(pi.key, open.key)
      assert(ValueEquivalence.defEq(pi, again))
    }
  }

  test("keys mean what conversion means: equal values keyed alike, distinct ones apart") {
    // Every list of length at most 4 over 0, 1 and 2, each built twice.
    def all(size: Int): Vector[Vector[Int]] =
      if (size == 0) Vector(Vector.empty) else for { rest <- all(size - 1); x <- Vector(0, 1, 2) } yield x +: rest
    val lists = (0 to 4).flatMap(all)
    val built = lists.map(list => listOf(list.map(BigInt(_))))
    val rebuilt = lists.map(list => listOf(list.map(BigInt(_))))
    assertEquals(built.map(_.key), rebuilt.map(_.key))
    assertEquals(built.map(_.key).distinct.length, lists.length)
    for {
      (left, i) <- built.zipWithIndex
      (right, j) <- rebuilt.zipWithIndex
    } assertEquals(ValueEquivalence.defEq(left, right), i == j, s"${lists(i)} vs ${lists(j)}")
    // A nullary constructor's bare head keys as its application to nothing, which evaluation builds.
    assertEquals(env("Bool.true").key, runProgram("{ Bool.true }").key)
    assertNotEquals(env("Bool.true").key, env("Bool.false").key)
  }
}
