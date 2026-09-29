package com.raccoonlang

import com.raccoonlang.Value.{Kind, Level, Lifetime}

/**
 * Kind and lifetime normal forms (spec §2.3): canonical at birth, so structural equality, keys and conversion agree;
 * and their refinement rule (spec §6.2): a lone variable links, the later-bound to the earlier-bound, and nothing else
 * is solved or refuted.
 */
class SortParameterNormalFormTests extends munit.FunSuite {
  private def lifetimeVar(): Lifetime = Lifetime.variable(FreshVar.freshVar("l", Value.LifetimeTpe).id)
  private def kindVar(): Kind = Kind.variable(FreshVar.freshVar("k", Value.KindTpe).id)

  test("a union is canonical whatever its order, nesting and repetition") {
    val (a, b, c) = (lifetimeVar(), lifetimeVar(), lifetimeVar())
    val left = Lifetime.union(Vector(Lifetime.union(Vector(a, b)), c))
    val right = Lifetime.union(Vector(c, Lifetime.union(Vector(b, a, a)), Lifetime.empty))

    assertEquals(left, right)
    assertEquals(left.hashCode(), right.hashCode())
    assertEquals(left.key, right.key)
    assertEquals(Lifetime.union(Vector(Lifetime.empty, a)), a)
    assertEquals(Lifetime.union(Vector.empty), Lifetime.empty)
  }

  test("a join is canonical, lin absorbs and unr is its identity") {
    val (j, k) = (kindVar(), kindVar())

    assertEquals(Kind.join(Vector(j, k)), Kind.join(Vector(k, j, k)))
    assertEquals(Kind.join(Vector(j, k)).key, Kind.join(Vector(k, j)).key)
    assertEquals(Kind.join(Vector(Kind.unr, k)), k)
    assertEquals(Kind.join(Vector(k, Kind.lin)), Kind.lin)
    assert(Kind.unr.isUnr && !Kind.lin.isUnr && !k.isUnr)
    assertNotEquals(Kind.lin.key, Kind.unr.key)
  }

  test("containment is set inclusion, with lin containing every kind") {
    val (a, b) = (lifetimeVar(), lifetimeVar())
    val (j, k) = (kindVar(), kindVar())

    assert(Lifetime.contains(Lifetime.union(Vector(a, b)), a))
    assert(Lifetime.contains(a, Lifetime.empty))
    assert(!Lifetime.contains(a, Lifetime.union(Vector(a, b))))
    assert(Kind.contains(Kind.lin, Kind.join(Vector(j, k))))
    assert(Kind.contains(Kind.join(Vector(j, k)), j))
    assert(Kind.contains(j, Kind.unr))
    assert(!Kind.contains(j, Kind.lin))
    assert(!Kind.contains(j, k))
  }

  test("less removes exactly the given lifetime variables") {
    val (a, b) = (lifetimeVar(), lifetimeVar())

    assertEquals(Lifetime.less(Lifetime.union(Vector(a, b)), a.vars), b)
    assertEquals(Lifetime.less(a, b.vars), a)
  }

  test("keys agree with conversion on kinds, lifetimes and the sorts built from them") {
    val (a, b) = (lifetimeVar(), lifetimeVar())
    val (j, k) = (kindVar(), kindVar())
    val lifetimes = Vector(Lifetime.empty, a, b, Lifetime.union(Vector(a, b)))
    val kinds = Vector(Kind.unr, Kind.lin, j, Kind.join(Vector(j, k)))
    val sorts = for {
      level <- Vector(Level.one, Level.const(2))
      kind <- kinds
      scope <- lifetimes
    } yield Sorts.sort(level, kind, scope)

    for (group <- Vector[Vector[Value]](lifetimes, kinds, sorts); x <- group; y <- group) {
      val identical = (x eq y) || (!x.isInstanceOf[Value.VSort] && x == y)
      assertEquals(ValueEquivalence.defEq(x, y), identical, s"$x vs $y")
      assertEquals(x.key == y.key, identical, s"$x vs $y")
    }
  }

  test("a lone variable links, the later-bound to the earlier-bound") {
    val (a, b, c) = (lifetimeVar(), lifetimeVar(), lifetimeVar())
    val (earlier, later) = (a.vars.max, b.vars.max)
    val refinable = EqStore.empty.allow(a.vars ++ b.vars ++ c.vars)

    val bothVariables = ValueEquivalence.tryUnify(a, b, refinable).getOrElse(fail("expected a link"))
    assertEquals(bothVariables.subst.keySet, Set(later))
    val swapped = ValueEquivalence.tryUnify(b, a, refinable).getOrElse(fail("expected a link"))
    assertEquals(swapped.subst.keySet, Set(later))
    assert(earlier < later)

    val toUnion = ValueEquivalence.tryUnify(Lifetime.union(Vector(a, b)), c, refinable)
    assertEquals(toUnion.map(_.subst.keySet), Right(Set(c.vars.max)))
  }

  test("an equation between unions, or one whose variable occurs on both sides, is stuck and never apart") {
    val (a, b, c, d) = (lifetimeVar(), lifetimeVar(), lifetimeVar(), lifetimeVar())
    val (j, k) = (kindVar(), kindVar())
    val refinable = EqStore.empty.allow(a.vars ++ b.vars ++ c.vars ++ d.vars ++ j.vars ++ k.vars)

    def stuck(x: Value, y: Value): Unit =
      ValueEquivalence.tryUnify(x, y, refinable) match {
        case Left(failure) => assert(!failure.apart, s"$x ~ $y reported apart")
        case Right(store)  => fail(s"$x ~ $y linked ${store.subst}")
      }

    stuck(Lifetime.union(Vector(a, b)), Lifetime.union(Vector(c, d)))
    stuck(a, Lifetime.union(Vector(a, b)))
    stuck(Kind.lin, Kind.unr)
    stuck(k, Kind.join(Vector(k, j)))
    assert(ValueEquivalence.tryUnify(Kind.lin, Kind.unr, EqStore.empty).left.exists(!_.apart))
  }
}
