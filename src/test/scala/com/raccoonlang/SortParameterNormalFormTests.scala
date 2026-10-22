package com.raccoonlang

import com.raccoonlang.Value.{Kind, Level}

/**
 * Kind normal forms: canonical at birth, so structural equality, keys and conversion agree; and refinement links a lone
 * variable, the later-bound to the earlier-bound, while non-variable equations remain stuck.
 */
class SortParameterNormalFormTests extends munit.FunSuite {
  private def kindVar(): Kind = Kind.variable(FreshVar.freshVar("k", Value.KindTpe).id)

  test("a join is canonical, lin absorbs and unr is its identity") {
    val (j, k) = (kindVar(), kindVar())

    assertEquals(Kind.join(Vector(j, k)), Kind.join(Vector(k, j, k)))
    assertEquals(Kind.join(Vector(j, k)).key, Kind.join(Vector(k, j)).key)
    assertEquals(Kind.join(Vector(Kind.unr, k)), k)
    assertEquals(Kind.join(Vector(k, Kind.lin)), Kind.lin)
    assert(Kind.unr.isUnr && !Kind.lin.isUnr && !k.isUnr)
    assertNotEquals(Kind.lin.key, Kind.unr.key)
  }

  test("kind containment is preserved, with lin containing every kind") {
    val (j, k) = (kindVar(), kindVar())

    assert(Kind.contains(Kind.lin, Kind.join(Vector(j, k))))
    assert(Kind.contains(Kind.join(Vector(j, k)), j))
    assert(Kind.contains(j, Kind.unr))
    assert(!Kind.contains(j, Kind.lin))
    assert(!Kind.contains(j, k))
  }

  test("keys agree with conversion on kinds and the sorts built from them") {
    val (j, k) = (kindVar(), kindVar())
    val kinds = Vector(Kind.unr, Kind.lin, j, Kind.join(Vector(j, k)))
    val sorts = for {
      level <- Vector(Level.one, Level.const(2))
      kind <- kinds
    } yield Sorts.sort(level, kind)

    for (group <- Vector[Vector[Value]](kinds, sorts); x <- group; y <- group) {
      val identical = (x eq y) || (!x.isInstanceOf[Value.VSort] && x == y)
      assertEquals(ValueEquivalence.defEq(x, y), identical, s"$x vs $y")
      assertEquals(x.key == y.key, identical, s"$x vs $y")
    }
  }

  test("a lone variable links, the later-bound to the earlier-bound") {
    val (a, b, c) = (kindVar(), kindVar(), kindVar())
    val (earlier, later) = (a.vars.max, b.vars.max)
    val refinable = EqStore.empty.allow(a.vars ++ b.vars ++ c.vars)

    val bothVariables = ValueEquivalence.tryUnify(a, b, refinable).getOrElse(fail("expected a link"))
    assertEquals(bothVariables.subst.keySet, Set(later))
    val swapped = ValueEquivalence.tryUnify(b, a, refinable).getOrElse(fail("expected a link"))
    assertEquals(swapped.subst.keySet, Set(later))
    assert(earlier < later)

    val toJoin = ValueEquivalence.tryUnify(Kind.join(Vector(a, b)), c, refinable)
    assertEquals(toJoin.map(_.subst.keySet), Right(Set(c.vars.max)))
  }

  test("an equation between joins, or one whose variable occurs on both sides, is stuck and never apart") {
    val (j, k) = (kindVar(), kindVar())
    val refinable = EqStore.empty.allow(j.vars ++ k.vars)

    def stuck(x: Value, y: Value): Unit =
      ValueEquivalence.tryUnify(x, y, refinable) match {
        case Left(failure) => assert(!failure.apart, s"$x ~ $y reported apart")
        case Right(store)  => fail(s"$x ~ $y linked ${store.subst}")
      }

    stuck(Kind.lin, Kind.unr)
    stuck(k, Kind.join(Vector(k, j)))
    assert(ValueEquivalence.tryUnify(Kind.lin, Kind.unr, EqStore.empty).left.exists(!_.apart))
  }
}
