package com.raccoonlang

class DepSetTests extends munit.FunSuite {
  test("operations leave original sets unchanged") {
    val one = DepSet(1)
    val two = one + 2
    val union = two ++ DepSet(3)
    val diff = union -- DepSet(1, 3)

    assert(one.contains(1))
    assert(!one.contains(2))
    assertEquals(two, DepSet(1, 2))
    assertEquals(union, DepSet(1, 2, 3))
    assertEquals(diff, DepSet(2))
  }

  test("roaring bitmap copies cannot mutate a set") {
    val deps = DepSet(1, 2)
    val bitmap = deps.toRoaringBitmap
    bitmap.add(3)

    assertEquals(deps, DepSet(1, 2))
    assert(!deps.contains(3))
  }

  test("builder result is isolated from later builder mutations") {
    val builder = DepSet.newBuilder
    builder.add(1)
    val first = builder.result()
    builder.add(2)

    assertEquals(first, DepSet(1))
    assertEquals(builder.result(), DepSet(1, 2))
  }

  test("intersects checks overlap without producing an intersection set") {
    assert(DepSet(1, 3, 5).intersects(DepSet(2, 3, 4)))
    assert(DepSet(2, 3, 4).intersects(DepSet(1, 3, 5)))
    assert(!DepSet(1, 3, 5).intersects(DepSet(2, 4, 6)))
    assert(!DepSet.empty.intersects(DepSet(1)))
    assert(!DepSet(1).intersects(DepSet.empty))
  }
}
