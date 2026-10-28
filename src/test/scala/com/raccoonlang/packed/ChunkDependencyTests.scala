package com.raccoonlang.packed

import com.raccoonlang._
import com.raccoonlang.Value._

class ChunkDependencyTests extends munit.FunSuite {
  private lazy val chainEnv: Env = {
    val source =
      """inductive Chain : Type
        | | end : Chain
        | | link (before: Nat)(tail: Chain)(after: Nat) : Chain
        |""".stripMargin
    val parsed = LanguageParser.parseProgram(source) match {
      case Success(program, _, _) => program
      case failure: Failure       => fail(s"Failed to parse fixture: $failure")
    }
    Elaborator.elab(parsed, Prelude.none).decls.foldLeft(Interpreter.initialEnv(Prelude.none)) { case (env, decl) =>
      Interpreter.evalDecl(decl, env)
    }
  }

  private def chunk(capacity: Int, origin: Int): Chunk = {
    val head = chainEnv("Chain.link").asInstanceOf[ConstructorHead]
    new Chunk(head, head.listShape.get, chainEnv("Chain"), capacity, origin)
  }

  /** Compare every range with a direct union of the independently retained payloads, including empty ranges. */
  private def assertRanges(chunk: Chunk, rows: Vector[Vector[Value]]): Unit = {
    assertEquals(chunk.back - chunk.front, rows.length)
    for {
      from <- 0 to rows.length
      until <- from to rows.length
    } {
      val expected = DepSet.unionAll(rows.slice(from, until).flatten.map(_.synDeps))
      assertEquals(chunk.payloadDeps(chunk.front + from, chunk.front + until), expected, s"range [$from, $until)")
    }
    assert(chunk.cachedDependencyBlocks < 2 * rows.length)
  }

  test("arbitrary ranges share exact summaries across prefixes and tails") {
    val pool = Vector.tabulate(8)(i => FreshVar.freshVar(s"x$i", Kernel.natType))
    // Two payloads per layer, repeated IDs, closed gaps and closed ends, in a non-power-of-two capacity.
    val rows = Vector.tabulate(67) { slot =>
      Vector.tabulate(2) { field =>
        if (slot < 4 || slot >= 63 || (slot + field) % 5 == 0) Kernel.zeroValue
        else pool((slot * 3 + field) % pool.length)
      }
    }
    val stored = chunk(rows.length, 0)
    assert(stored.claimBack(rows.length))
    stored.writePayloads(0, rows.flatten.toArray)
    assertRanges(stored, rows)
  }

  test("old range summaries remain exact after front growth, back growth and copies") {
    val a = FreshVar.freshVar("a", Kernel.natType)
    val b = FreshVar.freshVar("b", Kernel.natType)
    val copied = FreshVar.freshVar("copied", Kernel.natType)
    val stored = chunk(47, 17)
    var rows: Vector[Vector[Value]] = Vector.fill(13)(Vector(a, Kernel.zeroValue))
    assert(stored.claimBack(rows.length))
    stored.writePayloads(17, rows.flatten.toArray)
    assertRanges(stored, rows)

    val before = Vector.fill(7)(Vector(Kernel.zeroValue, b))
    assert(stored.claimFront(before.length))
    stored.writePayloads(stored.front, before.flatten.toArray)
    rows = before ++ rows
    assertRanges(stored, rows)

    val after = Vector.fill(11)(Vector(b, a))
    val previousBack = stored.back
    assert(stored.claimBack(after.length))
    stored.writePayloads(previousBack, after.flatten.toArray)
    rows ++= after
    assertRanges(stored, rows)

    // The copied dependency window includes closed gaps and excludes dependencies outside the source slice.
    val sourceRows = Vector
      .fill(11)(Vector(Kernel.zeroValue, Kernel.zeroValue): Vector[Value])
      .updated(0, Vector(a, b))
      .updated(5, Vector(copied, copied))
      .updated(10, Vector(a, b))
    val source = chunk(sourceRows.length, 0)
    assert(source.claimBack(sourceRows.length))
    source.writePayloads(0, sourceRows.flatten.toArray)
    val destination = stored.back
    assert(stored.claimBack(6))
    stored.copyLayers(destination, source, 2, 6)
    rows ++= sourceRows.slice(2, 8)
    assertRanges(stored, rows)
    assertEquals(stored.payloadDeps(17, 30), a.synDeps)
  }

  test("closed ranges allocate no summaries, including after nearby open growth") {
    val stored = chunk(1031, 0)
    assert(stored.claimBack(1024))
    stored.writePayloads(0, Array.fill[Value](2048)(Kernel.zeroValue))
    assertEquals(stored.payloadDeps(0, 1024), DepSet.empty)
    assertEquals(stored.cachedDependencyBlocks, 0)

    val x = FreshVar.freshVar("x", Kernel.natType)
    assert(stored.claimBack(7))
    stored.writePayloads(1024, Array.fill[Value](12)(Kernel.zeroValue) ++ Array[Value](x, x))
    assertEquals(stored.payloadDeps(0, 1031), x.synDeps)
    assertEquals(stored.cachedDependencyBlocks, 1)
    assertEquals(stored.payloadDeps(0, 1024), DepSet.empty)
    assertEquals(stored.cachedDependencyBlocks, 1)
  }

  test("saving growing open prefixes and their tails retains linearly many summaries") {
    val listNat = Interpreter.evalApply(Kernel.env("List"), Vector(Kernel.natType))
    val nilNat = Interpreter.evalApply(Kernel.env("List.nil"), Vector(Kernel.natType))
    val listLists = Interpreter.evalApply(Kernel.env("List"), Vector(listNat))
    var history = Interpreter.evalApply(Kernel.env("List.nil"), Vector(listNat))
    val x = FreshVar.freshVar("x", Kernel.natType)
    val piece = ConstructorValue(Kernel.listCons, Vector(x, nilNat), listNat)
    var prefix = nilNat
    val snapshots = Vector.newBuilder[VWord]
    (1 to 4096).foreach { n =>
      prefix = Words.append(prefix, piece)
      // Storing a prefix as a payload demands its dependencies through the ordinary constructor path.
      history = ConstructorValue(Kernel.listCons, Vector(prefix, history), listLists)
      assertEquals(prefix.synDeps, x.synDeps)
      val tail = ConstructorValue.unapply(prefix).get._2(1)
      assertEquals(tail.synDeps, if (n == 1) DepSet.empty else x.synDeps)
      val word = prefix.asInstanceOf[VWord]
      val stored = word.repr.chunk
      assert(stored.cachedDependencyBlocks < 2 * (stored.back - stored.front))
      if ((n & (n - 1)) == 0) snapshots += word
    }
    snapshots.result().foreach { word =>
      val segment = word.repr
      assertEquals(segment.chunk.payloadDeps(segment.start, segment.end), x.synDeps)
    }
    assertEquals(history.synDeps, x.synDeps)

    val y = FreshVar.freshVar("y", Kernel.natType)
    val z = FreshVar.freshVar("z", Kernel.natType)
    val left = Words.append(prefix, ConstructorValue(Kernel.listCons, Vector(y, nilNat), listNat))
    val right = Words.append(prefix, ConstructorValue(Kernel.listCons, Vector(z, nilNat), listNat))
    assertEquals(left.synDeps, x.synDeps ++ y.synDeps)
    assertEquals(right.synDeps, x.synDeps ++ z.synDeps)
    assertEquals(prefix.synDeps, x.synDeps)
  }
}
