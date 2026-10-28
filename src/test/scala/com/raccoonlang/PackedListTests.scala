package com.raccoonlang

import com.raccoonlang.ErrorReporter.Source
import com.raccoonlang.Value._
import com.raccoonlang.packed.{Storage, Words}
import com.raccoonlang.packed.Storage.{segment, segments}

import scala.util.Random

class PackedListTests extends munit.FunSuite {
  private val span = Span(0, 0)

  private def elabAndRun(src: String): Env =
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.default)
        try
          core.decls.foldLeft(Interpreter.initialEnv(Prelude.default)) { case (env, decl) =>
            Interpreter.evalDecl(decl, env)
          }
        catch { case t: TypeError => fail(ErrorReporter.pretty(t, Source(src))) }
      case err: Failure => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }

  private def runProgram(src: String): Value =
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.default)
        try Interpreter.run(core, Prelude.default).getOrElse(fail("Program has no body"))
        catch { case t: TypeError => fail(ErrorReporter.pretty(t, Source(src))) }
      case err: Failure => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }

  private def typeError[T <: TypeError](src: String)(implicit ct: reflect.ClassTag[T]): T =
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        intercept[T] {
          val core = Elaborator.elab(value, Prelude.default)
          Interpreter.run(core, Prelude.default)
        }
      case err: Failure => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }

  private lazy val env: Env = Interpreter.initialEnv(Prelude.default)
  private lazy val cons: ConstructorHead = env("List.cons").asInstanceOf[ConstructorHead]

  private def listType(element: Value): Value = Interpreter.evalApply(env("List"), Vector(element))
  private def nil(element: Value): Value = Interpreter.evalApply(env("List.nil"), Vector(element))
  private lazy val listNat: Value = listType(Kernel.natType)
  private lazy val nilNat: Value = nil(Kernel.natType)

  private def numeral(n: Int): String = (0 until n).foldLeft("Nat.zero")((term, _) => s"Nat.succ($term)")

  private def nat(n: Int): Value = NatNormalForm.literal(BigInt(n))

  private def consOnto(element: Value, tail: Value, tpe: Value): Value =
    ConstructorValue(cons, Vector(element, tail), tpe)

  private def build(elements: Seq[Value], terminator: Value, tpe: Value = listNat): Value =
    elements.foldRight(terminator)((element, tail) => consOnto(element, tail, tpe))

  /** The elements and terminator, through the constructor view. */
  private def decode(list: Value): (Vector[Value], Value) = {
    val elements = Vector.newBuilder[Value]
    var current = list
    var done = false
    while (!done) current match {
      case ConstructorValue(head, Vector(element, tail)) if head.name == "List.cons" =>
        elements += element
        current = tail
      case _ => done = true
    }
    (elements.result(), current)
  }

  private def withVerifiedKeys[T](body: => T): T = {
    val previous = Words.verifyKeys
    Words.verifyKeys = true
    try body
    finally Words.verifyKeys = previous
  }

  /** The tail of a kernel `List` cons, through the constructor view. */
  private def tail(list: Value): Value =
    ConstructorValue.unapply(list) match {
      case Some((_, Vector(_, rest))) => rest
      case other                      => fail(s"expected a cons, got $other")
    }

  /** Run on a thread with a small stack, so a recursion per element would overflow. */
  private def onSmallStack[T](body: => T): T = {
    var result: Option[Either[Throwable, T]] = None
    val thread = new Thread(
      null,
      () =>
        result = Some(
          try Right(body)
          catch { case t: Throwable => Left(t) }
        ),
      "small",
      512 * 1024
    )
    thread.start()
    thread.join()
    result.get.fold(throw _, identity)
  }

  private def assertSameList(left: Value, right: Value): Unit = {
    assert(ValueEquivalence.defEq(left, right), s"$left and $right do not convert")
    assert(ValueEquivalence.defEq(right, left))
    assertEquals(left.key, right.key)
    assertEquals(left.toString, right.toString)
    val (leftElements, leftEnd) = decode(left)
    val (rightElements, rightEnd) = decode(right)
    assertEquals(leftElements.map(_.key), rightElements.map(_.key))
    assertEquals(leftEnd.key, rightEnd.key)
    assertEquals(left.synDeps, right.synDeps)
  }

  // ------------ Shape detection ------------

  private def shapeOf(src: String, ctor: String): Option[ListShape] =
    elabAndRun(src)(ctor).asInstanceOf[ConstructorHead].listShape

  test("the kernel's List is list-shaped and Nat is not") {
    assertEquals(cons.listShape, Some(ListShape(1, 1)))
    assertEquals(env("List.nil").asInstanceOf[ConstructorHead].listShape, None)
    assertEquals(Kernel.succ.listShape, None)
    assert(consOnto(nat(1), nilNat, listNat).isInstanceOf[VWord])
  }

  test("user list-shaped types record the recursive field and the payload width") {
    val src =
      """
        |inductive Dir : Type
        | | left : Dir
        | | right : Dir
        |
        |inductive Path : Type
        | | done (dest: Nat) : Path
        | | step (dir: Dir)(rest: Path)(cost: Nat) : Path
        |
        |inductive Snoc (A: Type) : Type
        | | empty {A: Type} : Snoc(A)
        | | push {A: Type} (init: Snoc(A))(last: A) : Snoc(A)
        |
        |inductive Unary : Type
        | | z : Unary
        | | s (_: Unary) : Unary
        |""".stripMargin
    val loaded = elabAndRun(src)
    def shape(name: String) = loaded(name).asInstanceOf[ConstructorHead].listShape
    assertEquals(shape("Path.step"), Some(ListShape(1, 2)))
    assertEquals(shape("Path.done"), None)
    assertEquals(shape("Snoc.push"), Some(ListShape(0, 1)))
    assertEquals(shape("Unary.s"), Some(ListShape(0, 0)))
  }

  test("types that are not list-shaped keep constructor applications") {
    val notListShaped = Vector(
      // two recursive fields
      """inductive T : Type
        | | leaf : T
        | | node (l: T)(r: T) : T""" -> "T.node",
      // two recursive constructors
      """inductive T : Type
        | | leaf : T
        | | a (t: T) : T
        | | b (t: T) : T""" -> "T.a",
      // recursion under a binder
      """inductive T : Type
        | | leaf : T
        | | lim (f: Nat -> T) : T""" -> "T.lim",
      // no end constructor
      """inductive T : Type
        | | more (t: T) : T""" -> "T.more",
      // indices
      """inductive V (A: Type) indices (n: Nat) : Type
        | | vnil {A: Type} : V(A, Nat.zero)
        | | vcons {A: Type} (tail: V(A, $n)) (head: A) : V(A, Nat.succ(n))""" -> "V.vcons",
      // a proposition family
      """inductive P : Prop
        | | base : P
        | | more (p: P) : P""" -> "P.more",
      // not applied to its own parameters
      """inductive T (A: Type) : Type
        | | leaf {A: Type} : T(A)
        | | wrap {A: Type} (t: T(Nat)) : T(A)""" -> "T.wrap"
    )
    notListShaped.foreach { case (decl, ctor) =>
      assertEquals(shapeOf(decl.stripMargin + "\n", ctor), None, decl)
    }
  }

  // ------------ Storage ------------

  test("consing in order fills one chunk from the back, and branching starts a new chunk") {
    val one = consOnto(nat(1), nilNat, listNat)
    val two = consOnto(nat(2), one, listNat)
    assert(segment(two).chunk eq segment(one).chunk)
    assertEquals(
      (segment(two).start, segment(two).end, Storage.layers(two)),
      (segment(one).start - 1, segment(one).end, 2L)
    )
    // The slot before `one` is taken, so a second cons onto it starts a minimum-size chunk that links to it.
    val other = consOnto(nat(3), one, listNat)
    assert(!(segment(other).chunk eq segment(one).chunk))
    assert(segment(other).next eq one)
    assertEquals(segment(other).capacity, Storage.MinCapacity)
    assertEquals(decode(two)._1.map(_.key), Vector(nat(2), nat(1)).map(_.key))
    assertEquals(decode(other)._1.map(_.key), Vector(nat(3), nat(1)).map(_.key))
    // A type with the same key, built separately, claims too.
    val three = consOnto(nat(4), two, listType(Kernel.natType))
    assert(segment(three).chunk eq segment(one).chunk)
  }

  test("chunk capacities double up to the maximum") {
    val list = build((0 until 20000).map(nat), nilNat)
    val capacities = segments(list).map(_.capacity)
    assertEquals(capacities.last, Storage.MinCapacity)
    assertEquals(capacities.max, Storage.MaxCapacity)
    assertEquals(Storage.layers(list), 20000L)
  }

  test("replacing the head of a long list and branching onto mid-chunk tails allocate minimum-size chunks") {
    val list = build((0 until 10000).map(nat), nilNat)
    assertEquals(segment(list).capacity, Storage.MaxCapacity)
    val replaced = consOnto(nat(7), tail(list), listNat)
    assertEquals(segment(replaced).capacity, Storage.MinCapacity)
    var rest: Value = list
    (1 to 100).foreach { _ =>
      rest = tail(rest)
      val branch = consOnto(nat(8), rest, listNat)
      assertEquals(segment(branch).capacity, Storage.MinCapacity)
      assert(segment(branch).next eq rest)
    }
    // Consing onto the branch continues in its chunk; only a chunk filled down to slot 0 doubles.
    val extended = build((0 until Storage.MinCapacity).map(nat), replaced)
    val pieces = segments(extended)
    assertEquals(pieces(0).capacity, Storage.MinCapacity * 2)
    assert(pieces(1).chunk eq segment(replaced).chunk)
  }

  test("a list of many one-layer segments, built by branching at every cons, stays small and walks in loops") {
    val n = 200000
    onSmallStack {
      var branched = nilNat
      (0 until n).reverse.foreach { i =>
        consOnto(nat(1000), branched, listNat) // takes the slot before `branched`
        branched = consOnto(nat(i % 10), branched, listNat)
      }
      val pieces = segments(branched)
      assertEquals(pieces.length, n)
      assert(pieces.forall(_.capacity == Storage.MinCapacity))
      assertSameList(branched, build((0 until n).map(i => nat(i % 10)), nilNat))
    }
  }

  test("dependencies of a segment are exact and found through the dependency window") {
    val x = FreshVar.freshVar("x", Kernel.natType)
    val t = FreshVar.freshVar("t", listNat)
    val closedPrefix = build(Vector(nat(1), nat(2)), consOnto(x, t, listNat))
    assertEquals(closedPrefix.synDeps, DepSet(x.id, t.id) ++ listNat.synDeps)
    assert(tail(closedPrefix).synDeps.contains(x.id))
    assertEquals(build(Vector(nat(1), nat(2)), nilNat).synDeps, DepSet.empty)
    assert(Value.ReductionBlockers.of(closedPrefix).isEmpty)
  }

  // ------------ Storage is invisible ------------

  /** Build a list with the given elements and terminator by a randomly chosen mix of storage operations. */
  private def buildRandomly(random: Random, elements: Vector[Value], terminator: Value): Value = {
    var list = terminator
    elements.reverseIterator.foreach { element =>
      random.nextInt(4) match {
        case 0 =>
          // Branch: another cons takes the slot before the tail first.
          consOnto(nat(1000 + random.nextInt(5)), list, listNat)
        case 1 =>
          // Build a longer list and decode its extra layers away, leaving a tail in the middle of a chunk.
          val junk = Vector.fill(1 + random.nextInt(3))(nat(random.nextInt(7)))
          var longer = build(junk, list)
          junk.foreach(_ => longer = tail(longer))
          list = longer
        case _ => ()
      }
      list = consOnto(element, list, if (random.nextBoolean()) listNat else listType(Kernel.natType))
    }
    list
  }

  test("equal lists built in different ways convert, share keys, print and decode alike") {
    withVerifiedKeys {
      val random = new Random(7)
      val atoms = Vector.tabulate(3)(i => FreshVar.freshVar(s"a$i", Kernel.natType))
      val tails = Vector.tabulate(2)(i => FreshVar.freshVar(s"t$i", listNat))
      (0 until 200).foreach { _ =>
        val elements = Vector.fill(random.nextInt(40))(
          if (random.nextInt(5) == 0) atoms(random.nextInt(atoms.length)) else nat(random.nextInt(4))
        )
        val terminator = if (random.nextBoolean()) nilNat else tails(random.nextInt(tails.length))
        val direct = build(elements, terminator)
        val other = buildRandomly(random, elements, terminator)
        assertSameList(direct, other)

        if (elements.nonEmpty) {
          val changed = elements.updated(random.nextInt(elements.length), nat(17))
          val different = buildRandomly(random, changed, terminator)
          assert(!ValueEquivalence.defEq(direct, different))
          assertNotEquals(direct.key, different.key)
          val longer = buildRandomly(random, elements :+ nat(0), terminator)
          assert(!ValueEquivalence.defEq(direct, longer))
        }
      }
    }
  }

  test("materialization rebuilds affected segments and splices a solved terminator") {
    withVerifiedKeys {
      val random = new Random(11)
      (0 until 100).foreach { _ =>
        val elements = Vector.fill(random.nextInt(60))(nat(random.nextInt(5)))
        val suffix = Vector.fill(random.nextInt(10))(nat(random.nextInt(5)))
        val holes = elements.indices.filter(_ => random.nextInt(6) == 0).toSet
        val vars = elements.indices.map(i => FreshVar.freshVar(s"x$i", Kernel.natType))
        val t = FreshVar.freshVar("t", listNat)
        val open = buildRandomly(random, elements.indices.map(i => if (holes(i)) vars(i) else elements(i)).toVector, t)
        val solutions = holes.toVector.map(i => vars(i).id -> elements(i)) :+ (t.id -> build(suffix, nilNat))
        val store = solutions.foldLeft(EqStore.empty) { case (store, (id, value)) =>
          store.allow(DepSet(id)).addLink(id, value)
        }
        val materialized = ValueOps.materialize(open, store)
        assertSameList(materialized, build(elements ++ suffix, nilNat))
      }
    }
  }

  test("convertible elements with different keys convert structurally") {
    val program =
      """
        |def inc1 (n: Nat): Nat := Nat.succ(n)
        |def inc2 (m: Nat): Nat := Nat.add(m, Nat.succ(Nat.zero))
        |""".stripMargin
    val loaded = elabAndRun(program)
    val f = loaded("inc1")
    val g = loaded("inc2")
    assertNotEquals(f.key, g.key)
    assert(ValueEquivalence.defEq(f, g))
    val fnList = listType(f.tpe)
    val left = build(Vector(f, g, f), nil(f.tpe), fnList)
    val right = build(Vector(g, f, g), nil(f.tpe), fnList)
    assert(left.needsStructuralDefEq)
    assertNotEquals(left.key, right.key)
    assert(ValueEquivalence.defEq(left, right))
    assert(!ValueEquivalence.defEq(left, build(Vector(g, f), nil(f.tpe), fnList)))
  }

  test("words of different lengths are rejected before any element is compared") {
    val program =
      """
        |def inc1 (n: Nat): Nat := Nat.succ(n)
        |def inc2 (m: Nat): Nat := Nat.add(m, Nat.succ(Nat.zero))
        |""".stripMargin
    val loaded = elabAndRun(program)
    val f = loaded("inc1")
    val g = loaded("inc2")
    val fnList = listType(f.tpe)
    val n = 20000
    val fs = build(Vector.fill(n)(f), nil(f.tpe), fnList)
    val gs = build(Vector.fill(n)(g), nil(f.tpe), fnList)
    val longer = build(Vector.fill(n + 1)(g), nil(f.tpe), fnList)
    val threads = java.lang.management.ManagementFactory.getThreadMXBean
    def cpu(run: => Boolean): (Boolean, Long) = {
      val start = threads.getCurrentThreadCpuTime
      val result = run
      (result, threads.getCurrentThreadCpuTime - start)
    }
    // Equal lengths compare every pair of elements structurally; one more element on one side compares none.
    val (equal, walked) = cpu(ValueEquivalence.defEq(fs, gs))
    val (unequal, rejected) = cpu(ValueEquivalence.defEq(fs, longer))
    assert(equal)
    assert(!unequal)
    assert(rejected * 20 < walked, s"rejection took $rejected ns against $walked ns for the full walk")
  }

  // ------------ Unification ------------

  test("unification decomposes common prefixes and refutes nil against cons") {
    val x = FreshVar.freshVar("x", Kernel.natType)
    val y = FreshVar.freshVar("y", Kernel.natType)
    val t = FreshVar.freshVar("t", listNat)
    val store = EqStore.empty.allow(DepSet(x.id, y.id, t.id))
    val pattern = build(Vector(x, nat(2), y), t)
    val target = build(Vector(nat(1), nat(2), nat(3), nat(4)), nilNat)
    val solved = ValueEquivalence.tryUnify(pattern, target, store).fold(f => fail(s"unexpected $f"), identity)
    assertSameList(ValueOps.materialize(pattern, solved), target)

    ValueEquivalence.tryUnify(build(Vector(nat(1)), nilNat), build(Vector(nat(1), nat(2)), nilNat), store) match {
      case Left(_: ValueEquivalence.UnificationFailure.Contradiction) =>
      case other                                                      => fail(s"expected a contradiction, got $other")
    }
    ValueEquivalence.tryUnify(nilNat, pattern, store) match {
      case Left(_: ValueEquivalence.UnificationFailure.Contradiction) =>
      case other                                                      => fail(s"expected a contradiction, got $other")
    }
  }

  // ------------ Termination and positivity ------------

  test("structural recursion over packed lists accepts deeper suffixes and rejects larger arguments") {
    val result = runProgram(
      s"""
         |def everyOther (xs: List(Nat)): Nat decreases structural(xs) := {
         |  match xs returning Nat with
         |  | List.nil => Nat.zero
         |  | List.cons h t => {
         |    match t returning Nat with
         |    | List.nil => h
         |    | List.cons h2 t2 => Nat.add(h, everyOther(t2))
         |  }
         |}
         |
         |{
         |  everyOther(${(1 to 5).foldRight("List.nil(Nat)")((k, tail) => s"List.cons(${numeral(k)}, $tail)")})
         |}
         |""".stripMargin
    )
    assertEquals(result.key, nat(9).key)

    typeError[NonDecreasingRecursiveCall](
      """
        |def grow (xs: List(Nat)): Nat decreases structural(xs) := {
        |  match xs returning Nat with
        |  | List.nil => Nat.zero
        |  | List.cons h t => grow(List.cons(h, List.cons(h, t)))
        |}
        |""".stripMargin
    )
  }

  test("positivity sees through packed lists in family arguments") {
    elabAndRun(
      """
        |inductive Holds (ps: List(Prop)) : Prop
        |
        |inductive Good : Prop
        | | mk (h: Holds(List.cons(True, List.nil(Prop)))) : Good
        |""".stripMargin
    )
    typeError[NonStrictlyPositive](
      """
        |inductive Holds (ps: List(Prop)) : Prop
        |
        |inductive Bad : Prop
        | | mk (h: Holds(List.cons(True, List.cons(Bad, List.nil(Prop))))) : Bad
        |""".stripMargin
    )
  }

  // ------------ Long lists ------------

  test("a long list converts, unifies, materializes, quotes and prints without recursion per element") {
    val n = 100000
    val loaded =
      elabAndRun(
        "def inc1 (n: Nat): Nat := Nat.succ(n)\ndef inc2 (m: Nat): Nat := Nat.add(m, Nat.succ(Nat.zero))\ndef same (k: Nat): Nat := k"
      )
    val f = loaded("inc1")
    val g = loaded("inc2")
    val h = loaded("same")
    onSmallStack {
      val elements = (0 until n).map(i => nat(i % 10))
      val fnList = listType(f.tpe)
      // A function element makes every chunk need structural conversion, so conversion walks both lists.
      val left = build(f +: Vector.fill(n)(f), nil(f.tpe), fnList)
      val right = build(g +: Vector.fill(n)(f), nil(f.tpe), fnList)
      assert(ValueEquivalence.defEq(left, right))
      assert(!ValueEquivalence.defEq(left, build(g +: Vector.fill(n - 1)(f) :+ h, nil(f.tpe), fnList)))

      val t = FreshVar.freshVar("t", listNat)
      val open = build(elements, t)
      val closed = build(elements, nilNat)
      val store = EqStore.empty.allow(DepSet(t.id))
      val unified = ValueEquivalence.tryUnify(open, closed, store).fold(f => fail(s"unexpected $f"), identity)
      val materialized = ValueOps.materialize(open, unified)
      assertEquals(materialized.key, closed.key)

      val x = FreshVar.freshVar("x", Kernel.natType)
      val holes = build((0 until n).map(i => if (i % 1000 == 0) x else nat(i % 10)), nilNat)
      val filled = ValueOps.materialize(holes, EqStore.empty.allow(DepSet(x.id)).addLink(x.id, nat(0)))
      assertEquals(filled.key, closed.key)
      assert(ValueEquivalence.defEq(filled, closed))

      assert(closed.toString.length > n)
    }
  }

  test("a long list quotes as one flat word, and evaluating the quotation rebuilds it") {
    val n = 100000
    val loaded = elabAndRun(
      """
        |inductive Path : Type
        | | done (dest: Nat) : Path
        | | step (dir: Nat)(rest: Path)(cost: Nat) : Path
        |
        |inductive Snoc (A: Type) : Type
        | | empty {A: Type} : Snoc(A)
        | | push {A: Type} (init: Snoc(A))(last: A) : Snoc(A)
        |""".stripMargin
    )
    val pathType = loaded("Path")
    val step = loaded("Path.step").asInstanceOf[ConstructorHead]
    val snocNat = Interpreter.evalApply(loaded("Snoc"), Vector(Kernel.natType))
    val push = loaded("Snoc.push").asInstanceOf[ConstructorHead]
    onSmallStack {
      val kernel = build((0 until n).map(i => nat(i % 10)), nilNat)
      val path = (0 until n).foldRight(Interpreter.evalApply(loaded("Path.done"), Vector(nat(3)))) { (i, rest) =>
        ConstructorValue(step, Vector(nat(i % 10), rest, nat(i % 7)), pathType)
      }
      val snoc = (0 until n).foldRight(Interpreter.evalApply(loaded("Snoc.empty"), Vector(Kernel.natType))) {
        (i, init) => ConstructorValue(push, Vector(init, nat(i % 10)), snocNat)
      }
      Vector(kernel, path, snoc).foreach { list =>
        val quoted = ValueQuote.quoteTerm(list, ValueQuote.QuoteContext(Map.empty, 0), span)
        quoted match {
          case ElabAst.Term.Word(_, pieces, _) => assertEquals(pieces.length, n + 1) // the layers, then the end
          case other                           => fail(s"expected a word, got ${other.getClass}")
        }
        assert(quoted.toString.length > n)
        val rebuilt = Interpreter.evalTerm(quoted, loaded)
        assertEquals(rebuilt.key, list.key)
        assert(ValueEquivalence.defEq(rebuilt, list))
      }
      val snocQuoted = ValueQuote.quoteTerm(snoc, ValueQuote.QuoteContext(Map.empty, 0), span).toString
      assert(snocQuoted.startsWith("Snoc.push(Nat, Snoc.push(Nat, "), snocQuoted.take(80))
    }
  }
}
