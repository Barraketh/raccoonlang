package com.raccoonlang

import com.raccoonlang.ErrorReporter.Source
import com.raccoonlang.ValueEquivalence.UnificationFailure
import com.raccoonlang.Value._
import com.raccoonlang.packed.{Storage, Words}
import com.raccoonlang.packed.Storage.segment

import scala.util.Random

object KernelListTests {

  /** A list as its elements and its end: `nil`, or a stuck value such as a variable of type `List(Nat)`. */
  final case class Spec(elements: Vector[Value], end: Value)
}

class KernelListTests extends munit.FunSuite {
  import KernelListTests.Spec
  private val span = Span(0, 0)

  private val taggedListDeclarations =
    """axiom ys : List(Nat)
      |inductive Tagged (A: Type)(xs: List(Nat)) : Type
      | | mk {A: Type}{xs: List(Nat)} : Tagged(A, xs)
      |
      |""".stripMargin

  private def parse(src: String): SurfaceAst.Program =
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) => value
      case err: Failure         => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }

  private def elabAndRun(src: String, prelude: Prelude.Config = Prelude.default): Env = {
    val core = Elaborator.elab(parse(src), prelude)
    try
      core.decls.foldLeft(Interpreter.initialEnv(prelude)) { case (env, decl) =>
        Interpreter.evalDecl(decl, env)
      }
    catch { case t: TypeError => fail(ErrorReporter.pretty(t, Source(src))) }
  }

  private def runProgram(src: String): Value = {
    val core = Elaborator.elab(parse(src), Prelude.default)
    try Interpreter.run(core, Prelude.default).getOrElse(fail("Program has no body"))
    catch { case t: TypeError => fail(ErrorReporter.pretty(t, Source(src))) }
  }

  private def typeError[T <: TypeError](src: String)(implicit ct: reflect.ClassTag[T]): T =
    intercept[T] {
      val core = Elaborator.elab(parse(src), Prelude.default)
      Interpreter.run(core, Prelude.default)
    }

  private lazy val env: Env = Interpreter.initialEnv(Prelude.default)
  private lazy val cons: ConstructorHead = env("List.cons").asInstanceOf[ConstructorHead]
  private lazy val listNat: Value = Interpreter.evalApply(env("List"), Vector(Kernel.natType))
  private lazy val nilNat: Value = Interpreter.evalApply(env("List.nil"), Vector(Kernel.natType))

  private def nat(n: Int): Value = NatNormalForm.literal(BigInt(n))

  private def consOnto(element: Value, tail: Value): Value = ConstructorValue(cons, Vector(element, tail), listNat)

  private def append(l: Value, r: Value): Value = Interpreter.evalApply(env("List.append"), Vector(l, r))

  private def length(l: Value): Value = Interpreter.evalApply(env("List.length"), Vector(l))

  private def build(elements: Seq[Value], terminator: Value = nilNat): Value =
    elements.foldRight(terminator)(consOnto)

  /** The tail of a cons, through the constructor view. */
  private def tail(list: Value): Value =
    ConstructorValue.unapply(list) match {
      case Some((_, Vector(_, rest))) => rest
      case other                      => fail(s"expected a cons, got $other")
    }

  private def withVerifiedKeys[T](body: => T): T = {
    val previous = Words.verifyKeys
    Words.verifyKeys = true
    try body
    finally Words.verifyKeys = previous
  }

  /** Run on a thread with a large stack, for interpreted recursion as deep as a long list. */
  private def onLargeStack[T](body: => T): T = {
    var result: Option[Either[Throwable, T]] = None
    val thread = new Thread(
      null,
      () =>
        result = Some(
          try Right(body)
          catch { case t: Throwable => Left(t) }
        ),
      "large",
      1L << 30
    )
    thread.start()
    thread.join()
    result.get.fold(throw _, identity)
  }

  /** Run on a thread with a 1 MiB stack, so a recursion per element or per nested append would overflow. */
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
      1L << 20
    )
    thread.start()
    thread.join()
    result.get.fold(throw _, identity)
  }

  // ------------ Lists ------------

  private val stuck: Vector[Var] = Vector.tabulate(3)(i => FreshVar.freshVar(s"a$i", listNat))

  private def buildDirectly(spec: Spec): Value = build(spec.elements, spec.end)

  /**
   * The list split into random parts, each built directly or recursively, joined by a random tree of appends, with
   * random units. Only the last part carries the end, so every left operand ends in `nil`.
   */
  private def buildAssociated(random: Random, spec: Spec): Value =
    if (spec.elements.length <= 1 || random.nextInt(4) == 0) {
      val built = buildDirectly(spec)
      random.nextInt(4) match {
        case 0 => append(nilNat, built)
        case 1 => append(built, nilNat)
        case _ => built
      }
    } else {
      val split = 1 + random.nextInt(spec.elements.length - 1)
      append(
        buildAssociated(random, Spec(spec.elements.take(split), nilNat)),
        buildAssociated(random, Spec(spec.elements.drop(split), spec.end))
      )
    }

  private def randomSpec(random: Random, maxLength: Int, ends: Vector[Value]): Spec =
    Spec(Vector.fill(random.nextInt(maxLength + 1))(nat(random.nextInt(4))), ends(random.nextInt(ends.length)))

  private lazy val ends: Vector[Value] = nilNat +: stuck

  /** A list as its elements and end, read through its tokens. */
  private def decode(list: Value): Spec =
    list match {
      case word: VWord =>
        val elements = Vector.newBuilder[Value]
        var end: Value = null
        Words.foreach(word)(
          layer = token => {
            elements += token.payload(0)
            true
          },
          end = token => {
            end = token.value
            true
          }
        )
        Spec(elements.result(), end)
      case other => Spec(Vector.empty, other)
    }

  private def assertSameList(left: Value, right: Value): Unit = {
    assert(ValueEquivalence.defEq(left, right), s"$left and $right do not convert")
    assert(ValueEquivalence.defEq(right, left))
    assertEquals(left.key, right.key)
    assertEquals(left.toString, right.toString)
    val (l, r) = (decode(left), decode(right))
    assertEquals((l.elements.map(_.key), l.end.key), (r.elements.map(_.key), r.end.key))
    assertEquals(left.synDeps, right.synDeps)
  }

  /** Every word reachable from `value` through words' ends and applications' arguments, without recursion. */
  private def wordsIn(value: Value): Vector[VWord] = {
    val found = Vector.newBuilder[VWord]
    val pending = scala.collection.mutable.Stack(value)
    while (pending.nonEmpty) pending.pop() match {
      case word: VWord =>
        found += word
        pending.push(decode(word).end)
        decode(word).elements.foreach(pending.push)
      case VApp(_, args, _, _) => args.foreach(pending.push)
      case _                   =>
    }
    found.result()
  }

  private def assertNoStuckWord(value: Value): Unit =
    wordsIn(value).foreach { word =>
      assert(ReductionBlockers.of(word).isEmpty, word)
      assert(Blocked.unapply(word).isEmpty, word)
      assert(ConstructorValue.unapply(word).exists(_._1.name == Kernel.ListConsName), word)
    }

  test("kernel List cannot be redeclared, and programs without a prelude see it") {
    intercept[AlreadyDefined] {
      Elaborator.elab(parse("inductive List (A: Type) : Type\n | nil {A: Type} : List(A)\n"), Prelude.none)
    }
    val loaded =
      elabAndRun(
        "def two : Nat := List.length(List.cons(Nat.zero, List.cons(Nat.zero, List.nil(Nat))))\n",
        Prelude.none
      )
    assertEquals(loaded("two").key, nat(2).key)
  }

  test("units hold by conversion, and so does every association whose left operands end in nil") {
    withVerifiedKeys {
      val random = new Random(3)
      (0 until 300).foreach { _ =>
        val spec = randomSpec(random, 24, ends)
        val direct = buildDirectly(spec)
        assertEquals(decode(direct).elements.map(_.key), spec.elements.map(_.key))
        assertSameList(direct, buildAssociated(random, spec))
        assertSameList(direct, append(nilNat, direct))
        assert(append(direct, nilNat) eq direct)
        assertNoStuckWord(direct)
      }
    }
  }

  test("different lists do not convert and have different keys") {
    withVerifiedKeys {
      val random = new Random(5)
      (0 until 300).foreach { _ =>
        val spec = randomSpec(random, 20, ends)
        val changed =
          random.nextInt(3) match {
            case 0 =>
              val at = random.nextInt(spec.elements.length + 1)
              spec.copy(elements = spec.elements.take(at) ++ Vector(nat(random.nextInt(4))) ++ spec.elements.drop(at))
            case 1 => spec.copy(end = ends.filterNot(_ eq spec.end)(random.nextInt(ends.length - 1)))
            case _ if spec.elements.isEmpty => spec.copy(elements = Vector(nat(0)))
            case _ =>
              val at = random.nextInt(spec.elements.length)
              spec.copy(elements = spec.elements.updated(at, nat((spec.elements(at).key.hashCode & 3) + 4)))
          }
        val left = buildAssociated(random, spec)
        val right = buildAssociated(random, changed)
        assert(!ValueEquivalence.defEq(left, right), s"$left and $right convert")
        assert(!ValueEquivalence.defEq(right, left))
        assertNotEquals(left.key, right.key)
      }
    }
  }

  test("solving a stuck end gives the same value as building the spliced list directly") {
    withVerifiedKeys {
      val random = new Random(9)
      val others = Vector.tabulate(2)(i => FreshVar.freshVar(s"b$i", listNat))
      (0 until 300).foreach { _ =>
        val spec = randomSpec(random, 16, stuck)
        val solution = randomSpec(random, 5, nilNat +: others)
        val variable = spec.end.asInstanceOf[Var]
        val store =
          EqStore.empty.allow(DepSet(variable.id)).addLink(variable.id, buildAssociated(random, solution))
        val materialized = ValueOps.materialize(buildAssociated(random, spec), store)
        assertSameList(materialized, buildDirectly(Spec(spec.elements ++ solution.elements, solution.end)))
        assertNoStuckWord(materialized)
      }
    }
  }

  /**
   * The list split into random parts joined by a random tree of appends, as `buildAssociated`, but each part built by a
   * random mix of storage operations: branching conses that take the slot before a tail, tails decoded from the middle
   * of a chunk, and discarded appends that take the free slots beside an operand first, so the junction copies, grows
   * or links.
   */
  private def buildShuffled(random: Random, spec: Spec): Value =
    if (spec.elements.length <= 1 || random.nextInt(3) == 0) {
      var list = spec.end
      spec.elements.reverseIterator.foreach { element =>
        random.nextInt(4) match {
          case 0 => consOnto(nat(1000 + random.nextInt(5)), list)
          case 1 =>
            val junk = Vector.fill(1 + random.nextInt(3))(nat(random.nextInt(7)))
            var longer = build(junk, list)
            junk.foreach(_ => longer = tail(longer))
            list = longer
          case _ => ()
        }
        list = consOnto(element, list)
      }
      list
    } else {
      val split = 1 + random.nextInt(spec.elements.length - 1)
      val left = buildShuffled(random, Spec(spec.elements.take(split), nilNat))
      val right = buildShuffled(random, Spec(spec.elements.drop(split), spec.end))
      val junk = build(Vector.fill(1 + random.nextInt(4))(nat(random.nextInt(7))))
      random.nextInt(4) match {
        case 0 => append(left, junk)
        case 1 => append(junk, right)
        case _ => ()
      }
      append(left, right)
    }

  test("every tail of lists with open elements, built through the junction, has its key and exact dependencies") {
    withVerifiedKeys {
      val random = new Random(13)
      val atoms = Vector.tabulate(4)(i => FreshVar.freshVar(s"e$i", Kernel.natType))
      (0 until 300).foreach { _ =>
        val elements = Vector.fill(random.nextInt(40)) {
          random.nextInt(4) match {
            case 0 => atoms(random.nextInt(atoms.length))
            case 1 => FreshVar.freshVar("f", Kernel.natType)
            case _ => nat(random.nextInt(4))
          }
        }
        val spec = Spec(elements, ends(random.nextInt(ends.length)))
        val list = buildShuffled(random, spec)
        if (random.nextBoolean()) list.synDeps // fill the caches from the root first, or from the tails
        var rest = list
        var index = 0
        while (index <= elements.length) {
          val walked = decode(rest)
          assertEquals(walked.elements.map(_.key), elements.drop(index).map(_.key))
          val expected = DepSet.unionAll(walked.elements.map(_.synDeps) :+ walked.end.synDeps :+ listNat.synDeps)
          assertEquals(rest.synDeps, expected, s"tail $index of $list")
          if (index < elements.length) rest = tail(rest)
          index += 1
        }
        assertSameList(list, buildDirectly(spec))
      }
    }
  }

  // ------------ Stuck appends ------------

  private def appendApplication(value: Value): Option[(Value, Value)] =
    value match {
      case VApp(head, Vector(x, r), _, _) if head eq env("List.append") => Some((x, r))
      case _                                                            => None
    }

  test("a list ending in a stuck value appends as a word ending in the stuck application of the native") {
    withVerifiedKeys {
      val Vector(x, a, _) = stuck
      val open = build((0 until 3).map(nat), x)
      val right = build(Vector(nat(7)), a)
      val joined = append(open, right)
      assertEquals(decode(joined).elements.map(_.key), (0 until 3).map(nat(_).key).toVector)
      assertEquals(
        appendApplication(decode(joined).end).map { case (l, r) => (l eq x, r eq right) },
        Some((true, true))
      )
      // A stuck left operand is itself the stuck application; associativity does not flatten it.
      val nested = append(append(x, right), right)
      appendApplication(nested) match {
        case Some((inner, outer)) => assert(appendApplication(inner).isDefined && (outer eq right), nested)
        case None                 => fail(s"expected a stuck application, got $nested")
      }
      assert(!ValueEquivalence.defEq(nested, append(x, append(right, right))))
      assertNoStuckWord(joined)
    }
  }

  test("the right unit holds for stuck lists and for words ending in one") {
    val Vector(x, _, _) = stuck
    assert(append(x, nilNat) eq x)
    val open = build(Vector(nat(1)), append(x, build(Vector(nat(2)))))
    assert(append(open, nilNat) eq open)
    assertSameList(append(append(x, build(Vector(nat(2)))), nilNat), append(x, build(Vector(nat(2)))))
  }

  test("a stuck append is blocked on its right operand too when that could become nil, and then reduces to its left") {
    val Vector(x, a, b) = stuck
    val app = append(x, a)
    assertEquals(ReductionBlockers.of(app), DepSet(x.id, a.id))
    // A word never becomes nil, so it adds no blockers, however it ends.
    assertEquals(ReductionBlockers.of(append(x, build(Vector(nat(1)), b))), DepSet(x.id))
    val toNil = EqStore.empty.allow(DepSet(a.id)).addLink(a.id, nilNat)
    assert(ValueOps.materialize(app, toNil) eq x)
    // Inside a word: the end is the stuck application, and solving its right operand to nil restores the stuck left one.
    val word = build(Vector(nat(1), nat(2)), app)
    assertSameList(ValueOps.materialize(word, toNil), build(Vector(nat(1), nat(2)), x))
    // Solving the left operand to a list computes the append.
    val toList = EqStore.empty.allow(DepSet(x.id)).addLink(x.id, build(Vector(nat(3))))
    assertSameList(ValueOps.materialize(word, toList), build(Vector(nat(1), nat(2), nat(3)), a))
  }

  test("no word is ever stuck, however lists are built, appended and solved") {
    val random = new Random(21)
    val others = Vector.tabulate(2)(i => FreshVar.freshVar(s"c$i", listNat))
    (0 until 200).foreach { _ =>
      val parts = Vector.fill(1 + random.nextInt(4))(randomSpec(random, 6, ends ++ others))
      val joined =
        parts.map(buildDirectly).reduceLeft((l, r) => if (random.nextBoolean()) append(l, r) else append(r, l))
      assertNoStuckWord(joined)
      val solved = stuck.filter(_ => random.nextBoolean())
      val store = solved.foldLeft(EqStore.empty.allow(DepSet.from(solved.map(_.id)))) { (store, variable) =>
        store.addLink(variable.id, buildDirectly(randomSpec(random, 4, nilNat +: others)))
      }
      assertNoStuckWord(ValueOps.materialize(joined, store))
    }
  }

  // ------------ Storage ------------

  test("append shares the right operand and the left operand's element storage") {
    withVerifiedKeys {
      val long = build((0 until 100).map(nat))
      val short = build(Vector(nat(7)))
      // The smaller left operand is copied into the free slots before the right one.
      val joined = append(short, long)
      assert(segment(joined).chunk eq segment(long).chunk)
      assertEquals(
        (segment(joined).start, segment(joined).end, Storage.layers(joined)),
        (segment(long).start - 1, segment(long).end, 101L)
      )
      // A second append onto the same right operand finds the slot taken, and links.
      val other = append(build(Vector(nat(8))), long)
      assert(segment(other).next eq long)
      // A left operand ending in a stuck value keeps its segment, followed by the stuck application.
      val x = stuck(0)
      val open = build((0 until 3).map(nat), x)
      val withStuck = append(open, long)
      assert(segment(withStuck).chunk eq segment(open).chunk)
      assertEquals((segment(withStuck).start, segment(withStuck).end), (segment(open).start, segment(open).end))
      assertEquals(
        appendApplication(segment(withStuck).next).map { case (l, r) => (l eq x, r eq long) },
        Some((true, true))
      )
    }
  }

  test("branching appends onto shared values convert, share keys, print and decode alike") {
    withVerifiedKeys {
      val random = new Random(13)
      (0 until 200).foreach { _ =>
        val left = randomSpec(random, 12, Vector(nilNat))
        val right = randomSpec(random, 12, ends)
        val shared = buildAssociated(random, right)
        // Other appends take the free slots around the shared operands first.
        val prefix = buildAssociated(random, left)
        append(prefix, build(Vector(nat(9))))
        append(build(Vector(nat(9))), shared)
        assertSameList(append(prefix, shared), buildDirectly(Spec(left.elements ++ right.elements, right.end)))
      }
    }
  }

  // ------------ Unification ------------

  private def unify(left: Value, right: Value, variables: Var*): Either[UnificationFailure, EqStore] =
    ValueEquivalence.tryUnify(left, right, EqStore.empty.allow(DepSet.from(variables.map(_.id))))

  test("unification decomposes prefixes, solves a stuck end, and refutes nil against cons") {
    val x = FreshVar.freshVar("x", Kernel.natType)
    val y = FreshVar.freshVar("y", Kernel.natType)
    val Vector(a, b, _) = stuck
    // [x, 2] ++ (a ++ [3]) = [1, 2] ++ (a ++ [3]); the ends convert, while ends that differ inside are stuck below
    val pattern = build(Vector(x, nat(2)), append(a, build(Vector(nat(3)))))
    val target = build(Vector(nat(1), nat(2)), append(a, build(Vector(nat(3)))))
    val solved = unify(pattern, target, x).fold(f => fail(s"unexpected $f"), identity)
    assertEquals(ValueOps.materialize(x, solved).key, nat(1).key)
    // [1] ++ b = [1, 2, 3], solving the end with the remaining layers
    val rest = unify(build(Vector(nat(1)), b), build(Vector(nat(1), nat(2), nat(3))), b)
    assertEquals(rest.map(store => ValueOps.materialize(b, store).key), Right(build(Vector(nat(2), nat(3))).key))

    unify(
      build(Vector(nat(1)), append(a, build(Vector(y)))),
      build(Vector(nat(1)), append(a, build(Vector(nat(3))))),
      y
    ) match {
      case Left(_: UnificationFailure.Stuck) =>
      case other                             => fail(s"expected no cancellation inside a stuck append, got $other")
    }
    unify(nilNat, build(Vector(nat(1)), a)) match {
      case Left(_: UnificationFailure.Contradiction) =>
      case other                                     => fail(s"expected a contradiction, got $other")
    }
  }

  test("a stuck append against cons, nil, or another stuck append is stuck") {
    val Vector(a, b, _) = stuck
    val stuckApp = append(a, b)
    val cases = Vector(
      stuckApp -> build(Vector(nat(1))),
      build(Vector(nat(1)), a) -> build(Vector(nat(1)), stuckApp),
      stuckApp -> nilNat,
      nilNat -> stuckApp,
      stuckApp -> append(b, a),
      append(a, build(Vector(nat(1)))) -> append(a, build(Vector(nat(2))))
    )
    cases.foreach { case (left, right) =>
      unify(left, right, a, b) match {
        case Left(_: UnificationFailure.Stuck) =>
        case other                             => fail(s"expected $left = $right to be stuck, got $other")
      }
    }
  }

  // ------------ Laws in programs ------------

  test("units, the cons step and the length laws hold definitionally; associativity is the prelude theorem") {
    elabAndRun(
      """
        |def leftUnit (a: List($A)): Eq(List(A), List.append(List.nil(A), a), a) := Eq.refl(a)
        |def rightUnit (a: List($A)): Eq(List(A), List.append(a, List.nil(A)), a) := Eq.refl(a)
        |def consStep (t: List($A))(h: A)(r: List(A)): Eq(List(A), List.append(List.cons(h, t), r), List.cons(h, List.append(t, r))) :=
        |  Eq.refl(List.cons(h, List.append(t, r)))
        |def lengthAppend (l: List($A))(r: List(A)): Eq(Nat, List.length(List.append(l, r)), Nat.add(List.length(l), List.length(r))) :=
        |  Eq.refl(List.length(List.append(l, r)))
        |def lengthCons (t: List($A))(h: A): Eq(Nat, List.length(List.cons(h, t)), Nat.succ(List.length(t))) :=
        |  Eq.refl(Nat.succ(List.length(t)))
        |def lengthMixed (a: List(Nat))(b: List(Nat)): Eq(Nat, List.length(List.append(a, List.cons(Nat.zero, b))), Nat.add(Nat.succ(List.length(b)), List.length(a))) :=
        |  Eq.refl(List.length(List.append(a, List.cons(Nat.zero, b))))
        |def lengthNested (a: List(Nat))(b: List(Nat))(c: List(Nat)): Eq(Nat, List.length(List.append(List.append(a, b), c)), Nat.add(List.length(a), Nat.add(List.length(b), List.length(c)))) :=
        |  Eq.refl(List.length(List.append(a, List.append(b, c))))
        |def assoc (a: List($A))(b: List(A))(c: List(A)): Eq(List(A), List.append(List.append(a, b), c), List.append(a, List.append(b, c))) :=
        |  List.append_assoc(a, b, c)
        |def assocClosedPrefix (b: List(Nat))(c: List(Nat)): Eq(List(Nat), List.append(List.append(List.cons(Nat.zero, List.nil(Nat)), b), c), List.cons(Nat.zero, List.append(b, c))) :=
        |  Eq.refl(List.cons(Nat.zero, List.append(b, c)))
        |""".stripMargin
    )
    typeError[TypeError](
      """
        |def assoc (a: List(Nat))(b: List(Nat))(c: List(Nat)): Eq(List(Nat), List.append(List.append(a, b), c), List.append(a, List.append(b, c))) :=
        |  Eq.refl(List.append(a, List.append(b, c)))
        |""".stripMargin
    )
    typeError[TypeError](
      """
        |def comm (a: List(Nat))(b: List(Nat)): Eq(List(Nat), List.append(a, b), List.append(b, a)) := Eq.refl(List.append(a, b))
        |""".stripMargin
    )
  }

  test("length of a closed list is its numeral, and of an open list a sum of stuck lengths") {
    val n = 1000000
    val long = build((0 until n).map(i => nat(i % 3)))
    assertEquals(length(long).key, nat(n).key)
    val Vector(a, b, _) = stuck
    val list = build(Vector(nat(1), nat(2)), append(a, build(Vector(nat(3)), b)))
    val expected = NatNormalForm.add(NatNormalForm.add(nat(3), length(a)), length(b))
    assertEquals(length(list).key, expected.key)
    val store = EqStore.empty.allow(DepSet(a.id)).addLink(a.id, build(Vector(nat(4), nat(5))))
    assertEquals(ValueOps.materialize(length(list), store).key, NatNormalForm.add(nat(5), length(b)).key)
  }

  test("length looks through stuck appends nested 10,000 deep without recursion") {
    val depth = 10000
    val Vector(x, a, _) = stuck
    onSmallStack {
      // Nested on the left, as repeated `acc ++ [i]` onto a stuck list writes it, and on the right, onto `a`.
      var left: Value = x
      var right: Value = a
      (0 until depth).foreach { i =>
        left = append(left, build(Vector(nat(i % 5))))
        right = append(x, right)
      }
      assertEquals(length(left).key, NatNormalForm.add(nat(depth), length(x)).key)
      val xs = (0 until depth).foldLeft(length(a))((sum, _) => NatNormalForm.add(sum, length(x)))
      assertEquals(length(right).key, xs.key)
    }
  }

  // ------------ Termination, matching, quotation, printing ------------

  test("structural recursion accepts tails and rejects an appended tail") {
    elabAndRun(
      """
        |def count (xs: List(Nat)): Nat decreases structural(xs) := {
        |  match xs returning Nat with
        |  | List.nil => Nat.zero
        |  | List.cons h t => Nat.succ(count(t))
        |}
        |""".stripMargin
    )
    typeError[NonDecreasingRecursiveCall](
      """
        |def grow (xs: List(Nat)): Nat decreases structural(xs) := {
        |  match xs returning Nat with
        |  | List.nil => Nat.zero
        |  | List.cons h t => grow(List.append(t, List.cons(h, List.nil(Nat))))
        |}
        |""".stripMargin
    )
  }

  test("positivity treats a stuck append as an application of a native, also at the end of a word") {
    val holds = "inductive Holds (ps: List(Prop)) : Prop\n\naxiom ps : List(Prop)\n\n"
    elabAndRun(
      holds + "inductive Good : Prop\n | mk (h: Holds(List.append(ps, List.cons(True, List.nil(Prop))))) : Good\n"
    )
    typeError[NonStrictlyPositive](
      holds + "inductive Bad : Prop\n | mk (h: Holds(List.append(ps, List.cons(Bad, List.nil(Prop))))) : Bad\n"
    )
    typeError[NonStrictlyPositive](
      holds +
        "inductive Bad : Prop\n | mk (h: Holds(List.cons(True, List.append(ps, List.cons(Bad, List.nil(Prop)))))) : Bad\n"
    )
  }

  test("a match on a stuck append is stuck on its blockers and resumes once the left operand is solved") {
    val loaded = elabAndRun(
      """
        |def isEmpty (xs: List(Nat)): Bool := {
        |  match xs returning Bool with
        |  | List.nil => Bool.true
        |  | List.cons h t => Bool.false
        |}
        |""".stripMargin
    )
    val Vector(a, b, _) = stuck
    val stuckMatch = Interpreter.evalApply(loaded("isEmpty"), Vector(append(a, b)))
    assertEquals(ReductionBlockers.of(stuckMatch), DepSet(a.id, b.id))
    val store = EqStore.empty.allow(DepSet(a.id)).addLink(a.id, build(Vector(nat(1))))
    assertEquals(ValueOps.materialize(stuckMatch, store).key, Kernel.falseValue.key)
  }

  test("lists print as words and quote to syntax that rebuilds the same value") {
    val loaded = elabAndRun("axiom xs : List(Nat)\naxiom ys : List(Nat)\n")
    val xs = loaded("xs")
    val ys = loaded("ys")
    val list = build(Vector(nat(1), nat(2)), append(xs, build(Vector(nat(3)), ys)))
    val (one, two, three) = (nat(1).toString, nat(2).toString, nat(3).toString)
    assertEquals(list.toString, s"[$one, $two] ++ List.append(xs, [$three] ++ ys)")
    assertEquals(nilNat.toString, "[]")
    assertEquals(append(xs, ys).toString, "List.append(xs, ys)")
    assertEquals(build(Vector(nat(1)), xs).toString, s"[$one] ++ xs")

    val quoted = ValueQuote.quoteTerm(list, ValueQuote.QuoteContext(Map.empty, 0), span)
    assert(PrettyPrinter.printElabTerm(quoted).contains("List.append(xs, "), PrettyPrinter.printElabTerm(quoted))
    val rebuilt = Interpreter.evalTerm(quoted, loaded)
    assertSameList(rebuilt, list)
  }

  test("quotation preserves captured list words in type patterns") {
    val loaded = elabAndRun(taggedListDeclarations)
    val context = ValueQuote.QuoteContext(Map.empty, 0)
    Vector("List.cons(Nat.zero, List.nil(Nat))", "List.append(ys, ys)").foreach { list =>
      val closure = runProgram(
        taggedListDeclarations +
          s"""{
             |  let xs := $list
             |  fun (t: Tagged($$A, xs)): Nat => Nat.zero
             |}
             |""".stripMargin
      )
      val quoted = ValueQuote.quoteTerm(closure, context, span)
      assert(quoted.toString.contains(s"Tagged($$A, $list)"), quoted.toString)
      val rebuilt = Interpreter.evalTerm(quoted, loaded)
      assert(ValueEquivalence.defEq(rebuilt, closure), list)

      // The rebuilt binder already contains a Word, so quoting it again must inline that type term too.
      val requoted = ValueQuote.quoteTerm(rebuilt, context, span)
      assert(ValueEquivalence.defEq(Interpreter.evalTerm(requoted, loaded), closure), list)
    }
  }

  test("match result inference preserves captured list words in type patterns") {
    Vector("List.cons(Nat.zero, List.nil(Nat))", "List.append(ys, ys)").foreach { list =>
      val result = runProgram(
        taggedListDeclarations +
          s"""axiom flag : Bool
             |{
             |  match flag with
             |  | Bool.false => {
             |    let xs := $list
             |    fun (t: Tagged($$A, xs)): Nat => Nat.zero
             |  }
             |  | Bool.true => fun (t: Tagged($$A, $list)): Nat => Nat.zero
             |}
             |""".stripMargin
      )
      val expected = runProgram(taggedListDeclarations + s"{ fun (t: Tagged($$A, $list)): Nat => Nat.zero }")
      assert(ValueEquivalence.defEq(result.tpe, expected.tpe), list)
    }
  }

  // ------------ Long lists ------------

  /** `dbl`, which appends its argument to itself `doublings` times, over lists of `element`. */
  private def doublingProgram(element: String, doublings: Int): String = {
    val lets = (1 to doublings).map(i => s"  let d$i := List.append(d${i - 1}, d${i - 1})\n").mkString
    s"def dbl (xs: List($element)) : List($element) := {\n  let d0 := xs\n$lets  d$doublings\n}\n"
  }

  test("doubling a stuck list nests applications only as deep as the program, and solving it splices every copy") {
    val doublings = 14
    val copies = 1 << doublings
    onSmallStack {
      val loaded = elabAndRun(
        doublingProgram("Nat", doublings) +
          "def check (xs: List(Nat)) : Eq(List(Nat), dbl(xs), dbl(xs)) := Eq.refl(dbl(xs))\n"
      )
      val xs = FreshVar.freshVar("xs", listNat)
      val doubled = Interpreter.evalApply(loaded("dbl"), Vector(xs))
      val expected = (1 until copies).foldLeft(length(xs))((sum, _) => NatNormalForm.add(sum, length(xs)))
      assertEquals(length(doubled).key, expected.key)
      val piece = Vector(nat(1), nat(2))
      val store = EqStore.empty.allow(DepSet(xs.id)).addLink(xs.id, build(piece))
      assertSameList(ValueOps.materialize(doubled, store), build(Vector.fill(copies)(piece).flatten))
    }
  }

  test("positivity walks doubled stuck appends") {
    val doublings = 14
    val prefix =
      doublingProgram("Prop", doublings) + "inductive Holds (ps: List(Prop)) : Prop\n\naxiom ps : List(Prop)\n\n"
    onSmallStack {
      elabAndRun(prefix + "inductive Good : Prop\n | mk (h: Holds(dbl(ps))) : Good\n")
      typeError[NonStrictlyPositive](
        prefix + "inductive Bad : Prop\n | mk (h: Holds(List.append(dbl(ps), List.cons(Bad, List.nil(Prop))))) : Bad\n"
      )
    }
  }

  test("a long list ending in a stuck append converts, unifies, materializes, quotes and prints without recursion") {
    val n = 200000
    val loaded = elabAndRun("axiom zs : List(Nat)\n")
    val Vector(x, a, _) = stuck
    onSmallStack {
      val elements = (0 until n).map(i => nat(i % 7))
      val list = build(elements, append(x, a))
      val rebuilt = append(build(elements.take(n / 2)), build(elements.drop(n / 2), append(x, a)))
      assertSameList(list, rebuilt)
      assertEquals(length(list).key, NatNormalForm.add(NatNormalForm.add(nat(n), length(x)), length(a)).key)
      val y = FreshVar.freshVar("y", Kernel.natType)
      val pattern = build(elements.init :+ y, append(x, a))
      val solved = unify(pattern, list, y).fold(f => fail(s"unexpected $f"), identity)
      assertEquals(ValueOps.materialize(y, solved).key, elements.last.key)
      val toNil = EqStore.empty.allow(DepSet(a.id)).addLink(a.id, nilNat)
      assertSameList(ValueOps.materialize(list, toNil), build(elements, x))
      assert(list.toString.endsWith("] ++ List.append(" + x.toString + ", " + a.toString + ")"))
      val closed = build(elements, append(loaded("zs"), build(Vector(nat(1)))))
      val quoted = ValueQuote.quoteTerm(closed, ValueQuote.QuoteContext(Map.empty, 0), span)
      assertSameList(Interpreter.evalTerm(quoted, loaded), closed)
    }
  }

  // ------------ Performance ------------

  private val threads = java.lang.management.ManagementFactory.getThreadMXBean

  private def cpuNanos[T](body: => T): (T, Long) = {
    val started = threads.getCurrentThreadCpuTime
    val result = body
    (result, threads.getCurrentThreadCpuTime - started)
  }

  /** The CPU time of `run(n)` at the best of three, after warming up at the smallest size. */
  private def growth(sizes: Vector[Int])(run: Int => Unit): Vector[Long] = {
    (0 until 3).foreach(_ => run(sizes.head))
    sizes.map(n => (0 until 3).map(_ => cpuNanos(run(n))._2).min)
  }

  private def assertLinear(label: String, sizes: Vector[Int], times: Vector[Long]): Unit = {
    // Quadrupling the size quadruples a linear cost and multiplies a quadratic one by sixteen.
    val ratio = times.last.toDouble / math.max(1L, times.head)
    val sizeRatio = sizes.last.toDouble / sizes.head
    assert(ratio < sizeRatio * 2.5, s"$label grew $ratio times over sizes $sizes: $times ns")
  }

  test("left accumulation keeps one segment and stays linear; right accumulation stays linear") {
    val piece = build(Vector(nat(1), nat(2), nat(3)))
    def accumulateLeft(n: Int): Value = {
      var acc = nilNat
      (0 until n).foreach(_ => acc = append(acc, piece))
      acc
    }
    def accumulateRight(n: Int): Value = {
      var acc = nilNat
      (0 until n).foreach(_ => acc = append(build(Vector(nat(1), nat(2), nat(3))), acc))
      acc
    }
    val left = accumulateLeft(1000)
    assertEquals(Storage.segments(left).length, 1)
    assertEquals(Storage.layers(left), 3000L)
    assertSameList(left, accumulateRight(1000))

    val sizes = Vector(20000, 80000)
    assertLinear("left accumulation", sizes, growth(sizes)(n => accumulateLeft(n)))
    assertLinear("right accumulation", sizes, growth(sizes)(n => accumulateRight(n)))
  }

  test("length of nested stuck appends grows linearly") {
    def nested(n: Int): Value =
      (0 until n).foldLeft(stuck(0): Value)((acc, i) => append(acc, build(Vector(nat(i % 5)))))
    val sizes = Vector(4096, 16384)
    val lists = sizes.map(n => n -> nested(n)).toMap
    assertLinear("length", sizes, growth(sizes)(n => length(lists(n))))
  }

  test("length of a doubled stuck list is linear in the distinct applications, not in the uses") {
    val doublings = 24
    val x = stuck(0)
    val prefix = build(Vector(nat(1), nat(2)), x)
    val doubled = (0 until doublings).foldLeft(prefix)((d, _) => append(d, d))
    val expected =
      NatNormalForm.mul(NatNormalForm.literal(BigInt(1) << doublings), NatNormalForm.add(nat(2), length(x)))
    val (counted, nanos) = cpuNanos(length(doubled))
    assertEquals(counted.key, expected.key)
    assert(nanos < 1000000000L, s"length of $doublings doublings took $nanos ns")
  }

  test("walking open-list tails shares dependency summaries") {
    // Every element is open, but from a small pool, so each tail's dependencies stay small. Queries should reuse block
    // summaries with logarithmic work per segment range instead of rescanning its payloads.
    val pool = Vector.tabulate(16)(i => FreshVar.freshVar(s"v$i", Kernel.natType))
    def walk(n: Int): Unit = {
      var rest = build(Vector.tabulate(n)(i => pool(i % pool.length)))
      while (rest.isInstanceOf[VWord]) {
        rest = tail(rest)
        rest.synDeps
      }
    }
    val sizes = Vector(2000, 16000)
    val times = growth(sizes)(walk)
    // Eight times the size leaves room for the logarithmic query cost, but not a rescan of the segment per tail.
    val ratio = times.last.toDouble / math.max(1L, times.head)
    assert(ratio < 8 * 2.5, s"tail dependencies grew $ratio times over sizes $sizes: $times ns")
  }

  test("the prelude's List.reverse is linear") {
    val loaded = elabAndRun("def rev (xs: List(Nat)): List(Nat) := List.reverse(xs)\n")
    val rev = loaded("rev")
    val reversed = Interpreter.evalApply(rev, Vector(build((0 until 100).map(nat))))
    assertSameList(reversed, build((0 until 100).reverse.map(nat)))
    onLargeStack {
      val sizes = Vector(5000, 20000)
      val lists = sizes.map(n => n -> build((0 until n).map(i => nat(i % 7)))).toMap
      assertLinear("reverse", sizes, growth(sizes)(n => Interpreter.evalApply(rev, Vector(lists(n)))))
    }
  }
}
