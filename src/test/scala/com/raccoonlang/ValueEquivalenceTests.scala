package com.raccoonlang

import com.raccoonlang.Value._

import java.util.concurrent.atomic.AtomicReference

class ValueEquivalenceTests extends munit.FunSuite with TestSupport {
  private val span = Span(0, 0)
  private val typeSort: CoreAst.Term = CoreTestTerms.sortAt(CoreAst.Form.LevelZero, span)
  private val binderRef = CoreAst.LocalRef(0, "x")
  private val binder = CoreAst.Binder(binderRef, typeSort, Span(0, 0), CoreAst.BinderSite.Function)
  private val env = Env.empty
  private val typeToTypeClassifier = Sorts.sort(Level.one)

  private def parseBody(source: String): CoreAst.Term =
    LanguageParser.parseProgram(source) match {
      case Success(value, _, _) => Elaborator.elab(value).body.getOrElse(fail("program has no body"))
      case failure: Failure     => fail(s"failed to parse test program: $failure")
    }

  private def deps(values: Value*): DepSet = {
    val res = DepSet.newBuilder
    values.foreach(value => res.unionInPlace(value.synDeps))
    res.result()
  }

  private def onSmallStack(body: => Unit): Unit = {
    val failure = new AtomicReference[Throwable]()
    val thread = new Thread(
      null,
      new Runnable {
        override def run(): Unit =
          try body
          catch { case error: Throwable => failure.set(error) }
      },
      "deep-value-equivalence",
      256L * 1024L
    )
    thread.start()
    thread.join()
    val error = failure.get()
    if (error != null) throw error
  }

  private def pi(captures: Vector[Value], isPropValued: Boolean, out: Env => Value, id: NodeId): VPi =
    VPi(
      env,
      Vector(binder),
      out,
      deps(captures: _*),
      ValueId.LocalId(id, captures),
      () => if (isPropValued) Sorts.Prop else typeToTypeClassifier,
      isPropValued
    )

  test("Prop is a separate sort from the data universes") {
    assert(ValueEquivalence.defEq(Sorts.sort(Level.zero), Sorts.Type))
    assert(!ValueEquivalence.defEq(Sorts.sort(Level.one), Sorts.Type))
    assert(!ValueEquivalence.defEq(Sorts.Prop, Sorts.Type))
    assertEquals(ValueEquivalence.tryUnify(Sorts.Prop, Sorts.Type, EqStore.empty).left.map(_.apart), Left(false))
    intercept[InternalError](Sorts.Type == Sorts.sort(Level.one))
    intercept[InternalError](Sorts.Prop.hashCode())
  }

  test("Pi unification rejects solutions that depend on fresh binder vars") {
    val hole = FreshVar.freshVar("A", Sorts.Type)
    val meta = EqStore.empty.allow(DepSet(hole.id))
    val left = pi(Vector(hole), false, _ => hole, NodeId.fresh())
    val right = pi(Vector.empty, false, env => env(binderRef), NodeId.fresh())

    assert(ValueEquivalence.tryUnify(left, right, meta).isLeft)
  }

  test("Pi unification does not link holes beneath the Pi frame") {
    // Pi-former injectivity is not assumed, so codomain equations are not consequences of the
    // Pi equation: even a closed solution must be refused, not chosen.
    val hole = FreshVar.freshVar("A", Sorts.Type)
    val closed = FreshVar.freshVar("B", Sorts.Type)
    val meta = EqStore.empty.allow(DepSet(hole.id))
    val left = pi(Vector(hole), false, _ => hole, NodeId.fresh())
    val right = pi(Vector(closed), false, _ => closed, NodeId.fresh())

    assert(ValueEquivalence.tryUnify(left, right, meta).isLeft)
  }

  test("Pi definitional equality distinguishes telescope grouping") {
    val yRef = CoreAst.LocalRef(1, "y")
    val yBinder = CoreAst.Binder(yRef, typeSort, span, CoreAst.BinderSite.Function)
    val grouped = VPi(
      env,
      Vector(binder, yBinder),
      _ => Sorts.Type,
      DepSet.empty,
      ValueId.LocalId(NodeId.fresh(), Vector.empty),
      () => typeToTypeClassifier,
      false
    )
    val nested = VPi(
      env,
      Vector(binder),
      outerEnv =>
        VPi(
          outerEnv,
          Vector(yBinder),
          _ => Sorts.Type,
          DepSet.empty,
          ValueId.LocalId(NodeId.fresh(), Vector.empty),
          () => typeToTypeClassifier,
          false
        ),
      DepSet.empty,
      ValueId.LocalId(NodeId.fresh(), Vector.empty),
      () => typeToTypeClassifier,
      false
    )

    // Grouping is part of a function type's identity: `(x: A)(y: A) -> Type` is a 2-ary function
    // type and `(x: A) -> ((y: A) -> Type)` a 1-ary one returning a function. They are not
    // convertible. The failure is stuck, never apart — Pi-former injectivity is not assumed.
    assert(!ValueEquivalence.defEq(grouped, nested))
    assert(!ValueEquivalence.defEq(nested, grouped))
    assertEquals(ValueEquivalence.tryUnify(grouped, nested, EqStore.empty).left.map(_.apart), Left(false))
  }

  test("checked and residual applications cross nested Pi groups") {
    val yRef = CoreAst.LocalRef(2, "y")
    val yBinder = CoreAst.Binder(yRef, typeSort, span, CoreAst.BinderSite.Function)
    val nested = VPi(
      env,
      Vector(binder),
      outerEnv =>
        VPi(
          outerEnv,
          Vector(yBinder),
          _ => Sorts.Type,
          DepSet.empty,
          ValueId.LocalId(NodeId.fresh(), Vector.empty),
          () => typeToTypeClassifier,
          false
        ),
      DepSet.empty,
      ValueId.LocalId(NodeId.fresh(), Vector.empty),
      () => typeToTypeClassifier,
      false
    )
    val applicationEnv = env
      .putGlobal("nested", VConst("nested", Symbol, nested))
      .putGlobal("A", VConst("A", Symbol, Sorts.Type))
    val typeValue = CoreAst.Term.GlobalRef("A", span)
    val first = CoreAst.Term.App(CoreAst.Term.GlobalRef("nested", span), Vector(typeValue), span)
    val application = CoreAst.Term.App(first, Vector(typeValue), span)

    val checked = TypeChecker.checkTerm(application, applicationEnv)
    assert(ValueEquivalence.defEq(checked.value.tpe, Sorts.Type))
    assert(ValueEquivalence.defEq(Interpreter.evalTerm(checked.residual, applicationEnv), checked.value))
  }

  test("definitionally equal neutral matches ignore source identity and closure capture shape") {
    val source =
      """{
        |  fun (b: Bool): Bool =>
        |    match b returning Bool with
        |    | Bool.false => Bool.true
        |    | Bool.true => Bool.false
        |}
        |""".stripMargin
    val checkedEnv = Prelude.default.checkedEnv
    val left = TypeChecker.checkTerm(parseBody(source), checkedEnv).value
    val right = TypeChecker.checkTerm(parseBody(source), checkedEnv).value
    val different = TypeChecker
      .checkTerm(
        parseBody(
          """{
            |  fun (b: Bool): Bool =>
            |    match b returning Bool with
            |    | Bool.false => Bool.false
            |    | Bool.true => Bool.false
            |}
            |""".stripMargin
        ),
        checkedEnv
      )
      .value

    assert(ValueEquivalence.defEq(left, right))
    assert(!ValueEquivalence.defEq(left, different))
  }

  test("neutral match congruence compares branches at a parameterized scrutinee's own parameters") {
    def checked(source: String): Value = TypeChecker.checkTerm(parseBody(source), Prelude.default.checkedEnv).value
    def program(someBranch: String): String =
      s"""{
         |  fun (A: Type)(o: Option(A))(d: A): A =>
         |    match o returning A with
         |    | Option.none => d
         |    | Option.some a => $someBranch
         |}
         |""".stripMargin
    val written = checked(program("a"))
    // The same program one character later is another match node, so only its eliminator can decide the equation.
    val shifted = checked(" " + program("a"))
    val different = checked(" " + program("d"))

    assert(ValueEquivalence.defEq(written, shifted))
    assert(!ValueEquivalence.defEq(written, different))
  }

  test("neutral match congruence rejects a different scrutinee") {
    def checked(source: String): Value = TypeChecker.checkTerm(parseBody(source), Prelude.default.checkedEnv).value
    val onFirst = checked(
      """{
        |  fun (first: Bool)(second: Bool): Bool =>
        |    match first returning Bool with
        |    | Bool.false => Bool.true
        |    | Bool.true => Bool.false
        |}
        |""".stripMargin
    )
    val onSecond = checked(
      """{
        |  fun (first: Bool)(second: Bool): Bool =>
        |    match second returning Bool with
        |    | Bool.false => Bool.true
        |    | Bool.true => Bool.false
        |}
        |""".stripMargin
    )

    assert(!ValueEquivalence.defEq(onFirst, onSecond))
  }

  test("neutral match congruence conservatively rejects different case ordering") {
    def checked(source: String): Value = TypeChecker.checkTerm(parseBody(source), Prelude.default.checkedEnv).value
    val inSourceOrder = checked(
      """{
        |  fun (b: Bool): Bool =>
        |    match b returning Bool with
        |    | Bool.false => Bool.true
        |    | Bool.true => Bool.false
        |}
        |""".stripMargin
    )
    val reversed = checked(
      """{
        |  fun (b: Bool): Bool =>
        |    match b returning Bool with
        |    | Bool.true => Bool.false
        |    | Bool.false => Bool.true
        |}
        |""".stripMargin
    )

    assert(!ValueEquivalence.defEq(inSourceOrder, reversed))
  }

  test("neutral match congruence fails closed on a forged instantiated result type") {
    val checkedEnv = Prelude.default.checkedEnv
    val function = TypeChecker
      .checkTerm(
        parseBody(
          """{
            |  fun (b: Bool): Bool =>
            |    match b returning Bool with
            |    | Bool.false => Bool.true
            |    | Bool.true => Bool.false
            |}
            |""".stripMargin
        ),
        checkedEnv
      )
      .value
    val scrutinee = FreshVar.freshVar("b", checkedEnv("Bool"))
    val neutral = Interpreter.evalApply(function, Vector(scrutinee)).asInstanceOf[NeutralThunk]
    val wrongType = neutral.copy(
      id = ValueId.LocalId(NodeId.fresh(), neutral.id.captures),
      tpe = checkedEnv("Nat")
    )

    assert(!ValueEquivalence.defEq(neutral, wrongType))
  }

  // Within one outermost assertion each pair of values is checked once. Rechecking every repeated pair would walk this
  // fixed 41-node shared graph as a 2^40-node tree.
  test("the key-coherence assertion costs one structural pass on a shared value") {
    assert(ValueEquivalence.keyAssertionsEnabled)
    val program =
      """
        |inductive T : Type
        | | leaf : T
        | | node (l: T)(r: T) : T
        |
        |def dup (t: T): T := T.node(t, t)
        |
        |def big (n: Nat): T decreases structural(n) := match n returning T with
        | | .zero => T.leaf
        | | .succ m => dup(big(m))
        |
        |def same (n: Nat): Eq(T, big(n), big(n)) := Eq.refl(big(n))
        |
        |def check : Eq(T, big(40), big(40)) := same(40)
        |""".stripMargin
    typecheckDecls(program)
  }

  test("key-coherence assertions check deep ordinary constructor chains without using the host stack") {
    assert(ValueEquivalence.keyAssertionsEnabled)
    val checkedEnv = Prelude.default.checkedEnv
    val zero = checkedEnv("Nat.zero")
    val succ = checkedEnv("Nat.succ")

    onSmallStack {
      def chain(): Value = {
        var value = zero
        var depth = 0
        while (depth < 30000) {
          value = Interpreter.evalApply(succ, Vector(value))
          depth += 1
        }
        value
      }

      assert(ValueEquivalence.defEq(chain(), chain()))
    }
  }

  // Two function types of different syntax that share a node identity share a key (the F2 bug class, which no checked
  // term can reach now that only a rebuilt node shares an identity: the values here are made by hand). Beneath a
  // family application their keys make the applications' keys agree too, so only the assertion beneath the outer
  // verdict reaches the collision.
  test("the key-coherence assertion reaches a key collision beneath an agreeing parent") {
    assert(ValueEquivalence.keyAssertionsEnabled)
    val shared = NodeId.fresh()
    val toProp = pi(Vector.empty, true, _ => Sorts.Prop, shared)
    val toType = pi(Vector.empty, false, _ => Sorts.Type, shared)
    assertEquals(toProp.key, toType.key)
    val list = Prelude.default.checkedEnv("List")
    def listOf(elem: Value): Value = Interpreter.evalApply(list, Vector(Level.succ(Level.one), elem))
    val (left, right) = (listOf(toProp), listOf(toType))
    assertEquals(left.key, right.key)

    val error = intercept[InternalError](ValueEquivalence.defEq(left, right))
    assert(error.getMessage.contains("ValueKey disagrees with conversion"), error.getMessage)
  }

  test("the key-coherence assertion reaches a deep key collision iteratively") {
    assert(ValueEquivalence.keyAssertionsEnabled)
    val shared = NodeId.fresh()
    val toProp = pi(Vector.empty, true, _ => Sorts.Prop, shared)
    val toType = pi(Vector.empty, false, _ => Sorts.Type, shared)
    val list = Prelude.default.checkedEnv("List")
    def listOf(elem: Value): Value = Interpreter.evalApply(list, Vector(Level.succ(Level.one), elem))
    def wrap(value: Value): Value = {
      var current = value
      var depth = 0
      while (depth < 30000) {
        current = listOf(current)
        depth += 1
      }
      current
    }
    val left = wrap(toProp)
    val right = wrap(toType)
    assertEquals(left.key, right.key)

    val error = intercept[InternalError](ValueEquivalence.defEq(left, right))
    assert(error.getMessage.contains("ValueKey disagrees with conversion"), error.getMessage)
  }
}
