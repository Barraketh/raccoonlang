package com.raccoonlang

import com.raccoonlang.Value._

import scala.concurrent.duration.DurationInt
import scala.concurrent.{Await, ExecutionContext, Future}

class ValueEquivalenceTests extends munit.FunSuite with TestSupport {
  private val span = Span(0, 0)
  private val typeSort: CoreAst.Term = CoreTestTerms.sortAt(CoreAst.Form.LevelOne, span)
  private val binderRef = CoreAst.LocalRef(0, "x")
  private val binder = CoreAst.Binder(binderRef, typeSort, Span(0, 0), CoreAst.BinderSite.Function, BinderMode.Explicit)
  private val env = Env.empty
  private val typeToTypeClassifier = Sorts.sort(Level.succ(Level.one), Value.Kind.unr, Value.Lifetime.empty)

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

  private def pi(captures: Vector[Value], out: Env => Value, id: NodeId): VPi =
    VPi(
      env,
      Vector(binder),
      out,
      Value.Kind.unr,
      Value.Lifetime.empty,
      deps(captures: _*),
      ValueId.LocalId(id, captures),
      () => typeToTypeClassifier
    )

  test("sorts compare only by conversion, never structurally") {
    assert(ValueEquivalence.defEq(Sorts.sort(Level.one, Value.Kind.unr, Value.Lifetime.empty), Sorts.Type))
    intercept[InternalError](Sorts.Type == Sorts.sort(Level.one, Value.Kind.unr, Value.Lifetime.empty))
    intercept[InternalError](Sorts.Prop.hashCode())
  }

  test("Pi unification rejects solutions that depend on fresh binder vars") {
    val hole = FreshVar.freshVar("A", Sorts.Type)
    val meta = EqStore.empty.allow(DepSet(hole.id))
    val left = pi(Vector(hole), _ => hole, NodeId.fresh())
    val right = pi(Vector.empty, env => env(binderRef), NodeId.fresh())

    assert(ValueEquivalence.tryUnify(left, right, meta).isLeft)
  }

  test("Pi unification does not link holes beneath the Pi frame") {
    // Pi-former injectivity is not assumed, so codomain equations are not consequences of the
    // Pi equation: even a closed solution must be refused, not chosen.
    val hole = FreshVar.freshVar("A", Sorts.Type)
    val closed = FreshVar.freshVar("B", Sorts.Type)
    val meta = EqStore.empty.allow(DepSet(hole.id))
    val left = pi(Vector(hole), _ => hole, NodeId.fresh())
    val right = pi(Vector(closed), _ => closed, NodeId.fresh())

    assert(ValueEquivalence.tryUnify(left, right, meta).isLeft)
  }

  test("Pi definitional equality distinguishes telescope grouping") {
    val yRef = CoreAst.LocalRef(1, "y")
    val yBinder = CoreAst.Binder(yRef, typeSort, span, CoreAst.BinderSite.Function, BinderMode.Explicit)
    val grouped = VPi(
      env,
      Vector(binder, yBinder),
      _ => Sorts.Type,
      Value.Kind.unr,
      Value.Lifetime.empty,
      DepSet.empty,
      ValueId.LocalId(NodeId.fresh(), Vector.empty),
      () => typeToTypeClassifier
    )
    val nested = VPi(
      env,
      Vector(binder),
      outerEnv =>
        VPi(
          outerEnv,
          Vector(yBinder),
          _ => Sorts.Type,
          Value.Kind.unr,
          Value.Lifetime.empty,
          DepSet.empty,
          ValueId.LocalId(NodeId.fresh(), Vector.empty),
          () => typeToTypeClassifier
        ),
      Value.Kind.unr,
      Value.Lifetime.empty,
      DepSet.empty,
      ValueId.LocalId(NodeId.fresh(), Vector.empty),
      () => typeToTypeClassifier
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
    val yBinder = CoreAst.Binder(yRef, typeSort, span, CoreAst.BinderSite.Function, BinderMode.Explicit)
    val nested = VPi(
      env,
      Vector(binder),
      outerEnv =>
        VPi(
          outerEnv,
          Vector(yBinder),
          _ => Sorts.Type,
          Value.Kind.unr,
          Value.Lifetime.empty,
          DepSet.empty,
          ValueId.LocalId(NodeId.fresh(), Vector.empty),
          () => typeToTypeClassifier
        ),
      Value.Kind.unr,
      Value.Lifetime.empty,
      DepSet.empty,
      ValueId.LocalId(NodeId.fresh(), Vector.empty),
      () => typeToTypeClassifier
    )
    val applicationEnv = env.putGlobal("nested", VConst("nested", Symbol, nested))
    val ref = CoreTestTerms.sortAt(CoreAst.Form.LevelZero, span)
    val first = CoreAst.Term.App(CoreAst.Term.GlobalRef("nested", span), Vector(ref), Vector.empty, span)
    val application = CoreAst.Term.App(first, Vector(ref), Vector.empty, span)

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

  // Within one outermost assertion each pair of values is checked once. Rechecking every repeated pair walked a shared
  // value as a tree: 2^40 nodes here. The deadline only turns a hang into a failure. By then the suite has failed, and
  // the abandoned check may still be running on another thread, which the single-threaded checker does not support.
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
    Await.result(Future(typecheckDecls(program))(ExecutionContext.global), 60.seconds)
  }

  // Two function types of different syntax that share a node identity share a key (the F2 bug class, which no checked
  // term can reach now that only a rebuilt node shares an identity: the values here are made by hand). Beneath a
  // family application their keys make the applications' keys agree too, so only the assertion beneath the outer
  // verdict reaches the collision.
  test("the key-coherence assertion reaches a key collision beneath an agreeing parent") {
    assert(ValueEquivalence.keyAssertionsEnabled)
    val shared = NodeId.fresh()
    val toProp = pi(Vector.empty, _ => Sorts.Prop, shared)
    val toType = pi(Vector.empty, _ => Sorts.Type, shared)
    assertEquals(toProp.key, toType.key)
    val list = Prelude.default.checkedEnv("List")
    def listOf(elem: Value): Value = Interpreter.evalApply(list, Vector(Level.succ(Level.one), Lifetime.empty, elem))
    val (left, right) = (listOf(toProp), listOf(toType))
    assertEquals(left.key, right.key)

    val error = intercept[InternalError](ValueEquivalence.defEq(left, right))
    assert(error.getMessage.contains("ValueKey disagrees with conversion"), error.getMessage)
  }
}
