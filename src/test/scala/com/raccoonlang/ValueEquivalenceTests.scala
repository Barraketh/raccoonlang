package com.raccoonlang

import com.raccoonlang.CoreAst.{Term => CTerm}
import com.raccoonlang.Value._

class ValueEquivalenceTests extends munit.FunSuite {
  private val span = Span(0, 0)
  private val typeRef: CoreAst.Term = CTerm.GlobalRef("Type", span)
  private val binderRef = CoreAst.LocalRef(0, "x")
  private val binder = CoreAst.Binder(binderRef, typeRef, Span(0, 0))
  private val env = Env.empty.putGlobal("Type", TypeTpe)
  private val typeToTypeClassifier = VSort(Level.succ(Level.one))

  private def nodeId(start: Int): AstNodeId = AstNodeId(None, start)

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

  private def pi(captures: Vector[Value], out: Env => Value, start: Int): VPi =
    VPi(
      env,
      Vector(binder),
      out,
      deps(captures: _*),
      ValueId.LocalId(nodeId(start), captures),
      () => typeToTypeClassifier
    )

  test("Pi unification rejects solutions that depend on fresh binder vars") {
    val hole = FreshVar.freshVar("A", TypeTpe)
    val meta = EqStore.empty.allow(DepSet(hole.id))
    val left = pi(Vector(hole), _ => hole, 1)
    val right = pi(Vector.empty, env => env(binderRef), 2)

    assert(ValueEquivalence.tryUnify(left, right, meta).isLeft)
  }

  test("Pi unification does not link holes beneath the Pi frame") {
    // Pi-former injectivity is not assumed, so codomain equations are not consequences of the
    // Pi equation: even a closed solution must be refused, not chosen.
    val hole = FreshVar.freshVar("A", TypeTpe)
    val closed = FreshVar.freshVar("B", TypeTpe)
    val meta = EqStore.empty.allow(DepSet(hole.id))
    val left = pi(Vector(hole), _ => hole, 3)
    val right = pi(Vector(closed), _ => closed, 4)

    assert(ValueEquivalence.tryUnify(left, right, meta).isLeft)
  }

  test("Pi definitional equality distinguishes telescope grouping") {
    val yRef = CoreAst.LocalRef(1, "y")
    val yBinder = CoreAst.Binder(yRef, typeRef, span)
    val grouped = VPi(
      env,
      Vector(binder, yBinder),
      _ => TypeTpe,
      DepSet.empty,
      ValueId.LocalId(nodeId(5), Vector.empty),
      () => typeToTypeClassifier
    )
    val nested = VPi(
      env,
      Vector(binder),
      outerEnv =>
        VPi(
          outerEnv,
          Vector(yBinder),
          _ => TypeTpe,
          DepSet.empty,
          ValueId.LocalId(nodeId(6), Vector.empty),
          () => typeToTypeClassifier
        ),
      DepSet.empty,
      ValueId.LocalId(nodeId(7), Vector.empty),
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
    val yBinder = CoreAst.Binder(yRef, typeRef, span)
    val nested = VPi(
      env,
      Vector(binder),
      outerEnv =>
        VPi(
          outerEnv,
          Vector(yBinder),
          _ => TypeTpe,
          DepSet.empty,
          ValueId.LocalId(nodeId(8), Vector.empty),
          () => typeToTypeClassifier
        ),
      DepSet.empty,
      ValueId.LocalId(nodeId(9), Vector.empty),
      () => typeToTypeClassifier
    )
    val applicationEnv = env.putGlobal("Prop", PropTpe).putGlobal("nested", VConst("nested", Symbol, nested))
    val ref = CoreAst.Term.GlobalRef("Prop", span)
    val first = CoreAst.Term.App(CoreAst.Term.GlobalRef("nested", span), Vector(ref), span)
    val application = CoreAst.Term.App(first, Vector(ref), span)

    val checked = TypeChecker.checkTerm(application, applicationEnv)
    assert(ValueEquivalence.defEq(checked.value.tpe, TypeTpe))
    assert(ValueEquivalence.defEq(Interpreter.evalTerm(checked.residual, applicationEnv), checked.value))
  }

  test("definitionally equal neutral matches ignore source identity and closure capture shape") {
    val source =
      """{
        |  fun (b: Bool): Bool =>
        |    match b with
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
            |    match b with
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

  test("neutral match congruence rejects a different scrutinee") {
    def checked(source: String): Value = TypeChecker.checkTerm(parseBody(source), Prelude.default.checkedEnv).value
    val onFirst = checked(
      """{
        |  fun (first: Bool)(second: Bool): Bool =>
        |    match first with
        |    | Bool.false => Bool.true
        |    | Bool.true => Bool.false
        |}
        |""".stripMargin
    )
    val onSecond = checked(
      """{
        |  fun (first: Bool)(second: Bool): Bool =>
        |    match second with
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
        |    match b with
        |    | Bool.false => Bool.true
        |    | Bool.true => Bool.false
        |}
        |""".stripMargin
    )
    val reversed = checked(
      """{
        |  fun (b: Bool): Bool =>
        |    match b with
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
            |    match b with
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
      id = ValueId.LocalId(nodeId(100), neutral.id.captures),
      tpe = checkedEnv("Nat")
    )

    assert(!ValueEquivalence.defEq(neutral, wrongType))
  }
}
