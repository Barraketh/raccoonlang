package com.raccoonlang

class ValueEquivalenceTests extends munit.FunSuite {
  test("alpha-equivalent Pi values compare equal") {
    val left = TestSupport.eval("(A: Type) -> A")
    val right = TestSupport.eval("(B: Type) -> B")
    assert(ValueEquivalence.defEq(left, right))
  }

  test("alpha-equivalent lambda values compare equal") {
    val left = TestSupport.eval("fun (A: Type): Type => A")
    val right = TestSupport.eval("fun (B: Type): Type => B")
    assert(ValueEquivalence.defEq(left, right))
  }

  test("refinable metas link and occurs checks reject cycles") {
    val meta = Value.Var("u", 1001, Value.TypeValue.tpe)
    val store = EqStore.empty.allow(DepSet(1001))
    val linked = ValueEquivalence.tryUnify(meta, Value.TypeValue, store)
    assert(linked.isRight)
    assert(linked.toOption.get.force(meta) == Value.TypeValue)
    assert(
      ValueEquivalence.tryUnify(meta, Value.VApp(meta, Vector(Value.TypeValue), Value.TypeValue.tpe), store).isLeft
    )
  }

  test("linking a value meta first solves its refinable type meta") {
    val typeMeta = Value.Var("T", 1002, Value.TypeValue.tpe.tpe)
    val valueMeta = Value.Var("x", 1003, typeMeta)
    val store = EqStore.empty.allow(DepSet(1002, 1003))

    val solved = ValueEquivalence.tryUnify(valueMeta, Value.TypeValue, store).toOption.get

    assert(solved.force(typeMeta) == Value.TypeValue.tpe)
    assert(solved.force(valueMeta) == Value.TypeValue)
  }

  test("variable linking chooses the lower id as representative") {
    val lower = Value.Var("a", 1100, Value.TypeValue)
    val higher = Value.Var("b", 1101, Value.TypeValue)
    val solved = ValueEquivalence.tryUnify(higher, lower, EqStore.empty.allow(DepSet(1100, 1101))).toOption.get
    assertEquals(solved.subst.keySet, Set(1101))
    assertEquals(solved.force(higher), lower)
  }

  test("different Pi binder arity is not definitionally equal") {
    val one = TestSupport.eval("(A: Type) -> Type")
    val two = TestSupport.eval("(A: Type) -> (B: Type) -> Type")
    assert(!ValueEquivalence.defEq(one, two))
  }

  test("dependent Pi unification shares binders and rolls back failed links") {
    val span = Span(0, 1, None)
    val meta = Value.Var("A", 3001, Value.TypeValue)
    val leftRef = CoreAst.LocalRef(1, "x")
    val rightRef = CoreAst.LocalRef(2, "y")
    val leftOuter = CoreAst.LocalRef(10, "A")
    val rightOuter = CoreAst.LocalRef(11, "A")
    val leftEnv = Env.empty.putLocal(leftOuter, meta)
    val rightEnv = Env.empty.putLocal(rightOuter, Value.TypeValue)
    val leftBinderTy = CoreAst.Term.LocalRef(leftOuter, span)
    val rightBinderTy = CoreAst.Term.LocalRef(rightOuter, span)
    val left = Value.VPi(
      leftEnv,
      Vector(CoreAst.Binder(leftRef, leftBinderTy, span)),
      _.apply(leftRef),
      leftEnv.dependencies,
      Value.ValueId.LocalId(AstNodeId.synthetic(), Vector.empty),
      () => Value.TypeValue.asInstanceOf[Value.VSort]
    )
    val right = Value.VPi(
      rightEnv,
      Vector(CoreAst.Binder(rightRef, rightBinderTy, span)),
      _.apply(rightRef),
      rightEnv.dependencies,
      Value.ValueId.LocalId(AstNodeId.synthetic(), Vector.empty),
      () => Value.TypeValue.asInstanceOf[Value.VSort]
    )
    val initial = EqStore.empty.allow(DepSet(3001))
    val linked = ValueEquivalence.tryUnify(left, right, initial)
    assert(linked.isLeft)
    assert(initial.subst.isEmpty)
    val failingRight = right.copy(codomain = _ => Value.TypeValue)
    val failed = ValueEquivalence.tryUnify(left, failingRight, initial)
    assert(failed.isLeft)
    assert(initial.subst.isEmpty)
  }

  test("neutral thunks compare their identity and captures") {
    val span = Span(0, 1, None)
    val term = CoreAst.Term.Match(CoreAst.Term.GlobalRef("scrut", span), None, Vector.empty, span)
    val ref = CoreAst.LocalRef(4, "captured")
    val env = Env.empty.putLocal(ref, Value.TypeValue)
    val same = Value.NeutralThunk(
      term,
      env,
      Value.ValueId.LocalId(term.nodeId, Vector(Value.TypeValue)),
      Value.TypeValue,
      DepSet.empty
    )
    val differentCapture = Value.NeutralThunk(
      term,
      env.putLocal(ref.copy(id = 5), Value.Var("other", 4001, Value.TypeValue)),
      Value.ValueId.LocalId(term.nodeId, Vector(Value.Var("other", 4001, Value.TypeValue))),
      Value.TypeValue,
      DepSet.empty
    )
    assert(!ValueEquivalence.defEq(same, differentCapture))
    assert(
      ValueEquivalence.defEq(
        same,
        same.copy(env = env.copy(globals = Map("x" -> GlobalBinding.Strict(Value.TypeValue))))
      )
    )
  }

  test("opaque applications do not refine their arguments") {
    val typeRef = CoreAst.LocalRef(21, "Type")
    val fnEnv = Env.empty.putLocal(typeRef, Value.TypeValue)
    val fnType = Value.VPi(
      fnEnv,
      Vector(CoreAst.Binder(CoreAst.LocalRef(20, "x"), CoreAst.Term.LocalRef(typeRef, Span(0, 1)), Span(0, 1))),
      _ => Value.TypeValue,
      DepSet.empty,
      Value.ValueId.LocalId(AstNodeId.synthetic(), Vector.empty),
      () => Value.TypeValue.asInstanceOf[Value.VSort]
    )
    val f = Value.VConst("f", Value.Symbol, fnType)
    val meta = Value.Var("x", 5001, Value.TypeValue)
    val left = Value.VApp(f, Vector(meta), Value.TypeValue)
    val right = Value.VApp(f, Vector(Value.TypeValue), Value.TypeValue)
    val solved = ValueEquivalence.tryUnify(left, right, EqStore.empty.allow(DepSet(5001)))
    assert(solved.isLeft)
    assert(solved.left.toOption.exists(!_.apart))
  }

  test("opaque applications do not propagate constructor apartness") {
    val c1 = Value.ConstructorHead("C1", 0, 0, Value.TypeValue)
    val c2 = Value.ConstructorHead("C2", 0, 0, Value.TypeValue)
    val f = Value.VConst("opaque", Value.Symbol, Value.TypeValue)
    val left = Value.VApp(f, Vector(Value.VCtor(c1, Vector.empty, Value.TypeValue)), Value.TypeValue)
    val right = Value.VApp(f, Vector(Value.VCtor(c2, Vector.empty, Value.TypeValue)), Value.TypeValue)
    val result = ValueEquivalence.tryUnify(left, right, EqStore.empty)
    assert(result.left.toOption.exists(!_.apart))
  }

  test("same-id variables unify even when represented by distinct values") {
    val left = Value.Var("x", 5200, Value.TypeValue)
    val right = Value.Var("y", 5200, Value.TypeValue)
    assert(ValueEquivalence.tryUnify(left, right, EqStore.empty).isRight)
  }

  test("only genuine constructor clashes produce apartness") {
    val leftHead = Value.ConstructorHead("Left", 0, 0, Value.TypeValue)
    val rightHead = Value.ConstructorHead("Right", 0, 0, Value.TypeValue)
    val failure = ValueEquivalence.tryUnify(
      Value.VCtor(leftHead, Vector.empty, Value.TypeValue),
      Value.VCtor(rightHead, Vector.empty, Value.TypeValue),
      EqStore.empty.allow(DepSet(9998))
    )
    assert(failure.left.toOption.exists(_.apart))
  }

  test("constructors without no-confusion are only stuck") {
    val leftHead = Value.ConstructorHead("QuotL", 0, 0, Value.TypeValue, noConfusion = false)
    val rightHead = Value.ConstructorHead("QuotR", 0, 0, Value.TypeValue, noConfusion = false)
    val failure = ValueEquivalence.tryUnify(
      Value.VCtor(leftHead, Vector.empty, Value.TypeValue),
      Value.VCtor(rightHead, Vector.empty, Value.TypeValue),
      EqStore.empty.allow(DepSet(9997))
    )
    assert(failure.left.toOption.exists(!_.apart))
  }

  test("lambda comparison rejects metas escaping through a fresh binder") {
    val span = Span(0, 1)
    val outer = CoreAst.LocalRef(5300, "outer")
    val leftBinder = CoreAst.LocalRef(5301, "x")
    val rightBinder = CoreAst.LocalRef(5302, "y")
    val leftPi = CoreAst.Term.Pi(
      Vector(CoreAst.Binder(leftBinder, CoreAst.Term.GlobalRef("Type", span), span)),
      CoreAst.Term.GlobalRef("Type", span),
      span
    )
    val rightPi = leftPi.copy(binders = Vector(CoreAst.Binder(rightBinder, CoreAst.Term.GlobalRef("Type", span), span)))
    val meta = Value.Var("outer", 5300, Value.TypeValue)
    val leftEnv = Interpreter.builtins.putLocal(outer, meta)
    val rightEnv = Interpreter.builtins
    val leftTerm = CoreAst.Term.Lam(leftPi, CoreAst.Term.LocalRef(outer, span), span, None, None)
    val rightTerm = CoreAst.Term.Lam(rightPi, CoreAst.Term.LocalRef(rightBinder, span), span, None, None)
    val left = Value.VLam(
      Interpreter.evalPiClosed(leftPi, leftEnv),
      Value.ValueId.LocalId(leftTerm.nodeId, Vector(meta)),
      Value.LamBody.Core(leftTerm, leftEnv)
    )
    val right = Value.VLam(
      Interpreter.evalPiClosed(rightPi, rightEnv),
      Value.ValueId.LocalId(rightTerm.nodeId, Vector.empty),
      Value.LamBody.Core(rightTerm, rightEnv)
    )
    val initial = EqStore.empty.allow(DepSet(5300))
    assert(ValueEquivalence.tryUnify(left, right, initial).isLeft)
    assert(initial.subst.isEmpty)
  }

  test("inductive family applications refine invertible arguments") {
    val family = Value.VConst(
      "F",
      Value.Inductive(Value.InductiveMeta(Vector.empty, 1)),
      Value.VPi(
        Env.empty,
        Vector(CoreAst.Binder(CoreAst.LocalRef(30, "A"), CoreAst.Term.GlobalRef("Type", Span(0, 1)), Span(0, 1))),
        _ => Value.TypeValue,
        DepSet.empty,
        Value.ValueId.LocalId(AstNodeId.synthetic(), Vector.empty),
        () => Value.TypeValue.asInstanceOf[Value.VSort]
      )
    )
    val meta = Value.Var("A", 5100, Value.TypeValue.tpe)
    val result = ValueEquivalence.tryUnify(
      Value.VApp(family, Vector(meta), Value.TypeValue),
      Value.VApp(family, Vector(Value.TypeValue), Value.TypeValue),
      EqStore.empty.allow(DepSet(5100))
    )
    assert(result.isRight)
    assertEquals(result.toOption.get.force(meta), Value.TypeValue)
  }

  test("compatible stuck match eliminators compare extensionally") {
    def function(trueBranch: String): Value =
      TestSupport.eval(
        "inductive Bool : Type\n" +
          " | true : Bool\n" +
          " | false : Bool\n\n" +
          "fun (b: Bool): Bool => match b returning Bool with\n" +
          s" | Bool.true => $trueBranch\n" +
          " | Bool.false => Bool.false\n"
      )
    val leftFn = function("Bool.true")
    val rightFn = function("Bool.true")
    val differentFn = function("Bool.false")
    val neutral = FreshVar.freshVar(
      "b",
      TestSupport.eval("inductive Bool : Type\n | true : Bool\n | false : Bool\n\nBool.true").tpe
    )
    val left = Interpreter.evalApply(leftFn, Vector(neutral))
    val right = Interpreter.evalApply(rightFn, Vector(neutral))
    val different = Interpreter.evalApply(differentFn, Vector(neutral))
    assert(ValueEquivalence.defEq(left, right))
    assert(!ValueEquivalence.defEq(left, different))
    val mismatch = ValueEquivalence.tryUnify(left, different, EqStore.empty.allow(DepSet(9999)))
    assert(mismatch.left.toOption.exists(!_.apart))
  }
}
