package com.raccoonlang

class ValueOpsTests extends munit.FunSuite {
  test("materialization follows immutable variable substitutions") {
    val meta = Value.Var("u", 2001, Value.TypeValue)
    val store = EqStore.empty.allow(DepSet(2001))
    val solved = store.addLink(2001, Value.TypeValue)
    assert(ValueOps.materialize(meta, solved) == Value.TypeValue)
  }

  test("materialization preserves unaffected value identity") {
    val value = Value.VConst("closed", Value.Symbol, Value.TypeValue)
    val store = EqStore.empty.allow(DepSet(9999)).addLink(9999, Value.TypeValue)
    assert(ValueOps.materialize(value, store).asInstanceOf[AnyRef] eq value.asInstanceOf[AnyRef])
  }

  test("materialization follows substitutions inside neutral-thunk captures") {
    val span = Span(0, 1, None)
    val term = CoreAst.Term.Match(CoreAst.Term.GlobalRef("x", span), None, Vector.empty, span)
    val meta = Value.Var("u", 2002, Value.TypeValue)
    val thunk = Value.NeutralThunk(
      term,
      Env.empty,
      Value.ValueId.LocalId(term.nodeId, Vector(meta)),
      Value.TypeValue,
      DepSet.empty
    )
    val solved = EqStore.empty.allow(DepSet(2002)).addLink(2002, Value.TypeValue)
    val materialized = ValueOps.materialize(thunk, solved).asInstanceOf[Value.NeutralThunk]
    assert(materialized.id.captures == Vector(Value.TypeValue))
  }

  test("solving a neutral match blocker re-evaluates its closed match") {
    val program = TestSupport.core("inductive Bool : Type\n | true : Bool\n | false : Bool\n")
    val env = program.decls.foldLeft(Interpreter.builtins) { case (current, decl) =>
      Interpreter.evalDecl(decl, current)
    }
    val ref = CoreAst.LocalRef(2100, "b")
    val scrut = FreshVar.freshVar("b", env("Bool"))
    val withLocal = env.putLocal(ref, scrut)
    val span = Span(0, 1, None)
    val term = CoreAst.Term.Match(
      CoreAst.Term.LocalRef(ref, span),
      Some(CoreAst.Term.GlobalRef("Bool", span)),
      Vector(
        CoreAst
          .Case("Bool.true", isFullyQualified = true, Vector.empty, CoreAst.Term.GlobalRef("Bool.true", span), span),
        CoreAst
          .Case("Bool.false", isFullyQualified = true, Vector.empty, CoreAst.Term.GlobalRef("Bool.false", span), span)
      ),
      span
    )
    val thunk = Interpreter.evalTerm(term, withLocal).asInstanceOf[Value.NeutralThunk]
    val solved = EqStore.empty
      .allow(DepSet(scrut.id))
      .addLink(scrut.id, Interpreter.evalTerm(CoreAst.Term.GlobalRef("Bool.true", span), env))
    assertEquals(
      ValueOps.materialize(thunk, solved),
      Interpreter.evalTerm(CoreAst.Term.GlobalRef("Bool.true", span), env)
    )
  }

  test("materialization rewrites applications, Pi closures, and lambda closures") {
    val span = Span(0, 1, None)
    val captured = Value.Var("A", 2101, Value.TypeTpe)
    val capturedRef = CoreAst.LocalRef(2101, "A")
    val binderRef = CoreAst.LocalRef(2102, "x")
    val base = Interpreter.builtins.putLocal(capturedRef, captured)
    val piTerm = CoreAst.Term.Pi(
      Vector(CoreAst.Binder(binderRef, CoreAst.Term.GlobalRef("Type", span), span)),
      CoreAst.Term.LocalRef(capturedRef, span),
      span
    )
    val pi = Interpreter.evalPi(piTerm, base)
    val lambdaTerm = CoreAst.Term.Lam(
      piTerm,
      CoreAst.Term.LocalRef(capturedRef, span),
      span,
      None,
      None
    )
    val lambda = Interpreter.evalLam(lambdaTerm, base)
    val fn = Value.VConst("f", Value.Symbol, pi)
    val app = Value.VApp(fn, Vector(captured), captured)
    val solution = Value.VConst("Solved", Value.Symbol, Value.TypeTpe)
    val store = EqStore.empty.allow(DepSet(captured.id)).addLink(captured.id, solution)

    val materializedApp = ValueOps.materialize(app, store).asInstanceOf[Value.VApp]
    assertEquals(materializedApp.args, Vector(solution))
    val materializedPi = ValueOps.materialize(pi, store).asInstanceOf[Value.VPi]
    assertEquals(materializedPi.env(capturedRef), solution)
    val materializedLambda = ValueOps.materialize(lambda, store).asInstanceOf[Value.VLam]
    assertEquals(Interpreter.evalApply(materializedLambda, Vector(Value.TypeValue)), solution)
  }

  test("unrelated substitutions preserve blocked neutral identity") {
    val span = Span(0, 1, None)
    val term = CoreAst.Term.Match(CoreAst.Term.GlobalRef("x", span), None, Vector.empty, span)
    val blocked = Value.Var("scrut", 2201, Value.TypeValue)
    val thunk = Value.NeutralThunk(
      term,
      Env.empty,
      Value.ValueId.LocalId(term.nodeId, Vector(blocked)),
      Value.TypeValue,
      DepSet(2201)
    )
    val unrelated = EqStore.empty.allow(DepSet(2202)).addLink(2202, Value.TypeValue)
    assert(ValueOps.materialize(thunk, unrelated).asInstanceOf[AnyRef] eq thunk.asInstanceOf[AnyRef])
  }

  test("materializeEnv changes affected locals while preserving globals and the local-ref index") {
    val affectedRef = CoreAst.LocalRef(2203, "affected")
    val untouchedRef = CoreAst.LocalRef(2204, "untouched")
    val affected = Value.Var("affected", 2203, Value.TypeValue)
    val untouched = Value.VConst("untouched", Value.Symbol, Value.TypeValue)
    val global = Value.VConst("g", Value.Symbol, Value.TypeValue)
    val env = Env.empty.putGlobal("g", global).putLocal(affectedRef, affected).putLocal(untouchedRef, untouched)
    val solved = EqStore.empty.allow(DepSet(2203)).addLink(2203, Value.TypeValue)
    val materialized = ValueOps.materializeEnv(env, solved)
    assertEquals(materialized("g"), global)
    assertEquals(materialized(affectedRef), Value.TypeValue)
    assertEquals(materialized(untouchedRef), untouched)
    assertEquals(materialized.localRefs, env.localRefs)
    assert(materialized.locals(untouchedRef).asInstanceOf[AnyRef] eq untouched.asInstanceOf[AnyRef])
  }

  test("materialize rewrites constant, constructor-head, application arguments, and result types") {
    val meta = Value.Var("T", 2205, Value.TypeValue.tpe)
    val solved = Value.VConst("SolvedType", Value.Symbol, Value.TypeValue)
    val store = EqStore.empty.allow(DepSet(2205)).addLink(2205, solved)
    val constant = Value.VConst("c", Value.Symbol, meta)
    val head = Value.ConstructorHead("C", 0, 1, Value.TypeValue)
    val app = Value.VApp(head, Vector(meta), meta)
    assertEquals(ValueOps.materialize(constant, store).tpe, solved)
    assertEquals(ValueOps.materialize(head, store).asInstanceOf[Value.ConstructorHead].tpe, Value.TypeValue)
    val materializedApp = ValueOps.materialize(app, store).asInstanceOf[Value.VApp]
    assertEquals(materializedApp.args, Vector(solved))
    assertEquals(materializedApp.tpe, solved)
  }

  test("materialize rewrites neutral-thunk environment, captures, type, and solved blocker") {
    val span = Span(0, 1, None)
    val capturedRef = CoreAst.LocalRef(2206, "captured")
    val scrutRef = CoreAst.LocalRef(2207, "scrut")
    val captured = Value.Var("captured", 2206, Value.TypeValue)
    val scrut = Value.Var("scrut", 2207, Value.TypeValue)
    val boolProgram = TestSupport.core("inductive Bool : Type\n | true : Bool\n | false : Bool\n")
    val boolEnv = boolProgram.decls.foldLeft(Interpreter.builtins) { case (current, decl) =>
      Interpreter.evalDecl(decl, current)
    }
    val env = boolEnv.putLocal(capturedRef, captured).putLocal(scrutRef, scrut)
    val matchTerm = CoreAst.Term.Match(
      CoreAst.Term.LocalRef(scrutRef, span),
      Some(CoreAst.Term.GlobalRef("Bool", span)),
      Vector(
        CoreAst
          .Case("Bool.true", isFullyQualified = true, Vector.empty, CoreAst.Term.LocalRef(capturedRef, span), span),
        CoreAst
          .Case("Bool.false", isFullyQualified = true, Vector.empty, CoreAst.Term.LocalRef(capturedRef, span), span)
      ),
      span
    )
    val thunk = Value.NeutralThunk(
      matchTerm,
      env.closeForEval(Set(capturedRef, scrutRef)),
      Value.ValueId.LocalId(matchTerm.nodeId, Vector(captured, scrut)),
      captured,
      DepSet(2207)
    )
    val replacement = Value.VConst("replacement", Value.Symbol, Value.TypeValue)
    val captureStore = EqStore.empty.allow(DepSet(2206)).addLink(2206, replacement)
    val capturedThunk = ValueOps.materialize(thunk, captureStore).asInstanceOf[Value.NeutralThunk]
    assertEquals(capturedThunk.env(capturedRef), replacement)
    assertEquals(capturedThunk.id.captures.head, replacement)
    assertEquals(capturedThunk.tpe, replacement)
    val solvedScrut = Interpreter.evalTerm(CoreAst.Term.GlobalRef("Bool.true", span), boolEnv)
    val solved = EqStore.empty.allow(DepSet(2206, 2207)).addLink(2206, replacement).addLink(2207, solvedScrut)
    val materialized = ValueOps.materialize(thunk, solved)
    assertEquals(materialized, replacement)
  }

  test("Pi materialization rewrites deps and keeps classifier evaluation lazy") {
    val span = Span(0, 1, None)
    val capturedRef = CoreAst.LocalRef(2208, "captured")
    val captured = Value.Var("captured", 2208, Value.TypeValue)
    val binderRef = CoreAst.LocalRef(2209, "x")
    val env = Env.empty.putLocal(capturedRef, captured)
    val term = CoreAst.Term.Pi(
      Vector(CoreAst.Binder(binderRef, CoreAst.Term.GlobalRef("Type", span), span)),
      CoreAst.Term.LocalRef(capturedRef, span),
      span
    )
    val pi = Value.VPi(
      env,
      term.binders,
      _ => captured,
      captured.synDeps,
      Value.ValueId.LocalId(term.nodeId, Vector(captured)),
      () => Value.TypeValue
    )
    val replacement = Value.VConst("replacement", Value.Symbol, Value.TypeValue)
    val solved = EqStore.empty.allow(DepSet(2208)).addLink(2208, replacement)
    val materialized = ValueOps.materialize(pi, solved).asInstanceOf[Value.VPi]
    assertEquals(materialized.env(capturedRef), replacement)
    assert(!materialized.synDeps.contains(2208))
    assertEquals(materialized.tpe, Value.TypeValue)
  }

  test("native lambda body environments materialize without changing the callable") {
    val capturedRef = CoreAst.LocalRef(2210, "captured")
    val captured = Value.Var("captured", 2210, Value.TypeValue)
    val replacement = Value.VConst("replacement", Value.Symbol, Value.TypeValue)
    val env = Env.empty.putLocal(capturedRef, captured)
    val binderRef = CoreAst.LocalRef(2211, "x")
    val binder = CoreAst.Binder(binderRef, CoreAst.Term.GlobalRef("Type", Span(0, 1)), Span(0, 1))
    val pi = Value.VPi(
      env,
      Vector(binder),
      _ => Value.TypeValue,
      captured.synDeps,
      Value.ValueId.LocalId(AstNodeId.synthetic(), Vector(captured)),
      () => Value.TypeValue.asInstanceOf[Value.VSort]
    )
    val lambda = Value.VLam(
      pi,
      Value.ValueId.LocalId(AstNodeId.synthetic(), Vector(captured)),
      Value.LamBody.Native((_, nativeEnv) => nativeEnv(capturedRef), env, isRawRecursive = false)
    )
    val solved = EqStore.empty.allow(DepSet(2210)).addLink(2210, replacement)
    val materialized = ValueOps.materialize(lambda, solved).asInstanceOf[Value.VLam]
    assertEquals(Interpreter.evalApply(materialized, Vector(Value.TypeValue)), replacement)
  }
}
