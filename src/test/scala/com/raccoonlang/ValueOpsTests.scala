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
}
