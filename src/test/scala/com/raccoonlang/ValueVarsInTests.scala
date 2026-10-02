package com.raccoonlang

import com.raccoonlang.CoreAst.{Term => CTerm}
import com.raccoonlang.Value._

class ValueVarsInTests extends munit.FunSuite {
  private val span = Span(0, 0)
  private val valueType: Value = Sorts.Type
  private val typeRef: CoreAst.Term = CTerm.GlobalRef("Type", span)

  private def binder(index: Int, name: String, mode: BinderMode = BinderMode.Explicit): CoreAst.Binder =
    CoreAst.Binder(
      CoreAst.LocalRef(index, name),
      typeRef,
      span,
      CoreAst.BinderSite.Function,
      mode
    )

  private def pi(
      env: Env,
      binders: Vector[CoreAst.Binder],
      captures: Vector[Value]
  ): VPi =
    VPi(
      env,
      binders,
      _ => valueType,
      Kind.unr,
      Lifetime.empty,
      Lifetime.empty,
      Value.envDeps(env),
      ValueId.LocalId(NodeId.fresh(), captures),
      () => Sorts.Type,
      isPropValued = false
    )

  test("varsIn preserves first occurrence across shared closure type and environment paths") {
    val x = FreshVar.freshVar("x", valueType)
    val y = FreshVar.freshVar("y", valueType)
    val z = FreshVar.freshVar("z", valueType)
    val env = Env.empty
      .putLocal(CoreAst.LocalRef(0, "x"), x)
      .putLocal(CoreAst.LocalRef(1, "y"), y)
    val functionType = pi(env, Vector(binder(2, "arg")), Vector(x, y))
    val lamTerm = CTerm.Lam(
      CTerm.Pi(
        Vector(binder(2, "arg")),
        typeRef,
        CoreAst.Closure.unrestricted(span),
        span,
        NodeId.fresh()
      ),
      typeRef,
      span,
      NodeId.fresh(),
      name = None,
      recursion = None
    )
    val lambda = VLam(
      functionType,
      ValueId.LocalId(NodeId.fresh(), Vector(z)),
      LamBody.Core(lamTerm, env)
    )

    assertEquals(Value.varsIn(lambda, DepSet(x.id, y.id, z.id)), Vector(x, y, z))
  }

  test("varsIn skips evidence arguments omitted by an application's dependency set") {
    val explicit = FreshVar.freshVar("explicit", valueType)
    val evidence = FreshVar.freshVar("evidence", valueType)
    val functionType = pi(
      Env.empty,
      Vector(binder(0, "explicit"), binder(1, "evidence", BinderMode.Evidence)),
      Vector.empty
    )
    val function = VConst("testFunction", Symbol, functionType)
    val application = VApp(function, Vector(explicit, evidence), valueType)

    assertEquals(Value.varsIn(application, DepSet(explicit.id, evidence.id)), Vector(explicit))
  }

  test("varsIn recovers variable dependencies from a variable's type") {
    val typeVar = FreshVar.freshVar("type", valueType)
    val valueVar = FreshVar.freshVar("value", typeVar)

    assertEquals(Value.varsIn(valueVar, DepSet(valueVar.id, typeVar.id)), Vector(valueVar, typeVar))
    assertEquals(Value.varsIn(valueVar, DepSet(typeVar.id)), Vector(typeVar))
  }

  test("varsIn traverses a large shared application DAG without expanding repeated branches") {
    val x = FreshVar.freshVar("leaf", valueType)
    val pairType = pi(Env.empty, Vector(binder(0, "left"), binder(1, "right")), Vector.empty)
    val pair = VConst("Pair", Symbol, pairType)
    var dag: Value = x
    var depth = 0
    while (depth < 35) {
      dag = VApp(pair, Vector(dag, dag), valueType)
      depth += 1
    }

    assertEquals(Value.varsIn(dag, DepSet(x.id)), Vector(x))
  }
}
