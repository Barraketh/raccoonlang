package com.raccoonlang

import com.raccoonlang.CoreAst.{Term => CTerm}
import com.raccoonlang.Value._

class CapturedRefsTests extends munit.FunSuite {
  private val span = Span(0, 0)

  test("capture analysis keeps only locals present in the closure environment") {
    val outer = CoreAst.LocalRef(9000, "outer")
    val binder = CoreAst.LocalRef(9001, "x")
    val env = Env.empty.putLocal(outer, FreshVar.freshVar("outer", TypeTpe))
    val term = CTerm.Pi(
      Vector(CoreAst.Binder(binder, CTerm.GlobalRef("Type", span), span)),
      CTerm.App(CTerm.LocalRef(binder, span), Vector(CTerm.LocalRef(outer, span)), span),
      span
    )

    val refs = CapturedRefs.getCapturedRefs(term, env)
    assertEquals(refs, Set(outer))
  }

  test("global bindings remain globals when a closure is filtered") {
    val local = CoreAst.LocalRef(9002, "unused")
    val global = Value.VConst("g", Value.Symbol, TypeTpe)
    val env = Env.empty.putGlobal("g", global).putLocal(local, FreshVar.freshVar("unused", TypeTpe))
    val term = CTerm.GlobalRef("g", span)

    val closed = env.closeForEval(CapturedRefs.getCapturedRefs(term, env))
    assertEquals(closed("g"), global)
    intercept[NotFound] { closed(local) }
  }

  test("closing a Pi does not retain unrelated local dependencies") {
    val used = CoreAst.LocalRef(9003, "used")
    val unused = CoreAst.LocalRef(9004, "unused")
    val env = Env.empty
      .putLocal(used, FreshVar.freshVar("used", TypeTpe))
      .putLocal(unused, FreshVar.freshVar("unused", TypeTpe))
    val binder = CoreAst.LocalRef(9005, "x")
    val pi = CTerm.Pi(
      Vector(CoreAst.Binder(binder, CTerm.LocalRef(used, span), span)),
      CTerm.LocalRef(used, span),
      span
    )

    val value = Interpreter.evalPi(pi, env)
    assert(value.env.locals.contains(used))
    assert(!value.env.locals.contains(unused))
    assertEquals(value.env.globals, env.globals)
  }
}
