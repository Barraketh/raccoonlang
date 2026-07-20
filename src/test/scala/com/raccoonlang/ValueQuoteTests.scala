package com.raccoonlang

import com.raccoonlang.ElabAst.{Term => ETerm}
import com.raccoonlang.Value._

class ValueQuoteTests extends munit.FunSuite {
  private val span = Span(0, 0)

  private def constructorType(binderTy: ElabAst.Term, resultTy: Value): VPi = {
    val ref = CoreAst.LocalRef(0, "x")
    val env = Env.empty
      .putGlobal("Sort3", VSort(Level.const(3)))
      .putGlobal("Type", TypeTpe)

    VPi(
      env,
      Vector(ElabAst.Binder(ref, binderTy, Span(0, 0))),
      _ => resultTy,
      DepSet.empty,
      ValueId.Const("C.mk.type"),
      () => VSort(Level.const(4))
    )
  }

  test("constructor quote recovery accepts cumulatively fitting stored argument types") {
    val resultTy = VConst("Result", Symbol, TypeTpe)
    val ctor = ConstructorHead(
      "C.mk",
      numErasedFamilyArgs = 0,
      totalArity = 1,
      constructorType(ETerm.GlobalRef("Sort3", span), resultTy)
    )
    val value = VCtor(ctor, Vector(TypeTpe), resultTy)

    val quoted = ValueQuote.quoteTerm(value, ValueQuote.quoteContext(Env.empty), span)

    quoted match {
      case ETerm.App(ETerm.GlobalRef("C.mk", _), Vector(ETerm.GlobalRef("Type", _)), _) =>
      case other => fail(s"Expected C.mk(Type), got $other")
    }
  }

  test("constructor quote recovery accepts cumulatively fitting constructor result types") {
    val resultTy = TypeTpe
    val ctor = ConstructorHead(
      "C.mk",
      numErasedFamilyArgs = 0,
      totalArity = 1,
      constructorType(ETerm.GlobalRef("Type", span), resultTy)
    )
    val arg = VConst("arg", Symbol, TypeTpe)
    val value = VCtor(ctor, Vector(arg), VSort(Level.const(3)))

    val quoted = ValueQuote.quoteTerm(value, ValueQuote.quoteContext(Env.empty), span)

    quoted match {
      case ETerm.App(ETerm.GlobalRef("C.mk", _), Vector(ETerm.GlobalRef("arg", _)), _) =>
      case other => fail(s"Expected C.mk(arg), got $other")
    }
  }

  test("imax levels quote and evaluate round-trip") {
    val uRef = CoreAst.LocalRef(0, "u")
    val vRef = CoreAst.LocalRef(1, "v")
    val u = FreshVar.freshValue("u", LevelTpe)._2.asInstanceOf[Level]
    val v = FreshVar.freshValue("v", LevelTpe)._2.asInstanceOf[Level]
    val level = Level.succ(Level.imax(u, v))
    val env = Prelude.test.checkedEnv.putLocal(uRef, u).putLocal(vRef, v)

    val quoted = ValueQuote.quoteTerm(level, ValueQuote.quoteContext(env), span)
    val evaluated = Interpreter.evalTerm(quoted, env)

    assertEquals(evaluated, level)
    assert(PrettyPrinter.printElabTerm(quoted).contains("Level.imax"))
  }
}
