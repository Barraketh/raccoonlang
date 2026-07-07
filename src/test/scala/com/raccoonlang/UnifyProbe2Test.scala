package com.raccoonlang

class UnifyProbe2Test extends munit.FunSuite {
  test("PROBE A2: classifier of (n: Nat) -> Prop and predicate proof-irrelevance") {
    val src =
      """
        |def trueP (n: Nat): Prop := True
        |def falseP (n: Nat): Prop := False
        |
        |{
        |  trueP
        |}
        |""".stripMargin
    val parsed = LanguageParser.parseProgram(src) match {
      case Success(p, _, _) => p
      case err: Failure     => fail(s"parse: $err")
    }
    val core = Elaborator.elab(parsed)
    val worlds = core.decls.foldLeft(Interpreter.initialWorlds(Prelude.default)) { case (w, d) =>
      Interpreter.evalDecl(d, w)
    }
    val trueP = worlds.checkEnv("trueP")
    val falseP = worlds.checkEnv("falseP")
    println(s"trueP.tpe = ${trueP.tpe}, classifier = ${trueP.tpe.tpe}")
    println(s"defEq(trueP, falseP, propIrrelevant = true)  = ${ValueEquivalence.defEq(trueP, falseP, propIrrelevant = true)}")
    println(s"defEq(trueP, falseP, propIrrelevant = false) = ${ValueEquivalence.defEq(trueP, falseP, propIrrelevant = false)}")
  }
}
