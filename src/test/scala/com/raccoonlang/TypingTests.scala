package com.raccoonlang

class TypingTests extends munit.FunSuite {
  test("functions and dependent applications typecheck") {
    val (_, result) = TestSupport.check(
      "inductive Bool : Type\n | true : Bool\n | false : Bool\n\n" +
        "def id (A: Type)(x: A): A := x\n\nid(Bool, Bool.true)"
    )
    assert(result.nonEmpty)
    assertEquals(PrettyPrinter.print(result.get.value), "Bool.true")
  }

  test("wrong dependent function arguments are rejected") {
    intercept[TypeMismatch] {
      TestSupport.check(
        "inductive Bool : Type\n | true : Bool\n | false : Bool\n\n" +
          "def id (A: Type)(x: A): A := x\n\nid(Bool, Type)"
      )
    }
  }

  test("body values must match their declared type") {
    intercept[TypeMismatch] {
      TestSupport.check("def bad (A: Type): A := Type")
    }
  }

  test("opaque and transparent definitions publish checked values") {
    val (env, _) = TestSupport.check(
      "inductive Bool : Type\n | true : Bool\n | false : Bool\n\n" +
        "opaque def hidden : Bool := Bool.true\n\ndef visible : Bool := Bool.false\n"
    )
    assert(env.globals.contains("hidden"))
    assert(env.globals.contains("visible"))
  }

  test("matching requires an inductive scrutinee") {
    intercept[NonInductiveMatch] {
      TestSupport.check("axiom b : Type\n\nmatch b with\n")
    }
  }

  test("recursive groups are checked against their declared Pis and decreases evidence") {
    val (env, _) = TestSupport.check(
      "inductive Nat : Type\n | zero : Nat\n\n" +
        "def loop (n: Nat): Nat decreases structural(n) := n\n"
    )
    assert(env.globals.contains("loop"))
  }

  test("checked recursive definitions remain transparent to later declarations") {
    val (env, _) = TestSupport.check(
      "inductive Nat : Type\n | zero : Nat\n\n" +
        "def choose (n: Nat): Type decreases structural(n) := Nat\n" +
        "def y : choose(Nat.zero) := Nat.zero\n"
    )
    assert(env.globals.contains("y"))
  }

  test("checked recursive CoreAst groups validate peers and publish transparent lambdas") {
    val span = Span(0, 1)
    val n = CoreAst.LocalRef(10, "n")
    val fPeer = CoreAst.LocalRef(20, "f")
    val gPeer = CoreAst.LocalRef(21, "g")
    val pi = CoreAst.Term.Pi(
      Vector(CoreAst.Binder(n, CoreAst.Term.GlobalRef("Nat", span), span)),
      CoreAst.Term.GlobalRef("Nat", span),
      span
    )
    val decrease = CoreAst.DecreaseSpec.Lexicographic(Vector(n), span)
    val fBody = CoreAst.Term.LocalRef(n, span)
    val gBody = CoreAst.Term.LocalRef(n, span)
    val block = CoreAst.Decl.RecursiveDefBlock(
      Vector(
        CoreAst.RecursiveDef("f", fPeer, pi, fBody, decrease, span),
        CoreAst.RecursiveDef("g", gPeer, pi, gBody, decrease, span)
      ),
      span
    )
    val nat = CoreAst.Decl.InductiveDecl(
      CoreAst.InductiveHeader("Nat", Vector.empty, Vector.empty, CoreAst.Term.GlobalRef("Type", span), span),
      Vector(CoreAst.ConstructorDecl("Nat.zero", "zero", Vector.empty, CoreAst.Term.GlobalRef("Nat", span), span)),
      span
    )
    val (env, _) = TypeChecker.checkProgram(CoreAst.Program(Vector(nat, block), None))
    assert(env("f").isInstanceOf[Value.VLam])
    assert(env("g").isInstanceOf[Value.VLam])
  }
}
