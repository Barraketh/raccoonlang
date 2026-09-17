package com.raccoonlang

class TypingTests extends munit.FunSuite {
  test("functions and dependent applications typecheck") {
    val (_, result) = TestSupport.check(
      "def id (A: Type)(x: A): A := x\n\nid(Type, Type)"
    )
    assert(result.nonEmpty)
    assert(result.get.value.tpe == Value.TypeValue)
  }

  test("wrong dependent function arguments are rejected") {
    intercept[TypeMismatch] {
      TestSupport.check("def id (A: Type)(x: A): A := x\n\nid(Type, id)")
    }
  }

  test("body values must match their declared type") {
    intercept[TypeMismatch] {
      TestSupport.check("def bad (A: Type): A := Type")
    }
  }

  test("opaque and transparent definitions publish checked values") {
    val (env, _) = TestSupport.check("opaque def hidden : Type := Type\n\ndef visible : Type := Type\n")
    assert(env.globals.contains("hidden"))
    assert(env.globals.contains("visible"))
  }

  test("match checking is explicitly deferred") {
    intercept[WTF] {
      TestSupport.check("axiom b : Type\n\nmatch b with\n")
    }
  }

  test("recursive groups are checked against their declared Pis without termination evidence") {
    val (env, _) = TestSupport.check("def loop (n: Type): Type decreases structural(n) := n\n")
    assert(env.globals.contains("loop"))
  }

  test("checked recursive definitions remain transparent to later declarations") {
    val (env, _) = TestSupport.check(
      "axiom A : Type\n" +
        "axiom x : A\n" +
        "def choose (T: Type): Type decreases structural(T) := T\n" +
        "def y : choose(A) := x\n"
    )
    assert(env.globals.contains("y"))
  }

  test("checked recursive CoreAst groups validate peers and publish transparent lambdas") {
    val span = Span(0, 1)
    val n = CoreAst.LocalRef(10, "n")
    val fPeer = CoreAst.LocalRef(20, "f")
    val gPeer = CoreAst.LocalRef(21, "g")
    val pi = CoreAst.Term.Pi(
      Vector(CoreAst.Binder(n, CoreAst.Term.GlobalRef("Type", span), span)),
      CoreAst.Term.GlobalRef("Type", span),
      span
    )
    val decrease = CoreAst.DecreaseSpec.Lexicographic(Vector(n), span)
    val fBody = CoreAst.Term.App(CoreAst.Term.LocalRef(gPeer, span), Vector(CoreAst.Term.LocalRef(n, span)), span)
    val gBody = CoreAst.Term.LocalRef(n, span)
    val block = CoreAst.Decl.RecursiveDefBlock(
      Vector(
        CoreAst.RecursiveDef("f", fPeer, pi, fBody, decrease, span),
        CoreAst.RecursiveDef("g", gPeer, pi, gBody, decrease, span)
      ),
      span
    )
    val (env, _) = TypeChecker.checkProgram(CoreAst.Program(Vector(block), None))
    assert(env("f").isInstanceOf[Value.VLam])
    assert(env("g").isInstanceOf[Value.VLam])
  }
}
