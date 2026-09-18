package com.raccoonlang

class MatchCheckerTests extends munit.FunSuite {
  private def checked(source: String): (Env, Option[TypeChecker.CheckedTerm]) = TestSupport.check(source)

  test("all constructor cases check and preserve the result") {
    val (_, result) = checked(
      "inductive Bool : Type\n" +
        " | true : Bool\n" +
        " | false : Bool\n\n" +
        "def id (b: Bool): Bool := match b returning Bool with\n" +
        " | Bool.true => Bool.true\n" +
        " | Bool.false => Bool.false\n\n" +
        "id(Bool.true)"
    )
    assert(result.nonEmpty)
  }

  test("missing, duplicate, unknown, and malformed cases are rejected") {
    val prefix = "inductive Bool : Type\n | true : Bool\n | false : Bool\n\n"
    intercept[MissingCase] {
      checked(prefix + "def f (b: Bool): Bool := match b returning Bool with\n | Bool.true => Bool.true\n")
    }
    intercept[DuplicateCase] {
      checked(
        prefix + "def f (b: Bool): Bool := match b returning Bool with\n | Bool.true => Bool.true\n | Bool.true => Bool.true\n | Bool.false => Bool.false\n"
      )
    }
    intercept[UnknownConstructor] {
      checked(prefix + "def f (b: Bool): Bool := match b returning Bool with\n | Bool.nope => Bool.true\n")
    }
    intercept[ArityMismatch] {
      checked(
        prefix + "def f (b: Bool): Bool := match b returning Bool with\n | Bool.true x => Bool.true\n | Bool.false => Bool.false\n"
      )
    }
  }

  test("omitted motives infer equal reachable result types") {
    val (_, result) = checked(
      "inductive Bool : Type\n" +
        " | true : Bool\n" +
        " | false : Bool\n\n" +
        "def id (b: Bool): Bool := match b with\n" +
        " | Bool.true => Bool.true\n" +
        " | Bool.false => Bool.false\n"
    )
    assert(result.isEmpty)
  }

  test("declared return syntax is inherited by a match") {
    val (env, _) = checked(
      "inductive Bool : Type\n" +
        " | true : Bool\n" +
        " | false : Bool\n\n" +
        "def classify (b: Bool): Type := match b with\n" +
        " | Bool.true => Type\n" +
        " | Bool.false => Type\n"
    )
    assert(env.globals.contains("classify"))
  }

  test("concrete matches reject supplied unreachable cases") {
    intercept[UnreachableCase] {
      checked(
        "inductive Bool : Type\n" +
          " | true : Bool\n" +
          " | false : Bool\n\n" +
          "match Bool.true returning Bool with\n" +
          " | Bool.true => Bool.true\n" +
          " | Bool.false => Bool.false\n"
      )
    }
  }

  test("mismatched explicit motives are rejected") {
    intercept[TypeMismatch] {
      checked(
        "inductive Bool : Type\n" +
          " | true : Bool\n" +
          " | false : Bool\n\n" +
          "def bad (b: Bool): Bool := match b returning Type with\n" +
          " | Bool.true => Type\n" +
          " | Bool.false => Type\n"
      )
    }
  }

  test("indexed unreachable constructors are pruned") {
    intercept[UnreachableCase] {
      checked(
        "inductive Nat : Type\n" +
          " | zero : Nat\n" +
          " | succ (n: Nat) : Nat\n\n" +
          "inductive Vec (A: Type) indices (n: Nat) : Type\n" +
          " | nil : Vec(A, Nat.zero)\n" +
          " | cons (n: Nat) (xs: Vec(A, n)) (x: A) : Vec(A, Nat.succ(n))\n\n" +
          "def f (A: Type)(v: Vec(A, Nat.zero)): Nat := match v returning Nat with\n" +
          " | Vec.nil => Nat.zero\n" +
          " | Vec.cons n xs x => Nat.zero\n"
      )
    }
  }

  test("opaque neutral scrutinees still require every constructor") {
    intercept[MissingCase] {
      checked(
        "inductive Bool : Type\n" +
          " | true : Bool\n" +
          " | false : Bool\n\n" +
          "opaque def g (b: Bool): Bool := Bool.true\n\n" +
          "def f (b: Bool): Bool := match g(b) with\n" +
          " | Bool.true => Bool.true\n"
      )
    }
  }

  test("an impossible indexed match may have no cases under an expected result") {
    checked(
      "inductive Nat : Type\n" +
        " | zero : Nat\n" +
        " | succ (n: Nat) : Nat\n\n" +
        "inductive IsZero indices (n: Nat) : Type\n" +
        " | intro : IsZero(Nat.zero)\n\n" +
        "def absurd (n: Nat)(h: IsZero(Nat.succ(n))): Nat := match h with\n"
    )
  }

  test("a dependent declared return type is inherited by a match") {
    val (env, result) = checked(
      "inductive Bool : Type\n" +
        " | true : Bool\n" +
        " | false : Bool\n\n" +
        "def choose (A: Type)(b: Bool)(x: A): A := {\n" +
        " match b with\n" +
        " | Bool.true => x\n" +
        " | Bool.false => x\n" +
        "}\n\n" +
        "axiom a : Type\n\n" +
        "axiom x : a\n\n" +
        "choose(a, Bool.true, x)\n"
    )
    val choose = env("choose").asInstanceOf[Value.VLam]
    choose.body match {
      case Value.LamBody.Core(term, _) =>
        assert(term.body.asInstanceOf[CoreAst.Term.Body].res.asInstanceOf[CoreAst.Term.Match].motive.nonEmpty)
      case other => fail(s"Expected a core lambda, got $other")
    }
    assert(result.nonEmpty)
    assert(ValueEquivalence.defEq(result.get.value.tpe, env("a")))
  }

  test("a nested dependent match needs its own returning clause") {
    def source(returning: String): String =
      "inductive Nat : Type\n" +
        " | zero : Nat\n" +
        " | succ (n: Nat) : Nat\n\n" +
        "inductive Shape indices (n: Nat) : Type\n" +
        " | zeroCase : Shape(Nat.zero)\n" +
        " | succCase (m: Nat) : Shape(Nat.succ(m))\n\n" +
        "def nested (n: Nat)(s: Shape(n))(b: Nat)(c: Nat): Shape(n) := {\n" +
        " match b returning Shape(n) with\n" +
        " | Nat.zero => s\n" +
        " | Nat.succ _ => {\n" +
        s"   match c$returning with\n" +
        "   | Nat.zero => s\n" +
        "   | Nat.succ _ => s\n" +
        " }\n" +
        "}\n"
    intercept[MissingReturningClause] { checked(source("")) }
    checked(source(" returning Shape(n)"))
  }

  test("explicit equality-family refinement works with a neutral proof") {
    checked(
      "inductive Eq (A: Type) indices (a: A)(b: A) : Type\n" +
        " | refl (x: A) : Eq(A, x, x)\n\n" +
        "def symm (A: Type)(a: A)(b: A)(p: Eq(A, a, b)): Eq(A, b, a) := match p returning Eq(A, b, a) with\n" +
        " | Eq.refl x => Eq.refl(A, x)\n"
    )
  }

  test("a mismatched indexed motive is rejected") {
    intercept[TypeMismatch] {
      checked(
        "inductive Nat : Type\n" +
          " | zero : Nat\n" +
          " | succ (n: Nat) : Nat\n\n" +
          "inductive Eq (A: Type) indices (a: A)(b: A) : Type\n" +
          " | refl (x: A) : Eq(A, x, x)\n\n" +
          "def bad (a: Nat)(p: Eq(Nat, a, a)): Eq(Nat, a, Nat.succ(a)) := match p returning Eq(Nat, a, Nat.succ(a)) with\n" +
          " | Eq.refl x => Eq.refl(Nat, x)\n"
      )
    }
  }

  test("hidden non-family binders do not refine a requested index") {
    intercept[TypeMismatch] {
      checked(
        "inductive Nat : Type\n" +
          " | zero : Nat\n" +
          " | succ (n: Nat) : Nat\n\n" +
          "inductive Vec (A: Type) indices (n: Nat) : Type\n" +
          " | nil : Vec(A, Nat.zero)\n" +
          " | cons (n: Nat) (xs: Vec(A, n)) (x: A) : Vec(A, Nat.succ(n))\n\n" +
          "inductive Hidden indices (n: Nat) : Type\n" +
          " | mk {m: Nat} (x: Vec(Nat, m)) : Hidden(Nat.zero)\n\n" +
          "def bad (w: Hidden(Nat.zero)): Vec(Nat, Nat.zero) := match w returning Vec(Nat, Nat.zero) with\n" +
          " | Hidden.mk m x => x\n"
      )
    }
  }

  test("top-level synthesis leaves an omitted motive absent") {
    val (_, result) = checked(
      "inductive Bool : Type\n" +
        " | true : Bool\n" +
        " | false : Bool\n\n" +
        "axiom b : Bool\n\n" +
        "match b with\n" +
        " | Bool.true => Bool.true\n" +
        " | Bool.false => Bool.false\n"
    )
    assert(result.nonEmpty)
    assert(result.get.residual.asInstanceOf[CoreAst.Term.Match].motive.isEmpty)
  }

  test("synthesis rejects differing indexed results without an expectation") {
    val span = Span(0, 1)
    val nat = CoreAst.Decl.InductiveDecl(
      CoreAst.InductiveHeader("Nat", Vector.empty, Vector.empty, CoreAst.Term.GlobalRef("Type", span), span),
      Vector(
        CoreAst.ConstructorDecl("Nat.zero", "zero", Vector.empty, CoreAst.Term.GlobalRef("Nat", span), span),
        CoreAst.ConstructorDecl(
          "Nat.succ",
          "succ",
          Vector(CoreAst.Binder(CoreAst.LocalRef(300, "m"), CoreAst.Term.GlobalRef("Nat", span), span)),
          CoreAst.Term.GlobalRef("Nat", span),
          span
        )
      ),
      span
    )
    val index = CoreAst.LocalRef(301, "n")
    def shapeResult(indexTerm: CoreAst.Term): CoreAst.Term =
      CoreAst.Term.App(CoreAst.Term.GlobalRef("Shape", span), Vector(indexTerm), span)
    val shape = CoreAst.Decl.InductiveDecl(
      CoreAst.InductiveHeader(
        "Shape",
        Vector.empty,
        Vector(CoreAst.Binder(index, CoreAst.Term.GlobalRef("Nat", span), span)),
        CoreAst.Term.GlobalRef("Type", span),
        span
      ),
      Vector(
        CoreAst.ConstructorDecl(
          "Shape.zeroCase",
          "zeroCase",
          Vector.empty,
          shapeResult(CoreAst.Term.GlobalRef("Nat.zero", span)),
          span
        ),
        CoreAst.ConstructorDecl(
          "Shape.succCase",
          "succCase",
          Vector(CoreAst.Binder(CoreAst.LocalRef(302, "m"), CoreAst.Term.GlobalRef("Nat", span), span)),
          shapeResult(
            CoreAst.Term.App(
              CoreAst.Term.GlobalRef("Nat.succ", span),
              Vector(CoreAst.Term.LocalRef(CoreAst.LocalRef(302, "m"), span)),
              span
            )
          ),
          span
        )
      ),
      span
    )
    val (env, _) = TypeChecker.checkProgram(CoreAst.Program(Vector(nat, shape), None))
    val nRef = CoreAst.LocalRef(303, "n")
    val sRef = CoreAst.LocalRef(304, "s")
    val nValue = Interpreter.rigidBinderValue(nRef, env("Nat"))
    val withN = env.putLocal(nRef, nValue)
    val shapeType = Interpreter.evalApply(withN("Shape"), Vector(nValue))
    val withS = withN.putLocal(sRef, Interpreter.rigidBinderValue(sRef, shapeType))
    val matchTerm = CoreAst.Term.Match(
      CoreAst.Term.LocalRef(sRef, span),
      None,
      Vector(
        CoreAst.Case("Shape.zeroCase", true, Vector.empty, CoreAst.Term.LocalRef(sRef, span), span),
        CoreAst.Case(
          "Shape.succCase",
          true,
          Vector(Some(CoreAst.LocalRef(305, "m"))),
          CoreAst.Term.LocalRef(sRef, span),
          span
        )
      ),
      span
    )
    intercept[MissingReturningClause] { TypeChecker.checkTerm(matchTerm, withS) }
  }

  test("short constructor case heads are canonicalized") {
    checked(
      "inductive Bool : Type\n" +
        " | true : Bool\n" +
        " | false : Bool\n\n" +
        "def id (b: Bool): Bool := match b returning Bool with\n" +
        " | .true => Bool.true\n" +
        " | .false => Bool.false\n"
    )
  }
}
