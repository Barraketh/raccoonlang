package com.raccoonlang

class TerminationTests extends munit.FunSuite {
  private val nat =
    "inductive Nat : Type\n" +
      " | zero : Nat\n" +
      " | succ (n: Nat) : Nat\n\n"

  private def eval(source: String): Value = TestSupport.eval(source)

  test("structural recursion accepts a constructor field") {
    val (env, _) = TestSupport.check(
      nat +
        "def pred (n: Nat): Nat decreases structural(n) := match n with\n" +
        " | Nat.zero => Nat.zero\n" +
        " | Nat.succ k => pred(k)\n"
    )
    assert(env.globals.contains("pred"))
  }

  test("structural recursion executes to the expected result") {
    val source =
      nat +
        "def add (a: Nat)(b: Nat): Nat decreases structural(b) := match b with\n" +
        " | Nat.zero => a\n" +
        " | Nat.succ x => add(Nat.succ(a), x)\n\n" +
        "add(Nat.succ(Nat.zero), Nat.succ(Nat.zero))"
    eval(source) match {
      case Value.VCtor(head, Vector(Value.VCtor(inner, Vector(_), _)), _) =>
        assertEquals(head.name, "Nat.succ")
        assertEquals(inner.name, "Nat.succ")
      case other => fail(s"expected two successors, got $other")
    }
  }

  test("structural recursion searches transitive constructor fields") {
    val span = Span(0, 1)
    val n = CoreAst.LocalRef(100, "n")
    val x = CoreAst.LocalRef(101, "x")
    val y = CoreAst.LocalRef(102, "y")
    val self = CoreAst.LocalRef(103, "skipTwo")
    val natTy = CoreAst.Term.GlobalRef("Nat", span)
    val body = CoreAst.Term.Match(
      CoreAst.Term.LocalRef(n, span),
      Some(natTy),
      Vector(
        CoreAst.Case("Nat.zero", true, Vector.empty, CoreAst.Term.GlobalRef("Nat.zero", span), span),
        CoreAst.Case(
          "Nat.succ",
          true,
          Vector(Some(x)),
          CoreAst.Term.Match(
            CoreAst.Term.LocalRef(x, span),
            Some(natTy),
            Vector(
              CoreAst.Case("Nat.zero", true, Vector.empty, CoreAst.Term.GlobalRef("Nat.zero", span), span),
              CoreAst.Case(
                "Nat.succ",
                true,
                Vector(Some(y)),
                CoreAst.Term.App(CoreAst.Term.LocalRef(self, span), Vector(CoreAst.Term.LocalRef(y, span)), span),
                span
              )
            ),
            span
          ),
          span
        )
      ),
      span
    )
    val pi = CoreAst.Term.Pi(Vector(CoreAst.Binder(n, natTy, span)), natTy, span)
    val lam = CoreAst.Term.Lam(
      pi,
      body,
      span,
      Some("skipTwo"),
      Some(CoreAst.Recursion(self, CoreAst.DecreaseSpec.Lexicographic(Vector(n), span)))
    )
    TypeChecker.checkDecl(
      CoreAst.Decl.ConstDecl(false, "skipTwo", pi, CoreAst.ConstBody.TermBody(lam), span),
      TestSupport.check(this.nat)._1
    )
  }

  test("recursive refs remain available in nested binder types under match refinement") {
    TestSupport.check(
      nat +
        "inductive Box (n: Nat) : Type\n | mk : Box(n)\n\n" +
        "def f (n: Nat): Nat decreases structural(n) := match n with\n" +
        " | Nat.zero => Nat.zero\n" +
        " | Nat.succ k => {\n" +
        "   let g := fun (x: Box(f(k))): Nat => Nat.zero\n" +
        "   Nat.zero\n" +
        " }\n"
    )
  }

  test("a recursive call without descent is rejected") {
    intercept[NonDecreasingRecursiveCall] {
      TestSupport.check(nat + "def loop (n: Nat): Nat decreases structural(n) := loop(n)\n")
    }
  }

  test("lexicographic recursion accepts an earlier or later decrease") {
    TestSupport.check(
      nat +
        "def lex (a: Nat)(b: Nat): Nat decreases lexicographic(a,b) := match a with\n" +
        " | Nat.zero => Nat.zero\n" +
        " | Nat.succ a0 => lex(a0, b)\n"
    )
  }

  test("lexicographic recursion requires some component to decrease") {
    intercept[NonDecreasingRecursiveCall] {
      TestSupport.check(nat + "def bad (a: Nat)(b: Nat): Nat decreases lexicographic(a,b) := bad(a,b)\n")
    }
  }

  test("measure recursion compares the evaluated measure") {
    val (env, _) = TestSupport.check(
      nat +
        "def consume (n: Nat): Nat decreases measure(n) := match n with\n" +
        " | Nat.zero => Nat.zero\n" +
        " | Nat.succ k => consume(k)\n"
    )
    assert(env.globals.contains("consume"))
  }

  test("measure recursion uses a nontrivial evaluated measure") {
    TestSupport.check(
      nat +
        "inductive List (A: Type) : Type\n" +
        " | nil : List(A)\n" +
        " | cons (tail: List(A)) (head: A) : List(A)\n\n" +
        "def length (A: Type)(xs: List(A)): Nat decreases structural(xs) := match xs returning Nat with\n" +
        " | List.nil => Nat.zero\n" +
        " | List.cons tail _ => Nat.succ(length(A,tail))\n\n" +
        "def consume (A: Type)(xs: List(A)): Nat decreases measure(length(A,xs)) := match xs returning Nat with\n" +
        " | List.nil => Nat.zero\n" +
        " | List.cons tail _ => consume(A,tail)\n"
    )
  }

  test("recursive self without decreases is not bound") {
    intercept[NotFound] {
      TestSupport.check(nat + "def bad (n: Nat): Nat := bad(n)\n")
    }
  }

  test("invalid structural binder and non-inductive metric are rejected") {
    intercept[InvalidDecreaseSpec] {
      TestSupport.check(nat + "def bad (n: Nat): Nat decreases structural(Nat) := n\n")
    }
    intercept[InvalidDecreaseSpec] {
      TestSupport.check(nat + "def bad (n: Nat): Nat decreases measure(Type) := n\n")
    }
    intercept[InvalidDecreaseSpec] {
      TestSupport.check(nat + "axiom Opaque : Type\ndef bad (q: Opaque): Nat decreases structural(q) := Nat.zero\n")
    }
  }

  test("function-valued constructor fields count as descendants") {
    val source =
      nat +
        "inductive Tree : Type\n | leaf : Tree\n | node (f: Nat -> Tree) : Tree\n\n" +
        "def depth (t: Tree): Nat decreases structural(t) := match t with\n" +
        " | Tree.leaf => Nat.zero\n" +
        " | Tree.node f => Nat.succ(depth(f(Nat.zero)))\n"
    TestSupport.check(source)
  }

  test("applications of non-subterm functions do not count as descent") {
    intercept[NonDecreasingRecursiveCall] {
      TestSupport.check(
        nat +
          "inductive Tree : Type\n | leaf : Tree\n | node (f: Nat -> Tree) : Tree\n\n" +
          "def bad (t: Tree)(g: Nat -> Tree): Nat decreases structural(t) := match t with\n" +
          " | Tree.leaf => Nat.zero\n" +
          " | Tree.node f => bad(g(Nat.zero),g)\n"
      )
    }
  }

  test("raw recursive self cannot escape through a let") {
    intercept[InvalidRecursiveOccurrence] {
      TestSupport.check(
        nat +
          "def bad (n: Nat): Nat decreases structural(n) := {\n" +
          " let go := bad\n" +
          " Nat.zero\n" +
          "}\n"
      )
    }
  }

  test("raw recursive self cannot be passed through an opaque application") {
    intercept[InvalidRecursiveOccurrence] {
      TestSupport.check(
        nat +
          "opaque def apply (h: Nat -> Nat)(n: Nat): Nat := h(n)\n\n" +
          "def bad (n: Nat): Nat decreases structural(n) := {\n" +
          " let x := apply(bad,n)\n" +
          " Nat.zero\n" +
          "}\n"
      )
    }
  }

  test("raw recursive self cannot be stored in a constructor field") {
    intercept[InvalidRecursiveOccurrence] {
      TestSupport.check(
        nat +
          "inductive Tree : Type\n" +
          " | leaf : Tree\n" +
          " | node (f: Nat -> Tree) : Tree\n\n" +
          "def bad (n: Nat): Tree decreases structural(n) := match n with\n" +
          " | Nat.zero => Tree.leaf\n" +
          " | Nat.succ k => Tree.node(bad)\n"
      )
    }
  }

  test("re-evaluated singleton recursion rebinds its copied self") {
    val source =
      "inductive QuoteNat : Type\n" +
        " | zero : QuoteNat\n" +
        " | succ (n: QuoteNat) : QuoteNat\n\n" +
        "def quotedPred (n: QuoteNat): QuoteNat decreases structural(n) := match n with\n" +
        " | QuoteNat.zero => QuoteNat.zero\n" +
        " | QuoteNat.succ k => quotedPred(k)\n\n" +
        "def poison (n: QuoteNat): QuoteNat := QuoteNat.succ(QuoteNat.zero)\n"
    val checked = TypeChecker.checkProgram(TestSupport.core(source))
    val residual = checked._1("quotedPred") match {
      case Value.VLam(_, _, Value.LamBody.Core(term, _)) => term
      case other                                         => fail(s"expected checked recursive lambda, got $other")
    }
    val poisoned = checked._1.copy(globals = checked._1.globals.updated("quotedPred", checked._1.globals("poison")))
    val copied = Interpreter.evalTerm(residual, poisoned)
    val zero = Interpreter.evalTerm(CoreAst.Term.GlobalRef("QuoteNat.zero", Span(0, 1)), poisoned)
    val one = Interpreter.evalApply(poisoned("QuoteNat.succ"), Vector(zero))
    val two = Interpreter.evalApply(poisoned("QuoteNat.succ"), Vector(one))
    Interpreter.evalApply(copied, Vector(two)) match {
      case Value.VCtor(head, _, _) => assertEquals(head.name, "QuoteNat.zero")
      case other                   => fail(s"expected QuoteNat.zero, got $other")
    }
  }
}
