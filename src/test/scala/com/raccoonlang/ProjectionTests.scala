package com.raccoonlang

class ProjectionTests extends munit.FunSuite {
  test("structures publish ordinary named selectors") {
    val source =
      "struct Pair (A: Type)(B: Type) : Type\n" +
        " | mk (fst: A)(snd: B) : Pair(A, B)\n\n" +
        "def first (A: Type)(B: Type)(p: Pair(A, B)): A := p.fst\n"
    val (env, _) = TestSupport.check(source)
    assert(env.globals.contains("Pair.fst"))
    assert(env.globals.contains("Pair.snd"))
  }

  test("selector definitions are one-case matches on self") {
    val core = TestSupport.core(
      "struct Pair (A: Type)(B: Type) : Type\n" +
        " | mk (fst: A)(snd: B) : Pair(A, B)\n"
    )
    core.decls.collectFirst { case CoreAst.Decl.ConstDecl(false, "Pair.fst", _, CoreAst.ConstBody.TermBody(term), _) =>
      term
    } match {
      case Some(CoreAst.Term.Lam(_, CoreAst.Term.Match(CoreAst.Term.LocalRef(_, _), _, cases, _), _, _, _, _)) =>
        assertEquals(cases.size, 1)
      case other => fail(s"Expected generated selector match, got $other")
    }
  }

  test("concrete projections reduce through the generated match") {
    val source =
      "struct Pair (A: Type)(B: Type) : Type\n" +
        " | mk (fst: A)(snd: B) : Pair(A, B)\n\n" +
        "{ let p : Pair(Type, Type) := Pair.mk(Type, Type)\n" +
        "  p.fst }"
    assertEquals(PrettyPrinter.print(TestSupport.eval(source)), "Type")
  }

  test("both nondependent named selectors execute") {
    val source =
      "struct Pair (A: Type)(B: Type) : Type\n" +
        " | mk (fst: A)(snd: B) : Pair(A, B)\n\n" +
        "{ let p : Pair(Type, Type) := Pair.mk(Type, Type)\n" +
        "  p.snd }"
    assertEquals(PrettyPrinter.print(TestSupport.eval(source)), "Type")
  }

  test("plain one-constructor inductives do not publish selectors") {
    val source = "inductive One : Type\n | mk : One\n"
    val (env, _) = TestSupport.check(source)
    assert(!env.globals.contains("One.x"))
  }

  test("structures with multiple constructors are rejected by the parser") {
    assert(LanguageParser.parseProgram("struct Bad : Type\n | one : Bad\n | two : Bad\n").isInstanceOf[Failure])
  }

  test("later field types can depend on earlier selectors") {
    val source =
      "struct Dep : Sort(Level.succ(Level.one))\n" +
        " | mk (T: Type)(x: T) : Dep\n\n" +
        "def get : (p: Dep) -> Type := fun (p: Dep): Type => p.T\n"
    val (env, _) = TestSupport.check(source)
    assert(env.globals.contains("Dep.T"))
  }

  test("dependent family projections preserve explicit indices") {
    val source =
      "inductive Nat : Type\n" +
        " | zero : Nat\n" +
        " | succ (n: Nat) : Nat\n\n" +
        "inductive Vec (A: Type) indices (n: Nat) : Type\n" +
        " | nil : Vec(A, Nat.zero)\n\n" +
        "struct Wrap (A: Type) indices (n: Nat) : Type\n" +
        " | mk (k: Nat)(x: Vec(A, k)) : Wrap(A, k)\n\n" +
        "def get (A: Type)(n: Nat)(w: Wrap(A, n)): Vec(A, w.k) := w.x\n"
    TestSupport.check(source)
  }

  test("later fields may instantiate a family-valued earlier projection") {
    val source =
      "struct Sigma (A: Type)(B: A -> Type) : Type\n" +
        " | mk (fst: A)(snd: B(fst)) : Sigma(A, B)\n\n" +
        "def getSnd (A: Type)(B: A -> Type)(p: Sigma(A, B)): B(p.fst) := p.snd\n"
    TestSupport.check(source)
  }

  test("a projection is valid in a type position") {
    val source =
      "struct Dep : Sort(Level.succ(Level.one))\n" +
        " | mk (T: Type)(x: T) : Dep\n\n" +
        "def same (p: Dep): (x: p.T) -> p.T := fun (x: p.T): p.T => x\n"
    TestSupport.check(source)
  }

  test("function-valued and opaque projections remain usable") {
    val source =
      "inductive Nat : Type\n | zero : Nat\n\n" +
        "struct Fn (A: Type) : Type\n" +
        " | mk (run: A -> A) : Fn(A)\n\n" +
        "opaque def hidden : Fn(Nat) := Fn.mk(fun (x: Nat): Nat => x)\n" +
        "def applyHidden : Nat := hidden.run(Nat.zero)\n"
    val (env, _) = TestSupport.check(source)
    assert(env.globals.contains("Fn.run"))
    val checkedCore = TestSupport.core(source + "\n{ hidden.run(Nat.zero) }\n")
    val (checkedEnv, checkedBody) = TypeChecker.checkProgram(checkedCore)
    val checked = checkedBody.getOrElse(fail("expected a checked body"))
    assert(checked.value.isInstanceOf[Value.VApp])
    assert(ValueEquivalence.defEq(Interpreter.evalTerm(checked.residual, checkedEnv), checked.value))
  }

  test("dependent-function-valued projections typecheck") {
    val source =
      "struct HasDepFn (A: Type)(B: A -> Type) : Type\n" +
        " | mk (f: (x: A) -> B(x)) : HasDepFn(A, B)\n\n" +
        "def get (A: Type)(B: A -> Type)(h: HasDepFn(A, B)): (x: A) -> B(x) := h.f\n"
    TestSupport.check(source)
  }

  test("opaque explicit-universe structure projection is usable in a type position") {
    val source =
      "inductive Nat : Type\n" +
        " | zero : Nat\n\n" +
        "struct PairU {u1: Level}{u2: Level}(A: Sort(u1))(B: Sort(u2)) : Sort(Level.max(u1, u2))\n" +
        " | mk (fst: A)(snd: B) : PairU(A, B)\n\n" +
        "opaque def F : PairU(Type, Type) := " +
        "PairU.mk(Nat, Nat)\n\n" +
        "def idF (x: F.fst): F.fst := x\n"
    TestSupport.check(source)
  }

  test("projection from a stuck match returning a structure remains neutral") {
    val source =
      "inductive Nat : Type\n" +
        " | zero : Nat\n" +
        " | succ (n: Nat) : Nat\n\n" +
        "struct Pair (A: Type)(B: Type) : Type\n" +
        " | mk (fst: A)(snd: B) : Pair(A, B)\n\n" +
        "opaque def step (n: Nat): Nat := n\n" +
        "def choose (n: Nat): Pair(Nat, Nat) := {\n" +
        "  match step(n) returning Pair(Nat, Nat) with\n" +
        "  | Nat.zero => Pair.mk(Nat.zero, Nat.zero)\n" +
        "  | Nat.succ k => Pair.mk(Nat.succ(k), k)\n" +
        "}\n" +
        "def first (n: Nat): Nat := { let p := choose(n) p.fst }\n"
    TestSupport.check(source)
    assert(TestSupport.eval(source + "\n{ first(Nat.zero) }\n").isInstanceOf[Value.NeutralThunk])
  }

  test("structure indices may depend on constructor fields") {
    val source =
      "inductive Nat : Type\n" +
        " | zero : Nat\n" +
        " | succ (n: Nat) : Nat\n\n" +
        "inductive Vec (A: Type) indices (n: Nat) : Type\n" +
        " | nil : Vec(A, Nat.zero)\n\n" +
        "struct Indexed (A: Type) indices (n: Nat) : Type\n" +
        " | mk (k: Nat)(x: Vec(A, k)) : Indexed(A, k)\n"
    TestSupport.check(source)
  }

  test("multi-constructor inductives do not publish named selectors") {
    val source =
      "inductive Choice : Type\n" +
        " | left : Choice\n" +
        " | right : Choice\n\n" +
        "def bad (x: Choice): Choice := x.field\n"
    intercept[NotFound] { TestSupport.check(source) }
  }

  test("plain and unknown selections fail by missing canonical globals") {
    intercept[NotFound] {
      TestSupport.check("inductive One : Type\n | mk : One\n\ndef bad (x: One): One := x.field\n")
    }
    intercept[NotFound] {
      TestSupport.check(
        "inductive Nat : Type\n | zero : Nat\n\n" +
          "struct Pair : Type\n | mk (x: Nat) : Pair\n\n" +
          "def bad (x: Pair): Nat := x.unknown\n"
      )
    }
  }

  test("anonymous structure fields do not generate underscore selectors") {
    val source =
      "inductive Nat : Type\n | zero : Nat\n\n" +
        "struct Anon : Type\n | mk (_: Nat) : Anon\n"
    val (env, _) = TestSupport.check(source)
    assert(!env.globals.contains("Anon._"))
  }

  test("explicit family arguments work for specialized selectors") {
    val source =
      "struct Pair (A: Type)(B: Type) : Type\n" +
        " | mk (fst: A)(snd: B) : Pair(A, B)\n\n" +
        "Pair.fst(Pair.mk(Type, Type))"
    assertEquals(PrettyPrinter.print(TestSupport.eval(source)), "Type")
  }

  test("nested Pi binders shadow earlier field names in selector types") {
    val source =
      "struct Shadow : Sort(Level.succ(Level.one))\n" +
        " | mk (T: Type)(f: (T: Type) -> T) : Shadow\n\n" +
        "def get (s: Shadow): (T: Type) -> T := s.f\n"
    TestSupport.check(source)
  }

  test("nested Pi types retain references to earlier fields") {
    val source =
      "struct Capture : Sort(Level.succ(Level.one))\n" +
        " | mk (A: Type)(f: (x: A) -> A) : Capture\n\n" +
        "def get (s: Capture): (x: s.A) -> s.A := s.f\n"
    TestSupport.check(source)
  }
}
