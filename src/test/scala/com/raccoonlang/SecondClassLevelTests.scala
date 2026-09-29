package com.raccoonlang

/**
 * Levels are second-class (spec §2.2, §2.4, §8): `Level` is not a type, a level variable is bound only by a
 * declaration's header or a family parameter, a level stands only at a parameter position, and a function type that
 * binds a level is large. Each rule has an admitted program and the smallest mutation that reaches its diagnostic.
 */
class SecondClassLevelTests extends munit.FunSuite with TestSupport {

  test("a level binder is admitted in a declaration's header") {
    typecheckDecls("def f {u: Level}(A: Sort { level = u })(x: A): A := x\n")
    typecheckDecls("opaque def f (u: Level)(A: Sort { level = u }): Sort { level = u } := A\n")
    // Only the trusted prelude declares axioms (§7.3).
    val axiom = "axiom f {u: Level}(A: Sort { level = u }): Sort { level = u }\n"
    TestSupport.preludeAssuming(TestSupport.testPreludeSource, axiom).checkedEnv
  }

  test("a level binder is admitted as a family parameter, not as an index") {
    def program(binders: String, result: String): String = s"inductive Box $binders : Type\n | mk : Box($result)\n"

    typecheckDecls(program("(u: Level)", "u"))
    expectOnly[NotAType](typecheckDecls(program("indices (u: Level)", "Level.zero")))
  }

  test("a constructor field cannot bind a level") {
    def program(field: String): String = s"inductive Holder : Type\n | mk ($field) : Holder\n"

    typecheckDecls(program("n: Nat"))
    expectOnly[NotAType](typecheckDecls(program("u: Level")))
  }

  test("a function type cannot bind a level") {
    def program(domain: String): String = s"def apply (f: ($domain) -> Nat): Nat := 0\n"

    typecheckDecls(program("n: Nat"))
    expectOnly[NotAType](typecheckDecls(program("u: Level")))
  }

  test("a lambda cannot bind a level") {
    def program(binder: String): String = s"{ let f := fun ($binder): Nat => 0\n  0 }\n"

    runProgram(program("n: Nat"))
    expectOnly[NotAType](typecheckDecls(program("u: Level")))
  }

  // A header is the binders before a declaration's `:`; a function type written after it is an ordinary one.
  test("a function type written after a declaration's colon is not its header") {
    typecheckDecls("def f {u: Level}(A: Sort { level = u }): Nat := 0\n")
    expectOnly[NotAType](typecheckDecls("def f : {u: Level} -> Sort { level = u } -> Nat := 0\n"))
  }

  // The written function type would bind a level that its own codomain's universe escapes.
  test("a definition's written type cannot bind a level for its body") {
    typecheckDecls("def F (u: Level) : Sort { level = succ(u) } := Sort { level = u }\n")
    expectOnly[NotAType](
      typecheckDecls(
        "def F : (u: Level) -> Sort { level = succ(succ(u)) } := fun (u: Level): Sort { level = succ(succ(u)) } => " +
          "Sort { level = succ(u) }\n"
      )
    )
  }

  test("Level is not a type") {
    def program(body: String): String = s"def f {u: Level}(A: Sort { level = u })(x: A): Nat := $body\n"

    typecheckDecls(program("List.length(List.cons(x, List.nil(A)))"))
    expectOnly[NotAType](typecheckDecls(program("List.length(List.nil(Level))")))
    expectOnly[NotAType](typecheckDecls(program("{ let p : Eq(Level, u, u) := Eq.refl(u)\n 0 }")))
    expectOnly[NotAType](typecheckDecls("def l : Level := Level.zero\n"))
    expectOnly[NotAType](typecheckDecls("def next (u: Level) : Level := Level.succ(u)\n"))
    expectOnly[NotAType](typecheckDecls("{ Level }\n"))
  }

  test("a level is an argument only at a level binder") {
    def program(body: String): String =
      s"""
         |def at (u: Level)(A: Sort { level = u })(x: A): A := x
         |
         |def f {u: Level}(A: Sort { level = u })(x: A): A := $body
         |""".stripMargin

    typecheckDecls(program("at(u, A, x)"))
    expectOnly[NotAType](typecheckDecls(program("at(u, A, u)")))
    expectOnly[TypeMismatch](typecheckDecls(program("at(Nat.zero, A, x)")))
  }

  test("a level is a sort's level field, and a term of another type there is a type mismatch") {
    def program(level: String): String = s"def s : Sort { level = succ(one) } := Sort { level = $level }\n"

    typecheckDecls(program("Level.one"))
    expectOnly[TypeMismatch](typecheckDecls(program("Nat.zero")))
    expectOnly[NotAType](typecheckDecls(program("Level")))
  }

  test("a level stands nowhere else: not a scrutinee, a block's result, or a let") {
    def program(body: String): String = s"def f {u: Level}(A: Sort { level = u })(n: Nat)(x: A): Nat := $body\n"
    def scrutinee(term: String): String =
      s"match $term returning Nat with\n | Nat.zero => 0\n | Nat.succ k => k"

    typecheckDecls(program(scrutinee("n")))
    expectOnly[NotAType](typecheckDecls(program(scrutinee("u"))))
    typecheckDecls(program("{ n }"))
    expectOnly[NotAType](typecheckDecls(program("{ u }")))
    typecheckDecls(program("{ let m := n\n m }"))
    expectOnly[NotAType](typecheckDecls(program("{ let v := Level.succ(u)\n n }")))
    expectOnly[NotAType](typecheckDecls(program("{ let v : Level := u\n n }")))
  }

  // A level-polymorphic declaration is used only applied: its type is large, so no local can hold it.
  test("a large reference heads an application and stands nowhere else") {
    def program(body: String): String =
      s"""
         |def twice (f: Nat -> Nat)(n: Nat): Nat := f(f(n))
         |
         |def g (n: Nat): Nat := $body
         |""".stripMargin

    typecheckDecls(program("id(n)"))
    typecheckDecls(program("{ let f := fun (m: Nat): Nat => id(m)\n f(n) }"))
    expectOnly[NotAType](typecheckDecls(program("{ let f := id\n f(n) }")))
    typecheckDecls(program("twice(fun (m: Nat): Nat => id(m), n)"))
    expectOnly[NotAType](typecheckDecls(program("twice(id, n)")))
    expectOnly[NotAType](typecheckDecls("def natId : Nat -> Nat := id\n"))
  }

  test("a level-polymorphic declaration's type is large, and its instances are small") {
    val env = Prelude.default.checkedEnv
    assert(env("id").tpe.tpe eq Value.Large)
    assert(env("List").tpe.tpe eq Value.Large)
    assert(env("List.cons").tpe.tpe eq Value.Large)
    assert(env("Nat.add").tpe.tpe.isInstanceOf[Value.VSort])

    runProgram("{ List.cons(0, List.nil(Nat)) }").tpe.tpe match {
      case sort: Value.VSort => assert(ValueEquivalence.defEq(sort, Sorts.Type))
      case other             => fail(s"Expected List(Nat) to be a Type, got a type classified by $other")
    }
  }

  // Spec §2.4: a large function type into a proposition is proof-valued, like a small one.
  test("a level-polymorphic lemma publishes and applies as a proof, and its body never runs") {
    Prelude.default.checkedEnv("Eq.symm") match {
      case Value.VLam(pi, _, Value.LamBody.ProofEta) =>
        assert(pi.tpe eq Value.Large)
        assert(Sorts.isProposition(pi))
      case other => fail(s"Expected Eq.symm to publish as the canonical proof eta-lambda, got $other")
    }

    runProgram("{ Eq.symm(Eq.refl(0)) }") match {
      case Value.VCtor(head, Vector(field), _) =>
        assertEquals(head.name, "Eq.refl")
        assertEquals(PrettyPrinter.print(field), "0")
      case other => fail(s"Expected the reconstructed proof Eq.refl(0), got $other")
    }
  }

  test("a match's motive is a type") {
    def program(motive: String): String =
      s"def f (n: Nat): Nat := match n returning $motive with\n | Nat.zero => 0\n | Nat.succ k => k\n"

    typecheckDecls(program("Nat"))
    expectOnly[NotAType](typecheckDecls(program("Nat.zero")))
  }

  test("a let's annotation is a type") {
    def program(annotation: String): String = s"def f (n: Nat): Nat := {\n  let m : $annotation := n\n  m\n}\n"

    typecheckDecls(program("Nat"))
    expectOnly[NotAType](typecheckDecls(program("Nat.zero")))
  }
}
