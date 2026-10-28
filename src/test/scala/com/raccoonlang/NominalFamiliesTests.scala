package com.raccoonlang

class NominalFamiliesTests extends munit.FunSuite {
  private def typecheck(src: String, prelude: Prelude.Config = Prelude.test): Unit =
    LanguageParser.parseProgram(src + "\n") match {
      case Success(parsed, _, _) => Interpreter.run(Elaborator.elab(parsed, prelude), prelude); ()
      case err: Failure          => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }

  private val data =
    """
      |
      |inductive N : Type
      | | z : N
      |
      |inductive B : Type
      | | f : B
      |
      |inductive False : Prop
      |
      |inductive Big : Sort(Level.one)
      |
      |""".stripMargin

  test("higher-order parameters and indices require level one, even on empty families") {
    for (result <- Vector("Type", "Prop"); indexed <- Vector(false, true)) {
      val binder = s"${if (indexed) "indices " else ""}(F: Type -> $result)"
      val error = intercept[FamilyArgumentTooLarge] { typecheck(s"inductive Huge $binder : Type") }
      assertEquals(error.argument, "F")
      assertEquals(error.level, Value.Level.one)
      assert(error.span.nonEmpty)
      typecheck(s"inductive Huge $binder : Sort(Level.one)")
    }
  }

  test("small dependent functions, universe arguments, proof arguments and Prop families stay small") {
    typecheck(
      """
        |
        |inductive Small (A: Type)(B: A -> Type)(P: A -> Prop)(F: (a: A) -> (b: B(a)) -> Type) : Type
        |
        |inductive ProofArg (P: Prop)(h: (A: Type) -> P -> P) : Type
        |
        |inductive HugeProp (F: Type -> Type) : Prop
        |
        |inductive UniverseArg (u: Level)(A: Sort(u)) : Sort(u)
        |
        |inductive HigherResult (A: Type)(F: A -> Sort(Level.one)) : Sort(Level.one)
        |""".stripMargin
    )
  }

  test("symbolic bounds and evaluated type aliases cannot hide large family arguments") {
    typecheck("inductive Good (u: Level)(F: (Sort(u) -> Sort(u))) : Sort(Level.succ(u))")
    intercept[FamilyArgumentTooLarge] {
      typecheck("inductive Bad (u: Level)(F: (Sort(u) -> Prop)) : Sort(u)")
    }
    intercept[FamilyArgumentTooLarge] {
      typecheck("def LargeFn : Sort(Level.one) := { (X: Type) -> Prop }\n\ninductive Alias (F: LargeFn) : Type")
    }
    intercept[InductiveUniverseTooSmall] {
      typecheck("inductive Store : Type\n | mk (A: Type) : Store")
    }
  }

  test("N1 inverts nested Type family arguments") {
    typecheck(
      data +
        """
          |
          |def nested (A: Type)(B: Type)(h: Eq(Type, List(List(A)), List(List(B)))): Eq(Type, A, B) := {
          | match h returning Eq(Type, A, B) with
          | | Eq.refl z => Eq.refl(A)
          |}
          |""".stripMargin
    )
  }

  test("N2 and N3 exclude distinct nominal Type forms at arbitrary depth and in both directions") {
    for (
      (left, right, classifier) <- Vector(
        ("N", "B", "Type"),
        ("N", "List(N)", "Type"),
        ("N", "B -> B", "Type"),
        ("Big", "Type", "Sort(Level.one)"),
        ("B -> Type", "Type", "Sort(Level.one)")
      );
      (a, b) <- Vector((left, right), (right, left), (s"List($left)", s"List($right)"))
    ) typecheck(data + s"def empty (h: Eq($classifier, $a, $b)): False := { match h returning False with\n}")
  }

  test("constructor result types supply Prop index equations and equality refinement") {
    typecheck(
      data +
        """
          |
          |inductive At indices (A: Type) : Prop
          | | here : At(N)
          |
          |def root (A: Type)(h: At(A)): Eq(Type, A, N) := {
          | match h returning Eq(Type, A, N) with
          | | At.here => Eq.refl(N)
          |}
          |
          |def empty (h: At(B)): False := { match h returning False with
          |}
          |
          |def symmetry (A: Type)(x: A)(y: A)(h: Eq(A, x, y)): Eq(A, y, x) := {
          | match h returning Eq(A, y, x) with
          | | Eq.refl z => Eq.refl(x)
          |}
          |
          |def transport (P: Prop)(Q: Prop)(h: Eq(Prop, P, Q))(p: P): Q := {
          | match h returning Q with
          | | Eq.refl z => p
          |}
          |""".stripMargin
    )
  }

  test("Prop families have no general injectivity, including inside nominal Type families") {
    intercept[TypeMismatch] {
      typecheck("""
                  |
                  |def inject (F: Prop -> Prop)(G: Prop -> Prop)
                  | (h: Eq(Prop, Eq(Prop -> Prop, F, F), Eq(Prop -> Prop, G, G))): Eq(Prop -> Prop, F, G) := {
                  | match h returning Eq(Prop -> Prop, F, G) with
                  | | Eq.refl z => Eq.refl(F)
                  |}
                  |""".stripMargin)
    }
    intercept[TypeMismatch] {
      typecheck(
        """
          |
          |inductive Named (P: Prop) : Type
          |
          |def inject (P: Prop)(Q: Prop)(h: Eq(Type, Named(Eq(Prop, P, P)), Named(Eq(Prop, Q, Q)))): Eq(Prop, P, Q) := {
          | match h returning Eq(Prop, P, Q) with
          | | Eq.refl z => Eq.refl(P)
          |}
          |""".stripMargin
      )
    }
  }

  test("Prop families, proposition Pis, opaque types and universe mismatches supply no apartness") {
    for (
      (left, right, classifier) <- Vector(
        ("False", "True", "Prop"),
        ("False", "B -> True", "Prop"),
        ("At(N)", "At(B)", "Prop"),
        ("Unknown", "N", "Type"),
        ("Prop", "Type", "Sort(Level.one)"),
        ("Type", "Sort(Level.one)", "Sort(Level.succ(Level.one))")
      )
    ) intercept[MissingCase] {
      typecheck(
        data +
          "inductive True : Prop\n | intro : True\n\ninductive At (A: Type) : Prop\n\naxiom Unknown : Type\n\n" +
          s"def bad (h: Eq($classifier, $left, $right)): False := { match h returning False with\n}"
      )
    }
  }

  test("Russell's contradiction through equality propositions is rejected") {
    val source =
      """
        |
        |def encode (F: (x: Prop) -> Prop): Prop := Eq((x: Prop) -> Prop, F, F)
        |
        |def inject (F: (x: Prop) -> Prop)(G: (x: Prop) -> Prop)(h: Eq(Prop, encode(F), encode(G))): Eq((x: Prop) -> Prop, F, G) := {
        | match h returning Eq((x: Prop) -> Prop, F, G) with
        | | Eq.refl z => Eq.refl(F)
        |}
        |
        |def member (x: Prop): (F: (p: Prop) -> Prop) -> Prop := fun (F: (p: Prop) -> Prop): Prop => And(Eq(Prop, x, encode(F)), Not(F(x)))
        |
        |def Russell (x: Prop): Prop := Exists((p: Prop) -> Prop, member(x))
        |
        |def selfNot (r: Russell(encode(Russell))): False := {
        | match r returning False with
        | | Exists.intro F evidence => {
        |   match evidence returning False with
        |   | And.intro same negative => {
        |     let equal: Eq((x: Prop) -> Prop, F, Russell) := inject(F, Russell, Eq.symm(same))
        |     let atSelf: Eq(Prop, F(encode(Russell)), Russell(encode(Russell))) := congrFun(Prop, Prop, F, Russell, equal, encode(Russell))
        |     negative(Eq.mpr(atSelf, r))
        |   }
        | }
        |}
        |
        |def selfMember : Russell(encode(Russell)) := {
        | let code: Prop := encode(Russell)
        | let evidence: member(code)(Russell) := And.intro(Eq(Prop, code, code), Not(Russell(code)), Eq.refl(code), selfNot)
        | Exists.intro((p: Prop) -> Prop, member(code), Russell, evidence)
        |}
        |
        |def boom : False := selfNot(selfMember)
        |""".stripMargin
    intercept[TypeMismatch] { typecheck(source, Prelude.default) }
    // The remainder is a well-typed contradiction if the invalid injection is
    // assumed. Keep the entire exploit checked, not just its failing prefix.
    val injectionStart = source.indexOf("def inject")
    val injectionEnd = source.indexOf("def member")
    val assumedInjection =
      "axiom inject (F: (x: Prop) -> Prop)(G: (x: Prop) -> Prop)" +
        "(h: Eq(Prop, encode(F), encode(G))): Eq((x: Prop) -> Prop, F, G)\n\n"
    typecheck(source.take(injectionStart) + assumedInjection + source.substring(injectionEnd), Prelude.default)
  }
}
