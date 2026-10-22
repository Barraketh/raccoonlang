package com.raccoonlang

/** The nominal principles and their exact refinement boundary (docs/kernel.md#nominal-type-families). */
class NominalFamiliesTest extends munit.FunSuite with TestSupport {
  test("large higher-order parameters and indices require level one") {
    for (result <- Vector("Type", "Prop"); indexed <- Vector(false, true)) {
      val binder = if (indexed) "indices (F: Type -> " + result + ")" else "(F: Type -> " + result + ")"
      val low = s"inductive Huge $binder : Type"
      val error = expectTypeError[FamilyArgumentTooLarge](low)
      assertEquals(error.argument, "F")
      assertEquals(error.level, Value.Level.one)
      typecheckDecls(low + " { level = one }")
    }
  }

  test("small higher-order and dependent argument telescopes stay at level zero") {
    typecheckDecls(
      """
        |inductive Small (A: Type)(B: A -> Type)(P: A -> Prop)(F: (a: A)(b: B(a)) -> Type) : Type
        |inductive ProofArg (P: Prop)(h: (A: Type) -> P -> P) : Type
        |inductive HugeProp (F: Type -> Type) : Prop
        |inductive HigherResult (F: Bool -> Type { level = one }) : Type { level = one }
        |""".stripMargin
    )
  }

  test("symbolic bounds charge universe domains at successor and each mutual family's own grade") {
    typecheckDecls("inductive Good {u: Level}(F: Type { level = u } -> Type { level = u }) : Type { level = succ(u) }")
    expectTypeError[FamilyArgumentTooLarge](
      "inductive Bad {u: Level}(F: Type { level = u } -> Prop) : Type { level = u }"
    )
    expectTypeError[FamilyArgumentTooLarge](
      """
        |mutual {
        | inductive Big (F: Type -> Type) : Type { level = one }
        | inductive Small (F: Type -> Type) : Type
        |}
        |""".stripMargin
    )
    expectTypeError[FamilyArgumentTooLarge](
      "def LargeFn : Type { level = one } := { (X: Type) -> Prop }\ninductive Alias (F: LargeFn) : Type"
    )
    expectTypeError[InductiveUniverseTooSmall]("inductive Store : Type\n | mk (A: Type) : Store")
  }

  test("N1 is invertible inside nested Type family arguments") {
    typecheckDecls(
      """
        |def nested (A: Type)(B: Type)(h: Eq(Type, List(List(A)), List(List(B)))): Eq(Type, A, B) := {
        | match h returning Eq(Type, A, B) with
        | | Eq.refl z => Eq.refl(A)
        |}
        |""".stripMargin
    )
  }

  test("N2 propagates through nested Type families") {
    typecheckDecls(
      """
        |def empty (h: Eq(Type, List(List(Nat)), List(List(Bool)))): False := {
        | match h returning False with
        |}
        |""".stripMargin
    )
  }

  test("N3 separates family, Type-valued Pi and Type universe forms") {
    val prefix = "inductive Big : Type { level = one }\n | mk : Big\n"
    for (
      (left, right, classifier) <- Vector(
        ("Nat", "Bool -> Bool", "Type"),
        ("Big", "Type", "Type { level = one }"),
        ("Bool -> Type", "Type", "Type { level = one }")
      )
    ) {
      for ((a, b) <- Vector((left, right), (s"List($left)", s"List($right)")))
        typecheckDecls(prefix + s"def empty (h: Eq($classifier, $a, $b)): False := { match h returning False with\n}")
    }
  }

  test("nested Prop family equations supply no injectivity, including the Russell injection") {
    expectTypeError[TypeMismatch](
      """
        |def inject (F: Prop -> Prop)(G: Prop -> Prop)
        | (h: Eq(Prop, Eq(Prop -> Prop, F, F), Eq(Prop -> Prop, G, G))): Eq(Prop -> Prop, F, G) := {
        | match h returning Eq(Prop -> Prop, F, G) with
        | | Eq.refl z => Eq.refl(F)
        |}
        |""".stripMargin
    )
    expectTypeError[TypeMismatch](
      """
        |inductive Named (P: Prop) : Type
        |def inject (P: Prop)(Q: Prop)(h: Eq(Type, Named(Eq(Prop, P, P)), Named(Eq(Prop, Q, Q)))): Eq(Prop, P, Q) := {
        | match h returning Eq(Prop, P, Q) with
        | | Eq.refl z => Eq.refl(P)
        |}
        |""".stripMargin
    )
  }

  test("Russell's contradiction through nested Eq propositions is rejected") {
    // The pre-nominal kernel accepts this complete False proof; the first injection is the invalid step.
    val source =
      """
        |def encode (F: (x: Prop) -> Prop): Prop := { Eq((x: Prop) -> Prop, F, F) }
        |
        |def inject (F: (x: Prop) -> Prop)(G: (x: Prop) -> Prop)(h: Eq(Prop, encode(F), encode(G))): Eq((x: Prop) -> Prop, F, G) := {
        | match h returning Eq((x: Prop) -> Prop, F, G) with
        | | Eq.refl z => Eq.refl(F)
        |}
        |
        |def member (x: Prop): (F: (p: Prop) -> Prop) -> Prop := fun (F: (p: Prop) -> Prop): Prop => And(Eq(Prop, x, encode(F)), Not(F(x)))
        |def Russell (x: Prop): Prop := { Exists((p: Prop) -> Prop, member(x)) }
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
        |def selfMember : Russell(encode(Russell)) := Exists.intro(member(encode(Russell)), Russell, And.intro(Eq.refl(encode(Russell)), selfNot))
        |def boom : False := selfNot(selfMember)
        |""".stripMargin
    val diagnostics = interceptDiagnostics { typecheckDecls(source) }
    assert(diagnostics.head.error.isInstanceOf[TypeMismatch])
  }

  test("root Prop indexed matching and homogeneous equality refinement remain available") {
    typecheckDecls(
      """
        |inductive At indices (n: Nat) : Prop
        | | here : At(0)
        |def root (n: Nat)(h: At(n)): Eq(Nat, n, 0) := {
        | match h returning Eq(Nat, n, 0) with
        | | At.here => Eq.refl(0)
        |}
        |def symmetry (A: Type)(x: A)(y: A)(h: Eq(A, x, y)): Eq(A, y, x) := {
        | match h returning Eq(A, y, x) with
        | | Eq.refl z => Eq.refl(x)
        |}
        |""".stripMargin
    )
  }

  test("rigid nullary root Prop matches inspect closed nested nominal clashes") {
    typecheckDecls(
      """
        |inductive At indices (A: Type) : Prop
        | | mk : At(List(Nat))
        |def empty (h: At(List(Bool))): False := {
        | match h returning False with
        |}
        |inductive Big : Type { level = one }
        |inductive HigherAt indices (A: Type { level = one }) : Prop
        | | mk : HigherAt(List(Big))
        |def higherEmpty (h: HigherAt(List(Type))): False := {
        | match h returning False with
        |}
        |inductive AtWithN indices (A: Type)(n: Nat) : Prop
        | | mk : AtWithN(List(Nat), 0)
        |def emptyWithN (n: Nat)(h: AtWithN(List(Bool), n)): False := {
        | match h returning False with
        |}
        |inductive HigherAtWithN indices (A: Type { level = one })(n: Nat) : Prop
        | | mk : HigherAtWithN(List(Big), 0)
        |def higherEmptyWithN (n: Nat)(h: HigherAtWithN(List(Type), n)): False := {
        | match h returning False with
        |}
        |""".stripMargin
    )
    for ((left, right) <- Vector(("List(List(Nat))", "List(List(Bool))"), ("List(Nat)", "List((x: Bool) -> Bool)"))) {
      val a = runProgram(s"{ $left }")
      val b = runProgram(s"{ $right }")
      ValueEquivalence.tryUnify(a, b, EqStore.empty) match {
        case Left(failure) => assert(failure.apart)
        case Right(_)      => fail("Closed nominal clash was identified")
      }
    }
  }

  test("opaque type and Quot heads supply no nominal apartness") {
    val assumed = TestSupport.preludeAssuming(TestSupport.bundledPreludeSource, "axiom Unknown : Type\n")
    expectTypeError[MissingCase](
      "def f (h: Eq(Type, Unknown, Nat)): False := { match h returning False with\n}",
      assumed
    )
    expectTypeError[MissingCase](
      """
        |def relation (a: Bool)(b: Bool): Prop := True
        |def f (h: Eq(Type, Quot(Bool, relation), Nat)): False := {
        | match h returning False with
        |}
        |""".stripMargin
    )
  }

  test("Prop-versus-Type forms, proposition Pis and all sort-field failures stay stuck") {
    import Value._
    def stuck(left: Value, right: Value): Unit = ValueEquivalence.tryUnify(left, right, EqStore.empty) match {
      case Left(failure) => assert(!failure.apart)
      case Right(_)      => fail("Expected a stuck equation")
    }
    stuck(Sorts.Prop, Sorts.Type)
    stuck(Sorts.Type, Sorts.sort(Level.one, Kind.unr))
    stuck(Sorts.Type, Sorts.sort(Level.zero, Kind.lin))
    expectTypeError[MissingCase]("def f (h: Eq(Prop, True, Bool -> True)): False := { match h returning False with\n}")
  }
}
