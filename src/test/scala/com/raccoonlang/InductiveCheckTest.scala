package com.raccoonlang

class InductiveCheckTest extends munit.FunSuite {
  private val testSpan = Span(0, 1)

  private def coreDecl(
      name: String,
      params: Vector[CoreAst.Binder] = Vector.empty,
      indices: Vector[CoreAst.Binder] = Vector.empty,
      result: CoreAst.Term = CoreAst.Term.GlobalRef("Type", testSpan),
      ctors: Vector[CoreAst.ConstructorDecl] = Vector.empty
  ): CoreAst.Decl.InductiveDecl =
    CoreAst.Decl.InductiveDecl(
      CoreAst.InductiveHeader(name, params, indices, result, testSpan),
      ctors,
      testSpan
    )

  private def ctor(
      name: String,
      fields: Vector[CoreAst.Binder],
      result: CoreAst.Term,
      shortName: String = "mk"
  ): CoreAst.ConstructorDecl =
    CoreAst.ConstructorDecl(s"$name.$shortName", shortName, fields, result, testSpan)

  test("basic inductive formation and constructor publication typecheck") {
    val (env, _) = TestSupport.check("inductive Bool : Type\n | true : Bool\n | false : Bool\n\nBool.true")
    assert(env.globals.contains("Bool.true"))
  }

  test("malformed constructor results are rejected") {
    intercept[InvalidConstructorResult] {
      TestSupport.check("inductive Bool : Type\n | bad : Type\n")
    }
  }

  test("inductive publication is atomic when a constructor fails") {
    val core = TestSupport.core("inductive Bool : Type\n | bad : Type\n")
    val env = Interpreter.builtins
    intercept[InvalidConstructorResult] { TypeChecker.checkDecl(core.decls.head, env) }
    assert(!env.globals.contains("Bool"))
  }

  test("non-positive recursive occurrences are rejected") {
    intercept[NonStrictlyPositive] {
      TestSupport.check(
        "inductive Bad : Sort(Level.succ(Level.one))\n | mk (f: Bad -> Bad) : Bad\n"
      )
    }
  }

  test("non-uniform recursive family parameters are rejected by positivity") {
    intercept[NonStrictlyPositive] {
      TestSupport.check(
        """
          |inductive Bool : Type
          | | true : Bool
          |
          |inductive Bad(A: Type) : Type
          | | mk (tail: Bad(Bool)) : Bad(A)
          |""".stripMargin + "\n"
      )
    }
  }

  test("partial recursive family applications are rejected") {
    intercept[TypeError] {
      TestSupport.check(
        """
          |inductive Partial(A: Type) : Type
          | | mk (f: Partial -> Type) : Partial(A)
          |""".stripMargin + "\n"
      )
    }
  }

  test("duplicate constructors are rejected before publication") {
    intercept[AlreadyDefined] {
      TestSupport.check("inductive Bool : Type\n | same : Bool\n | same : Bool\n")
    }
  }

  test("mutual inductive formation sees every provisional family") {
    val span = Span(0, 1)
    val left = CoreAst.Decl.InductiveDecl(
      CoreAst.InductiveHeader("Left", Vector.empty, Vector.empty, CoreAst.Term.GlobalRef("Type", span), span),
      Vector(CoreAst.ConstructorDecl("Left.l", "l", Vector.empty, CoreAst.Term.GlobalRef("Left", span), span)),
      span
    )
    val right = CoreAst.Decl.InductiveDecl(
      CoreAst.InductiveHeader("Right", Vector.empty, Vector.empty, CoreAst.Term.GlobalRef("Type", span), span),
      Vector(
        CoreAst.ConstructorDecl(
          "Right.r",
          "r",
          Vector(CoreAst.Binder(CoreAst.LocalRef(2, "left"), CoreAst.Term.GlobalRef("Left", span), span)),
          CoreAst.Term.GlobalRef("Right", span),
          span
        )
      ),
      span
    )
    val (env, _) =
      TypeChecker.checkProgram(CoreAst.Program(Vector(CoreAst.Decl.InductiveBlock(Vector(left, right), span)), None))
    assert(env.globals.contains("Left"))
    assert(env.globals.contains("Right"))
  }

  test("mutual inductives reject non-uniform parameter telescopes") {
    val span = Span(0, 1)
    val binder = CoreAst.Binder(CoreAst.LocalRef(1, "A"), CoreAst.Term.GlobalRef("Type", span), span)
    val left = CoreAst.Decl.InductiveDecl(
      CoreAst.InductiveHeader("Left", Vector(binder), Vector.empty, CoreAst.Term.GlobalRef("Type", span), span),
      Vector(
        CoreAst.ConstructorDecl(
          "Left.l",
          "l",
          Vector.empty,
          CoreAst.Term
            .App(CoreAst.Term.GlobalRef("Left", span), Vector(CoreAst.Term.LocalRef(binder.localRef, span)), span),
          span
        )
      ),
      span
    )
    val right = CoreAst.Decl.InductiveDecl(
      CoreAst.InductiveHeader("Right", Vector.empty, Vector.empty, CoreAst.Term.GlobalRef("Type", span), span),
      Vector(CoreAst.ConstructorDecl("Right.r", "r", Vector.empty, CoreAst.Term.GlobalRef("Right", span), span)),
      span
    )
    intercept[InvalidInductiveBlock] {
      TypeChecker.checkProgram(CoreAst.Program(Vector(CoreAst.Decl.InductiveBlock(Vector(left, right), span)), None))
    }
  }

  test("constructors must return their declared parameter") {
    val span = Span(0, 1)
    val param = CoreAst.Binder(CoreAst.LocalRef(40, "A"), CoreAst.Term.GlobalRef("Type", span), span)
    val wrongResult = CoreAst.Term.App(
      CoreAst.Term.GlobalRef("Box", span),
      // Level is a well-typed value of Type, but it is not the declared
      // parameter A.  This reaches the constructor-parameter discipline check
      // instead of failing because the argument is itself ill-typed.
      Vector(CoreAst.Term.GlobalRef("Level", span)),
      span
    )
    val decl = CoreAst.Decl.InductiveDecl(
      CoreAst.InductiveHeader("Box", Vector(param), Vector.empty, CoreAst.Term.GlobalRef("Type", span), span),
      Vector(CoreAst.ConstructorDecl("Box.mk", "mk", Vector.empty, wrongResult, span)),
      span
    )
    intercept[NonUniformInductiveParam] {
      TypeChecker.checkProgram(CoreAst.Program(Vector(decl), None))
    }
  }

  test("mutual families accept alpha-equivalent dependent parameters") {
    val span = Span(0, 1)
    def family(name: String, aId: Int, bId: Int, ctorName: String): CoreAst.Decl.InductiveDecl = {
      val a = CoreAst.Binder(CoreAst.LocalRef(aId, "A"), CoreAst.Term.GlobalRef("Type", span), span)
      val b = CoreAst.Binder(CoreAst.LocalRef(bId, "B"), CoreAst.Term.LocalRef(a.localRef, span), span)
      val result = CoreAst.Term.App(
        CoreAst.Term.GlobalRef(name, span),
        Vector(CoreAst.Term.LocalRef(a.localRef, span), CoreAst.Term.LocalRef(b.localRef, span)),
        span
      )
      CoreAst.Decl.InductiveDecl(
        CoreAst.InductiveHeader(name, Vector(a, b), Vector.empty, CoreAst.Term.GlobalRef("Type", span), span),
        Vector(CoreAst.ConstructorDecl(s"$name.$ctorName", ctorName, Vector.empty, result, span)),
        span
      )
    }
    val (env, _) = TypeChecker.checkProgram(
      CoreAst.Program(
        Vector(CoreAst.Decl.InductiveBlock(Vector(family("Left", 60, 61, "l"), family("Right", 70, 71, "r")), span)),
        None
      )
    )
    assert(env.globals.contains("Left"))
    assert(env.globals.contains("Right"))
  }

  test("indexed constructors may compute their result index from fields") {
    val span = Span(0, 1)
    val a = CoreAst.Binder(CoreAst.LocalRef(80, "A"), CoreAst.Term.GlobalRef("Type", span), span)
    val x = CoreAst.Binder(CoreAst.LocalRef(81, "x"), CoreAst.Term.LocalRef(a.localRef, span), span)
    val y = CoreAst.Binder(CoreAst.LocalRef(82, "y"), CoreAst.Term.LocalRef(a.localRef, span), span)
    val result = CoreAst.Term.App(
      CoreAst.Term.GlobalRef("Eq", span),
      Vector(CoreAst.Term.LocalRef(a.localRef, span), CoreAst.Term.LocalRef(y.localRef, span)),
      span
    )
    val declaration = CoreAst.Decl.InductiveDecl(
      CoreAst.InductiveHeader("Eq", Vector(a), Vector(x), CoreAst.Term.GlobalRef("Type", span), span),
      Vector(CoreAst.ConstructorDecl("Eq.refl", "refl", Vector(y), result, span)),
      span
    )
    val (env, _) = TypeChecker.checkProgram(CoreAst.Program(Vector(declaration), None))
    assert(env.globals.contains("Eq.refl"))
  }

  test("indexed constructor results cannot refer to header indices as fields") {
    val span = Span(0, 1)
    val a = CoreAst.Binder(CoreAst.LocalRef(90, "A"), CoreAst.Term.GlobalRef("Type", span), span)
    val x = CoreAst.Binder(CoreAst.LocalRef(91, "x"), CoreAst.Term.LocalRef(a.localRef, span), span)
    val result = CoreAst.Term.App(
      CoreAst.Term.GlobalRef("Eq", span),
      Vector(CoreAst.Term.LocalRef(a.localRef, span), CoreAst.Term.LocalRef(x.localRef, span)),
      span
    )
    val declaration = CoreAst.Decl.InductiveDecl(
      CoreAst.InductiveHeader("Eq", Vector(a), Vector(x), CoreAst.Term.GlobalRef("Type", span), span),
      Vector(CoreAst.ConstructorDecl("Eq.bad", "bad", Vector.empty, result, span)),
      span
    )
    intercept[NotFound] {
      TypeChecker.checkProgram(CoreAst.Program(Vector(declaration), None))
    }
  }

  test("constructor parameter discipline is based on definitional equality") {
    val span = Span(0, 1)
    val a = CoreAst.Binder(CoreAst.LocalRef(100, "A"), CoreAst.Term.GlobalRef("Type", span), span)
    val b = CoreAst.LocalRef(101, "B")
    val wrapped = CoreAst.Term.Body(
      Vector(CoreAst.Let(b, None, CoreAst.Term.LocalRef(a.localRef, span), span)),
      CoreAst.Term.App(CoreAst.Term.GlobalRef("Box", span), Vector(CoreAst.Term.LocalRef(b, span)), span),
      span
    )
    val declaration = CoreAst.Decl.InductiveDecl(
      CoreAst.InductiveHeader("Box", Vector(a), Vector.empty, CoreAst.Term.GlobalRef("Type", span), span),
      Vector(CoreAst.ConstructorDecl("Box.mk", "mk", Vector.empty, wrapped, span)),
      span
    )
    val (env, _) = TypeChecker.checkProgram(CoreAst.Program(Vector(declaration), None))
    assert(env.globals.contains("Box.mk"))
  }

  test("a nullary family result must be a Sort") {
    val base = CoreAst.Decl.AxiomDecl("Base", CoreAst.Term.GlobalRef("Type", testSpan), testSpan)
    intercept[InductiveTypeNotASort] {
      TypeChecker.checkProgram(
        CoreAst.Program(Vector(base, coreDecl("Bad", result = CoreAst.Term.GlobalRef("Base", testSpan))), None)
      )
    }
  }

  test("a Pi family result must itself be a Sort") {
    val a = CoreAst.Binder(CoreAst.LocalRef(201, "A"), CoreAst.Term.GlobalRef("Type", testSpan), testSpan)
    intercept[InductiveTypeNotASort] {
      TypeChecker.checkProgram(
        CoreAst.Program(
          Vector(coreDecl("BadPi", params = Vector(a), result = CoreAst.Term.LocalRef(a.localRef, testSpan))),
          None
        )
      )
    }
  }

  test("a constructor with the wrong head reports its specific result error") {
    val bad = coreDecl("Good", ctors = Vector(ctor("Good", Vector.empty, CoreAst.Term.GlobalRef("Type", testSpan))))
    val error = intercept[InvalidConstructorResult] {
      TypeChecker.checkProgram(CoreAst.Program(Vector(bad), None))
    }
    assertEquals(error.ctor, "Good.mk")
    assertEquals(error.inductive, "Good")
  }

  test("a constructor with an incomplete result spine reports its specific result error") {
    val a = CoreAst.Binder(CoreAst.LocalRef(202, "A"), CoreAst.Term.GlobalRef("Type", testSpan), testSpan)
    val incomplete = coreDecl(
      "Partial",
      params = Vector(a),
      ctors = Vector(ctor("Partial", Vector.empty, CoreAst.Term.GlobalRef("Partial", testSpan)))
    )
    intercept[InvalidConstructorResult] {
      TypeChecker.checkProgram(CoreAst.Program(Vector(incomplete), None))
    }
  }

  test("field universes are bounded by the declared inductive universe") {
    val highField = CoreAst.Binder(
      CoreAst.LocalRef(203, "f"),
      CoreAst.Term.Pi(
        Vector(CoreAst.Binder(CoreAst.LocalRef(204, "A"), CoreAst.Term.GlobalRef("Type", testSpan), testSpan)),
        CoreAst.Term.GlobalRef("Type", testSpan),
        testSpan
      ),
      testSpan
    )
    val bad =
      coreDecl("Small", ctors = Vector(ctor("Small", Vector(highField), CoreAst.Term.GlobalRef("Small", testSpan))))
    intercept[InductiveUniverseTooSmall] {
      TypeChecker.checkProgram(CoreAst.Program(Vector(bad), None))
    }
  }

  test("direct positive recursion is accepted") {
    val n = CoreAst.Binder(CoreAst.LocalRef(205, "n"), CoreAst.Term.GlobalRef("Nat", testSpan), testSpan)
    val decl = coreDecl(
      "Nat",
      ctors = Vector(
        ctor("Nat", Vector.empty, CoreAst.Term.GlobalRef("Nat", testSpan)),
        ctor("Nat", Vector(n), CoreAst.Term.GlobalRef("Nat", testSpan), "succ")
      )
    )
    val (env, _) = TypeChecker.checkProgram(CoreAst.Program(Vector(decl), None))
    assert(env.globals.contains("Nat.mk"))
  }

  test("negative recursion in a Pi domain is rejected") {
    val highResult = CoreAst.Term.App(
      CoreAst.Term.GlobalRef("Sort", testSpan),
      Vector(
        CoreAst.Term.App(
          CoreAst.Term.GlobalRef("Level.succ", testSpan),
          Vector(CoreAst.Term.GlobalRef("Level.one", testSpan)),
          testSpan
        )
      ),
      testSpan
    )
    val f = CoreAst.Binder(
      CoreAst.LocalRef(206, "f"),
      CoreAst.Term.Pi(
        Vector(CoreAst.Binder(CoreAst.LocalRef(207, "x"), CoreAst.Term.GlobalRef("Bad", testSpan), testSpan)),
        CoreAst.Term.GlobalRef("Type", testSpan),
        testSpan
      ),
      testSpan
    )
    intercept[NonStrictlyPositive] {
      TypeChecker.checkProgram(
        CoreAst.Program(
          Vector(
            coreDecl(
              "Bad",
              result = highResult,
              ctors = Vector(ctor("Bad", Vector(f), CoreAst.Term.GlobalRef("Bad", testSpan)))
            )
          ),
          None
        )
      )
    }
  }

  test("positive recursion in a Pi codomain is accepted at a high universe") {
    val field = CoreAst.Binder(
      CoreAst.LocalRef(208, "f"),
      CoreAst.Term.Pi(
        Vector(CoreAst.Binder(CoreAst.LocalRef(209, "A"), CoreAst.Term.GlobalRef("Type", testSpan), testSpan)),
        CoreAst.Term.GlobalRef("High", testSpan),
        testSpan
      ),
      testSpan
    )
    val high = coreDecl(
      "High",
      result = CoreAst.Term.App(
        CoreAst.Term.GlobalRef("Sort", testSpan),
        Vector(
          CoreAst.Term.App(
            CoreAst.Term.GlobalRef("Level.succ", testSpan),
            Vector(CoreAst.Term.GlobalRef("Level.one", testSpan)),
            testSpan
          )
        ),
        testSpan
      ),
      ctors = Vector(ctor("High", Vector(field), CoreAst.Term.GlobalRef("High", testSpan)))
    )
    val (env, _) = TypeChecker.checkProgram(CoreAst.Program(Vector(high), None))
    assert(env.globals.contains("High.mk"))
  }

  test("nested positive recursion through an established positive parameter is accepted") {
    val boxA = CoreAst.Binder(CoreAst.LocalRef(230, "A"), CoreAst.Term.GlobalRef("Type", testSpan), testSpan)
    val boxResult = CoreAst.Term.App(
      CoreAst.Term.GlobalRef("Box", testSpan),
      Vector(CoreAst.Term.LocalRef(boxA.localRef, testSpan)),
      testSpan
    )
    val boxDecl = coreDecl(
      "Box",
      params = Vector(boxA),
      ctors = Vector(
        ctor(
          "Box",
          Vector(CoreAst.Binder(CoreAst.LocalRef(231, "x"), CoreAst.Term.LocalRef(boxA.localRef, testSpan), testSpan)),
          boxResult
        )
      )
    )
    val treeField = CoreAst.Binder(
      CoreAst.LocalRef(232, "boxedTree"),
      CoreAst.Term
        .App(CoreAst.Term.GlobalRef("Box", testSpan), Vector(CoreAst.Term.GlobalRef("Tree", testSpan)), testSpan),
      testSpan
    )
    val treeDecl = coreDecl(
      "Tree",
      ctors = Vector(ctor("Tree", Vector(treeField), CoreAst.Term.GlobalRef("Tree", testSpan)))
    )
    val (env, _) = TypeChecker.checkProgram(CoreAst.Program(Vector(boxDecl, treeDecl), None))
    val boxValue = env("Box").asInstanceOf[Value.VConst]
    assert(boxValue.constType.asInstanceOf[Value.Inductive].meta.block.positiveParams.contains(0))
  }

  test("nested negative recursion through an established non-positive parameter is rejected") {
    val contraA = CoreAst.Binder(CoreAst.LocalRef(233, "A"), CoreAst.Term.GlobalRef("Type", testSpan), testSpan)
    val contraField = CoreAst.Binder(
      CoreAst.LocalRef(234, "f"),
      CoreAst.Term.Pi(
        Vector(CoreAst.Binder(CoreAst.LocalRef(235, "x"), CoreAst.Term.LocalRef(contraA.localRef, testSpan), testSpan)),
        CoreAst.Term.LocalRef(contraA.localRef, testSpan),
        testSpan
      ),
      testSpan
    )
    val contraResult = CoreAst.Term.App(
      CoreAst.Term.GlobalRef("Contra", testSpan),
      Vector(CoreAst.Term.LocalRef(contraA.localRef, testSpan)),
      testSpan
    )
    val contraDecl = coreDecl(
      "Contra",
      params = Vector(contraA),
      ctors = Vector(ctor("Contra", Vector(contraField), contraResult))
    )
    val (contraEnv, _) = TypeChecker.checkProgram(CoreAst.Program(Vector(contraDecl), None))
    val contraMeta = contraEnv("Contra").asInstanceOf[Value.VConst].constType.asInstanceOf[Value.Inductive].meta
    assert(contraMeta.block.positiveParams.isEmpty)

    val badTreeField = CoreAst.Binder(
      CoreAst.LocalRef(236, "contraTree"),
      CoreAst.Term
        .App(CoreAst.Term.GlobalRef("Contra", testSpan), Vector(CoreAst.Term.GlobalRef("BadTree", testSpan)), testSpan),
      testSpan
    )
    val badTree = coreDecl(
      "BadTree",
      ctors = Vector(ctor("BadTree", Vector(badTreeField), CoreAst.Term.GlobalRef("BadTree", testSpan)))
    )
    intercept[NonStrictlyPositive] {
      TypeChecker.checkProgram(CoreAst.Program(Vector(contraDecl, badTree), None))
    }
  }

  test("recursive occurrences in their own family arguments are rejected") {
    val i = CoreAst.Binder(
      CoreAst.LocalRef(210, "i"),
      CoreAst.Term
        .App(CoreAst.Term.GlobalRef("Sort", testSpan), Vector(CoreAst.Term.GlobalRef("Level.one", testSpan)), testSpan),
      testSpan
    )
    val prop = CoreAst.Term.App(
      CoreAst.Term.GlobalRef("Sort", testSpan),
      Vector(CoreAst.Term.GlobalRef("Level.zero", testSpan)),
      testSpan
    )
    val nestedIndex = CoreAst.Term.App(CoreAst.Term.GlobalRef("Ix", testSpan), Vector(prop), testSpan)
    val nestedResult = CoreAst.Term.App(CoreAst.Term.GlobalRef("Ix", testSpan), Vector(nestedIndex), testSpan)
    val ix = coreDecl("Ix", indices = Vector(i), ctors = Vector(ctor("Ix", Vector.empty, nestedResult)))
    intercept[NonStrictlyPositive] {
      TypeChecker.checkProgram(CoreAst.Program(Vector(ix), None))
    }
  }

  test("true indices do not become positive-parameter capabilities") {
    val a = CoreAst.Binder(CoreAst.LocalRef(211, "A"), CoreAst.Term.GlobalRef("Type", testSpan), testSpan)
    val i = CoreAst.Binder(CoreAst.LocalRef(212, "i"), CoreAst.Term.GlobalRef("Type", testSpan), testSpan)
    val prop = CoreAst.Term.App(
      CoreAst.Term.GlobalRef("Sort", testSpan),
      Vector(CoreAst.Term.GlobalRef("Level.zero", testSpan)),
      testSpan
    )
    val result = CoreAst.Term.App(
      CoreAst.Term.GlobalRef("Indexed", testSpan),
      Vector(CoreAst.Term.LocalRef(a.localRef, testSpan), prop),
      testSpan
    )
    val indexed = coreDecl(
      "Indexed",
      params = Vector(a),
      indices = Vector(i),
      ctors = Vector(ctor("Indexed", Vector.empty, result))
    )
    val (env, _) = TypeChecker.checkProgram(CoreAst.Program(Vector(indexed), None))
    val meta = env("Indexed").asInstanceOf[Value.VConst].constType.asInstanceOf[Value.Inductive].meta
    assertEquals(meta.familyArity, 2)
    assert(meta.block.positiveParams.contains(0))
    assert(!meta.block.positiveParams.contains(1))
  }

  test("higher-kinded source parameters retain positive metadata") {
    val fType = CoreAst.Term.Pi(
      Vector(CoreAst.Binder(CoreAst.LocalRef(213, "A"), CoreAst.Term.GlobalRef("Type", testSpan), testSpan)),
      CoreAst.Term.GlobalRef("Type", testSpan),
      testSpan
    )
    val f = CoreAst.Binder(CoreAst.LocalRef(214, "F"), fType, testSpan)
    val a = CoreAst.Binder(CoreAst.LocalRef(215, "A"), CoreAst.Term.GlobalRef("Type", testSpan), testSpan)
    val fApplied = CoreAst.Term.App(
      CoreAst.Term.LocalRef(f.localRef, testSpan),
      Vector(CoreAst.Term.LocalRef(a.localRef, testSpan)),
      testSpan
    )
    val result = CoreAst.Term.App(
      CoreAst.Term.GlobalRef("HK", testSpan),
      Vector(CoreAst.Term.LocalRef(f.localRef, testSpan), CoreAst.Term.LocalRef(a.localRef, testSpan)),
      testSpan
    )
    val hk = coreDecl(
      "HK",
      params = Vector(f, a),
      ctors = Vector(ctor("HK", Vector(CoreAst.Binder(CoreAst.LocalRef(216, "x"), fApplied, testSpan)), result))
    )
    val (env, _) = TypeChecker.checkProgram(CoreAst.Program(Vector(hk), None))
    val meta = env("HK").asInstanceOf[Value.VConst].constType.asInstanceOf[Value.Inductive].meta
    assert(meta.block.positiveParams.contains(0))
  }

  test("mutual positive sibling recursion publishes one checked descriptor") {
    val left = coreDecl(
      "MutLeft",
      ctors = Vector(
        ctor(
          "MutLeft",
          Vector(CoreAst.Binder(CoreAst.LocalRef(216, "r"), CoreAst.Term.GlobalRef("MutRight", testSpan), testSpan)),
          CoreAst.Term.GlobalRef("MutLeft", testSpan)
        )
      )
    )
    val right = coreDecl(
      "MutRight",
      ctors = Vector(ctor("MutRight", Vector.empty, CoreAst.Term.GlobalRef("MutRight", testSpan)))
    )
    val (env, _) = TypeChecker.checkProgram(
      CoreAst.Program(Vector(CoreAst.Decl.InductiveBlock(Vector(left, right), testSpan)), None)
    )
    val leftMeta = env("MutLeft").asInstanceOf[Value.VConst].constType.asInstanceOf[Value.Inductive].meta
    val rightMeta = env("MutRight").asInstanceOf[Value.VConst].constType.asInstanceOf[Value.Inductive].meta
    assert(leftMeta.block.asInstanceOf[AnyRef] eq rightMeta.block.asInstanceOf[AnyRef])
  }

  test("mutual sibling recursion with a non-uniform common parameter is rejected atomically") {
    val leftA = CoreAst.Binder(CoreAst.LocalRef(240, "A"), CoreAst.Term.GlobalRef("Type", testSpan), testSpan)
    val rightA = CoreAst.Binder(CoreAst.LocalRef(241, "A"), CoreAst.Term.GlobalRef("Type", testSpan), testSpan)
    val nonUniformField = CoreAst.Binder(
      CoreAst.LocalRef(242, "right"),
      CoreAst.Term.App(
        CoreAst.Term.GlobalRef("MutParamRight", testSpan),
        Vector(
          CoreAst.Term.App(
            CoreAst.Term.GlobalRef("Sort", testSpan),
            Vector(CoreAst.Term.GlobalRef("Level.zero", testSpan)),
            testSpan
          )
        ),
        testSpan
      ),
      testSpan
    )
    val leftResult = CoreAst.Term.App(
      CoreAst.Term.GlobalRef("MutParamLeft", testSpan),
      Vector(CoreAst.Term.LocalRef(leftA.localRef, testSpan)),
      testSpan
    )
    val rightResult = CoreAst.Term.App(
      CoreAst.Term.GlobalRef("MutParamRight", testSpan),
      Vector(CoreAst.Term.LocalRef(rightA.localRef, testSpan)),
      testSpan
    )
    val left = coreDecl(
      "MutParamLeft",
      params = Vector(leftA),
      ctors = Vector(ctor("MutParamLeft", Vector(nonUniformField), leftResult))
    )
    val right = coreDecl(
      "MutParamRight",
      params = Vector(rightA),
      ctors = Vector(ctor("MutParamRight", Vector.empty, rightResult))
    )
    val env = Interpreter.builtins
    intercept[NonStrictlyPositive] {
      TypeChecker.checkProgram(
        CoreAst.Program(Vector(CoreAst.Decl.InductiveBlock(Vector(left, right), testSpan)), None),
        env
      )
    }
    assert(!env.globals.contains("MutParamLeft"))
    assert(!env.globals.contains("MutParamRight"))
  }

  test("a mutual recursive family occurrence in a result index is rejected atomically") {
    val index = CoreAst.Binder(CoreAst.LocalRef(243, "i"), CoreAst.Term.GlobalRef("Type", testSpan), testSpan)
    val prop = CoreAst.Term.App(
      CoreAst.Term.GlobalRef("Sort", testSpan),
      Vector(CoreAst.Term.GlobalRef("Level.zero", testSpan)),
      testSpan
    )
    val rightIndex = CoreAst.Term.App(CoreAst.Term.GlobalRef("MutIndexRight", testSpan), Vector(prop), testSpan)
    val leftResult = CoreAst.Term.App(CoreAst.Term.GlobalRef("MutIndexLeft", testSpan), Vector(rightIndex), testSpan)
    val rightResult = CoreAst.Term.App(CoreAst.Term.GlobalRef("MutIndexRight", testSpan), Vector(prop), testSpan)
    val left = coreDecl(
      "MutIndexLeft",
      indices = Vector(index),
      ctors = Vector(ctor("MutIndexLeft", Vector.empty, leftResult))
    )
    val right = coreDecl(
      "MutIndexRight",
      indices = Vector(CoreAst.Binder(CoreAst.LocalRef(244, "i"), CoreAst.Term.GlobalRef("Type", testSpan), testSpan)),
      ctors = Vector(ctor("MutIndexRight", Vector.empty, rightResult))
    )
    val env = Interpreter.builtins
    intercept[NonStrictlyPositive] {
      TypeChecker.checkProgram(
        CoreAst.Program(Vector(CoreAst.Decl.InductiveBlock(Vector(left, right), testSpan)), None),
        env
      )
    }
    assert(!env.globals.contains("MutIndexLeft"))
    assert(!env.globals.contains("MutIndexRight"))
  }

  test("mutual sibling constructors remain matchable after shared metadata publication") {
    val left = coreDecl(
      "MatchLeft",
      ctors = Vector(ctor("MatchLeft", Vector.empty, CoreAst.Term.GlobalRef("MatchLeft", testSpan)))
    )
    val right = coreDecl(
      "MatchRight",
      ctors = Vector(ctor("MatchRight", Vector.empty, CoreAst.Term.GlobalRef("MatchRight", testSpan)))
    )
    val leftWitness = CoreAst.Decl.AxiomDecl("leftWitness", CoreAst.Term.GlobalRef("MatchLeft", testSpan), testSpan)
    val rightWitness = CoreAst.Decl.AxiomDecl("rightWitness", CoreAst.Term.GlobalRef("MatchRight", testSpan), testSpan)
    val leftMatch = CoreAst.Term.Match(
      CoreAst.Term.GlobalRef("leftWitness", testSpan),
      None,
      Vector(
        CoreAst.Case(
          "MatchLeft.mk",
          isFullyQualified = true,
          Vector.empty,
          CoreAst.Term.GlobalRef("MatchLeft.mk", testSpan),
          testSpan
        )
      ),
      testSpan
    )
    val rightMatch = CoreAst.Term.Match(
      CoreAst.Term.GlobalRef("rightWitness", testSpan),
      None,
      Vector(
        CoreAst.Case(
          "MatchRight.mk",
          isFullyQualified = true,
          Vector.empty,
          CoreAst.Term.GlobalRef("MatchRight.mk", testSpan),
          testSpan
        )
      ),
      testSpan
    )
    val leftId = CoreAst.Decl.ConstDecl(
      isOpaque = false,
      "leftId",
      CoreAst.Term.GlobalRef("MatchLeft", testSpan),
      CoreAst.ConstBody.TermBody(leftMatch),
      testSpan
    )
    val rightId = CoreAst.Decl.ConstDecl(
      isOpaque = false,
      "rightId",
      CoreAst.Term.GlobalRef("MatchRight", testSpan),
      CoreAst.ConstBody.TermBody(rightMatch),
      testSpan
    )
    val (env, _) = TypeChecker.checkProgram(
      CoreAst.Program(
        Vector(CoreAst.Decl.InductiveBlock(Vector(left, right), testSpan), leftWitness, rightWitness, leftId, rightId),
        None
      )
    )
    val leftMeta = env("MatchLeft").asInstanceOf[Value.VConst].constType.asInstanceOf[Value.Inductive].meta
    val rightMeta = env("MatchRight").asInstanceOf[Value.VConst].constType.asInstanceOf[Value.Inductive].meta
    assert(leftMeta.block.asInstanceOf[AnyRef] eq rightMeta.block.asInstanceOf[AnyRef])
    assert(env.globals.contains("leftId"))
    assert(env.globals.contains("rightId"))
  }

  test("mutual negative sibling recursion fails atomically") {
    val highResult = CoreAst.Term.App(
      CoreAst.Term.GlobalRef("Sort", testSpan),
      Vector(
        CoreAst.Term.App(
          CoreAst.Term.GlobalRef("Level.succ", testSpan),
          Vector(CoreAst.Term.GlobalRef("Level.one", testSpan)),
          testSpan
        )
      ),
      testSpan
    )
    val badField = CoreAst.Binder(
      CoreAst.LocalRef(217, "f"),
      CoreAst.Term.Pi(
        Vector(CoreAst.Binder(CoreAst.LocalRef(218, "x"), CoreAst.Term.GlobalRef("MutBadRight", testSpan), testSpan)),
        CoreAst.Term.GlobalRef("Type", testSpan),
        testSpan
      ),
      testSpan
    )
    val left = coreDecl(
      "MutBadLeft",
      result = highResult,
      ctors = Vector(ctor("MutBadLeft", Vector(badField), CoreAst.Term.GlobalRef("MutBadLeft", testSpan)))
    )
    val right = coreDecl(
      "MutBadRight",
      result = highResult,
      ctors = Vector(ctor("MutBadRight", Vector.empty, CoreAst.Term.GlobalRef("MutBadRight", testSpan)))
    )
    val env = Interpreter.builtins
    intercept[NonStrictlyPositive] {
      TypeChecker.checkProgram(
        CoreAst.Program(Vector(CoreAst.Decl.InductiveBlock(Vector(left, right), testSpan)), None),
        env
      )
    }
    assert(!env.globals.contains("MutBadLeft"))
    assert(!env.globals.contains("MutBadRight"))
  }

  test("mutual families with different universes are rejected exactly") {
    val low = coreDecl(
      "Low",
      result = CoreAst.Term.GlobalRef("Type", testSpan),
      ctors = Vector(ctor("Low", Vector.empty, CoreAst.Term.GlobalRef("Low", testSpan)))
    )
    val highResult = CoreAst.Term.App(
      CoreAst.Term.GlobalRef("Sort", testSpan),
      Vector(
        CoreAst.Term.App(
          CoreAst.Term.GlobalRef("Level.succ", testSpan),
          Vector(CoreAst.Term.GlobalRef("Level.one", testSpan)),
          testSpan
        )
      ),
      testSpan
    )
    val high = coreDecl(
      "HighMut",
      result = highResult,
      ctors = Vector(ctor("HighMut", Vector.empty, CoreAst.Term.GlobalRef("HighMut", testSpan)))
    )
    intercept[InvalidInductiveBlock] {
      TypeChecker.checkProgram(CoreAst.Program(Vector(CoreAst.Decl.InductiveBlock(Vector(low, high), testSpan)), None))
    }
  }

  test("mutual block positivity uses the intersection of family capabilities") {
    val a1 = CoreAst.Binder(CoreAst.LocalRef(219, "A"), CoreAst.Term.GlobalRef("Type", testSpan), testSpan)
    val a2 = CoreAst.Binder(CoreAst.LocalRef(220, "A"), CoreAst.Term.GlobalRef("Type", testSpan), testSpan)
    val highFamilyResult = CoreAst.Term.App(
      CoreAst.Term.GlobalRef("Sort", testSpan),
      Vector(
        CoreAst.Term.App(
          CoreAst.Term.GlobalRef("Level.succ", testSpan),
          Vector(CoreAst.Term.GlobalRef("Level.one", testSpan)),
          testSpan
        )
      ),
      testSpan
    )
    val contra = CoreAst.Binder(
      CoreAst.LocalRef(221, "f"),
      CoreAst.Term.Pi(
        Vector(CoreAst.Binder(CoreAst.LocalRef(222, "x"), CoreAst.Term.LocalRef(a2.localRef, testSpan), testSpan)),
        CoreAst.Term.GlobalRef("Type", testSpan),
        testSpan
      ),
      testSpan
    )
    def result(name: String, a: CoreAst.Binder) = CoreAst.Term.App(
      CoreAst.Term.GlobalRef(name, testSpan),
      Vector(CoreAst.Term.LocalRef(a.localRef, testSpan)),
      testSpan
    )
    val left = coreDecl(
      "MeetLeft",
      params = Vector(a1),
      result = highFamilyResult,
      ctors = Vector(ctor("MeetLeft", Vector.empty, result("MeetLeft", a1)))
    )
    val right = coreDecl(
      "MeetRight",
      params = Vector(a2),
      result = highFamilyResult,
      ctors = Vector(ctor("MeetRight", Vector(contra), result("MeetRight", a2)))
    )
    val (env, _) = TypeChecker.checkProgram(
      CoreAst.Program(Vector(CoreAst.Decl.InductiveBlock(Vector(left, right), testSpan)), None)
    )
    val meta = env("MeetLeft").asInstanceOf[Value.VConst].constType.asInstanceOf[Value.Inductive].meta
    assert(meta.block.positiveParams.isEmpty)
  }

  test("mutual parameter binder modes must agree") {
    val explicit =
      CoreAst.Binder(CoreAst.LocalRef(223, "A"), CoreAst.Term.GlobalRef("Type", testSpan), testSpan, isImplicit = false)
    val implicitParam = explicit.copy(localRef = CoreAst.LocalRef(224, "B"), isImplicit = true)
    val left = coreDecl(
      "ModeLeft",
      params = Vector(explicit),
      ctors = Vector(
        ctor(
          "ModeLeft",
          Vector.empty,
          CoreAst.Term.App(
            CoreAst.Term.GlobalRef("ModeLeft", testSpan),
            Vector(CoreAst.Term.LocalRef(explicit.localRef, testSpan)),
            testSpan
          )
        )
      )
    )
    val right = coreDecl(
      "ModeRight",
      params = Vector(implicitParam),
      ctors = Vector(
        ctor(
          "ModeRight",
          Vector.empty,
          CoreAst.Term.App(
            CoreAst.Term.GlobalRef("ModeRight", testSpan),
            Vector(CoreAst.Term.LocalRef(implicitParam.localRef, testSpan)),
            testSpan
          )
        )
      )
    )
    intercept[InvalidInductiveBlock] {
      TypeChecker.checkProgram(
        CoreAst.Program(Vector(CoreAst.Decl.InductiveBlock(Vector(left, right), testSpan)), None)
      )
    }
  }
}
