package com.raccoonlang

import com.raccoonlang.Value.{ConstructorHead, Inductive, NeutralThunk, VApp, VConst, VLam, VPi, VSort}

class InterpreterTests extends munit.FunSuite {
  private def program(source: String): CoreAst.Program = LanguageParser.parseProgram(source) match {
    case Success(surface, _, _) => Elaborator.elab(surface)
    case failure                => fail(s"Expected parse success, got $failure")
  }

  private def run(source: String): Value = Interpreter.run(program(source)).getOrElse(fail("Expected a result"))

  test("the first evaluator deliberately models Type as Type") {
    run("Type") match {
      case sort: VSort => assert(sort == Value.TypeValue)
      case other       => fail(s"Expected Type, got $other")
    }
    assertEquals(Value.TypeValue.tpe, Value.TypeValue)
  }

  test("dependent closures retain their captured binder environment") {
    run("(fun (A: Type)(x: A): A => x)(Type, Type)") match {
      case sort: VSort => assert(sort == Value.TypeValue)
      case other       => fail(s"Expected the dependent identity result Type, got $other")
    }
  }

  test("ordinary function declarations publish named lambdas") {
    run("def id (A: Type): Type := A\n\nid") match {
      case VLam(_, Value.ValueId.Const(name), _) => assertEquals(name, "id")
      case other                                 => fail(s"Expected a named lambda, got $other")
    }
  }

  test("surface brace blocks flatten into ordinary declarations") {
    val core = program("{\ndef first : Type := Type\n\ndef second : Type := first\n}\n")
    assertEquals(core.decls.map(_.getClass), Vector(classOf[CoreAst.Decl.ConstDecl], classOf[CoreAst.Decl.ConstDecl]))
  }

  test("nullary inductive constructors are published and usable") {
    run("inductive Bool : Type\n | true : Bool\n | false : Bool\n\nBool.true") match {
      case VApp(head: ConstructorHead, args, _, _) =>
        assertEquals(head.name, "Bool.true")
        assert(args.isEmpty)
        assertEquals(
          Value.ConstructorForm.unapply(run("inductive Bool : Type\n | true : Bool\n\nBool.true")),
          Some("Bool.true" -> Vector.empty)
        )
      case other => fail(s"Expected constructor head, got $other")
    }
  }

  test("parameterized families and constructors compute their applications") {
    val value = run("inductive Box (A: Type) : Type\n | mk (value: A) : Box(A)\n\nBox.mk(Type, Type)")
    value match {
      case VApp(head: ConstructorHead, args, _, _) =>
        assertEquals(head.name, "Box.mk")
        assertEquals(args.length, 1)
      case other => fail(s"Expected applied constructor, got $other")
    }
    Value.VCtor.unapply(value) match {
      case Some((head, fields, _)) =>
        assertEquals(head.name, "Box.mk")
        assertEquals(fields.length, 1)
      case other => fail(s"Expected constructor view, got $other")
    }
  }

  test("indexed family applications include every parameter and index") {
    val core = program("inductive Eq (A: Type) indices (x: A) : Type\n").decls.head
    val env = Interpreter.evalDecl(core, Interpreter.builtins)
    env("Eq") match {
      case VConst(_, Inductive(meta), familyType: VPi) =>
        assertEquals(meta.familyArity, 2)
        val applied = Interpreter.evalApply(env("Eq"), Vector(Value.TypeValue, Value.TypeValue))
        applied match {
          case VApp(_, args, tpe, _) =>
            assertEquals(args.length, 2)
            assert(tpe == Value.TypeValue)
          case other => fail(s"Expected fully applied indexed family, got $other")
        }
        assertEquals(familyType.binders.length, 2)
      case other => fail(s"Expected indexed family, got $other")
    }
  }

  test("explicit mutual inductive CoreAst blocks publish atomically") {
    val span = Span(0, 1)
    val left = CoreAst.Decl.InductiveDecl(
      CoreAst.InductiveHeader("Left", Vector.empty, Vector.empty, CoreAst.Term.GlobalRef("Type", span), span),
      Vector(
        CoreAst.ConstructorDecl(
          "Left.left",
          "left",
          Vector(CoreAst.Binder(CoreAst.LocalRef(1, "right"), CoreAst.Term.GlobalRef("Right", span), span)),
          CoreAst.Term.GlobalRef("Left", span),
          span
        )
      ),
      span
    )
    val right = CoreAst.Decl.InductiveDecl(
      CoreAst.InductiveHeader("Right", Vector.empty, Vector.empty, CoreAst.Term.GlobalRef("Type", span), span),
      Vector(
        CoreAst.ConstructorDecl(
          "Right.right",
          "right",
          Vector(CoreAst.Binder(CoreAst.LocalRef(2, "left"), CoreAst.Term.GlobalRef("Left", span), span)),
          CoreAst.Term.GlobalRef("Right", span),
          span
        )
      ),
      span
    )
    val env = Interpreter.evalDecl(CoreAst.Decl.InductiveBlock(Vector(left, right), span), Interpreter.builtins)
    assert(env.globals.keySet.contains("Left"))
    assert(env.globals.keySet.contains("Right"))
    assert(env.globals.keySet.contains("Left.left"))
    assert(env.globals.keySet.contains("Right.right"))
    val leftType = env("Left.left").tpe
    val rightType = env("Right.right").tpe
    assert(leftType.isInstanceOf[VPi])
    assert(rightType.isInstanceOf[VPi])
  }

  test("sibling constructor telescopes receive distinct local identities") {
    program("inductive Sum : Type\n | left (a: Type) : Sum\n | right (b: Type) : Sum\n") match {
      case CoreAst.Program(Vector(CoreAst.Decl.InductiveDecl(_, ctors, _)), _) =>
        assertNotEquals(ctors(0).binders.head.localRef.id, ctors(1).binders.head.localRef.id)
      case other => fail(s"Expected inductive declaration, got $other")
    }
  }

  test("runtime matching selects a constructor branch") {
    run(
      "inductive Bool : Type\n | true : Bool\n | false : Bool\n\nmatch Bool.true with\n | Bool.true => Type\n | Bool.false => Bool.true\n"
    ) match {
      case sort: VSort => assert(sort == Value.TypeValue)
      case other       => fail(s"Expected Type branch, got $other")
    }
  }

  test("recursive definitions execute unchecked decreases annotations") {
    val source =
      "inductive Nat : Type\n | zero : Nat\n | succ (n: Nat) : Nat\n\n" +
        "def loop (n: Nat): Nat decreases structural(n) := match n with\n" +
        " | Nat.zero => Nat.zero\n" +
        " | Nat.succ k => loop(k)\n\n" +
        "loop(Nat.succ(Nat.zero))"
    program(source).decls(1) match {
      case CoreAst.Decl.ConstDecl(_, "loop", _, CoreAst.ConstBody.TermBody(lam: CoreAst.Term.Lam), _) =>
        val self = lam.recursion.get.selfRef
        assert(CoreAst.mentionedRefs(lam.body).contains(self))
      case other => fail(s"Expected named recursive lambda, got $other")
    }
    run(source) match {
      case VApp(head: ConstructorHead, args, _, _) =>
        assertEquals(head.name, "Nat.zero")
        assert(args.isEmpty)
      case other => fail(s"Expected recursive result, got $other")
    }
  }

  test("recursive measure and body allocation use disjoint local identities") {
    val core = program(
      "def loop (n: Type): Type decreases measure (fun (m: Type): Type => m) :=\n" +
        "(fun (b: Type): Type => b)(n)"
    )
    core.decls(0) match {
      case CoreAst.Decl.ConstDecl(_, _, _, CoreAst.ConstBody.TermBody(lam: CoreAst.Term.Lam), _) =>
        val measured = lam.recursion.get.decreases match {
          case CoreAst.DecreaseSpec.Measure(term, _) => CoreAst.mentionedRefs(term).map(_.id)
          case other                                 => fail(s"Expected a measure, got $other")
        }
        val body = CoreAst.mentionedRefs(lam.body).map(_.id)
        assert(measured.intersect(body).isEmpty)
      case other => fail(s"Expected recursive named lambda, got $other")
    }
  }

  test("explicit recursive CoreAst groups publish a knot with local peers") {
    val span = Span(0, 1)
    val firstArg = CoreAst.LocalRef(10, "n")
    val secondArg = CoreAst.LocalRef(11, "n")
    val firstPeer = CoreAst.LocalRef(20, "first")
    val secondPeer = CoreAst.LocalRef(21, "second")
    def functionType(arg: CoreAst.LocalRef): CoreAst.Term.Pi =
      CoreAst.Term.Pi(
        Vector(CoreAst.Binder(arg, CoreAst.Term.GlobalRef("Type", span), span)),
        CoreAst.Term.GlobalRef("Type", span),
        span
      )
    val decrease = CoreAst.DecreaseSpec.Lexicographic(Vector(firstArg), span)
    val first = CoreAst.RecursiveDef(
      "first",
      firstPeer,
      functionType(firstArg),
      CoreAst.Term.LocalRef(secondPeer, span),
      decrease,
      span
    )
    val second = CoreAst.RecursiveDef(
      "second",
      secondPeer,
      functionType(secondArg),
      CoreAst.Term.LocalRef(firstPeer, span),
      decrease,
      span
    )
    val env = Interpreter.evalDecl(CoreAst.Decl.RecursiveDefBlock(Vector(first, second), span), Interpreter.builtins)
    Interpreter.evalApply(env("first"), Vector(Value.TypeValue)) match {
      case _: VLam => ()
      case other   => fail(s"Expected the peer lambda from the recursive knot, got $other")
    }
  }

  test("a neutral match retains its motive type and can be applied") {
    val source = "axiom choice (A: Type): Type\n\nmatch choice returning (A: Type) -> Type with\n"
    val core = program(source)
    val value = Interpreter.run(core).get
    value match {
      case stuck: NeutralThunk =>
        stuck.tpe match {
          case pi: VPi => assertEquals(pi.binders.length, 1)
          case other   => fail(s"Expected evaluated function motive, got $other")
        }
        assert(stuck.env.globals.contains("Type"))
        val applied = Interpreter.evalApply(stuck, Vector(Value.TypeValue))
        applied match {
          case VApp(head, args, _, _) =>
            assertEquals(head, stuck)
            assertEquals(args.length, 1)
          case other => fail(s"Expected applied neutral match, got $other")
        }
      case other => fail(s"Expected retained neutral match, got $other")
    }
  }

  test("each function application consumes one complete Pi binder group") {
    intercept[ArityMismatch] {
      run("axiom f (A: Type)(B: Type): Type\n\nf(Type)")
    }
  }

  test("an empty application cannot bypass Pi-group arity") {
    val core = program("axiom f (A: Type): Type\n")
    val env = Interpreter.evalDecl(core.decls.head, Interpreter.builtins)
    intercept[ArityMismatch] {
      Interpreter.evalApply(env("f"), Vector.empty)
    }
  }

  test("local environment insertion exposes identity collisions") {
    val ref = CoreAst.LocalRef(17, "x")
    val env = Env.empty.putLocal(ref, Value.TypeValue)
    intercept[AlreadyDefined] {
      env.putLocal(ref, Value.TypeValue)
    }
  }
}
