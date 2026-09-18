package com.raccoonlang

import com.raccoonlang.CoreAst.{Term => CTerm}

class ResidualizationTests extends munit.FunSuite {
  private def checkedBody(source: String): TypeChecker.CheckedTerm = {
    val program = TestSupport.core(source)
    val env = program.decls.foldLeft(Interpreter.builtins) { case (current, decl) =>
      Interpreter.evalDecl(decl, current)
    }
    TypeChecker.checkTerm(program.body.getOrElse(fail("program has no body")), env)
  }

  private def checkedLastDeclBody(source: String): CTerm = {
    val program = TestSupport.core(source)
    val last = program.decls.lastOption.getOrElse(fail("program has no declarations"))
    val env = program.decls.dropRight(1).foldLeft(Interpreter.builtins) { case (current, decl) =>
      Interpreter.evalDecl(decl, current)
    }
    last match {
      case CoreAst.Decl.ConstDecl(_, _, ty, CoreAst.ConstBody.TermBody(body), _) =>
        TypeChecker.checkTerm(body, TypeChecker.checkTerm(ty, env).value, env).residual
      case other => fail(s"expected a term definition, got $other")
    }
  }

  private def checkedLastDeclType(source: String): CTerm = {
    val program = TestSupport.core(source)
    val last = program.decls.lastOption.getOrElse(fail("program has no declarations"))
    val env = program.decls.dropRight(1).foldLeft(Interpreter.builtins) { case (current, decl) =>
      Interpreter.evalDecl(decl, current)
    }
    val ty = last match {
      case CoreAst.Decl.AxiomDecl(_, declared, _)       => declared
      case CoreAst.Decl.ConstDecl(_, _, declared, _, _) => declared
      case other                                        => fail(s"expected a typed declaration, got $other")
    }
    TypeChecker.checkTerm(ty, env).residual
  }

  private def containsGlobal(term: CTerm, name: String): Boolean = term match {
    case CTerm.GlobalRef(found, _) => found == name
    case other                     => CoreAst.children(other).exists(containsGlobal(_, name))
  }

  private def resultTerm(term: CTerm): CTerm = term match {
    case CTerm.Body(_, result, _) => resultTerm(result)
    case other                    => other
  }

  private val naturals =
    """
      |inductive Nat : Type
      | | zero : Nat
      | | succ (_: Nat) : Nat
      |""".stripMargin

  test("checked transparent applications remain explicit in the residual") {
    val checked = checkedBody(
      naturals +
        """
          |def id (n: Nat): Nat := n
          |{
          |  id(Nat.zero)
          |}
          |""".stripMargin
    )
    assert(containsGlobal(checked.residual, "id"))
    assert(containsGlobal(checked.residual, "Nat.zero"))
  }

  test("checked selectors residualize as applications with the local let preserved") {
    val checked = checkedBody(
      naturals +
        """
          |struct Pair (A: Type)(B: Type) : Type
          | | mk (fst: A)(snd: B) : Pair(A, B)
          |{
          |  let p := Pair.mk(Nat.zero, Nat.succ(Nat.zero))
          |  p.fst
          |}
          |""".stripMargin
    )
    checked.residual match {
      case CTerm.Body(Vector(let), CTerm.App(CTerm.GlobalRef("Pair.fst", _), Vector(CTerm.LocalRef(ref, _)), _), _) =>
        assertEquals(ref, let.localRef)
      case other => fail(s"expected selector application over the checked let, got $other")
    }
  }

  test("checked lambda bodies retain their checked application syntax") {
    val checked = checkedBody(
      naturals +
        """
          |def id (n: Nat): Nat := n
          |{
          |  fun (n: Nat): Nat => id(Nat.zero)
          |}
          |""".stripMargin
    )
    resultTerm(checked.residual) match {
      case CTerm.Lam(_, body, _, _, _, _) =>
        assert(containsGlobal(body, "id"))
        assert(containsGlobal(body, "Nat.zero"))
      case other => fail(s"expected checked lambda residual, got $other")
    }
  }

  test("motive-less matches inherit declared return syntax") {
    val program = TestSupport.core(
      naturals +
        """
          |inductive Bool : Type
          | | true : Bool
          | | false : Bool
          |
          |opaque def opaqueBool (b: Bool): Bool := b
          |
          |def pick (b: Bool): Nat := match opaqueBool(b) with
          |  | Bool.true => Nat.zero
          |  | Bool.false => Nat.zero
          |""".stripMargin
    )
    val env = program.decls.dropRight(1).foldLeft(Interpreter.builtins) { case (current, decl) =>
      Interpreter.evalDecl(decl, current)
    }
    program.decls.last match {
      case CoreAst.Decl.ConstDecl(_, _, ty, CoreAst.ConstBody.TermBody(body), _) =>
        TypeChecker.checkTerm(body, TypeChecker.checkTerm(ty, env).value, env).residual match {
          case CTerm.Lam(_, CTerm.Match(_, Some(CTerm.GlobalRef("Nat", _)), _, _), _, _, _, _) =>
          case CTerm.Match(_, Some(CTerm.GlobalRef("Nat", _)), _, _)                           =>
          case CTerm.Body(_, CTerm.Match(_, Some(CTerm.GlobalRef("Nat", _)), _, _), _)         =>
          case other => fail(s"expected a checked lambda with inherited Nat motive, got $other")
        }
      case other => fail(s"expected a term definition, got $other")
    }
  }

  test("stuck transparent applications retain both callee and argument syntax") {
    val residual = checkedBody(
      naturals +
        """
          |inductive Bool : Type
          | | true : Bool
          | | false : Bool
          |
          |opaque def opaqueBool (b: Bool): Bool := b
          |def choose (b: Bool): Nat := match b returning Nat with
          | | Bool.true => Nat.zero
          | | Bool.false => Nat.succ(Nat.zero)
          |
          |{ choose(opaqueBool(Bool.true)) }
          |""".stripMargin
    ).residual
    assert(containsGlobal(residual, "choose"))
    assert(containsGlobal(residual, "opaqueBool"))
  }

  test("explicit generated selectors remain ordinary residual applications") {
    val residual = checkedBody(
      naturals +
        """
          |struct Pair (A: Type)(B: Type) : Type
          | | mk (fst: A)(snd: B) : Pair(A, B)
          |{
          | let p := Pair.mk(Nat.zero, Nat.succ(Nat.zero))
          | Pair.fst(p)
          |}
          |""".stripMargin
    ).residual
    residual match {
      case CTerm.Body(Vector(let), CTerm.App(CTerm.GlobalRef("Pair.fst", _), Vector(CTerm.LocalRef(ref, _)), _), _) =>
        assertEquals(ref, let.localRef)
      case other => fail(s"expected an explicit selector application, got $other")
    }
  }

  test("stuck match branches retain checked application syntax") {
    val residual = checkedLastDeclBody(
      naturals +
        """
          |inductive Bool : Type
          | | true : Bool
          | | false : Bool
          |
          |def id (n: Nat): Nat := n
          |opaque def opaqueBool (b: Bool): Bool := b
          |def pick (b: Bool): Nat := match opaqueBool(b) returning Nat with
          | | Bool.true => id(Nat.zero)
          | | Bool.false => id(Nat.zero)
          |""".stripMargin
    )
    residual match {
      case CTerm.Lam(_, CTerm.Match(_, _, cases, _), _, _, _, _) =>
        cases.foreach(c => assert(containsGlobal(c.body, "id")))
      case CTerm.Match(_, _, cases, _) => cases.foreach(c => assert(containsGlobal(c.body, "id")))
      case other                       => fail(s"expected a checked match residual, got $other")
    }
  }

  test("stuck matches retain the checked scrutinee syntax") {
    val residual = checkedLastDeclBody(
      naturals +
        """
          |inductive Bool : Type
          | | true : Bool
          | | false : Bool
          |
          |def idBool (b: Bool): Bool := b
          |opaque def opaqueBool (b: Bool): Bool := b
          |def pick (b: Bool): Nat := match idBool(opaqueBool(b)) returning Nat with
          | | Bool.true => Nat.zero
          | | Bool.false => Nat.zero
          |""".stripMargin
    )
    def inspect(term: CTerm): Unit = term match {
      case CTerm.Match(scrut, _, _, _) =>
        assert(containsGlobal(scrut, "idBool")); assert(containsGlobal(scrut, "opaqueBool"))
      case CTerm.Body(_, nested, _)       => inspect(nested)
      case CTerm.Lam(_, body, _, _, _, _) => inspect(body)
      case other                          => fail(s"expected a match residual, got $other")
    }
    inspect(residual)
  }

  test("Pi binders preserve reducible type-head syntax") {
    checkedBody(
      naturals +
        """
          |def TyId (A: Type): Type := A
          |{ (_: TyId(Nat)) -> Nat }
          |""".stripMargin
    ).residual match {
      case CTerm.Body(_, pi: CTerm.Pi, _) => assertEquals(pi.binders.head.ty.toString, "TyId(Nat)")
      case pi: CTerm.Pi                   => assertEquals(pi.binders.head.ty.toString, "TyId(Nat)")
      case other                          => fail(s"expected residual Pi, got $other")
    }
  }

  test("forced implicit Pi binders retain their projection specifications") {
    checkedLastDeclType("axiom f : {A: Type} -> (x: A) -> A") match {
      case pi: CTerm.Pi =>
        assert(pi.binders.head.isImplicit)
        assert(pi.binders.head.projection.nonEmpty)
        assert(!pi.binders(1).isImplicit)
      case other => fail(s"expected residual Pi, got $other")
    }
  }

  test("implicit dependent binders retain their local references") {
    checkedLastDeclType(
      "axiom f : {A: Type} -> (x: A) -> A"
    ) match {
      case pi: CTerm.Pi =>
        assertEquals(pi.binders.length, 2)
        val a = pi.binders.head.localRef
        assert(pi.binders(1).ty == CTerm.LocalRef(a, pi.binders(1).ty.span))
        assert(pi.out == CTerm.LocalRef(a, pi.out.span))
      case other => fail(s"expected residual Pi, got $other")
    }
  }

  test("explicit type binders retain their checked syntax") {
    checkedLastDeclType("axiom f : (A: Type) -> A") match {
      case pi: CTerm.Pi =>
        assert(!pi.binders.head.isImplicit)
        assert(pi.out == CTerm.LocalRef(pi.binders.head.localRef, pi.out.span))
      case other => fail(s"expected residual Pi, got $other")
    }
  }

  test("implicit level binders retain their checked syntax") {
    checkedLastDeclType("axiom f : {u: Level} -> (_: Sort(Level.succ(u))) -> Sort(u)") match {
      case pi: CTerm.Pi =>
        assert(pi.binders.head.isImplicit)
        assert(pi.binders.head.ty == CTerm.GlobalRef("Level", pi.binders.head.ty.span))
        assert(containsGlobal(pi.out, "Sort"))
      case other => fail(s"expected residual Pi, got $other")
    }
  }

  test("checked residual trees contain syntax nodes only") {
    val residual = checkedLastDeclBody(
      naturals +
        """
          |inductive Bool : Type
          | | true : Bool
          | | false : Bool
          |
          |opaque def opaqueBool (b: Bool): Bool := b
          |
          |def pick (b: Bool): Nat := match opaqueBool(b) returning Nat with
          | | Bool.true => Nat.zero
          | | Bool.false => Nat.zero
          |""".stripMargin
    )
    def walk(term: CTerm): Unit = {
      term match {
        case _: CTerm.GlobalRef | _: CTerm.LocalRef | _: CTerm.NatLit | _: CTerm.StrLit | _: CTerm.Select |
            _: CTerm.App | _: CTerm.Pi | _: CTerm.Body | _: CTerm.Lam | _: CTerm.Match =>
        case other => fail(s"residual contains non-syntax node: $other")
      }
      CoreAst.children(term).foreach(walk)
    }
    walk(residual)
  }

  test("checked recursive residuals publish once with implicit self reconstruction") {
    val source =
      naturals +
        """
          |def loop {A: Type}(n: Nat)(x: A): Nat decreases structural(n) := {
          |  match n returning Nat with
          |  | Nat.zero => Nat.zero
          |  | Nat.succ k => Nat.succ(loop(k, x))
          |}
          |{ loop(Nat.succ(Nat.zero), Nat.zero) }
          |""".stripMargin
    val (env, checked) = TestSupport.check(source)
    val loop = env("loop").asInstanceOf[Value.VLam]
    loop.body match {
      case Value.LamBody.Core(term, _) =>
        def isRecursiveFn(t: CTerm): Boolean = t match {
          case CTerm.GlobalRef("loop", _)                   => true
          case CTerm.LocalRef(ref, _) if ref.name == "loop" => true
          case _                                            => false
        }
        def recursiveCall(t: CTerm): Option[CTerm.App] = t match {
          case app: CTerm.App if isRecursiveFn(app.fn) => Some(app)
          case other => CoreAst.children(other).iterator.flatMap(recursiveCall).toSeq.headOption
        }
        val call = recursiveCall(term).getOrElse(fail(s"checked recursive body lost its self call: $term"))
        assertEquals(call.args.length, 2)
      case other => fail(s"expected checked recursive core closure, got $other")
    }
    assert(checked.nonEmpty)
    assertEquals(PrettyPrinter.print(TestSupport.eval(source)), "1")
  }
}
