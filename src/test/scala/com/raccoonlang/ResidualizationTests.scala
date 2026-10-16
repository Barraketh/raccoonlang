package com.raccoonlang

import com.raccoonlang.{CoreAst => CA}

class ResidualizationTests extends munit.FunSuite {
  case class Checked(value: Value, term: CA.Term)

  private def checkBody(src: String): Checked =
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        val env = core.decls.foldLeft(Prelude.test.checkedEnv) { case (curEnv, decl) =>
          Interpreter.evalDecl(decl, curEnv)
        }
        val body = core.body.getOrElse(fail("Program has no body"))
        val checked = TypeChecker.checkTerm(body, env)
        Checked(checked.value, checked.residual)

      case err: Failure => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }

  private def resultTerm(term: CA.Term): CA.Term =
    term match {
      case CA.Term.Body(Vector(), res, _) => res
      case other                          => other
    }

  private def checkLastDeclBody(src: String): CA.Term =
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        val last = core.decls.lastOption.getOrElse(fail("Program has no declarations"))
        val env = core.decls.dropRight(1).foldLeft(Prelude.test.checkedEnv) { case (curEnv, decl) =>
          Interpreter.evalDecl(decl, curEnv)
        }
        last match {
          case CoreAst.Decl.ConstDecl(_, ty, CoreAst.ConstBody.TermBody(term), _) =>
            TypeChecker.checkTerm(term, TypeChecker.checkDeclType(ty, env).value, env).residual
          case other => fail(s"Expected a term definition, got $other")
        }
      case err: Failure => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }

  private def checkLastDeclType(src: String): CA.Term =
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        val last = core.decls.lastOption.getOrElse(fail("Program has no declarations"))
        val env = core.decls.dropRight(1).foldLeft(Prelude.test.checkedEnv) { case (curEnv, decl) =>
          Interpreter.evalDecl(decl, curEnv)
        }
        val ty = last match {
          case CoreAst.Decl.ConstDecl(_, ty, _, _) => ty
          case other                               => fail(s"Expected a definition, got $other")
        }
        TypeChecker.checkDeclType(ty, env).residual

      case err: Failure => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }

  private def containsGlobal(term: CA.Term, name: String): Boolean =
    term match {
      case CA.Term.GlobalRef(n, _) => n == name
      case other                   => CA.children(other).exists(containsGlobal(_, name))
    }

  private val natDecls =
    """
      |inductive Peano : Type
      | | zero : Peano
      | | succ (_: Peano) : Peano
      |""".stripMargin

  test("checked residual preserves transparent applications literally") {
    val p =
      natDecls +
        """
          |inductive Bool : Type
          | | true : Bool
          | | false : Bool
          |
          |def expensive (n: Peano): Peano := n
          |
          |def choose (b: Bool)(x: Peano): Peano := {
          |  match b returning Peano with
          |  | Bool.true => x
          |  | Bool.false => Peano.zero
          |}
          |
          |{
          |  choose(Bool.false, expensive(Peano.zero))
          |}
          |""".stripMargin

    val checked = checkBody(p)
    val res = resultTerm(checked.term)
    assert(containsGlobal(res, "choose"))
    assert(containsGlobal(res, "expensive"))
  }

  test("checked residual preserves stuck transparent applications literally") {
    val p =
      natDecls +
        """
          |inductive Bool : Type
          | | true : Bool
          | | false : Bool
          |
          |axiom neutralBool (b: Bool): Bool
          |
          |def choose (b: Bool): Peano := {
          |  match b returning Peano with
          |  | Bool.true => Peano.zero
          |  | Bool.false => Peano.succ(Peano.zero)
          |}
          |
          |{
          |  choose(neutralBool(Bool.true))
          |}
          |""".stripMargin

    val res = resultTerm(checkBody(p).term)
    assert(containsGlobal(res, "choose"))
    assert(containsGlobal(res, "neutralBool"))
  }

  test("checked residual elaborates field syntax to a selector application") {
    val p =
      natDecls +
        """
          |struct Pair (A: Type)(B: Type) : Type
          | | mk (fst: A)(snd: B) : Pair(A, B)
          |
          |{
          |  let p := Pair.mk(Peano.zero, Peano.succ(Peano.zero))
          |  p.fst
          |}
          |""".stripMargin

    checkBody(p).term match {
      case CA.Term.Body(
            lets,
            CA.Term.App(CA.Term.GlobalRef("Pair.fst", _), Vector(CA.Term.LocalRef(ref, _)), _),
            _
          ) =>
        assertEquals(lets.length, 1)
        assertEquals(ref, lets.head.localRef)
        assert(containsGlobal(lets.head.value, "Pair.mk"))
      case other => fail(s"Expected a Pair.fst application over the local pair, got $other")
    }
  }

  test("an explicit generated selector remains an ordinary function call") {
    val p =
      natDecls +
        """
          |struct Pair (A: Type)(B: Type) : Type
          | | mk (fst: A)(snd: B) : Pair(A, B)
          |
          |{
          |  let p := Pair.mk(Peano.zero, Peano.succ(Peano.zero))
          |  Pair.fst(p)
          |}
          |""".stripMargin

    checkBody(p).term match {
      case CA.Term.Body(
            Vector(let),
            CA.Term.App(CA.Term.GlobalRef("Pair.fst", _), Vector(CA.Term.LocalRef(ref, _)), _),
            _
          ) =>
        assertEquals(ref, let.localRef)
      case other => fail(s"Expected an explicit selector call, got $other")
    }
  }

  test("lambda bodies preserve checked application syntax") {
    val p =
      natDecls +
        """
          |def id (n: Peano): Peano := n
          |
          |{
          |  fun (n: Peano): Peano => id(Peano.zero)
          |}
          |""".stripMargin

    resultTerm(checkBody(p).term) match {
      case CA.Term.Lam(_, body, _, _, _, _, _) =>
        assert(containsGlobal(body, "id"))
        assert(containsGlobal(body, "Peano.zero"))
      case other => fail(s"Expected literal lambda body, got $other")
    }
  }

  test("stuck match branch bodies preserve checked application syntax") {
    val p =
      natDecls +
        """
          |inductive Bool : Type
          | | true : Bool
          | | false : Bool
          |
          |def id (n: Peano): Peano := n
          |axiom neutralBool (b: Bool): Bool
          |
          |{
          |  match neutralBool(Bool.true) returning Peano with
          |  | Bool.true => id(Peano.zero)
          |  | Bool.false => id(Peano.zero)
          |}
          |""".stripMargin

    resultTerm(checkBody(p).term) match {
      case CA.Term.Match(_, _, cases, _, _) =>
        assertEquals(cases.map(_.ctorName).toSet, Set("Bool.true", "Bool.false"))
        cases.foreach(c => assert(containsGlobal(c.body, "id")))
      case other => fail(s"Expected stuck match with literal branches, got $other")
    }
  }

  test("stuck match preserves checked scrutinee syntax") {
    val p =
      natDecls +
        """
          |inductive Bool : Type
          | | true : Bool
          | | false : Bool
          |
          |def idBool (b: Bool): Bool := b
          |axiom neutralBool (b: Bool): Bool
          |
          |{
          |  match idBool(neutralBool(Bool.true)) returning Peano with
          |  | Bool.true => Peano.zero
          |  | Bool.false => Peano.zero
          |}
          |""".stripMargin

    resultTerm(checkBody(p).term) match {
      case CA.Term.Match(scrut, _, _, _, _) =>
        assert(containsGlobal(scrut, "idBool"))
        assert(containsGlobal(scrut, "neutralBool"))
      case other => fail(s"Expected stuck match residual, got $other")
    }
  }

  test("Pi binder residual preserves reducible plain binder heads") {
    val p =
      natDecls +
        """
          |def TyId (A: Type): Type := A
          |
          |{
          |  (_: TyId(Peano)) -> Peano
          |}
          |""".stripMargin

    resultTerm(checkBody(p).term) match {
      case pi: CA.Term.Pi =>
        assertEquals(pi.binders.head.ty.toString, "TyId(Peano)")
      case other => fail(s"Expected residualized Pi, got $other")
    }
  }

  test("Pi binder residual preserves forced implicit binders with projection specs") {
    val p =
      """
        |def f {A: Type}(x: A): A := x
        |""".stripMargin

    checkLastDeclType(p) match {
      case pi: CA.Term.Pi =>
        assertEquals(pi.binders.length, 2)
        val implicitBinder = pi.binders.head
        assert(implicitBinder.isImplicit, "expected leading binder to stay implicit in the residual")
        assert(implicitBinder.projection.isDefined, "expected forced implicit binder to carry a projection spec")
        implicitBinder.ty match {
          case CA.Term.Sort(CA.Term.FormOp(CA.LevelForm.LevelZero, _, _), _) =>
          case other => fail(s"Expected Type binder annotation, got $other")
        }
        val explicitBinder = pi.binders(1)
        assert(!explicitBinder.isImplicit, "expected forcing binder to stay explicit in the residual")
        explicitBinder.ty match {
          case CA.Term.LocalRef(tyRef, _) => assertEquals(tyRef, implicitBinder.localRef)
          case other                      => fail(s"Expected explicit binder typed by implicit A, got $other")
        }
        pi.out match {
          case CA.Term.LocalRef(outRef, _) => assertEquals(outRef, implicitBinder.localRef)
          case other                       => fail(s"Expected codomain to reuse implicit A, got $other")
        }
      case other => fail(s"Expected residualized Pi, got $other")
    }
  }

  test("Pi binder residual preserves implicit dependent binders") {
    val p =
      natDecls +
        """
          |inductive Vec (A: Type) indices (n: Peano) : Type
          | | nil : Vec(A, Peano.zero)
          | | cons {n: Peano} (tail: Vec(A, n)) (head: A) : Vec(A, Peano.succ(n))
          |
          |def f {n: Peano}(v: Vec(Peano, n)): Vec(Peano, n) := v
          |""".stripMargin

    checkLastDeclType(p) match {
      case pi: CA.Term.Pi =>
        assertEquals(pi.binders.length, 2)
        val nRef = pi.binders.head.localRef
        pi.binders.head.ty match {
          case CA.Term.GlobalRef("Peano", _) =>
          case other                         => fail(s"Expected Peano implicit binder, got $other")
        }
        pi.binders(1).ty match {
          case CA.Term.App(
                CA.Term.GlobalRef("Vec", _),
                Vector(CA.Term.GlobalRef("Peano", _), CA.Term.LocalRef(argRef, _)),
                _
              ) =>
            assertEquals(argRef, nRef)
          case other => fail(s"Expected Vec(Peano, n) binder annotation, got $other")
        }
        pi.out match {
          case CA.Term.App(
                CA.Term.GlobalRef("Vec", _),
                Vector(CA.Term.GlobalRef("Peano", _), CA.Term.LocalRef(outRef, _)),
                _
              ) =>
            assertEquals(outRef, nRef)
          case other => fail(s"Expected Pi codomain to reuse n, got $other")
        }

      case other => fail(s"Expected residualized Pi, got $other")
    }
  }

  test("Pi binder residual preserves explicit type binders") {
    val p =
      """
        |def f (A: Type)(x: A): A := x
        |""".stripMargin

    checkLastDeclType(p) match {
      case pi: CA.Term.Pi =>
        assert(!pi.binders.head.isImplicit, "expected explicit binder to stay explicit in the residual")
        pi.binders.head.ty match {
          case CA.Term.Sort(CA.Term.FormOp(CA.LevelForm.LevelZero, _, _), _) =>
          case other => fail(s"Expected Type binder, got $other")
        }
        pi.out match {
          case CA.Term.LocalRef(outRef, _) => assertEquals(outRef, pi.binders.head.localRef)
          case other                       => fail(s"Expected codomain to reuse A, got $other")
        }

      case other => fail(s"Expected residualized Pi, got $other")
    }
  }

  test("a declaration header's residual preserves implicit level binders") {
    val p =
      """
        |def f {u: Level}(A: Type { level = u }): Type { level = u } := A
        |""".stripMargin

    checkLastDeclType(p) match {
      case pi: CA.Term.Pi =>
        assertEquals(pi.binders.length, 2)
        val uRef = pi.binders.head.localRef
        pi.binders.head.ty match {
          case CA.Term.GlobalRef("Level", _) =>
          case other                         => fail(s"Expected Level binder, got $other")
        }
        pi.out match {
          case CA.Term.Sort(CA.Term.LocalRef(outRef, _), _) =>
            assertEquals(outRef, uRef)
          case other => fail(s"Expected codomain to reuse universe level, got $other")
        }

      case other => fail(s"Expected residualized Pi, got $other")
    }
  }

  // Every match writes its motive. A generated selector's match writes the selector's declared
  // result type: the field's type, under a let binding each earlier field it mentions to that
  // field's selector applied to `self`.
  test("a generated selector's match residualizes its field type, under its earlier fields, as its motive") {
    val p =
      """
        |struct Boxed : Type { level = succ(one) }
        | | mk (T: Type)(x: T) : Boxed
        |""".stripMargin

    val body = checkLastDeclBody(p) match {
      case CA.Term.Lam(_, body, _, _, _, _, _) => resultTerm(body)
      case other                               => fail(s"Expected a checked lambda, got $other")
    }
    body match {
      case CA.Term.Match(
            CA.Term.LocalRef(scrut, _),
            CA.Term.Body(
              Vector(
                CA.Let(bound, _, CA.Term.App(CA.Term.GlobalRef("Boxed.T", _), Vector(CA.Term.LocalRef(self, _)), _), _)
              ),
              CA.Term.LocalRef(fieldType, _),
              _
            ),
            _,
            _,
            _
          ) =>
        assertEquals(self, scrut)
        assertEquals(fieldType, bound)
      case other => fail(s"Expected the selector match to return { let T := Boxed.T(self); T }, got $other")
    }
  }

  // Residuals are pure syntax: every node a checked term contains is reachable through
  // `CoreAst.children`, so re-evaluating one needs nothing but the term and an env.
  test("checked residuals contain only syntax nodes") {
    val p =
      natDecls +
        """
          |inductive Bool : Type
          | | true : Bool
          | | false : Bool
          |
          |axiom neutralBool (b: Bool): Bool
          |
          |def pick (b: Bool): Peano := {
          |  match neutralBool(b) returning Peano with
          |  | Bool.true => Peano.zero
          |  | Bool.false => Peano.zero
          |}
          |""".stripMargin

    def walk(term: CA.Term): Unit = {
      term match {
        case _: CA.Term.GlobalRef | _: CA.Term.LocalRef | _: CA.Term.Select | _: CA.Term.App | _: CA.Term.Pi |
            _: CA.Term.Body | _: CA.Term.Lam | _: CA.Term.Match | _: CA.Term.Sort | _: CA.Term.FormOp =>
        case other => fail(s"Residual contains a non-syntax node: $other")
      }
      CA.children(term).foreach(walk)
    }

    walk(checkLastDeclBody(p))
  }
}
