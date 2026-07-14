package com.raccoonlang

import com.raccoonlang.{ElabAst => EA}

class ResidualizationTests extends munit.FunSuite {
  case class Checked(value: Value, term: EA.Term)

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

  private def resultTerm(term: EA.Term): EA.Term =
    term match {
      case EA.Term.Body(Vector(), res, _) => res
      case other                          => other
    }

  private def checkLastDeclType(src: String): EA.Term =
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        val last = core.decls.lastOption.getOrElse(fail("Program has no declarations"))
        val env = core.decls.dropRight(1).foldLeft(Prelude.test.checkedEnv) {
          case (curEnv, decl) => Interpreter.evalDecl(decl, curEnv)
        }
        val ty = last match {
          case CoreAst.Decl.AxiomDecl(_, ty, _)          => ty
          case CoreAst.Decl.ConstDecl(_, _, ty, _, _, _) => ty
          case other                                     => fail(s"Expected typed declaration, got $other")
        }
        TypeChecker.checkTerm(ty, env).residual

      case err: Failure => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }

  private def containsGlobal(term: EA.Term, name: String): Boolean =
    term match {
      case EA.Term.GlobalRef(n, _) => n == name
      case EA.Term.LocalRef(_, _)  => false
      case EA.Term.App(fn, args, _) =>
        containsGlobal(fn, name) || args.exists(arg => containsGlobal(arg, name))
      case EA.Term.Pi(binders, out, _, _) =>
        binders.exists(binder => containsGlobal(binder.ty, name)) || containsGlobal(out, name)
      case EA.Term.Body(lets, res, _) =>
        lets.exists(l => l.ty.exists(ty => containsGlobal(ty, name)) || containsGlobal(l.value, name)) ||
        containsGlobal(res, name)
      case EA.Term.Lam(ty, body, _, _, _, _) =>
        containsGlobal(ty, name) ||
        containsGlobal(body, name)
      case EA.Term.Match(scrut, motive, cases, _, _) =>
        containsGlobal(scrut, name) ||
        motive.exists(ty => containsGlobal(ty, name)) ||
        cases.exists(c => containsGlobal(c.body, name))
    }

  private val natDecls =
    """
      |inductive Nat : Type
      | | zero : Nat
      | | succ (_: Nat) : Nat
      |""".stripMargin

  test("checked residual preserves transparent applications literally") {
    val p =
      natDecls +
        """
          |inductive Bool : Type
          | | true : Bool
          | | false : Bool
          |
          |def expensive (n: Nat): Nat := n
          |
          |def choose (b: Bool)(x: Nat): Nat := {
          |  match b returning Nat with
          |  | Bool.true => x
          |  | Bool.false => Nat.zero
          |}
          |
          |{
          |  choose(Bool.false, expensive(Nat.zero))
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
          |opaque def opaqueBool (b: Bool): Bool := b
          |
          |def choose (b: Bool): Nat := {
          |  match b returning Nat with
          |  | Bool.true => Nat.zero
          |  | Bool.false => Nat.succ(Nat.zero)
          |}
          |
          |{
          |  choose(opaqueBool(Bool.true))
          |}
          |""".stripMargin

    val res = resultTerm(checkBody(p).term)
    assert(containsGlobal(res, "choose"))
    assert(containsGlobal(res, "opaqueBool"))
  }

  test("checked residual elaborates projection syntax to selector application") {
    val p =
      natDecls +
        """
          |struct Pair (A: Type)(B: Type) : Type
          | | mk (fst: A)(snd: B) : Pair(A, B)
          |
          |{
          |  let p := Pair.mk(Nat.zero, Nat.succ(Nat.zero))
          |  p.fst
          |}
          |""".stripMargin

    checkBody(p).term match {
      case EA.Term.Body(
            lets,
            EA.Term.App(
              EA.Term.GlobalRef("Pair.fst", _),
              Vector(EA.Term.LocalRef(ref, _)),
              _
            ),
            _
          ) =>
        assertEquals(lets.length, 1)
        assertEquals(ref, lets.head.localRef)
        assert(containsGlobal(lets.head.value, "Pair.mk"))
      case other => fail(s"Expected selector application over local pair, got $other")
    }
  }

  test("lambda bodies preserve checked application syntax") {
    val p =
      natDecls +
        """
          |def id (n: Nat): Nat := n
          |
          |{
          |  fun (n: Nat): Nat => id(Nat.zero)
          |}
          |""".stripMargin

    resultTerm(checkBody(p).term) match {
      case EA.Term.Lam(_, body, _, _, _, _) =>
        assert(containsGlobal(body, "id"))
        assert(containsGlobal(body, "Nat.zero"))
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
          |def id (n: Nat): Nat := n
          |opaque def opaqueBool (b: Bool): Bool := b
          |
          |{
          |  match opaqueBool(Bool.true) returning Nat with
          |  | Bool.true => id(Nat.zero)
          |  | Bool.false => id(Nat.zero)
          |}
          |""".stripMargin

    resultTerm(checkBody(p).term) match {
      case EA.Term.Match(_, _, cases, _, _) =>
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
          |opaque def opaqueBool (b: Bool): Bool := b
          |
          |{
          |  match idBool(opaqueBool(Bool.true)) returning Nat with
          |  | Bool.true => Nat.zero
          |  | Bool.false => Nat.zero
          |}
          |""".stripMargin

    resultTerm(checkBody(p).term) match {
      case EA.Term.Match(scrut, _, _, _, _) =>
        assert(containsGlobal(scrut, "idBool"))
        assert(containsGlobal(scrut, "opaqueBool"))
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
          |  (_: TyId(Nat)) -> Nat
          |}
          |""".stripMargin

    resultTerm(checkBody(p).term) match {
      case pi: EA.Term.Pi =>
        assertEquals(pi.binders.head.ty.toString, "TyId(Nat)")
      case other => fail(s"Expected residualized Pi, got $other")
    }
  }

  test("Pi binder residual preserves forced implicit binders with projection specs") {
    val p =
      """
        |axiom f : {A: Type} -> (x: A) -> A
        |""".stripMargin

    checkLastDeclType(p) match {
      case pi: EA.Term.Pi =>
        assertEquals(pi.binders.length, 2)
        val implicitBinder = pi.binders.head
        assert(implicitBinder.isImplicit, "expected leading binder to stay implicit in the residual")
        assert(implicitBinder.projection.isDefined, "expected forced implicit binder to carry a projection spec")
        implicitBinder.ty match {
          case EA.Term.GlobalRef("Type", _) =>
          case other                        => fail(s"Expected Type binder annotation, got $other")
        }
        val explicitBinder = pi.binders(1)
        assert(!explicitBinder.isImplicit, "expected forcing binder to stay explicit in the residual")
        explicitBinder.ty match {
          case EA.Term.LocalRef(tyRef, _) => assertEquals(tyRef, implicitBinder.localRef)
          case other                      => fail(s"Expected explicit binder typed by implicit A, got $other")
        }
        pi.out match {
          case EA.Term.LocalRef(outRef, _) => assertEquals(outRef, implicitBinder.localRef)
          case other                       => fail(s"Expected codomain to reuse implicit A, got $other")
        }
      case other => fail(s"Expected residualized Pi, got $other")
    }
  }

  test("Pi binder residual preserves implicit dependent binders") {
    val p =
      natDecls +
        """
          |inductive Vec (A: Type) indices (n: Nat) : Type
          | | nil : Vec(A, Nat.zero)
          | | cons {n: Nat} (tail: Vec(A, n)) (head: A) : Vec(A, Nat.succ(n))
          |
          |axiom f : {n: Nat} -> (v: Vec(Nat, n)) -> Vec(Nat, n)
          |""".stripMargin

    checkLastDeclType(p) match {
      case pi: EA.Term.Pi =>
        assertEquals(pi.binders.length, 2)
        val nRef = pi.binders.head.localRef
        pi.binders.head.ty match {
          case EA.Term.GlobalRef("Nat", _) =>
          case other                       => fail(s"Expected Nat implicit binder, got $other")
        }
        pi.binders(1).ty match {
          case EA.Term.App(
                EA.Term.GlobalRef("Vec", _),
                Vector(EA.Term.GlobalRef("Nat", _), EA.Term.LocalRef(argRef, _)),
                _
              ) =>
            assertEquals(argRef, nRef)
          case other => fail(s"Expected Vec(Nat, n) binder annotation, got $other")
        }
        pi.out match {
          case EA.Term.App(
                EA.Term.GlobalRef("Vec", _),
                Vector(EA.Term.GlobalRef("Nat", _), EA.Term.LocalRef(outRef, _)),
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
        |axiom f : (A: Type) -> A
        |""".stripMargin

    checkLastDeclType(p) match {
      case pi: EA.Term.Pi =>
        assert(!pi.binders.head.isImplicit, "expected explicit binder to stay explicit in the residual")
        pi.binders.head.ty match {
          case EA.Term.GlobalRef("Type", _) =>
          case other                        => fail(s"Expected Type binder, got $other")
        }
        pi.out match {
          case EA.Term.LocalRef(outRef, _) => assertEquals(outRef, pi.binders.head.localRef)
          case other                       => fail(s"Expected codomain to reuse A, got $other")
        }

      case other => fail(s"Expected residualized Pi, got $other")
    }
  }

  test("Pi binder residual preserves implicit level binders") {
    val p =
      """
        |axiom f : {u: Level} -> (_: Sort(Level.succ(u))) -> Sort(u)
        |""".stripMargin

    checkLastDeclType(p) match {
      case pi: EA.Term.Pi =>
        assertEquals(pi.binders.length, 2)
        val uRef = pi.binders.head.localRef
        pi.binders.head.ty match {
          case EA.Term.GlobalRef("Level", _) =>
          case other                         => fail(s"Expected Level binder, got $other")
        }
        pi.out match {
          case EA.Term.App(EA.Term.GlobalRef("Sort", _), Vector(EA.Term.LocalRef(outRef, _)), _) =>
            assertEquals(outRef, uRef)
          case other => fail(s"Expected codomain to reuse universe level, got $other")
        }

      case other => fail(s"Expected residualized Pi, got $other")
    }
  }
}
