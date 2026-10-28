package com.raccoonlang

import com.raccoonlang.{ElabAst => EA}

class ResidualizationTests extends munit.FunSuite {
  case class Checked(value: Value, term: EA.Term)

  private def checkBody(src: String): Checked =
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        val env = core.decls.foldLeft(Interpreter.initialEnv(Prelude.test)) { case (curEnv, decl) =>
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

  private def containsGlobal(term: EA.Term, name: String): Boolean =
    term match {
      case EA.Term.GlobalRef(n, _) => n == name
      case EA.Term.LocalRef(_, _)  => false
      case EA.Term.NatLit(_, _)    => false
      case EA.Term.StrLit(_, _)    => false
      case EA.Term.Word(head, pieces, _) =>
        head.name == name || pieces.exists {
          case EA.Term.WordPiece.Layer(before, after) => (before ++ after).exists(arg => containsGlobal(arg, name))
          case EA.Term.WordPiece.Splice(list)         => containsGlobal(list, name)
        }
      case EA.Term.App(fn, args, _) =>
        containsGlobal(fn, name) || args.exists(arg => containsGlobal(arg, name))
      case EA.Term.Pi(binders, out, _, _, _) =>
        binders.exists(binder => containsGlobalBinderType(binder.ty, name)) || containsGlobal(out, name)
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

  private def containsGlobalBinderType(ty: EA.BinderType, name: String): Boolean =
    ty match {
      case EA.BinderType.TypePattern(tp, _)                   => containsGlobalTypePattern(tp, name)
      case EA.BinderType.ConstrainedCapture(_, constraint, _) => containsGlobalTypePattern(constraint, name)
    }

  private def containsGlobalTypePattern(tp: EA.TypePattern, name: String): Boolean =
    tp match {
      case EA.TypePattern.Type(term) => containsGlobal(term, name)
      case EA.TypePattern.App(fn, args, _) =>
        containsGlobal(fn, name) || args.exists(arg => containsGlobalTypePattern(arg, name))
      case EA.TypePattern.Capture(_, _) => false
    }

  test("checked residual preserves transparent applications literally") {
    val p =
      """
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
      """
        |axiom opaqueBool (b: Bool): Bool
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
      """
        |struct Pair (A: Type)(B: Type) : Type
        | | mk {A: Type}{B: Type} (fst: A)(snd: B) : Pair(A, B)
        |
        |{
        |  let p := Pair.mk(Nat, Nat, Nat.zero, Nat.succ(Nat.zero))
        |  p.fst
        |}
        |""".stripMargin

    checkBody(p).term match {
      case EA.Term.Body(lets, EA.Term.App(EA.Term.GlobalRef("Pair.fst", _), Vector(EA.Term.LocalRef(ref, _)), _), _) =>
        assertEquals(lets.length, 1)
        assertEquals(ref, lets.head.localRef)
        assert(containsGlobal(lets.head.value, "Pair.mk"))
      case other => fail(s"Expected selector application over local pair, got $other")
    }
  }

  test("lambda bodies preserve checked application syntax") {
    val p =
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
      """
        |def id (n: Nat): Nat := n
        |axiom opaqueBool (b: Bool): Bool
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
      """
        |def idBool (b: Bool): Bool := b
        |axiom opaqueBool (b: Bool): Bool
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
      """
        |def TyId (A: Type): Type := A
        |
        |{
        |  (_: TyId(Nat)) -> Nat
        |}
        |""".stripMargin

    resultTerm(checkBody(p).term) match {
      case pi: EA.Term.Pi =>
        pi.binders.head.ty match {
          case EA.BinderType.TypePattern(pattern, _) =>
            assertEquals(pattern.toString, "TyId(Nat)")
          case other => fail(s"Expected Pi binder annotation to preserve TyId(Nat), got $other")
        }
      case other => fail(s"Expected residualized Pi, got $other")
    }
  }

  test("Pi binder residual preserves captures under reducible type-pattern heads") {
    val p =
      """
        |def IdT (A: Type): Type := A
        |
        |{
        |  (_: IdT($A)) -> A
        |}
        |""".stripMargin

    resultTerm(checkBody(p).term) match {
      case pi: EA.Term.Pi =>
        pi.binders.head.ty match {
          case EA.BinderType.TypePattern(
                EA.TypePattern.App(EA.Term.GlobalRef("IdT", _), Vector(EA.TypePattern.Capture(aRef, _)), _),
                _
              ) =>
            pi.out match {
              case EA.Term.LocalRef(outRef, _) => assertEquals(outRef, aRef)
              case other                       => fail(s"Expected codomain to reuse captured A, got $other")
            }
          case other => fail(s"Expected IdT($${A}) binder pattern, got $other")
        }
      case other => fail(s"Expected residualized Pi, got $other")
    }
  }

  test("Pi binder residual preserves type-pattern captures") {
    val p =
      """
        |inductive Vec (A: Sort($u)) indices (n: Nat) : Sort(u)
        | | nil {A: Sort($u)} : Vec(A, Nat.zero)
        | | cons {A: Sort($u)} (tail: Vec(A, $n)) (head: A) : Vec(A, Nat.succ(n))
        |
        |{
        |  (v: Vec(Nat, $n)) -> Vec(Nat, n)
        |}
        |""".stripMargin

    resultTerm(checkBody(p).term) match {
      case pi: EA.Term.Pi =>
        assertEquals(pi.binders.length, 1)
        pi.binders.head.ty match {
          case EA.BinderType.TypePattern(
                EA.TypePattern.App(
                  EA.Term.GlobalRef("Vec", _),
                  Vector(EA.TypePattern.Type(EA.Term.GlobalRef("Nat", _)), EA.TypePattern.Capture(nRef, _)),
                  _
                ),
                _
              ) =>
            pi.out match {
              case EA.Term.App(
                    EA.Term.GlobalRef("Vec", _),
                    Vector(EA.Term.GlobalRef("Nat", _), EA.Term.LocalRef(outRef, _)),
                    _
                  ) =>
                assertEquals(outRef, nRef)

              case other => fail(s"Expected Pi codomain to reuse captured n, got $other")
            }

          case other => fail(s"Expected Vec(Nat, $${n}) binder pattern, got $other")
        }

      case other => fail(s"Expected residualized Pi, got $other")
    }
  }

  test("Pi binder residual preserves constrained capture binders") {
    val p =
      """
        |{
        |  (_: $A in Type) -> A
        |}
        |""".stripMargin

    resultTerm(checkBody(p).term) match {
      case pi: EA.Term.Pi =>
        pi.binders.head.ty match {
          case EA.BinderType.ConstrainedCapture(aRef, EA.TypePattern.Type(EA.Term.GlobalRef("Type", _)), _) =>
            pi.out match {
              case EA.Term.LocalRef(outRef, _) => assertEquals(outRef, aRef)
              case other                       => fail(s"Expected codomain to reuse constrained capture A, got $other")
            }
          case other => fail(s"Expected constrained capture binder, got $other")
        }

      case other => fail(s"Expected residualized Pi, got $other")
    }
  }

  test("Pi binder residual preserves level captures") {
    val p =
      """
        |{
        |  (_: Sort(Level.succ($u))) -> Sort(u)
        |}
        |""".stripMargin

    resultTerm(checkBody(p).term) match {
      case pi: EA.Term.Pi =>
        pi.binders.head.ty match {
          case EA.BinderType.TypePattern(
                EA.TypePattern.App(
                  EA.Term.GlobalRef("Sort", _),
                  Vector(
                    EA.TypePattern.App(EA.Term.GlobalRef("Level.succ", _), Vector(EA.TypePattern.Capture(uRef, _)), _)
                  ),
                  _
                ),
                _
              ) =>
            pi.out match {
              case EA.Term.App(EA.Term.GlobalRef("Sort", _), Vector(EA.Term.LocalRef(outRef, _)), _) =>
                assertEquals(outRef, uRef)
              case other => fail(s"Expected codomain to reuse captured universe level, got $other")
            }

          case other => fail(s"Expected Sort(Level.succ($${u})) binder pattern, got $other")
        }

      case other => fail(s"Expected residualized Pi, got $other")
    }
  }
}
