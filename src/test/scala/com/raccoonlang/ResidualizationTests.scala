package com.raccoonlang

import com.raccoonlang.{ElabAst => EA}

class ResidualizationTests extends munit.FunSuite {
  case class Checked(value: Value, term: EA.Term)

  private def checkBody(src: String): Checked =
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        val worlds = core.decls.foldLeft(Interpreter.initialWorlds(Prelude.test)) { case (curWorlds, decl) =>
          Interpreter.evalDecl(decl, curWorlds)
        }
        val body = core.body.getOrElse(fail("Program has no body"))
        implicit val eqStore: EqStore = EqStore.empty
        val resV = TypeChecker.check(body, worlds.checkEnv)
        val ctx = ValueQuote.quoteContext(worlds.checkEnv)
        val term = ValueQuote.quoteTerm(resV, ctx, body.span)
        Checked(resV, term)

      case err: Failure => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }

  private def assertGlobal(term: EA.Term, name: String): Unit =
    term match {
      case EA.Term.GlobalRef(`name`, _) =>
      case other                        => fail(s"Expected global $name, got $other")
    }

  private def containsGlobal(term: EA.Term, name: String): Boolean =
    term match {
      case EA.Term.GlobalRef(n, _) => n == name
      case EA.Term.LocalRef(_, _)  => false
      case EA.Term.Select(base, _, resultTy, _) =>
        containsGlobal(base, name) || containsGlobal(resultTy, name)
      case EA.Term.App(fn, args, _) =>
        containsGlobal(fn, name) || args.exists(arg => containsGlobal(arg, name))
      case EA.Term.Pi(binders, out, _, _) =>
        binders.exists(binder => containsGlobalBinderType(binder.ty, name)) || containsGlobal(out, name)
      case EA.Term.Body(lets, res, _) =>
        lets.exists(l => l.ty.exists(ty => containsGlobal(ty, name)) || containsGlobal(l.value, name)) ||
        containsGlobal(res, name)
      case EA.Term.Lam(ty, uses, body, _, _, _) =>
        containsGlobal(ty, name) ||
        uses.exists(use => containsGlobal(use.normalizer, name)) ||
        containsGlobal(body, name)
      case EA.Term.Match(scrut, motive, cases, _) =>
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

  private val natDecls =
    """
      |inductive Nat : Type
      | | zero : Nat
      | | succ (_: Nat) : Nat
      |""".stripMargin

  test("residualizes a transparent match application to the selected constructor") {
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
    assertGlobal(checked.term, "Nat.zero")
    assert(!containsGlobal(checked.term, "expensive"))
  }

  test("struct projection from a known constructor residualizes to the selected field") {
    val p =
      natDecls +
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
      case res @ EA.Term.GlobalRef(_, _) =>
        assertGlobal(res, "Nat.zero")
      case other => fail(s"Expected projection to residualize to Nat.zero, got $other")
    }
  }

  test("lambda bodies residualize at the lambda boundary") {
    val p =
      natDecls +
        """
          |def id (n: Nat): Nat := n
          |
          |{
          |  fun (n: Nat): Nat => id(Nat.zero)
          |}
          |""".stripMargin

    checkBody(p).term match {
      case EA.Term.Lam(_, _, body, _, _, _) =>
        assertGlobal(body, "Nat.zero")
      case other => fail(s"Expected lambda body to residualize to Nat.zero, got $other")
    }
  }

  test("stuck match branch bodies residualize at the case boundary") {
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

    checkBody(p).term match {
      case EA.Term.Match(_, _, cases, _) =>
        assertEquals(cases.map(_.ctorName).toSet, Set("Bool.true", "Bool.false"))
        cases.foreach(c => assertGlobal(c.body, "Nat.zero"))
      case other => fail(s"Expected stuck match with residualized branches, got $other")
    }
  }

  test("stuck match residualizes its scrutinee") {
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

    checkBody(p).term match {
      case EA.Term.Match(scrut, _, _, _) =>
        assert(!containsGlobal(scrut, "idBool"))
        assert(containsGlobal(scrut, "opaqueBool"))
      case other => fail(s"Expected stuck match residual, got $other")
    }
  }

  test("Pi binder quotation preserves reducible plain binder heads") {
    val p =
      natDecls +
        """
          |def TyId (A: Type): Type := A
          |
          |{
          |  (_: TyId(Nat)) -> Nat
          |}
          |""".stripMargin

    checkBody(p).term match {
      case pi: EA.Term.Pi =>
        pi.binders.head.ty match {
          case EA.BinderType.TypePattern(pattern, _) =>
            assertEquals(pattern.toString, "TyId(Nat)")
          case other => fail(s"Expected Pi binder annotation to preserve TyId(Nat), got $other")
        }
      case other => fail(s"Expected residualized Pi, got $other")
    }
  }

  test("Pi binder quotation preserves captures under reducible type-pattern heads") {
    val p =
      """
        |def IdT (A: Type): Type := A
        |def Fn : Type := (_: IdT($A)) -> A
        |
        |{
        |  Fn
        |}
        |""".stripMargin

    checkBody(p).term match {
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

  test("residualizes Pi binders with type-pattern captures") {
    val p =
      natDecls +
        """
          |inductive Vec (A: Sort($u)) indices (n: Nat) : Sort(u)
          | | nil {A: Sort($u)} : Vec(A, Nat.zero)
          | | cons {A: Sort($u)} (tail: Vec(A, $n)) (head: A) : Vec(A, Nat.succ(n))
          |
          |def IndexedFn (_: Nat): Type := (v: Vec(Nat, $n)) -> Vec(Nat, n)
          |
          |{
          |  IndexedFn(Nat.zero)
          |}
          |""".stripMargin

    checkBody(p).term match {
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

  test("residualized type-pattern binders quote closed-over type arguments semantically") {
    val p =
      natDecls +
        """
          |inductive Vec (A: Sort($u)) indices (n: Nat) : Sort(u)
          | | nil {A: Sort($u)} : Vec(A, Nat.zero)
          | | cons {A: Sort($u)} (tail: Vec(A, $n)) (head: A) : Vec(A, Nat.succ(n))
          |
          |def IndexedFn (A: Type): Type := (v: Vec(A, $n)) -> Vec(A, n)
          |
          |{
          |  IndexedFn(Nat)
          |}
          |""".stripMargin

    checkBody(p).term match {
      case pi: EA.Term.Pi =>
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

              case other => fail(s"Expected Pi codomain to reuse captured n with Nat element type, got $other")
            }

          case other => fail(s"Expected Vec(Nat, $${n}) binder pattern, got $other")
        }

      case other => fail(s"Expected residualized Pi, got $other")
    }
  }

  test("Pi binder quotation preserves constrained capture binders") {
    val p =
      """
        |{
        |  (_: $A in Type) -> A
        |}
        |""".stripMargin

    checkBody(p).term match {
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

  test("Pi binder quotation preserves level captures") {
    val p =
      """
        |{
        |  (_: Sort(Level.succ($u))) -> Sort(u)
        |}
        |""".stripMargin

    checkBody(p).term match {
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
