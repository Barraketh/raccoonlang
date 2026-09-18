package com.raccoonlang

class QuotientTests extends munit.FunSuite with TestSupport {

  private def evalDecls(src: String): Env =
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value)
        core.decls.foldLeft(Prelude.default.checkedEnv) { case (env, decl) =>
          Interpreter.evalDecl(decl, env)
        }
      case err: Failure => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }

  sealed trait Shape
  case class SConst(name: String) extends Shape
  case class SApp(head: Shape, args: List[Shape]) extends Shape

  private def toShape(v: Value): Shape = v match {
    case Value.ConstructorHead(n, _, _, _, _) => SConst(n)
    case Value.VCtor(h, storedArgs, _) =>
      val args = storedArgs
      if (args.isEmpty) SConst(h.name) else SApp(SConst(h.name), args.toList.map(toShape))
    case Value.VConst(n, _, _)     => SConst(n)
    case Value.VApp(h, args, _, _) => SApp(toShape(h), args.toList.map(toShape))
    case other                     => SConst(other.toString)
  }

  private val natZero = SConst("0")
  private val natOne = SConst("1")

  private val natPrelude =
    """
      |def Rel (a: Nat)(b: Nat): Prop := Eq(Nat, a, b)
      |""".stripMargin

  test("Quot.mk is a constructor head that stores only the representative") {
    val res = runProgram(
      natPrelude +
        """
          |{
          |  Quot.mk(Rel, Nat.zero)
          |}
          |""".stripMargin
    )

    res match {
      case Value.VCtor(head, storedArgs, _) =>
        assertEquals(head.name, "Quot.mk")
        assertEquals(storedArgs.length, 1)
        assertEquals(storedArgs.map(toShape), Vector(natZero))
      case other =>
        fail(s"Expected Quot.mk constructor value, got $other")
    }
  }

  test("Quot.lift reduces on Quot.mk") {
    val res = runProgram(
      natPrelude +
        """
          |def sound (a: Nat)(b: Nat)(h: Rel(a, b)): Eq(Nat, Nat.succ(a), Nat.succ(b)) := {
          |  match h returning Eq(Nat, Nat.succ(a), Nat.succ(b)) with
          |  | Eq.refl x => Eq.refl(Nat.succ(x))
          |}
          |
          |{
          |  Quot.lift(Quot.mk(Rel, Nat.zero), Nat, fun (x: Nat): Nat => Nat.succ(x), sound)
          |}
          |""".stripMargin
    )

    assertEquals(toShape(res), natOne)
  }

  test("Quot.ind canonicalizes the proof of its motive") {
    val res = runProgram(
      natPrelude +
        """
          |def motive (q: Quot(Nat, Rel)): Prop := True
          |
          |{
          |  Quot.inductionOn(Quot.mk(Rel, Nat.zero), motive, fun (a: Nat): motive(Quot.mk(Rel, a)) => True.intro)
          |}
          |""".stripMargin
    )

    // The mkCase body is never consulted. Exact-type canonicalization reconstructs True.intro
    // from motive(q) = True.
    res match {
      case Value.VCtor(head, fields, tpe) =>
        assertEquals(head.name, "True.intro")
        assertEquals(fields, Vector.empty)
        assertEquals(toShape(tpe), SConst("True"))
      case other => fail(s"Expected the canonical True.intro proof, got $other")
    }
  }

  test("implicit wrapper can recover quotient parameters") {
    val res = runProgram(
      natPrelude +
        """
          |def idSound (a: Nat)(b: Nat)(h: Rel(a, b)): Eq(Nat, a, b) := h
          |
          |{
          |  Quot.liftOn(Quot.mk(Rel, Nat.zero), Nat, fun (x: Nat): Nat => x, idSound)
          |}
          |""".stripMargin
    )

    assertEquals(toShape(res), natZero)
  }

  test("Quot.sound proves related representatives equal in the quotient") {
    val res = runProgram(
      natPrelude +
        """
          |{
          |  Quot.sound(Nat.zero, Nat.zero, Rel, Eq.refl(Nat.zero))
          |}
          |""".stripMargin
    )

    res.tpe match {
      case Value.VApp(Value.VConst("Eq", _, _), Vector(_, quotTy, left, right), _, _) =>
        val printedQuot = PrettyPrinter.print(quotTy)
        assert(printedQuot.startsWith("Quot("))
        assert(printedQuot.contains("Nat"))
        assertEquals(toShape(left), SApp(SConst("Quot.mk"), List(natZero)))
        assertEquals(toShape(right), SApp(SConst("Quot.mk"), List(natZero)))
      case other =>
        fail(s"Expected quotient equality proof, got $other")
    }
  }

  test("unknown builtin declaration is rejected") {
    val src =
      """
        |def bogus : Type := builtin
        |""".stripMargin

    // A program may not declare builtins at all; a prelude may, but only known ones.
    intercept[ReservedKernelName] {
      LanguageParser.parseProgram(src) match {
        case Success(value, _, _) =>
          Interpreter.run(Elaborator.elab(value))
        case parseErr: Failure =>
          fail(s"Failed to parse: $parseErr, ${src.substring(parseErr.curIdx)}")
      }
    }
    val err = intercept[WTF](Prelude.fromSource("bogus-prelude", src).checkedEnv)

    assertEquals(err.msg, "Unknown builtin bogus")
  }

  test("genuine constructor disjointness still prunes impossible refl cases") {
    runProgram(
      """
        |def noConf (n: Nat)(h: Eq(Nat, Nat.zero, Nat.succ(n))): False := {
        |  match h returning False with
        |}
        |
        |{
        |  Bool.true
        |}
        |""".stripMargin
    )
  }

  test("Quot.mk fields do not force implicit parameters (no projection through soundness-quotiented heads)") {
    // Quot.mk has noConfusion=false: Quot.sound identifies mk applications with distinct
    // representatives, so projecting x out of a Quot.mk value appearing in h's index would not
    // be well-defined on the quotient. The implicit is therefore unforced and the def is
    // rejected at declaration instead of x being reconstructed from the Quot.mk field.
    val src =
      natPrelude +
        """
          |def extract {x: Nat}(h: Eq(Quot(Nat, Rel), Quot.mk(Rel, x), Quot.mk(Rel, Nat.zero))): Nat := x
          |
          |{
          |  extract(Eq.refl(Quot.mk(Rel, Nat.zero)))
          |}
          |""".stripMargin
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value)
        intercept[NonForcedImplicitParam] { Interpreter.run(core) }
      case err: Failure =>
        fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }
  }

  test("Quot exposes no generated field selectors") {
    val env = evalDecls(
      natPrelude +
        """
          |axiom q : Quot(Nat, Rel)
          |""".stripMargin
    )
    val span = Span(0, 0)

    // Quot is not a struct: field syntax has no selector to resolve to on a quotient.
    intercept[TypeError] {
      TypeChecker.checkTerm(
        CoreAst.Term.Select(CoreAst.Term.GlobalRef("q", span), "value", span),
        env
      )
    }
  }
}
