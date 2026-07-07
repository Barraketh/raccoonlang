package com.raccoonlang

import com.raccoonlang.ErrorReporter.Source

class QuotientTests extends munit.FunSuite {
  private def runProgram(src: String): Value = {
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value)
        try {
          Interpreter.run(core).getOrElse(fail("Program has no body"))
        } catch {
          case t: TypeError => fail(ErrorReporter.pretty(t, Source(src)))
        }
      case err: Failure =>
        fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }
  }

  sealed trait Shape
  case class SConst(name: String) extends Shape
  case class SApp(head: Shape, args: List[Shape]) extends Shape

  private def toShape(v: Value): Shape = v match {
    case Value.ConstructorHead(n, _, _, _, _) => SConst(n)
    case Value.VCtor(h, storedArgs, _) =>
      val args = Value.constructorPatternArgs(h, storedArgs)
      if (args.isEmpty) SConst(h.name) else SApp(SConst(h.name), args.toList.map(toShape))
    case Value.VConst(n, _, _)     => SConst(n)
    case Value.VApp(h, args, _, _) => SApp(toShape(h), args.toList.map(toShape))
    case other                     => SConst(other.toString)
  }

  private val natZero = SConst("Nat.zero")
  private def natSucc(value: Shape): Shape = SApp(SConst("Nat.succ"), List(value))

  private val natPrelude =
    """
      |def Rel (a: Nat)(b: Nat): Prop := Eq(Nat, a, b)
      |""".stripMargin

  test("Quot.mk is a constructor head that stores only the representative") {
    val res = runProgram(
      natPrelude +
        """
          |{
          |  Quot.mk(Nat, Rel, Nat.zero)
          |}
          |""".stripMargin
    )

    res match {
      case Value.VCtor(head, storedArgs, _) =>
        assertEquals(head.name, "Quot.mk")
        assertEquals(storedArgs.length, 1)
        assertEquals(Value.constructorPatternArgs(head, storedArgs).map(toShape), Vector(natZero))
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
          |  Quot.lift(Quot.mk(Nat, Rel, Nat.zero), Nat, fun (x: Nat): Nat => Nat.succ(x), sound)
          |}
          |""".stripMargin
    )

    assertEquals(toShape(res), natSucc(natZero))
  }

  test("Quot.ind reduces on Quot.mk for Prop motives") {
    val res = runProgram(
      natPrelude +
        """
          |def motive (q: Quot(Nat, Rel)): Prop := True
          |
          |{
          |  Quot.inductionOn(Quot.mk(Nat, Rel, Nat.zero), motive, fun (a: Nat): motive(Quot.mk(Nat, Rel, a)) => True.intro)
          |}
          |""".stripMargin
    )

    assertEquals(toShape(res), SConst("True.intro"))
  }

  test("implicit wrapper can recover quotient parameters") {
    val res = runProgram(
      natPrelude +
        """
          |def idSound (a: Nat)(b: Nat)(h: Rel(a, b)): Eq(Nat, a, b) := h
          |
          |{
          |  Quot.liftOn(Quot.mk(Nat, Rel, Nat.zero), Nat, fun (x: Nat): Nat => x, idSound)
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

    val err = intercept[WTF] {
      LanguageParser.parseProgram(src) match {
        case Success(value, _, _) =>
          Interpreter.run(Elaborator.elab(value))
        case parseErr: Failure =>
          fail(s"Failed to parse: $parseErr, ${src.substring(parseErr.curIdx)}")
      }
    }

    assertEquals(err.msg, "Unknown builtin bogus")
  }

  private def expectTypeError[E <: TypeError](
      src: String
  )(implicit ct: scala.reflect.ClassTag[E], loc: munit.Location): E =
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value)
        intercept[E](Interpreter.run(core))
      case err: Failure =>
        fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }

  // Quot.sound identifies Quot.mk applications with distinct representatives, so match checking
  // must not apply constructor no-confusion to Quot.mk. Both programs below derived False before
  // ConstructorHead.noConfusion was introduced.

  test("Quot.mk is not disjoint: refl stays reachable for equalities between distinct representatives") {
    val err = expectTypeError[MissingCase](
      """
        |def TrivRel (a: Bool)(b: Bool): Prop := True
        |
        |def boom (p: Eq(Quot(Bool, TrivRel), Quot.mk(Bool, TrivRel, Bool.true), Quot.mk(Bool, TrivRel, Bool.false))): False := {
        |  match p returning False with
        |}
        |""".stripMargin
    )
    assertEquals(err.ctor, "Eq.refl")
  }

  test("Quot.mk is not injective: match refinement cannot derive representative equality") {
    expectTypeError[TypeMismatch](
      """
        |def TrivRel (a: Bool)(b: Bool): Prop := True
        |
        |def mkInj (x: Bool)(y: Bool)(p: Eq(Quot(Bool, TrivRel), Quot.mk(Bool, TrivRel, x), Quot.mk(Bool, TrivRel, y))): Eq(Bool, x, y) := {
        |  match p returning Eq(Bool, x, y) with
        |  | Eq.refl z => Eq.refl(x)
        |}
        |""".stripMargin
    )
  }

  test("congruence failures under opaque heads are not refutations") {
    // Eq(g(mk true), g(mk false)) is provable via congrArg over Quot.sound, so unification failing
    // on the arguments of the non-injective head g must not prune the refl case.
    val err = expectTypeError[MissingCase](
      """
        |def TrivRel (a: Bool)(b: Bool): Prop := True
        |
        |axiom g (q: Quot(Bool, TrivRel)): Nat
        |
        |def gEq : Eq(Nat, g(Quot.mk(Bool, TrivRel, Bool.true)), g(Quot.mk(Bool, TrivRel, Bool.false))) :=
        |  congrArg(Quot.sound(Bool.true, Bool.false, TrivRel, True.intro), Nat, g)
        |
        |def boom (p: Eq(Nat, g(Quot.mk(Bool, TrivRel, Bool.true)), g(Quot.mk(Bool, TrivRel, Bool.false)))): False := {
        |  match p returning False with
        |}
        |""".stripMargin
    )
    assertEquals(err.ctor, "Eq.refl")
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

  test("elaboration solves implicit metas through Quot.mk arguments") {
    // In Solve mode, decomposing same-head Quot.mk applications is a sound heuristic
    // (links only need to make the equation true), so x is inferred as Bool.true here.
    val res = runProgram(
      natPrelude +
        """
          |def extract {x: Nat}(h: Eq(Quot(Nat, Rel), Quot.mk(Nat, Rel, x), Quot.mk(Nat, Rel, Nat.zero))): Nat := x
          |
          |{
          |  extract(Eq.refl(Quot.mk(Nat, Rel, Nat.zero)))
          |}
          |""".stripMargin
    )
    assertEquals(toShape(res), natZero)
  }
}
