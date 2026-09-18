package com.raccoonlang

import com.raccoonlang.CoreAst.{ConstBody, Decl, Program}

/** Quotient primitives are installed through the builtin admission boundary; this fixture supplies only their types. */
class QuotientTests extends munit.FunSuite {
  private val bootstrap =
    """
      |axiom Quot {u: Level}(A: Sort(u))(r: (x: A) -> (y: A) -> Prop): Sort(u)
      |
      |inductive Eq {u: Level}(A: Sort(u)) indices (x: A)(y: A) : Prop
      | | refl (x: A) : Eq(A, x, x)
      |
      |axiom QuotMkType {u: Level}{A: Sort(u)}(r: (x: A) -> (y: A) -> Prop)(a: A): Quot(A, r)
      |
      |axiom QuotLiftType {u: Level}{v: Level}{A: Sort(u)}{r: (x: A) -> (y: A) -> Prop}
      |  (q: Quot(A, r))(B: Sort(v))(f: A -> B)
      |  (sound: (a: A) -> (b: A) -> (h: r(a, b)) -> Eq(B, f(a), f(b))): B
      |
      |axiom QuotIndType {u: Level}{A: Sort(u)}{r: (x: A) -> (y: A) -> Prop}
      |  (q: Quot(A, r))(motive: (q: Quot(A, r)) -> Prop)
      |  (mk: (a: A) -> motive(Quot.mk(r, a))): motive(q)
      |
      |def liftOn {u: Level}{v: Level}{A: Sort(u)}{r: (x: A) -> (y: A) -> Prop}
      |  (q: Quot(A, r))(B: Sort(v))(f: A -> B)
      |  (sound: (a: A) -> (b: A) -> (h: r(a, b)) -> Eq(B, f(a), f(b))): B :=
      |  Quot.lift(q, B, f, sound)
      |
      |def inductionOn {u: Level}{A: Sort(u)}{r: (x: A) -> (y: A) -> Prop}
      |  (q: Quot(A, r))(motive: (q: Quot(A, r)) -> Prop)
      |  (mk: (a: A) -> motive(Quot.mk(r, a))): motive(q) :=
      |  Quot.ind(q, motive, mk)
      |
      |axiom sound {u: Level}{A: Sort(u)}
      |  (a: A)(b: A)(r: (x: A) -> (y: A) -> Prop)(h: r(a, b)):
      |  Eq(Quot(A, r), Quot.mk(r, a), Quot.mk(r, b))
      |
      |""".stripMargin

  private def core(source: String): Program = LanguageParser.parseProgram(bootstrap + source) match {
    case Success(program, _, _) =>
      val elaborated = Elaborator.elab(program)
      Program(
        elaborated.decls.map {
          case Decl.AxiomDecl("QuotMkType", ty, span) =>
            Decl.ConstDecl(false, "Quot.mk", ty, ConstBody.Builtin(span), span)
          case Decl.AxiomDecl("QuotLiftType", ty, span) =>
            Decl.ConstDecl(false, "Quot.lift", ty, ConstBody.Builtin(span), span)
          case Decl.AxiomDecl("QuotIndType", ty, span) =>
            Decl.ConstDecl(false, "Quot.ind", ty, ConstBody.Builtin(span), span)
          case other => other
        },
        elaborated.body
      )
    case Failure(_, idx, message) =>
      fail(s"Failed to parse at $idx: $message; near=${(bootstrap + source).drop(idx).take(80)}")
  }

  private def checked(source: String): (Env, Value) = {
    val (env, body) = TypeChecker.checkProgramTrusted(core(source))
    env -> body.map(_.value).getOrElse(fail("Program has no body"))
  }

  private def eval(source: String): Value = checked(source)._2

  private def evalRaw(source: String): Value = LanguageParser.parseProgram(source) match {
    case Success(program, _, _)   => Interpreter.run(Elaborator.elab(program)).getOrElse(fail("Program has no body"))
    case Failure(_, idx, message) => fail(s"Failed to parse at $idx: $message")
  }

  private def evalTrustedRaw(source: String): Value = LanguageParser.parseProgram(source) match {
    case Success(program, _, _) =>
      val (_, body) = TypeChecker.checkProgramTrusted(Elaborator.elab(program))
      body.map(_.value).getOrElse(fail("Program has no body"))
    case Failure(_, idx, message) => fail(s"Failed to parse at $idx: $message")
  }

  private def checkRaw(source: String): Unit = LanguageParser.parseProgram(source) match {
    case Success(program, _, _)   => TypeChecker.checkProgram(Elaborator.elab(program))
    case Failure(_, idx, message) => fail(s"Failed to parse at $idx: $message")
  }

  private def trustedEnv(source: String): Env = TypeChecker.checkProgramTrusted(core(source))._1

  private def checkTrustedSource(source: String): Env = TypeChecker.checkProgramTrusted(core(source))._1

  private def shape(value: Value): String = value match {
    case Value.VCtor(head, fields, _)            => head.name + fields.map(shape).mkString("(", ",", ")")
    case Value.VApp(head, args, _, _)            => shape(head) + args.map(shape).mkString("(", ",", ")")
    case Value.VConst(name, _, _)                => name
    case Value.ConstructorHead(name, _, _, _, _) => name + "()"
    case other                                   => other.toString
  }

  test("Quot.mk stores only its representative") {
    val value = eval(
      """
        |inductive Peano : Type
        | | zero : Peano
        |
        |def Rel (a: Peano)(b: Peano): Prop := Eq(Peano, a, b)
        |
        |{ Quot.mk(Rel, Peano.zero) }
        |""".stripMargin
    )
    value match {
      case Value.VCtor(head, fields, _) =>
        assertEquals(head.name, "Quot.mk")
        assert(!head.noConfusion)
        assertEquals(fields.length, 1)
        assertEquals(shape(fields.head), "Peano.zero()")
      case other => fail(s"Expected quotient constructor, got $other")
    }
  }

  test("Quot.lift reduces on Quot.mk") {
    val value = eval(
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (n: Peano) : Peano
        |
        |def Rel (a: Peano)(b: Peano): Prop := Eq(Peano, a, b)
        |
        |def liftSound (a: Peano)(b: Peano)(h: Rel(a, b)): Eq(Peano, Peano.succ(a), Peano.succ(b)) := {
        |  match h returning Eq(Peano, Peano.succ(a), Peano.succ(b)) with
        |  | Eq.refl x => Eq.refl(Peano.succ(x))
        |}
        |{ Quot.lift(Quot.mk(Rel, Peano.zero), Peano, fun (x: Peano): Peano => Peano.succ(x), liftSound) }
        |""".stripMargin
    )
    assertEquals(shape(value), "Peano.succ(Peano.zero())")
  }

  test("the inductionOn wrapper canonicalizes a proof motive") {
    val value = eval(
      """
        |inductive Peano : Type
        | | zero : Peano
        |
        |def Rel (a: Peano)(b: Peano): Prop := Eq(Peano, a, b)
        |
        |inductive True : Prop
        | | intro : True
        |
        |def motive (q: Quot(Peano, Rel)): Prop := True
        |
        |{ inductionOn(Quot.mk(Rel, Peano.zero), motive, fun (a: Peano): motive(Quot.mk(Rel, a)) => True.intro) }
        |""".stripMargin
    )
    value match {
      case Value.VCtor(head, _, _) => assertEquals(head.name, "True.intro")
      case other                   => fail(s"Expected canonical proof, got $other")
    }
  }

  test("the implicit liftOn wrapper recovers quotient parameters") {
    val value = eval(
      """
        |inductive Peano : Type
        | | zero : Peano
        |
        |def Rel (a: Peano)(b: Peano): Prop := Eq(Peano, a, b)
        |def idSound (a: Peano)(b: Peano)(h: Rel(a, b)): Eq(Peano, a, b) := h
        |
        |{ liftOn(Quot.mk(Rel, Peano.zero), Peano, fun (x: Peano): Peano => x, idSound) }
        |""".stripMargin
    )
    assertEquals(shape(value), "Peano.zero()")
  }

  test("Quot.sound has equality of quotient representatives as its type") {
    val value = eval(
      """
        |inductive Peano : Type
        | | zero : Peano
        |
        |def Rel (a: Peano)(b: Peano): Prop := Eq(Peano, a, b)
        |
        |{ sound(Peano.zero, Peano.zero, Rel, Eq.refl(Peano.zero)) }
        |""".stripMargin
    )
    assert(PrettyPrinter.print(value.tpe).contains("Quot"))
    assert(PrettyPrinter.print(value.tpe).contains("Quot.mk"))
  }

  test("ordinary constructor disjointness remains available") {
    eval(
      """
        |inductive Peano : Type
        | | zero : Peano
        | | succ (n: Peano) : Peano
        |
        |inductive False : Prop
        |
        |def noConf (n: Peano)(h: Eq(Peano, Peano.zero, Peano.succ(n))): False := {
        |  match h returning False with
        |}
        |{ Peano.zero }
        |""".stripMargin
    )
  }

  test("Quot.mk fields do not force implicit parameters") {
    intercept[NonForcedImplicitParam] {
      checkTrustedSource(
        """
          |inductive Peano : Type
          | | zero : Peano
          |
          |def Rel (a: Peano)(b: Peano): Prop := Eq(Peano, a, b)
          |
          |def extract {x: Peano}
          |  (h: Eq(Quot(Peano, Rel), Quot.mk(Rel, x), Quot.mk(Rel, Peano.zero))): Peano := x
          |""".stripMargin
      )
    }
  }

  test("Quot exposes no generated field selectors") {
    val env = trustedEnv(
      """
        |inductive Peano : Type
        | | zero : Peano
        |
        |def Rel (a: Peano)(b: Peano): Prop := Eq(Peano, a, b)
        |
        |axiom q : Quot(Peano, Rel)
        |""".stripMargin
    )
    val span = Span(0, 0)
    intercept[TypeError] {
      TypeChecker.checkTerm(
        CoreAst.Term.Select(CoreAst.Term.GlobalRef("q", span), "value", span),
        env
      )
    }
  }

  test("unknown builtin declarations are rejected") {
    intercept[ReservedKernelName] {
      evalRaw("def bogus : Type := builtin\n{ Type }")
    }
    intercept[ReservedKernelName] {
      evalRaw("def Sort : Type := builtin\n{ Type }")
    }
    intercept[ReservedKernelName] {
      checkRaw("def Sort : Type := builtin\n{ Type }")
    }
    val error = intercept[WTF] {
      evalTrustedRaw("def bogus : Type := builtin\n{ Type }")
    }
    assertEquals(error.msg, "Unknown builtin bogus")
  }
}
