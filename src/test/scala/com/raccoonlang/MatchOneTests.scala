package com.raccoonlang

import java.util.concurrent.atomic.AtomicInteger

import com.raccoonlang.{CoreAst => CA, ElabAst => EA}
import com.raccoonlang.Value._

class MatchOneTests extends munit.FunSuite {
  private val span = Span(0, 1)

  private def parse(source: String): SurfaceAst.Program =
    LanguageParser.parseProgram(source) match {
      case Success(program, _, _) => program
      case failure: Failure       => fail(s"Failed to parse: $failure, ${source.substring(failure.curIdx)}")
    }

  private def core(source: String): CA.Program = Elaborator.elab(parse(source), Prelude.test)

  private def run(source: String): Value =
    Interpreter.run(core(source), Prelude.test).getOrElse(fail("Program has no body"))

  private def typecheck(source: String): Unit = {
    Interpreter.run(core(source), Prelude.test)
    ()
  }

  private def compileEnv(source: String): (CA.Program, Env) = {
    val program = core(source)
    val env = program.decls.foldLeft(Interpreter.initialEnv(Prelude.test)) { case (current, decl) =>
      Interpreter.evalDecl(decl, current)
    }
    (program, env)
  }

  private def matchOnes(term: CA.Term): Vector[CA.Term.MatchOne] = term match {
    case m: CA.Term.MatchOne                 => Vector(m) ++ matchOnes(m.body) ++ matchOnes(m.scrut)
    case CA.Term.Body(lets, res, _)          => lets.flatMap(l => matchOnes(l.value)) ++ matchOnes(res)
    case CA.Term.Lam(_, _, body, _, _, _, _) => matchOnes(body)
    case CA.Term.Match(scrut, _, cases, _, _) =>
      matchOnes(scrut) ++ cases.flatMap(c => matchOnes(c.body))
    case CA.Term.App(fn, args, _)   => matchOnes(fn) ++ args.flatMap(matchOnes)
    case CA.Term.Select(base, _, _) => matchOnes(base)
    case _                          => Vector.empty
  }

  test("destructuring lowers to ordinary lets and dense nested MatchOne terms") {
    val program = core(
      """
        |
        |inductive Triple : Type
        | | mk (a: Nat)(b: Nat)(c: Nat): Triple
        |
        |inductive Nest : Type
        | | mk (left: Nat)(right: Triple): Nest
        |
        |def pick (value: Nest): Nat := {
        |  let (left, (a, b, c)) := value
        |  b
        |}
        |""".stripMargin
    )
    val declaration = program.decls.collectFirst {
      case d: CA.Decl.ConstDecl if d.name == "pick" => d.body
    }.get
    val term = declaration.asInstanceOf[CA.ConstBody.TermBody].term
    val matches = matchOnes(term)
    assertEquals(matches.length, 2)
    val outer = matches.head
    assertEquals(outer.fieldRefs.map(_.id), Vector(2, 3))
    val nested = matches(1)
    assertEquals(nested.fieldRefs.map(_.id), Vector(4, 5, 6))
    val lambda = term.asInstanceOf[CA.Term.Lam]
    val body = lambda.body.asInstanceOf[CA.Term.Body]
    assertEquals(body.lets.map(_.localRef.id), Vector(1))
    assertEquals(body.res, outer)
  }

  test("nested sibling patterns allocate all immediate fields before descendants") {
    val program = core(
      """
        |inductive Pair : Type
        | | pair (first: Nat)(second: Nat): Pair
        |
        |inductive Quad : Type
        | | quad (left: Pair)(right: Pair): Quad
        |
        |def pick (quad: Quad): Nat := {
        |  let ((a, b), (c, d)) := quad
        |  d
        |}
        |""".stripMargin
    )
    val declaration = program.decls.collectFirst {
      case d: CA.Decl.ConstDecl if d.name == "pick" => d.body
    }.get
    val matches = matchOnes(declaration.asInstanceOf[CA.ConstBody.TermBody].term)
    assertEquals(matches.map(_.fieldRefs.map(_.id)), Vector(Vector(2, 3), Vector(4, 5), Vector(6, 7)))
  }

  test("nested patterns, ignored fields, shadowing, and original RHS scope work") {
    val value = run(
      """
        |
        |inductive Inner : Type
        | | mk (first: Nat)(second: Nat): Inner
        |
        |inductive Outer : Type
        | | mk (left: Nat)(inner: Inner)(right: Nat): Outer
        |
        |def pick (outer: Outer): Nat := {
        |  let (left, (outer, chosen), _) := outer
        |  outer
        |}
        |
        |{
        |  pick(Outer.mk(Nat.zero, Inner.mk(Nat.succ(Nat.zero), Nat.zero), Nat.zero))
        |}
        |""".stripMargin
    )
    value match {
      case ConstructorValue(head, _) => assertEquals(head.name, "Nat.succ")
      case other                     => fail(s"Expected a constructor result, got $other")
    }
  }

  test("MatchOne accepts one-constructor families for known and neutral values") {
    val (program, env) = compileEnv(
      """
        |
        |inductive One : Type
        | | mk (value: Nat): One
        |
        |axiom neutral: One
        |""".stripMargin
    )
    val ref = CA.LocalRef(0, "field")
    val known = CA.Term.MatchOne(
      CA.Term.App(CA.Term.GlobalRef("One.mk", span), Vector(CA.Term.GlobalRef("Nat.zero", span)), span),
      None,
      Vector(ref),
      CA.Term.LocalRef(ref, span),
      span,
      NodeId.fresh()
    )
    val checkedKnown = TypeChecker.checkTerm(known, env)
    checkedKnown.value match {
      case ConstructorValue(head, _) => assertEquals(head.name, "Nat.zero")
      case other                     => fail(s"Expected a constructor result, got $other")
    }
    assert(checkedKnown.residual.isInstanceOf[EA.Term.Match])

    val neutral = known.copy(scrut = CA.Term.GlobalRef("neutral", span), nodeId = NodeId.fresh())
    val checkedNeutral = TypeChecker.checkTerm(neutral, env)
    val stuck = checkedNeutral.value.asInstanceOf[NeutralThunk]
    assert(ValueEquivalence.defEq(stuck.tpe, env("Nat")))
    assert(stuck.term.motive.nonEmpty)
  }

  test("MatchOne rejects non-inductive, zero/multiple constructor, and wrong arity scrutinees") {
    val defs =
      """
        |
        |inductive Empty : Type
        |
        |inductive One : Type
        | | mk (value: Nat): One
        |
        |inductive Many : Type
        | | left : Many
        | | right : Many
        |
        |axiom impossible: Empty
        |
        |axiom one: One
        |
        |axiom many: Many
        |""".stripMargin
    val (_, env) = compileEnv(defs)
    def matchOne(scrut: CA.Term, fields: Vector[CA.LocalRef]) =
      CA.Term.MatchOne(scrut, None, fields, CA.Term.GlobalRef("Nat.zero", span), span, NodeId.fresh())

    intercept[NonInductiveMatch] {
      TypeChecker.checkTerm(matchOne(CA.Term.GlobalRef("Type", span), Vector.empty), env)
    }
    intercept[InvalidSingleConstructorMatch] {
      TypeChecker.checkTerm(matchOne(CA.Term.GlobalRef("impossible", span), Vector.empty), env)
    }
    intercept[InvalidSingleConstructorMatch] {
      TypeChecker.checkTerm(matchOne(CA.Term.GlobalRef("many", span), Vector.empty), env)
    }
    intercept[InvalidSingleConstructorMatch] {
      TypeChecker.checkTerm(matchOne(CA.Term.GlobalRef("Many.left", span), Vector.empty), env)
    }
    intercept[InvalidDestructuring] {
      TypeChecker.checkTerm(matchOne(CA.Term.GlobalRef("one", span), Vector.empty), env)
    }
    intercept[InvalidDestructuring] {
      TypeChecker.checkTerm(
        matchOne(CA.Term.GlobalRef("one", span), Vector(CA.LocalRef(0, "a"), CA.LocalRef(1, "b"))),
        env
      )
    }
  }

  test("empty and unary destructuring patterns work") {
    typecheck(
      """
        |
        |inductive Unit : Type
        | | unit : Unit
        |
        |inductive One : Type
        | | mk (value: Nat): One
        |
        |def ignoreUnit: Unit := {
        |  let () := Unit.unit
        |  Unit.unit
        |}
        |
        |def unary (one: One): Nat := {
        |  let (value) := one
        |  value
        |}
        |""".stripMargin
    )
  }

  test("named match uses expected result types and infers common branch body types") {
    typecheck(
      """
        |
        |inductive Answer : Type
        | | yes : Answer
        | | no : Answer
        |
        |def contextual (n: Nat): Nat := {
        |  match n with
        |  | Nat.zero => Nat.zero
        |  | Nat.succ rest => rest
        |}
        |""".stripMargin
    )
    val program = core(
      """
        |
        |inductive Answer : Type
        | | yes : Answer
        | | no : Answer
        |
        |axiom flag: Answer
        |
        |def inferred(ignored: Nat): Nat := {
        |  let result := {
        |    match flag with
        |    | Answer.yes => Nat.zero
        |    | Answer.no => Nat.zero
        |  }
        |  result
        |}
        |""".stripMargin
    )
    val env = program.decls.foldLeft(Interpreter.initialEnv(Prelude.test)) { case (current, decl) =>
      Interpreter.evalDecl(decl, current)
    }
    env("inferred") match {
      case fn: VLam => assert(ValueEquivalence.defEq(fn.tpe.codomain(env), env("Nat")))
      case other    => fail(s"Expected an inferred function, got $other")
    }
  }

  test("contextual motive permits empty matches; explicit motive keeps priority") {
    typecheck(
      """
        |
        |inductive Empty : Type
        |
        |axiom absurd: Empty
        |
        |def emptyElim (e: Empty): Nat := {
        |  match e with
        |}
        |""".stripMargin
    )
    intercept[MissingReturningClause] {
      run(
        """
          |
          |inductive Empty : Type
          |
          |axiom absurd: Empty
          |
          |match absurd with
          |""".stripMargin
      )
    }
    intercept[TypeMismatch] {
      typecheck(
        """
          |
          |inductive Answer : Type
          | | yes : Answer
          |
          |def mismatch (n: Nat): Answer := {
          |  match n returning Nat with
          |  | Nat.zero => Nat.zero
          |  | Nat.succ rest => rest
          |}
          |""".stripMargin
      )
    }
  }

  test("duplicate leaves have a span and instance patterns remain named-only") {
    val source =
      """
        |
        |inductive Pair : Type
        | | mk (left: Nat)(right: Nat): Pair
        |
        |def bad (pair: Pair): Nat := {
        |  let (same, same) := pair
        |  same
        |}
        |""".stripMargin
    val error = intercept[InvalidDestructuring] { core(source) }
    assertEquals(error.span.map(_.start), Some(source.indexOf("same, same") + "same, ".length))
    assert(
      LanguageParser
        .parseProgram(
          """{
            |  let instance (x, y) := pair
            |  Nat.zero
            |}""".stripMargin
        )
        .isInstanceOf[Failure]
    )
  }

  test("destructured instance-marked fields are ordinary locals") {
    intercept[NoInstanceFound] {
      typecheck(
        """
          |
          |inductive Search : Type
          | | marker : Search
          |
          |inductive Holder : Type
          | | hold [search: Search]: Holder
          |
          |def missing (holder: Holder): Search := {
          |  let (search) := holder
          |  derive[Search]
          |}
          |""".stripMargin
      )
    }
  }

  test("whole-RHS annotation and annotation mismatch are checked before unpacking") {
    typecheck(
      """
        |
        |inductive One : Type
        | | mk (value: Nat): One
        |
        |def good: Nat := {
        |  let (value): One := One.mk(Nat.zero)
        |  value
        |}
        |""".stripMargin
    )
    intercept[TypeMismatch] {
      typecheck(
        """
          |
          |inductive One : Type
          | | mk (value: Nat): One
          |
          |def bad: Nat := {
          |  let (value): Nat := One.mk(Nat.zero)
          |  Nat.zero
          |}
          |""".stripMargin
      )
    }
  }

  test("hidden constructor captures can stay in scope but cannot escape inferred motives") {
    val source =
      """
        |
        |inductive Vec (A: Type) indices (n: Nat): Type
        | | nil {A: Type}: Vec(A, Nat.zero)
        | | cons {A: Type}(tail: Vec(A, $n))(head: A): Vec(A, Nat.succ(n))
        |
        |inductive Hidden (A: Type): Type
        | | mk {A: Type}(items: Vec(A, $n)): Hidden(A)
        |
        |def length (A: Type)(items: Vec(A, $n)): Nat := n
        |
        |axiom hidden: Hidden(Nat)
        |
        |def useHidden (h: Hidden(Nat)): Nat := {
        |  let (items) := h
        |  length(Nat, items)
        |}
        |
        |def escape (h: Hidden(Nat)): Nat := {
        |  let answer := {
        |    let (items) := h
        |    items
        |  }
        |  Nat.zero
        |}
        |""".stripMargin
    intercept[MissingReturningClause] { typecheck(source) }
    typecheck(source.take(source.indexOf("def escape")))
  }

  test("indexed MatchOne refinement checks dependent branch results") {
    typecheck(
      """
        |inductive OnlyZero indices (n: Nat): Type
        | | mk: OnlyZero(Nat.zero)
        |
        |def zeroProof (n: Nat)(proof: OnlyZero(n)): Eq(Nat, n, Nat.zero) := {
        |  let () := proof
        |  Eq.refl(n)
        |}
        |""".stripMargin
    )
  }

  test("recursive MatchOne binds strict subterms and rejects reconstruction") {
    typecheck(
      """
        |inductive Chain : Type
        | | node (next: Chain): Chain
        |
        |def shrink (chain: Chain): Nat decreases structural(chain) := {
        |  let (next) := chain
        |  shrink(next)
        |}
        |""".stripMargin
    )
    intercept[NonDecreasingRecursiveCall] {
      typecheck(
        """
          |inductive Chain : Type
          | | node (next: Chain): Chain
          |
          |def loop (chain: Chain): Nat decreases structural(chain) := {
          |  let (next) := chain
          |  loop(Chain.node(next))
          |}
          |""".stripMargin
      )
    }
  }

  test("Prop MatchOne allows proof results and rejects data elimination for neutral and known values") {
    typecheck(
      """
        |inductive Proof : Prop
        | | proof: Proof
        |
        |inductive PropPack : Prop
        | | mk (value: Nat)(witness: Proof): PropPack
        |
        |def getProof (pack: PropPack): Proof := {
        |  let (_, witness) := pack
        |  witness
        |}
        |""".stripMargin
    )
    intercept[PropEliminationRestricted] {
      typecheck(
        """
          |inductive Proof : Prop
          | | proof: Proof
          |
          |inductive PropPack : Prop
          | | mk (value: Nat)(witness: Proof): PropPack
          |
          |axiom neutralPack: PropPack
          |
          |def badNeutral (pack: PropPack): Nat := {
          |  let (value, _) := pack
          |  value
          |}
          |""".stripMargin
      )
    }
    intercept[PropEliminationRestricted] {
      typecheck(
        """
          |inductive Proof : Prop
          | | proof: Proof
          |
          |inductive PropPack : Prop
          | | mk (value: Nat)(witness: Proof): PropPack
          |
          |def badKnown: Nat := {
          |  let (value, _) := PropPack.mk(Nat.zero, Proof.proof)
          |  value
          |}
          |""".stripMargin
      )
    }
  }

  test("inferred branch motives cannot leak refined outer types; annotation keeps scoped use") {
    val refinedPrelude =
      """
        |inductive CheckVec indices (n: Nat): Type
        | | nil: CheckVec(Nat.zero)
        | | cons (tail: CheckVec($n)): CheckVec(Nat.succ(n))
        |
        |inductive OnlyZero indices (n: Nat): Type
        | | mk: OnlyZero(Nat.zero)
        |
        |inductive NeedsZero (v: CheckVec(Nat.zero)): Type
        | | mk {v: CheckVec(Nat.zero)}: NeedsZero(v)
        |
        |""".stripMargin
    intercept[MissingReturningClause] {
      typecheck(
        refinedPrelude +
          """
            |def bad (n: Nat)(tag: OnlyZero(n))(v: CheckVec(n)): Nat := {
            |  let answer := {
            |    let () := tag
            |    NeedsZero.mk(v)
            |  }
            |  Nat.zero
            |}
            |""".stripMargin
      )
    }
    typecheck(
      refinedPrelude +
        """
          |inductive Unit : Type
          | | unit: Unit
          |
          |def scoped (n: Nat)(tag: OnlyZero(n))(v: CheckVec(n)): Unit := {
          |  let answer: Unit := {
          |    let () := tag
          |    let inner := NeedsZero.mk(v)
          |    Unit.unit
          |  }
          |  answer
          |}
          |""".stripMargin
    )
  }

  test("checking and reevaluation each run destructuring RHS and continuation once") {
    val source =
      """
        |
        |inductive Box : Type
        | | mk (value: Nat): Box
        |
        |axiom makeBox (n: Nat): Box
        |
        |axiom consume (n: Nat): Nat
        |
        |{
        |  let (value) := makeBox(Nat.zero)
        |  consume(value)
        |}
        |""".stripMargin
    val program = core(source)
    val rhsCalls = new AtomicInteger(0)
    val continuationCalls = new AtomicInteger(0)
    val baseEnv = program.decls.foldLeft(Interpreter.initialEnv(Prelude.test)) { case (current, decl) =>
      Interpreter.evalDecl(decl, current)
    }
    val makeBoxPi = baseEnv("makeBox").tpe.asInstanceOf[VPi]
    val consumePi = baseEnv("consume").tpe.asInstanceOf[VPi]
    val makeBox = VLam(
      makeBoxPi,
      ValueId.Const("native-makeBox"),
      LamBody.Native(
        (args, _) => {
          rhsCalls.incrementAndGet()
          Interpreter.evalApply(baseEnv("Box.mk"), Vector(args.head))
        },
        baseEnv,
        isRawRecursive = false
      )
    )
    val consume = VLam(
      consumePi,
      ValueId.Const("native-consume"),
      LamBody.Native(
        (args, _) => {
          continuationCalls.incrementAndGet()
          args.head
        },
        baseEnv,
        isRawRecursive = false
      )
    )
    val env = baseEnv
      .asInstanceOf[TypecheckEnv]
      .copy(
        globals = baseEnv.asInstanceOf[TypecheckEnv].globals ++ Map(
          "makeBox" -> GlobalBinding.Strict(makeBox),
          "consume" -> GlobalBinding.Strict(consume)
        )
      )
    val checked = TypeChecker.checkTerm(program.body.get, env)
    assertEquals(rhsCalls.get(), 1)
    assertEquals(continuationCalls.get(), 1)
    rhsCalls.set(0)
    continuationCalls.set(0)
    Interpreter.evalTerm(checked.residual, env)
    assertEquals(rhsCalls.get(), 1)
    assertEquals(continuationCalls.get(), 1)
  }
}
