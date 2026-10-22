package com.raccoonlang

import com.raccoonlang.Value.{Level, NeutralThunk, VSort}
import com.raccoonlang.{ElabAst => EA}

class RefinementTests extends munit.FunSuite {
  import ValueEquivalence.UnificationFailure.{Contradiction, Stuck}

  private val span = Span(0, 0)
  private val declarations =
    """
      |inductive N : Type
      | | z : N
      | | s (_: N): N
      |
      |inductive Hold (n: N): Prop
      | | intro {n: N} (payload: N): Hold(n)
      | | other {n: N}: Hold(n)
      |
      |inductive At indices (n: N): Type
      | | zeroAt : At(N.z)
      | | succAt (k: N): At(N.s(k))
      |
      |inductive Other indices (n: N): Type
      | | only : Other(N.z)
      |
      |axiom axiomF (n: N): N
      |axiom axiomG (n: N): N
      |axiom F (n: N): Type
      |
      |inductive Vec (A: Type) indices (n: N): Type
      | | nil {A: Type}: Vec(A, N.z)
      | | cons {A: Type} (n: N) (tail: Vec(A, n)) (head: A): Vec(A, N.s(n))
      |
      |def pick (captured: N)(n: N): N := {
      |  match n returning N with
      |  | N.z => captured
      |  | N.s k => N.z
      |}
      |
      |def identityN (n: N): N := n
      |def constantN (n: N): N := N.z
      |""".stripMargin

  private lazy val env: Env = {
    LanguageParser.parseProgram(declarations) match {
      case Success(parsed, _, _) =>
        val core = Elaborator.elab(parsed, Prelude.test)
        core.decls.foldLeft(Interpreter.initialEnv(Prelude.test)) { case (curEnv, decl) =>
          Interpreter.evalDecl(decl, curEnv)
        }
      case err: Failure => fail(s"Failed to parse fixture: $err")
    }
  }

  private def global(name: String): Value = Interpreter.evalTerm(EA.Term.GlobalRef(name, span), env)

  private def applyGlobal(name: String, args: Value*): Value = Interpreter.evalApply(env(name), args.toVector)

  private def expectContradiction(result: Either[ValueEquivalence.UnificationFailure, EqStore]): Unit =
    result match {
      case Left(_: Contradiction) => ()
      case other                  => fail(s"Expected a contradiction, got $other")
    }

  private def expectStuck(result: Either[ValueEquivalence.UnificationFailure, EqStore]): Unit =
    result match {
      case Left(_: Stuck) => ()
      case other          => fail(s"Expected a stuck comparison, got $other")
    }

  private def typecheckDecls(src: String): Unit =
    LanguageParser.parseProgram(src) match {
      case Success(parsed, _, _) => Interpreter.run(Elaborator.elab(parsed, Prelude.test), Prelude.test); ()
      case err: Failure          => fail(s"Failed to parse source: $err, ${src.substring(err.curIdx)}")
    }

  private def runProgram(src: String): Value =
    LanguageParser.parseProgram(src) match {
      case Success(parsed, _, _) =>
        Interpreter.run(Elaborator.elab(parsed, Prelude.test), Prelude.test).getOrElse(fail("Program has no body"))
      case err: Failure => fail(s"Failed to parse source: $err, ${src.substring(err.curIdx)}")
    }

  test("refinement solves links and detects data constructor clashes through safe structure") {
    val nType = env("N")
    val z = global("N.z")
    val sz = applyGlobal("N.s", z)
    val ssz = applyGlobal("N.s", sz)
    val x = FreshVar.freshVar("x", nType)

    ValueEquivalence.tryUnify(x, z, EqStore.empty.allow(x.synDeps)) match {
      case Right(store)  => assertEquals(store.force(x), z)
      case Left(failure) => fail(s"Expected a successful variable link, got $failure")
    }

    expectContradiction(ValueEquivalence.tryUnify(z, sz, EqStore.empty))
    expectContradiction(ValueEquivalence.tryUnify(sz, ssz, EqStore.empty))

    val atZ = applyGlobal("At", z)
    val atSz = applyGlobal("At", sz)
    expectContradiction(ValueEquivalence.tryUnify(atZ, atSz, EqStore.empty))

    val otherZ = applyGlobal("Other", z)
    expectStuck(ValueEquivalence.tryUnify(atZ, otherZ, EqStore.empty))
  }

  test("axiom applications, occurs checks, levels, and blocked captures stay inconclusive") {
    val nType = env("N")
    val z = global("N.z")
    val sz = applyGlobal("N.s", z)
    val fZ = applyGlobal("axiomF", z)
    val fSz = applyGlobal("axiomF", sz)
    val gZ = applyGlobal("axiomG", z)

    expectStuck(ValueEquivalence.tryUnify(fZ, fSz, EqStore.empty))
    expectStuck(ValueEquivalence.tryUnify(fZ, gZ, EqStore.empty))
    expectStuck(ValueEquivalence.tryUnify(env("identityN"), env("constantN"), EqStore.empty))
    expectStuck(ValueEquivalence.tryUnify(env("N.s").tpe, env("F").tpe, EqStore.empty))

    val x = FreshVar.freshVar("x", nType)
    val fX = applyGlobal("axiomF", x)
    expectStuck(ValueEquivalence.tryUnify(x, fX, EqStore.empty.allow(x.synDeps)))

    val start = EqStore.empty.allow(x.synDeps)
    expectStuck(ValueEquivalence.tryUnify(fX, fZ, start))
    assertEquals(start.force(x), x)

    val a = FreshVar.freshVar("a", Value.LevelTpe)
    val b = FreshVar.freshVar("b", Value.LevelTpe)
    val c = FreshVar.freshVar("c", Value.LevelTpe)
    val level1 = Level.of(Map(a.id -> 1, b.id -> 1), 0)
    val level2 = Level.of(Map(b.id -> 1, c.id -> 1), 0)
    val refinable = level1.synDeps ++ level2.synDeps
    expectStuck(ValueEquivalence.tryUnify(VSort(level1), VSort(level2), EqStore.empty.allow(refinable)))

    val neutralN = FreshVar.freshVar("n", nType)
    val thunkZ = Interpreter.evalApply(env("pick"), Vector(z, neutralN))
    val thunkSz = Interpreter.evalApply(env("pick"), Vector(sz, neutralN))
    val idZ = thunkZ.asInstanceOf[NeutralThunk].id
    val idSz = thunkSz.asInstanceOf[NeutralThunk].id
    assertEquals(idZ.nodeId, idSz.nodeId)
    assertNotEquals(idZ.captures, idSz.captures)
    expectStuck(ValueEquivalence.tryUnify(thunkZ, thunkSz, EqStore.empty))
  }

  test("axiom family arguments prevent speculative links before later index clashes") {
    val z = global("N.z")
    val sz = applyGlobal("N.s", z)
    val x = FreshVar.freshVar("x", env("N"))
    val fx = applyGlobal("F", x)
    val fz = applyGlobal("F", z)
    val left = applyGlobal("Vec", fx, x)
    val right = applyGlobal("Vec", fz, sz)
    val start = EqStore.empty.allow(x.synDeps)

    expectStuck(ValueEquivalence.tryUnify(left, right, start))
    assertEquals(start.force(x), x)
  }

  test("unknown indexed constructors remain reachable for coverage and Prop elimination") {
    val missingCase =
      """
        |inductive N : Type
        | | z : N
        | | s (_: N): N
        |
        |inductive At indices (n: N): Type
        | | zeroAt : At(N.z)
        | | succAt (k: N): At(N.s(k))
        |
        |axiom axiomF (n: N): N
        |
        |def bad (value: At(axiomF(N.z))): N := {
        |  match value returning N with
        |  | At.zeroAt => N.z
        |}
        |""".stripMargin
    intercept[MissingCase] { typecheckDecls(missingCase) }

    val exhaustiveUnknown = missingCase.replace(
      "  | At.zeroAt => N.z",
      "  | At.zeroAt => N.z\n  | At.succAt k => N.z"
    )
    typecheckDecls(exhaustiveUnknown)

    val propElimination =
      """
        |inductive N : Type
        | | z : N
        | | s (_: N): N
        |
        |inductive Shape indices (n: N): Prop
        | | zeroShape : Shape(N.z)
        | | succShape (k: N): Shape(N.s(k))
        |
        |axiom axiomF (n: N): N
        |
        |def bad (shape: Shape(axiomF(N.z))): N := {
        |  match shape returning N with
        |  | Shape.zeroShape => N.z
        |}
        |""".stripMargin
    intercept[PropEliminationRestricted] { typecheckDecls(propElimination) }

    val stuckSingletonPropElimination =
      """
        |inductive N : Type
        | | z : N
        | | s (_: N): N
        |
        |axiom axiomF (n: N): N
        |
        |inductive OnlyShape indices (n: N): Prop
        | | only : OnlyShape(axiomF(N.z))
        |
        |def bad (shape: OnlyShape(axiomF(N.s(N.z)))): N := {
        |  match shape returning N with
        |  | OnlyShape.only => N.z
        |}
        |""".stripMargin
    intercept[PropEliminationRestricted] { typecheckDecls(stuckSingletonPropElimination) }
  }

  test("same axiom application in a constructor index remains reachable and can infer its motive") {
    val source =
      """
        |inductive N : Type
        | | z : N
        | | s (_: N): N
        |
        |axiom f (n: N): N
        |
        |inductive Computed indices (n: N): Type
        | | only : Computed(f(N.z))
        |
        |def missing (v: Computed(f(N.s(N.z)))): N := {
        |  match v returning N with
        |}
        |
        |def explicit (v: Computed(f(N.s(N.z)))): N := {
        |  match v returning N with
        |  | Computed.only => N.z
        |}
        |
        |def inferred (v: Computed(f(N.s(N.z)))): Computed(f(N.s(N.z))) := {
        |  match v with
        |  | Computed.only => v
        |}
        |""".stripMargin

    intercept[MissingCase] { typecheckDecls(source) }

    typecheckDecls(
      source.replace(
        "  match v returning N with\n}",
        "  match v returning N with\n  | Computed.only => N.z\n}"
      )
    )
  }

  test("transparent blocked matches cannot justify an unrelated equality proof") {
    val source =
      """
        |inductive N : Type
        | | z : N
        | | s (_: N): N
        |
        |def pick (captured: N)(n: N): N := {
        |  match n returning N with
        |  | N.z => captured
        |  | N.s k => N.z
        |}
        |
        |def bad (a: N)(b: N)(n: N)(p: Eq(N, pick(a, n), pick(b, n))): Eq(N, a, b) := {
        |  match p returning Eq(N, a, b) with
        |  | Eq.refl x => Eq.refl(a)
        |}
        |""".stripMargin

    intercept[TypeMismatch] { typecheckDecls(source) }
  }

  test("proof equality refines propositions before inspecting proof constructors or payloads") {
    val x = FreshVar.freshVar("x", env("N"))
    val y = FreshVar.freshVar("y", env("N"))
    val z = global("N.z")
    val sz = applyGlobal("N.s", z)
    val introX = applyGlobal("Hold.intro", x, z)
    val introY = applyGlobal("Hold.intro", y, sz)
    val otherY = applyGlobal("Hold.other", y)
    val refinable = EqStore.empty.allow(x.synDeps ++ y.synDeps)

    val sameConstructor = ValueEquivalence.tryUnify(introX, introY, refinable) match {
      case Right(store)  => store
      case Left(failure) => fail(s"Expected proof irrelevance after refining proposition indices, got $failure")
    }
    assert(
      ValueEquivalence.defEq(
        ValueOps.materialize(introX, sameConstructor),
        ValueOps.materialize(introY, sameConstructor)
      )
    )

    val differentConstructors = ValueEquivalence.tryUnify(introX, otherY, refinable) match {
      case Right(store)  => store
      case Left(failure) => fail(s"Expected proof irrelevance across proof constructors, got $failure")
    }
    assert(
      ValueEquivalence.defEq(
        ValueOps.materialize(introX, differentConstructors),
        ValueOps.materialize(otherY, differentConstructors)
      )
    )

    expectStuck(ValueEquivalence.tryUnify(introX, introY, EqStore.empty))
    expectStuck(ValueEquivalence.tryUnify(introX, otherY, EqStore.empty))
  }

  test("a hidden equality between packed proofs cannot make an empty match exhaustive") {
    val source =
      """
        |inductive N : Type
        | | z : N
        | | s (_: N): N
        |
        |inductive B : Type
        | | f : B
        | | t : B
        |
        |inductive Hold (b: B): Prop
        | | intro {b: B} (n: N): Hold(b)
        |
        |inductive Packed : Type
        | | mk (p: $P in Prop): Packed
        |
        |def bad (x: B)(y: B)(h: Eq(Packed,
        |  Packed.mk(Hold.intro(x, N.z)),
        |  Packed.mk(Hold.intro(y, N.s(N.z))))): N := {
        |  match h returning N with
        |}
        |
        |bad(B.f, B.f, Eq.refl(Packed.mk(Hold.intro(B.f, N.z))))
        |""".stripMargin

    intercept[MissingCase] { runProgram(source) }

    val explicitRefl =
      source.replace(
        "  match h returning N with\n}",
        "  match h returning N with\n  | Eq.refl packed => N.z\n}"
      )
    runProgram(explicitRefl) match {
      case Value.VCtor(head, _, _) => assertEquals(head.name, "N.z")
      case other                   => fail(s"Expected N.z from the explicit Eq.refl branch, got $other")
    }
  }
}
