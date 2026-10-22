package com.raccoonlang

import com.raccoonlang.Value._

import java.util.concurrent.atomic.AtomicInteger
import scala.concurrent.duration.DurationInt
import scala.concurrent.{Await, ExecutionContext, Future}

class ConstructorMetadataTests extends munit.FunSuite with TestSupport {
  private val env = Prelude.default.checkedEnv
  private val nat = env("Nat")
  private val span = Span(0, 0)
  private val classifier = Sorts.Type

  private def binder(name: String, id: Int, mode: BinderMode): CoreAst.Binder = {
    val ref = CoreAst.LocalRef(id, name)
    CoreAst.Binder(
      ref,
      CoreAst.Term.GlobalRef("Nat", span),
      span,
      CoreAst.BinderSite.Function,
      mode
    )
  }

  private def manualPi(binders: Vector[CoreAst.Binder], codomain: Env => Value): VPi =
    VPi(
      env,
      binders,
      codomain,
      Value.Kind.unr,
      DepSet.empty,
      ValueId.LocalId(NodeId.fresh(), Vector.empty),
      () => classifier,
      isPropValued = false
    )

  private def checkedCodomain(
      binders: Vector[CoreAst.Binder],
      independent: Boolean
  )(run: Env => Value): CheckedPiCodomain =
    new CheckedPiCodomain(binders, independent, None, env) {
      override def apply(env: Env): Value = run(env)
    }

  private def evaluatedPi(source: String): VPi =
    runProgram(source) match {
      case pi: VPi => pi
      case other   => fail(s"Expected a Pi value, got $other")
    }

  private def syntaxPi(binders: Vector[CoreAst.Binder], out: CoreAst.Term): CoreAst.Term.Pi =
    CoreAst.Term.Pi(binders, out, CoreAst.Closure.unrestricted(span), span, NodeId.fresh())

  private def envWith(pi: VPi, argument: Value): Env =
    telescope.BinderOps.instantiateFull(pi.binders, pi.env, Vector(argument))

  test("Pi reference summaries cache exact codomain eligibility independently across syntax copies") {
    val x = CoreAst.LocalRef(72001, "x")
    val xBinder = binder("x", x.id, BinderMode.Explicit)
    val independent = syntaxPi(Vector(xBinder), CoreAst.Term.GlobalRef("Nat", span))
    assert(independent.codomainIndependent)
    assertEquals(independent.codeRefs, Set.empty[CoreAst.LocalRef])

    val dependent = syntaxPi(Vector(xBinder), CoreAst.Term.LocalRef(x, span))
    assert(!dependent.codomainIndependent)
    assertEquals(dependent.codomainBinderIndices, Vector(0))
    assertEquals(dependent.codeRefs, Set(x))

    val changedOut = dependent.copy(out = CoreAst.Term.GlobalRef("Nat", span))
    assert(changedOut.codomainIndependent)
    assertEquals(changedOut.codomainBinderIndices, Vector.empty[Int])
    assertEquals(changedOut.codeRefs, Set.empty[CoreAst.LocalRef])

    val changedBinders = dependent.copy(binders = Vector(binder("replacement", 72002, BinderMode.Explicit)))
    assert(changedBinders.codomainIndependent)
    assertEquals(changedBinders.codeRefs, Set(x))

    def nestedWithClosureRef(ref: CoreAst.LocalRef): CoreAst.Term.Pi = {
      val refTerm = CoreAst.Term.LocalRef(ref, span)
      val closure = CoreAst.Closure(CoreAst.ClosureField.Written(refTerm))
      CoreAst.Term.Pi(
        Vector(binder("nested", 72003, BinderMode.Explicit)),
        CoreAst.Term.GlobalRef("Nat", span),
        closure,
        span,
        NodeId.fresh()
      )
    }

    val nestedCapture = syntaxPi(Vector(xBinder), nestedWithClosureRef(x))
    assert(!nestedCapture.codomainIndependent)
    assert(nestedCapture.codeRefs.contains(x))
    assertEquals(nestedCapture.codomainBinderIndices, Vector(0))

    val outerCapture = CoreAst.LocalRef(72004, "outer")
    val nestedOuterCapture = syntaxPi(Vector(xBinder), nestedWithClosureRef(outerCapture))
    assert(nestedOuterCapture.codomainIndependent)
    assert(nestedOuterCapture.codeRefs.contains(outerCapture))

    val expectedNestedRefs = (nestedOuterCapture.binders.map(_.ty) :+ nestedOuterCapture.out)
      .foldLeft(Set.empty[CoreAst.LocalRef])((acc, term) => acc | CoreAst.mentionedRefs(term))
    assertEquals(nestedOuterCapture.codeRefs, expectedNestedRefs)
  }

  test("checked constructor codomains bind only referenced arguments and cache exact closed values") {
    val binders = Vector(binder("index", 72101, BinderMode.Explicit), binder("unused", 72102, BinderMode.Explicit))
    val evaluations = new AtomicInteger
    val sliced = new AtomicInteger
    val codomain = new CheckedPiCodomain(binders, false, Some(Vector(0)), env) {
      override def apply(bound: Env): Value = {
        evaluations.incrementAndGet()
        if (!bound.containsLocal(binders(1).localRef)) sliced.incrementAndGet()
        bound(binders(0).localRef)
      }
    }
    val pi = manualPi(binders, codomain)
    val one = VPacked.nat(1, nat)
    val two = VPacked.nat(2, nat)
    val unused = VPacked.nat(8, nat)
    assert(pi.constructorResultType(Vector(one, unused), fail("full binding used")) eq one)
    assert(pi.constructorResultType(Vector(one, two), fail("full binding used")) eq one)
    assertEquals(evaluations.get(), 1)
    assert(pi.constructorResultType(Vector(two, unused), fail("full binding used")) eq two)
    assertEquals(evaluations.get(), 2)
    assertEquals(sliced.get(), 2)

    val copiedEnv = pi.copy(env = Env.empty)
    val fullEnv = telescope.BinderOps.instantiateFull(binders, env, Vector(one, unused))
    copiedEnv.constructorResultType(Vector(one, unused), fullEnv)
    assertEquals(evaluations.get(), 3)
    val changedCode = pi.copy(codomain = _ => nat)
    assert(changedCode.constructorResultType(Vector(one, unused), fullEnv) eq nat)
    val changedBinders = pi.copy(binders = binders.map(_.copy(span = Span(1, 1))))
    changedBinders.constructorResultType(Vector(one, unused), fullEnv)
    assertEquals(evaluations.get(), 4)
  }

  test("indexed results distinguish changing values and do not cache unresolved indices") {
    val pi = evaluatedPi("{ (n: Nat) -> Eq(Nat, n, n) }")
    val zero = VPacked.nat(0, nat)
    val one = VPacked.nat(1, nat)
    val zeroResult = pi.constructorResultType(Vector(zero), fail("full binding used"))
    assert(pi.constructorResultType(Vector(zero), fail("full binding used")) eq zeroResult)
    val oneResult = pi.constructorResultType(Vector(one), fail("full binding used"))
    assertNotEquals(zeroResult.key, oneResult.key)

    val unresolved = FreshVar.freshVar("index", nat)
    val unresolvedFirst = pi.constructorResultType(Vector(unresolved), fail("full binding used"))
    val unresolvedSecond = pi.constructorResultType(Vector(unresolved), fail("full binding used"))
    assert(!(unresolvedFirst eq unresolvedSecond))
    assertEquals(unresolvedFirst.key, unresolvedSecond.key)
  }

  test("checked constructors reuse uniform family results without mixing indices or nominal owners") {
    val cons = env("List.cons").asInstanceOf[ConstructorHead]
    val familyArgs = Vector[Value](Value.Level.zero, nat)
    val nil = Interpreter.evalApply(env("List.nil"), familyArgs)
    val first = Interpreter.evalApply(cons, familyArgs ++ Vector(VPacked.nat(1, nat), nil))
    val second = Interpreter.evalApply(cons, familyArgs ++ Vector(VPacked.nat(2, nat), nil))
    assert(first.tpe eq second.tpe)
    assert(ValueEquivalence.defEq(first.tpe, Interpreter.evalApply(env("List"), familyArgs)))

    val source = """
                   |inductive Indexed indices (n: Nat) : Type
                   | | mk (n: Nat) : Indexed(n)
                   |{ Indexed.mk(1) }
                   |""".stripMargin
    val ownerOne = runProgram(source)
    val ownerTwo = runProgram(source)
    assert(!(ownerOne.tpe eq ownerTwo.tpe))
    val otherIndex = runProgram(source.replace("Indexed.mk(1)", "Indexed.mk(2)"))
    assert(!ValueEquivalence.defEq(ownerOne.tpe, otherIndex.tpe))
  }

  test("only a codomain with no own or nested binder references gets the constructor cache") {
    val constant = evaluatedPi("{ (x: Nat) -> Nat }")
    val unusedFallbacks = new AtomicInteger
    val zero = VPacked.nat(0, nat)
    val one = VPacked.nat(1, nat)
    val first = constant.constructorResultType(
      Vector(zero), {
        unusedFallbacks.incrementAndGet()
        envWith(constant, zero)
      }
    )
    val second = constant.constructorResultType(
      Vector(one), {
        unusedFallbacks.incrementAndGet()
        envWith(constant, one)
      }
    )
    assert(first eq second)
    assert(ValueEquivalence.defEq(first, nat))
    assertEquals(unusedFallbacks.get(), 0)

    val dependent = evaluatedPi("{ (n: Nat) -> Eq(Nat, n, n) }")
    val firstVar = FreshVar.freshVar("first", nat)
    val secondVar = FreshVar.freshVar("second", nat)
    val firstResult = dependent.constructorResultType(Vector(firstVar), envWith(dependent, firstVar))
    val secondResult = dependent.constructorResultType(Vector(secondVar), envWith(dependent, secondVar))
    assertNotEquals(firstResult.key, secondResult.key)

    val nested = evaluatedPi("{ (x: Nat) -> ((y: Nat) -> Eq(Nat, x, x)) }")
    val nestedFirst = nested.constructorResultType(Vector(firstVar), envWith(nested, firstVar))
    val nestedSecond = nested.constructorResultType(Vector(secondVar), envWith(nested, secondVar))
    assertNotEquals(nestedFirst.key, nestedSecond.key)

    val solved = EqStore.empty.allow(DepSet(firstVar.id)).addLink(firstVar.id, VPacked.nat(3, nat))
    val refinedResult = ValueOps.materialize(firstResult, solved)
    assert(!ValueEquivalence.defEq(firstResult, refinedResult))

    val captures = evaluatedPi("{ (n: Nat) -> ((x: Nat) -> Eq(Nat, n, n)) }")
    val capturedVar = FreshVar.freshVar("captured", nat)
    val inner = captures.codomain(envWith(captures, capturedVar)).asInstanceOf[VPi]
    val innerArg = VPacked.nat(0, nat)
    val innerResult = inner.constructorResultType(Vector(innerArg), envWith(inner, innerArg))
    assert(innerResult.synDeps.contains(capturedVar.id))
    val captureStore = EqStore.empty.allow(DepSet(capturedVar.id)).addLink(capturedVar.id, VPacked.nat(4, nat))
    val materializedInner = ValueOps.materialize(inner, captureStore).asInstanceOf[VPi]
    val materializedArg = VPacked.nat(0, nat)
    val materializedResult = materializedInner.constructorResultType(
      Vector(materializedArg),
      envWith(materializedInner, materializedArg)
    )
    assert(ValueEquivalence.defEq(ValueOps.materialize(innerResult, captureStore), materializedResult))
    assert(!materializedResult.synDeps.contains(capturedVar.id))
  }

  test("constructor eligibility and result caching are lazy, per VPi, thread-safe, and copy-safe") {
    implicit val executionContext: ExecutionContext = ExecutionContext.global
    val calls = new AtomicInteger
    val binders = Vector(binder("x", 70001, BinderMode.Explicit))
    val codomain = checkedCodomain(binders, independent = true) { _ =>
      calls.incrementAndGet()
      nat
    }
    val pi = manualPi(binders, codomain)
    val argument = VPacked.nat(0, nat)
    val skippedFallbacks = new AtomicInteger
    assertEquals(calls.get(), 0)
    val tasks = Vector.fill(16)(
      Future(
        pi.constructorResultType(
          Vector(argument), {
            skippedFallbacks.incrementAndGet()
            Env.empty
          }
        )
      )
    )
    val results = Await.result(Future.sequence(tasks), 10.seconds)
    assertEquals(calls.get(), 1)
    assertEquals(skippedFallbacks.get(), 0)
    assert(results.forall(_ eq results.head))

    val copied = pi.copy(env = Env.empty)
    copied.constructorResultType(Vector(argument), Env.empty)
    copied.constructorResultType(Vector(argument), Env.empty)
    assertEquals(calls.get(), 2)

    val fallbackCalls = new AtomicInteger
    val changedCode = pi.copy(codomain = _ => {
      calls.incrementAndGet()
      nat
    })
    changedCode.constructorResultType(
      Vector(argument), {
        fallbackCalls.incrementAndGet()
        Env.empty
      }
    )
    changedCode.constructorResultType(
      Vector(argument), {
        fallbackCalls.incrementAndGet()
        Env.empty
      }
    )
    assertEquals(calls.get(), 4)
    assertEquals(fallbackCalls.get(), 2)

    val changedBinders = pi.copy(binders = Vector(binder("replacement", 70002, BinderMode.Explicit)))
    changedBinders.constructorResultType(
      Vector(argument), {
        fallbackCalls.incrementAndGet()
        Env.empty
      }
    )
    changedBinders.constructorResultType(
      Vector(argument), {
        fallbackCalls.incrementAndGet()
        Env.empty
      }
    )
    assertEquals(calls.get(), 6)
    assertEquals(fallbackCalls.get(), 4)

    val ordinaryCalls = new AtomicInteger
    val ordinary = manualPi(
      binders,
      _ => {
        ordinaryCalls.incrementAndGet()
        nat
      }
    )
    ordinary.constructorResultType(
      Vector(argument), {
        fallbackCalls.incrementAndGet()
        Env.empty
      }
    )
    ordinary.constructorResultType(
      Vector(argument), {
        fallbackCalls.incrementAndGet()
        Env.empty
      }
    )
    assertEquals(ordinaryCalls.get(), 2)
    assertEquals(fallbackCalls.get(), 6)
  }

  test("constructor and neutral application metadata reuse interleaved evidence layouts") {
    val binders = Vector(
      binder("left", 71001, BinderMode.Explicit),
      binder("proof", 71002, BinderMode.Evidence),
      binder("right", 71003, BinderMode.Explicit)
    )
    val pi = manualPi(binders, _ => nat)
    assertEquals(pi.determiningArgIndices, Vector(0, 2))

    val propositionPi = evaluatedPi("{ (n: Nat) -> Eq(Nat, n, n) }")
    val propositionVar = FreshVar.freshVar("proof-index", nat)
    val proposition = propositionPi.codomain(envWith(propositionPi, propositionVar))
    val evidenceRuns = new AtomicInteger
    def deferred: DeferredEvidence = new DeferredEvidence(() => {
      evidenceRuns.incrementAndGet()
      proposition
    })

    val left = FreshVar.freshVar("left-value", nat)
    val right = FreshVar.freshVar("right-value", nat)
    val constructor = ConstructorHead("Metadata.mk", 0, 3, pi)
    assertEquals(constructor.determiningStoredArgIndices, Vector(0, 2))
    val first = VApp(constructor, Vector(left, deferred, right), nat)
    val second = VApp(constructor, Vector(left, deferred, right), nat)
    assertEquals(first.determiningArgs, Vector(left, right))
    assertEquals(first.synDeps, left.synDeps ++ right.synDeps)
    assertEquals(first.key, second.key)
    assert(ValueEquivalence.defEq(first, second))

    val neutralHead = VConst("metadataFunction", Symbol, pi)
    val neutral = VApp(neutralHead, Vector(left, deferred, right), nat)
    assertEquals(neutral.determiningArgs, Vector(left, right))
    assertEquals(neutral.synDeps, left.synDeps ++ right.synDeps)
    assertEquals(neutral.key, VApp(neutralHead, Vector(left, deferred, right), nat).key)
    assertEquals(evidenceRuns.get(), 0)
  }

  test("CharList scalar keys match the previous sequential mix exactly") {
    val scalars = Vector(0, 65, 0x7f, 0x80, 0x1f642, 0x10ffff)
    val seed = ValueKey.constructorName("char-list-key-seed")
    val previous = scalars.foldLeft(ValueKey.mixLong(seed, scalars.length.toLong)) { (key, scalar) =>
      ValueKey.mixLong(key, scalar.toLong & 0xffffffffL)
    }
    assertEquals(ValueKey.mixCharScalars(seed, scalars), previous)
  }
}
