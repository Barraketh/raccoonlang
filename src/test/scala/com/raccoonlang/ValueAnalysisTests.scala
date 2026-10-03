package com.raccoonlang

import com.raccoonlang.CoreAst.{Term => CTerm}
import com.raccoonlang.Value._

class ValueAnalysisTests extends munit.FunSuite {
  private val span = Span(0, 0)
  private val env = Prelude.default.checkedEnv
  private val nat = env("Nat")
  private val bool = env("Bool")
  private val natBlock = nat.asInstanceOf[VConst].constType.asInstanceOf[Inductive].meta.block.key
  private var nextRef = 80000

  private def ref(name: String): CoreAst.LocalRef = {
    nextRef += 1
    CoreAst.LocalRef(nextRef, name)
  }

  private def binder(local: CoreAst.LocalRef, ty: CoreAst.Term): CoreAst.Binder =
    CoreAst.Binder(local, ty, span, CoreAst.BinderSite.Function, BinderMode.Explicit)

  private def pi(domain: CoreAst.Term, codomain: Env => Value): VPi =
    piIn(domain, codomain, env)

  private def piIn(domain: CoreAst.Term, codomain: Env => Value, closureEnv: Env): VPi =
    piAt(domain, codomain, closureEnv, ref("argument"))

  private def piAt(
      domain: CoreAst.Term,
      codomain: Env => Value,
      closureEnv: Env,
      argument: CoreAst.LocalRef
  ): VPi = {
    VPi(
      closureEnv,
      Vector(binder(argument, domain)),
      codomain,
      Kind.unr,
      Lifetime.empty,
      Lifetime.empty,
      Value.envDeps(closureEnv),
      ValueId.LocalId(NodeId.fresh(), Vector.empty),
      () => Sorts.Type,
      isPropValued = false
    )
  }

  private def familyMeta(key: InductiveBlockKey, block: InductiveBlockDescriptor, arity: Int): InductiveMeta = {
    require(block.key == key)
    InductiveMeta(Vector.empty, arity, block, None, None, None, evidenceEligible = false)
  }

  private def evalDeclarations(source: String): Env =
    LanguageParser.parseProgram(source) match {
      case Success(program, _, _) =>
        Elaborator.elab(program, Prelude.default).decls.foldLeft(env) { case (current, declaration) =>
          Interpreter.evalDecl(declaration, current)
        }
      case failure: Failure => fail(s"Failed to parse: $failure")
    }

  test("Pi occurrence and positivity share one lazy rigid codomain inspection") {
    var inspections = 0
    val functionType = pi(
      CTerm.GlobalRef("Bool", span),
      _ => {
        inspections += 1
        nat
      }
    )
    val context = ValueAnalysis.defaultResolutionContext

    assert(functionType.occurrences.containsBlock(natBlock))
    assert(!functionType.positivity.forbidsBlock(natBlock, context))
    assert(functionType.occurrences.containsBlock(natBlock))
    assertEquals(inspections, 1)
  }

  test("strict positivity rejects double-negative domains and accepts a positive codomain") {
    val context = ValueAnalysis.defaultResolutionContext
    val negative = pi(CTerm.GlobalRef("Nat", span), _ => bool)
    val inner = pi(CTerm.GlobalRef("Nat", span), _ => bool)
    val nestedRef = ref("nested")
    val outer = piIn(CTerm.LocalRef(nestedRef, span), _ => bool, env.putLocal(nestedRef, inner))
    val positive = pi(CTerm.GlobalRef("Bool", span), _ => nat)

    assert(negative.positivity.forbidsBlock(natBlock, context))
    assert(outer.positivity.forbidsBlock(natBlock, context))
    assert(!positive.positivity.forbidsBlock(natBlock, context))
  }

  test("curried type-level matches summarize the selected branch after application") {
    val declarations = evalDeclarations(
      """
        |def choose (b: Bool): (A: Type) -> Type := fun (A: Type): Type => {
        |  match b returning Type with
        |  | Bool.true => A
        |  | Bool.false => (x: A) -> Nat
        |}
        |""".stripMargin
    )
    val choose = declarations("choose")
    val context = ValueAnalysis.defaultResolutionContext
    val afterTrue = Interpreter.evalApply(choose, Vector(declarations("Bool.true")))
    val afterFalse = Interpreter.evalApply(choose, Vector(declarations("Bool.false")))
    val genericPositivity = afterFalse.positivity
    val selectedNat = Interpreter.evalApply(afterTrue, Vector(nat))
    val selectedArrow = Interpreter.evalApply(afterFalse, Vector(nat))

    assert(afterTrue.isInstanceOf[VLam])
    assert(!genericPositivity.forbidsBlock(natBlock, context))
    assert(selectedNat.occurrences.containsBlock(natBlock))
    assert(!selectedNat.positivity.forbidsBlock(natBlock, context))
    assert(selectedArrow.occurrences.containsBlock(natBlock))
    assert(selectedArrow.positivity.forbidsBlock(natBlock, context))
  }

  test("provisional family arguments resolve under each fixed-point assumption set") {
    val key = InductiveBlockKey(Vector("First", "Second"), 1)
    val provisional = ProvisionalInductiveBlockInfo(key, DepSet(0))
    val meta = familyMeta(key, provisional, arity = 1)
    val head = VConst("First", Inductive(meta), Sorts.Type)
    val parameter = FreshVar.freshVar("parameter", Sorts.Type)
    val application = VApp(head, Vector(parameter), Sorts.Type)
    val summary = application.positivity

    val initiallyPositive = ValueAnalysis.resolutionContext(Some(key), DepSet(0))
    val removedLater = ValueAnalysis.resolutionContext(Some(key), DepSet.empty)
    assert(!summary.forbidsLocal(parameter.id, initiallyPositive))
    assert(summary.forbidsLocal(parameter.id, removedLater))
    assert(summary eq application.positivity)
  }

  test("whole-block head exemptions mask every sibling member together") {
    val key = InductiveBlockKey(Vector("Left", "Right"), 0)
    val checked = CheckedInductiveBlockSchema(key, DepSet.empty)
    val leftMeta = familyMeta(key, checked, arity = 1)
    val rightMeta = familyMeta(key, checked, arity = 0)
    val left = VConst("Left", Inductive(leftMeta), Sorts.Type)
    val right = VConst("Right", Inductive(rightMeta), Sorts.Type)
    val recursiveIndex = VApp(left, Vector(right), Sorts.Type)
    val native = VLam(
      pi(CTerm.GlobalRef("Bool", span), _ => bool),
      ValueId.LocalId(NodeId.fresh(), Vector.empty),
      LamBody.Native((_, _) => env("Bool.true"), Env.empty, isRawRecursive = false)
    )
    val opaqueIndex = VApp(left, Vector(native), Sorts.Type)
    val context = ValueAnalysis.defaultResolutionContext

    assert(recursiveIndex.occurrences.containsBlock(key))
    assert(!recursiveIndex.positivity.forbidsBlock(key, context))
    assert(!opaqueIndex.positivity.forbidsBlock(key, context))
    assert(opaqueIndex.positivity.forbidsBlock(natBlock, context))
  }

  test("generic application heads omit only their direct variable target") {
    val captured = FreshVar.freshVar("captured", Sorts.Type)
    val function = FreshVar.freshVar("function", captured)
    val application = VApp(function, Vector(nat), Sorts.Type)
    val context = ValueAnalysis.defaultResolutionContext

    assert(application.positivity.forbidsLocal(captured.id, context))
    assert(!application.positivity.forbidsLocal(function.id, context))
  }

  test("closure summaries retain code globals without leaking private Pi witnesses into local dependencies") {
    val domainRef = ref("A")
    val capturedPi = piAt(
      CoreTestTerms.sortAt(CoreAst.Form.LevelZero, span),
      fresh => fresh(domainRef),
      env,
      domainRef
    ).copy(classifier0 = () => Sorts.sort(Level.one, Kind.unr, Lifetime.empty))
    val witness = capturedPi.analysisTelescope.knownResult.asInstanceOf[Var]

    val typeBinder = binder(ref("argument"), CTerm.GlobalRef("Bool", span))
    val syntaxType = CTerm.Pi(
      Vector(typeBinder),
      CTerm.GlobalRef("Bool", span),
      CoreAst.Closure.unrestricted(span),
      span,
      NodeId.fresh()
    )
    val lambdaSyntax = CTerm.Lam(
      syntaxType,
      CTerm.Body(
        Vector(
          CoreAst.Let(
            CoreAst.LetPattern.Local(ref("unused")),
            None,
            CTerm.GlobalRef("Nat", span),
            span
          )
        ),
        CTerm.GlobalRef("Bool.true", span),
        span
      ),
      span,
      NodeId.fresh(),
      name = None,
      recursion = None
    )
    val functionType = pi(CTerm.GlobalRef("Bool", span), _ => bool)
    val closure = VLam(
      functionType,
      ValueId.LocalId(NodeId.fresh(), Vector(capturedPi)),
      LamBody.Core(lambdaSyntax, env)
    )

    assert(closure.occurrences.containsBlock(natBlock))
    assert(!CoreAst.mentionsGlobal(syntaxType, Set("Nat")))
    assert(CoreAst.mentionsGlobal(lambdaSyntax.body, Set("Nat")))
    assert(!closure.occurrences.containsLocal(witness.id))
  }

  test("native lambda occurrence is locally precise and does not execute its body") {
    var executions = 0
    val unrelated = FreshVar.freshVar("unrelated", Sorts.Type)
    val functionType = pi(CTerm.GlobalRef("Bool", span), _ => bool)
    val native = VLam(
      functionType,
      ValueId.LocalId(NodeId.fresh(), Vector.empty),
      LamBody.Native(
        (_, _) => {
          executions += 1
          env("Bool.true")
        },
        Env.empty,
        isRawRecursive = false
      )
    )
    val context = ValueAnalysis.defaultResolutionContext

    assert(native.occurrences.containsBlock(natBlock))
    assert(!native.occurrences.containsLocal(unrelated.id))
    assert(native.positivity.forbidsLocal(unrelated.id, context))
    assertEquals(executions, 0)
  }

  test("identity cycles resolve conservatively and leave reusable metadata after reentry") {
    lazy val cyclic: VPi = pi(CTerm.GlobalRef("Bool", span), _ => cyclic)
    val occurrence = cyclic.occurrences
    val positivity = cyclic.positivity

    assert(occurrence.containsBlock(natBlock))
    assert(positivity.forbidsBlock(natBlock, ValueAnalysis.defaultResolutionContext))
    assert(cyclic.occurrences eq occurrence)
    assert(cyclic.positivity eq positivity)
  }

  test("shared application graphs keep permanent occurrence and positivity summaries") {
    val head = VConst("shared", Symbol, nat.tpe)
    var graph: Value = nat
    var depth = 0
    while (depth < 30) {
      graph = VApp(head, Vector(graph, graph), nat, DepSet.empty)
      depth += 1
    }
    val occurrence = graph.occurrences
    val positivity = graph.positivity

    assert(occurrence.containsBlock(natBlock))
    assert(positivity.forbidsBlock(natBlock, ValueAnalysis.defaultResolutionContext))
    assert(graph.occurrences eq occurrence)
    assert(graph.positivity eq positivity)
  }

  test("rebuilt values own fresh occurrence metadata") {
    val variable = FreshVar.freshVar("source", Sorts.Type)
    val original = VConst("Alias", Symbol, variable)
    val originalSummary = original.occurrences
    val solution = VConst("Replacement", Symbol, Sorts.Type)
    val store = EqStore.empty.allow(DepSet(variable.id)).addLink(variable.id, solution)
    val rebuilt = ValueOps.materialize(original, store).asInstanceOf[VConst]

    assert(originalSummary.containsLocal(variable.id))
    assert(!rebuilt.occurrences.containsLocal(variable.id))
    assert(originalSummary ne rebuilt.occurrences)
  }

  test("materialized Pi values inspect their rebuilt dependent environment") {
    val parameter = FreshVar.freshVar("A", Sorts.Type)
    val parameterRef = ref("A")
    val argumentRef = ref("x")
    val piEnv = env.putLocal(parameterRef, parameter)
    val dependent = VPi(
      piEnv,
      Vector(binder(argumentRef, CTerm.LocalRef(parameterRef, span))),
      _ => bool,
      Kind.unr,
      Lifetime.empty,
      Lifetime.empty,
      Value.envDeps(piEnv),
      ValueId.LocalId(NodeId.fresh(), Vector.empty),
      () => Sorts.Type,
      isPropValued = false
    )
    val originalSummary = dependent.occurrences
    val store = EqStore.empty.allow(DepSet(parameter.id)).addLink(parameter.id, nat)
    val materialized = ValueOps.materialize(dependent, store).asInstanceOf[VPi]

    assert(originalSummary.containsLocal(parameter.id))
    assert(!originalSummary.containsBlock(natBlock))
    assert(materialized.occurrences.containsBlock(natBlock))
    assert(!materialized.occurrences.containsLocal(parameter.id))
    assert(dependent.occurrences eq originalSummary)
  }
}
