package com.raccoonlang.telescope

import com.raccoonlang.Value._
import com.raccoonlang._

/**
 * Directional matcher for type patterns (docs/type-patterns.md section 5). The expected side is the opened
 * pattern value — capture atoms inside rigid structure — and the actual side is the argument's type, which
 * is read-only input. Matching walks the expected value's presentation:
 *
 *   - a capture atom is assigned the actual piece at its position, after its declared type accepts the
 *     piece's type (recursively matched when the declared type still contains captures, a cumulativity
 *     check when it is rigid);
 *   - capture-free pieces are decided by definitional equality, never by solving;
 *   - application spines decompose positionally with the actual's presentation; a capture atom in head
 *     position applied to distinct rigid variables solves by lambda abstraction (the higher-order matching
 *     fragment — the unique solution, no search);
 *   - level positions admit one arithmetic form, a single capture plus a constant offset;
 *   - Pi values relate binder-wise: the actual side's own pattern binders open as rigid skolems, both
 *     binders are entered at one shared fresh atom, and the codomains recurse. Skolems and shared atoms are
 *     match-local; the V-closed watermark in `solveOpenedCaptures` rejects solutions that mention them.
 *
 * Unlike unification there is no refinement of the actual side, no flex-flex case, and no postponement:
 * every rule either consumes a fixed position of the presentation or fails. Patterns whose openings present
 * shapes this matcher cannot traverse are rejected at declaration time (`TypePatternOps.validateMatchable`).
 */
object TypePatternMatcher {
  private val SyntheticSpan = Span(0, 0)

  private[raccoonlang] def matchBinderPattern(
      opened: TypePatternOps.OpenedBinderPattern,
      actual: Value,
      normalizerMap: Normalizers.NormalizerMap
  ): EqStore =
    matchValue(opened.value, actual, EqStore.empty.allow(opened.captureDeps))(normalizerMap)

  private def matchFailed(expected: Value, actual: Value): Nothing = throw TypeMismatch(expected, actual)

  private def matchValue(expected: Value, actual: Value, subst: EqStore)(implicit
      normalizerMap: Normalizers.NormalizerMap
  ): EqStore = {
    val materialized = ValueOps.materialize(expected, subst)
    if (!materialized.synDeps.intersects(subst.refinable)) {
      if (ValueEquivalence.defEq(materialized, actual, normalizerMap, propIrrelevant = true)) subst
      else matchFailed(materialized, actual)
    } else {
      val normalizerF = ValueEquivalence.normalizerFor(materialized, actual, normalizerMap)
      val e = normalizerF(materialized)
      val a = normalizerF(actual)

      e match {
        case atom @ Var(_, id, _) if subst.isRefinable(id) =>
          linkCapture(atom, a, subst)

        case level: Level =>
          a match {
            case actualLevel: Level => matchLevel(level, actualLevel, subst)
            case _                  => matchFailed(e, a)
          }

        case VSort(level) =>
          a match {
            case VSort(actualLevel) => matchLevel(level, actualLevel, subst)
            case _                  => matchFailed(e, a)
          }

        case app: VApp =>
          trySolveFlexSpine(app, a, subst).getOrElse {
            a match {
              case actualApp: VApp if actualApp.args.length == app.args.length =>
                var cur = matchValue(app.head, actualApp.head, subst)
                app.args.zip(actualApp.args).foreach { case (arg, actualArg) =>
                  cur = matchValue(arg, actualArg, cur)
                }
                matchValue(app.tpe, actualApp.tpe, cur)
              case _ => matchFailed(e, a)
            }
          }

        case pi: VPi =>
          a match {
            case actualPi: VPi if actualPi.binders.length == pi.binders.length => matchPi(pi, actualPi, subst)
            case _                                                             => matchFailed(e, a)
          }

        case _ => matchFailed(e, a)
      }
    }
  }

  // Assignment classifies first: the capture's declared type must accept the solution's type. A declared
  // type still holding captures is matched (this is how hidden head-telescope captures and `of` chains
  // solve); a rigid one is a cumulativity check.
  private def linkCapture(atom: Var, actual: Value, subst: EqStore)(implicit
      normalizerMap: Normalizers.NormalizerMap
  ): EqStore = {
    val atomTpe = ValueOps.materialize(atom.tpe, subst)
    val next =
      if (atomTpe.synDeps.intersects(subst.refinable)) matchValue(atomTpe, actual.tpe, subst)
      else {
        TypeChecker.checkFits(actual.tpe, atomTpe, normalizerMap)
        subst
      }
    next.addLink(atom.id, actual)
  }

  private def matchLevel(expected: Level, actual: Level, subst: EqStore): EqStore =
    if (!expected.synDeps.intersects(subst.refinable)) {
      if (Level.leq(expected, actual) && Level.leq(actual, expected)) subst
      else matchFailed(expected, actual)
    } else
      expected.atoms.toList match {
        case (id, offset) :: Nil if expected.c == 0 && subst.isRefinable(id) && Level.geq(actual, offset) =>
          subst.addLink(id, Level.addOffset(actual, -offset))
        case _ => matchFailed(expected, actual)
      }

  // A capture atom in head position applied to distinct rigid variables has a unique solution: the actual
  // piece abstracted over those variables (higher-order pattern matching). Quote failure falls through to
  // the ordinary spine rule.
  private def trySolveFlexSpine(app: VApp, actual: Value, subst: EqStore)(implicit
      normalizerMap: Normalizers.NormalizerMap
  ): Option[EqStore] =
    app.head match {
      case head @ Var(_, id, _) if subst.isRefinable(id) =>
        val pi =
          head.tpe match {
            case pi: VPi => pi
            case _       => return None
          }
        if (pi.binders.length != app.args.length) return None
        if (!isRigidSpine(app.args, subst)) return None
        // An actual spine over the same variables relates head-to-head (the plain spine rule); abstraction
        // would only eta-expand it, and α-equivalence checks need the bare head link.
        if (sameSpineArgs(app.args, actual)) return None

        val next = matchValue(app.tpe, actual.tpe, subst)
        val materializedPi =
          ValueOps.materialize(pi, next) match {
            case pi: VPi => pi
            case _       => return None
          }
        val materializedArgs = app.args.map(arg => ValueOps.materialize(arg, next))
        val materializedActual = ValueOps.materialize(actual, next)
        try Some(next.addLink(id, ValueQuote.quoteLambda(materializedPi, materializedArgs, materializedActual, SyntheticSpan)))
        catch {
          case _: CannotQuoteValue => None
        }
      case _ => None
    }

  private def isRigidSpine(args: Vector[Value], subst: EqStore): Boolean = {
    var seen = Set.empty[VarId]
    args.forall {
      case arg: Var if !subst.isRefinable(arg.id) && !seen(arg.id) =>
        seen += arg.id
        true
      case _ => false
    }
  }

  private def sameSpineArgs(args: Vector[Value], actual: Value): Boolean =
    actual match {
      case actualApp: VApp if actualApp.args.length == args.length =>
        args.zip(actualApp.args).forall {
          case (Var(_, id1, _), Var(_, id2, _)) => id1 == id2
          case _                                => false
        }
      case _ => false
    }

  /**
   * α-equivalence of two binder patterns (docs/type-patterns.md section 7): matching one opening against
   * the other must solve every capture to a distinct fresh atom of the other side — a pure renaming. A
   * capture solved to structure (or to anything ambient) means the two patterns put flexibility in
   * different places and the types are not equal.
   */
  private[raccoonlang] def matchesUpToRenaming(
      expected: TypePatternOps.OpenedBinderPattern,
      actual: TypePatternOps.OpenedBinderPattern,
      normalizerMap: Normalizers.NormalizerMap
  ): Option[EqStore] =
    try {
      val store = matchBinderPattern(expected, actual.value, normalizerMap)
      if (isRenaming(store, actual.captureDeps)) Some(store) else None
    } catch {
      case _: TypeError => None
    }

  private def isRenaming(store: EqStore, targetAtoms: DepSet): Boolean = {
    var seen = Set.empty[VarId]
    store.subst.values.forall { solution =>
      val atomId =
        solution match {
          case Var(_, id, _) => Some(id)
          case level: Level if level.c == 0 && level.atoms.sizeIs == 1 && level.atoms.head._2 == 0 =>
            Some(level.atoms.head._1)
          case _ => None
        }
      atomId.exists { id =>
        val fresh = targetAtoms.contains(id) && !seen.contains(id)
        if (fresh) seen += id
        fresh
      }
    }
  }

  /**
   * Directional instantiation (docs/type-patterns.md section 7): a pattern Pi is usable at a target Pi iff
   * matching the pattern against the target succeeds with solutions over the target alone — nothing
   * allocated during the match (skolems, shared atoms, or the pattern's own capture atoms) may appear in a
   * solution.
   */
  private[raccoonlang] def instantiates(patternPi: VPi, target: VPi, normalizerMap: Normalizers.NormalizerMap): Boolean = {
    val watermark = FreshVar.currentId
    try {
      val store = matchPi(patternPi, target, EqStore.empty)(normalizerMap)
      store.subst.values.forall { solution =>
        val deps = ValueOps.materialize(solution, store).synDeps
        deps.isEmpty || deps.max <= watermark
      }
    } catch {
      case _: TypeError => false
    }
  }

  private def matchPi(expectedPi: VPi, actualPi: VPi, subst: EqStore)(implicit
      normalizerMap: Normalizers.NormalizerMap
  ): EqStore = {
    if (expectedPi.binders.zip(actualPi.binders).exists { case (b1, b2) => b1.isInstance != b2.isInstance })
      matchFailed(expectedPi, actualPi)

    var cur = subst
    var expectedEnv = expectedPi.env
    var actualEnv = actualPi.env

    expectedPi.binders.zip(actualPi.binders).foreach { case (expectedBinder, actualBinder) =>
      val openedExpected = TypePatternOps.openBinderPattern(expectedEnv, expectedBinder)
      val openedActual = TypePatternOps.openBinderPattern(actualEnv, actualBinder)
      // Pattern binders on the expected side (the instantiation entry point) contribute their capture
      // atoms; within ordinary binding the expected side is compiled and this adds nothing.
      cur = matchValue(openedExpected.value, openedActual.value, cur.allow(openedExpected.captureDeps))

      val shared = FreshVar.freshVar(expectedBinder.name, ValueOps.materialize(openedExpected.value, cur))
      val expectedKey =
        if (expectedBinder.isInstance) Some(InstanceSearch.instanceKey(expectedBinder.name, shared))
        else None
      val actualKey =
        if (actualBinder.isInstance) Some(InstanceSearch.instanceKey(actualBinder.name, shared))
        else None

      expectedEnv = ValueOps.materializeEnv(openedExpected.env, cur).putLocal(expectedBinder.localRef, shared, expectedKey)
      actualEnv = ValueOps.materializeEnv(openedActual.env, cur).putLocal(actualBinder.localRef, shared, actualKey)
    }

    matchValue(expectedPi.codomain(expectedEnv), actualPi.codomain(actualEnv), cur)
  }
}
