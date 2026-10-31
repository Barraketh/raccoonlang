package com.raccoonlang

import com.raccoonlang.Value._
import com.raccoonlang.packed.{Token, Words, Zipped}
import com.raccoonlang.telescope.BinderOps

object ValueEquivalence {
  sealed trait UnificationFailure {
    def left: Value
    def right: Value
  }

  object UnificationFailure {
    final case class Contradiction(left: Value, right: Value) extends UnificationFailure
    final case class Stuck(left: Value, right: Value) extends UnificationFailure
  }

  def defEq(v1: Value, v2: Value): Boolean =
    DefEq.defEq(v1, v2)

  private def isProof(value: Value): Boolean =
    value.tpe.tpe == PropTpe

  def unify(v1: Value, v2: Value, meta: EqStore): EqStore =
    tryUnify(v1, v2, meta) match {
      case Right(eqStore) => eqStore
      case Left(failure)  => throw UnificationFailed(failure.left, failure.right)
    }

  /**
   * Unify only through structure whose injectivity entails the resulting equalities. A Stuck result cannot justify
   * omitting a match branch, and failed attempts expose no partial substitutions.
   */
  def tryUnify(
      v1: Value,
      v2: Value,
      store: EqStore
  ): Either[UnificationFailure, EqStore] =
    Unify.tryUnify(v1, v2, store)

  private object DefEq {
    private def sameBinderShape(left: VBinder, right: VBinder): Boolean =
      left.isInstance == right.isInstance && left.captures.length == right.captures.length &&
        left.captures.zip(right.captures).forall { case (a, b) =>
          a.root == b.root && a.path == b.path && a.captureType == b.captureType
        }

    private def defEqPi(pi1: VPi, pi2: VPi): Option[Vector[Value]] = {
      // Matching one telescope's fresh arguments against another proves only
      // inclusion unless their capture operations also agree. For example,
      // Sort($u) and Sort(succ($v)) admit different universe domains.
      if (
        pi1.binders.length != pi2.binders.length ||
        !pi1.binders.zip(pi2.binders).forall { case (b1, b2) => sameBinderShape(b1, b2) }
      )
        return None

      val nextEnv1 = BinderOps.freshen(pi1)
      val sharedVars = pi1.binders.map(binder => nextEnv1(binder.localRef))
      val nextEnv2 = BinderOps.tryCheckAndInstantiate(pi2.binders, pi2.env, sharedVars).getOrElse(return None)
      // Agreeing capture operations make the inclusion an equality only at family heads, where a capture's position
      // holds the head's argument. At a head that computes, `(xs: SList($A))` opens like `(xs: List($A))` but admits
      // only copyable A, so the generic arguments of the second telescope must fit the first as well.
      val reverseEnv = BinderOps.freshen(pi2)
      val reverseVars = pi2.binders.map(binder => reverseEnv(binder.localRef))
      if (BinderOps.tryCheckAndInstantiate(pi1.binders, pi1.env, reverseVars).isEmpty) return None

      val out1 = pi1.codomain(nextEnv1)
      val out2 = pi2.codomain(nextEnv2)

      if (defEq(out1, out2)) Some(sharedVars) else None
    }

    private def defEqLamId(id1: ValueId, id2: ValueId): Boolean = {
      (id1, id2) match {
        case (ValueId.Const(n1), ValueId.Const(n2)) if n1 == n2 => true
        case (l1: ValueId.LocalId, l2: ValueId.LocalId)
            if l1.nodeId == l2.nodeId && l1.captures.length == l2.captures.length =>
          l1.captures.zip(l2.captures).forall { case (v1, v2) => defEq(v1, v2) }
        case _ => false
      }
    }

    private def isNative(lam: VLam): Boolean = lam.body.isInstanceOf[LamBody.Native]

    /**
     * A recursive function as the fixpoint it is: `members` is its block, in the block's order, and it is member
     * `index`; a recursive definition is the one member of its own, read through its self slot, not through a peer slot
     * (`mutual`). Its body reaches its block only through those slots, never by name, since a definition is checked
     * before it is published.
     */
    private final case class Fixpoint(members: Vector[VLam], index: Int, mutual: Boolean)

    private object Fixpoint {
      def of(lam: VLam): Option[Fixpoint] =
        lam.body match {
          case LamBody.Core(term, _) if term.recursiveSelf.isDefined => Some(Fixpoint(Vector(lam), 0, mutual = false))
          case LamBody.Core(term, env) if term.recursivePeers.nonEmpty =>
            val index = lam.id match {
              case ValueId.Const(name) => term.recursivePeers.indexWhere(_._2 == name)
              case _: ValueId.LocalId  => -1
            }
            // Every member of a block is a recursive lambda over that block (`Interpreter.evalDecl`).
            Some(
              Fixpoint(term.recursivePeers.map { case (_, name) => env(name).asInstanceOf[VLam] }, index, mutual = true)
            )
          case _ => None
        }
    }

    /**
     * Two fixpoints convert when they are the same member of blocks of one shape whose members' bodies convert pairwise
     * with the blocks' recursive slots bound to shared fresh variables, one for each pair of members, as `fix` bodies
     * compare (Coq's conversion of mutual fixpoints). Unfolding the slots to the functions instead would compare the
     * same pair again inside the bodies' stuck matches, which capture them, without end. It is sound: the paired
     * variables stand for any common values of the slots, so the blocks' bodies are one function of their recursive
     * slots, and the blocks, which are its fixpoints and terminate, are the same functions. A pair of different shapes
     * does not convert.
     */
    private def defEqFixpoints(f1: Fixpoint, f2: Fixpoint): Boolean =
      f1.mutual == f2.mutual && f1.index >= 0 && f1.index == f2.index && f1.members.length == f2.members.length && {
        val pairs = f1.members.zip(f2.members)
        // Each pair's shared arguments, while every pair so far has one type.
        val opened = pairs.foldLeft(Option(Vector.empty[Vector[Value]])) { case (done, (m1, m2)) =>
          done.flatMap { args =>
            if (m1.tpe.binders.length != m2.tpe.binders.length) None else defEqPi(m1.tpe, m2.tpe).map(args :+ _)
          }
        }
        opened.exists { args =>
          // Every pair has one type, so a variable of the first member's type stands for both.
          val shared = f1.members.map(member => FreshVar.freshVar(PrettyPrinter.print(member), member.tpe))
          pairs.lazyZip(args).forall { case ((m1, m2), memberArgs) =>
            defEq(
              Interpreter.runLamOnRecursive(m1, memberArgs, shared),
              Interpreter.runLamOnRecursive(m2, memberArgs, shared)
            )
          }
        }
      }

    private def sameValueObject(v1: Value, v2: Value): Boolean =
      v1.asInstanceOf[AnyRef] eq v2.asInstanceOf[AnyRef]

    private def shouldTryStructuralDefEq(a: Value, b: Value): Boolean =
      a.needsStructuralDefEq || b.needsStructuralDefEq

    private def proofIrrelevant(a: Value, b: Value): Boolean =
      isProof(a) && defEq(a.tpe, b.tpe)

    private def defEqStructural(a: Value, b: Value): Boolean =
      (a, b) match {
        // Structurally, a suspended proof is its forced value, which comparing keys has computed already (docs/
        // kernel.md, "Proof calls"). Proofs of convertible propositions never get here.
        case (proof: VSuspendedProof, _) => defEq(Interpreter.force(proof), b)
        case (_, proof: VSuspendedProof) => defEq(a, Interpreter.force(proof))
        case (PropTpe, PropTpe)          => true
        case (LevelTpe, LevelTpe)        => true
        case (KindTpe, KindTpe)          => true
        case (l1: Level, l2: Level)      => l1 == l2 || Level.leq(l1, l2) && Level.leq(l2, l1)
        // Kinds are in normal form, so equal kinds are equal values.
        case (k1: Kind, k2: Kind)                                         => k1 == k2
        case (VUniv(k1, l1), VUniv(k2, l2))                               => defEq(k1, k2) && defEq(l1, l2)
        case (VConst(n1, _, _), VConst(n2, _, _)) if n1 == n2             => true
        case (p1: VPi, p2: VPi) if p1.binders.length == p2.binders.length => defEqPi(p1, p2).isDefined
        case (l1: VLam, l2: VLam) if l1.tpe.binders.length == l2.tpe.binders.length =>
          if (l1.eq(l2) || defEqLamId(l1.id, l2.id)) true
          // Distinct native lambdas never convert: builtins are extensionally different functions (see Builtins), and
          // other natives, such as termination-checking stand-ins, are opaque. Opening a stuck native on fresh
          // arguments would only return its own application again.
          else if (isNative(l1) && isNative(l2)) false
          else
            (Fixpoint.of(l1), Fixpoint.of(l2)) match {
              case (Some(f1), Some(f2)) => defEqFixpoints(f1, f2)
              // At most one recursive function, opened with its slots bound to its block. Only its own slots lead back
              // to it, so the comparison meets it again only against values the other function's code builds, from its
              // arguments and its closure, and opening those, when they are not recursive, runs out; a recursive one
              // among them is a pair of fixpoints.
              case _ =>
                defEqPi(l1.tpe, l2.tpe)
                  .exists(vars => defEq(Interpreter.runLam(l1, vars), Interpreter.runLam(l2, vars)))
            }

        case (l: VWord, r: VWord) => defEqWords(l, r)

        case (v1: VApp, v2: VApp) if v1.args.length == v2.args.length =>
          defEq(v1.head, v2.head) &&
          (v1.args.zip(v2.args).forall { case (arg1, arg2) => defEq(arg1, arg2) } ||
            // A stuck kernel beq has two Nat arguments ordered by key. Convertible atoms can have different keys and
            // reverse that order, so structural conversion also admits the symmetric orientation.
            (v1.head eq Kernel.beq) && defEq(v1.args(0), v2.args(1)) && defEq(v1.args(1), v2.args(0))) &&
          defEq(v1.tpe, v2.tpe) // Important for constructors

        case (_: VNatPoly, _) | (_, _: VNatPoly) => NatNormalForm.equivalent(a, b)

        case (c1: ConstructorHead, c2: ConstructorHead) if c1.name == c2.name => true

        // One code on convertible captures evaluates alike (`Value.MatchId`).
        case (s1: NeutralThunk, s2: NeutralThunk) =>
          (s1.id.code eq s2.id.code) && s1.id.captures.length == s2.id.captures.length &&
          s1.id.captures.lazyZip(s2.id.captures).forall(defEq)

        case (Var(_, id1, _), Var(_, id2, _)) if id1 == id2 => true
        case _                                              => false
      }

    /**
     * Two words whose keys differ, compared layer by layer in one loop (`Words.zip`): convertible words have
     * convertible layers, of the same constructor with convertible payloads, in order, then convertible ends. The layer
     * types need no comparison, since every layer of a word has its end's type. An end is never a word, so words of
     * different lengths never convert and are rejected before the walk; words of one length end together, and their
     * ends remain to compare.
     */
    private def defEqWords(left: VWord, right: VWord): Boolean =
      Words.sameLength(left, right) &&
        (Words.zip(left, right)((l, r) =>
          ((l.head eq r.head) || l.head.name == r.head.name) && payloadsConvert(l, r)
        ) match {
          case Zipped.Refused      => false
          case Zipped.Agreed       => true
          case rests: Zipped.Rests => defEq(rests.left, rests.right)
        })

    // Two layers of one constructor, which therefore have the same payload width.
    private def payloadsConvert(left: Token, right: Token): Boolean = {
      var index = 0
      while (index < left.payloadWidth) {
        if (!defEq(left.payload(index), right.payload(index))) return false
        index += 1
      }
      true
    }

    def defEq(v1: Value, v2: Value): Boolean = {
      sameValueObject(v1, v2) || proofIrrelevant(v1, v2) ||
      v1.key == v2.key || (shouldTryStructuralDefEq(v1, v2) && defEqStructural(v1, v2)) || defEqEta(v1, v2)
    }

    /**
     * Structure eta: a constructor-headed value and one that is not, at one eligible type, convert when the stored
     * fields convert with the other's projections (`StructEta`).
     */
    private def defEqEta(v1: Value, v2: Value): Boolean =
      StructEta.fieldPairs(v1, v2).exists { pairs =>
        defEq(v1.tpe, v2.tpe) && pairs.forall { case (a, b) => defEq(a, b) }
      }
  }

  private object Unify {
    import UnificationFailure._

    private type Result = Either[UnificationFailure, EqStore]

    private def stuck(left: Value, right: Value): Result = Left(Stuck(left, right))

    // Broad idea: we can unify (v + k) = other as v = other - k.  Everything else fails.
    private def unifyLevels(l1: Level, l2: Level, meta: EqStore): Option[EqStore] = {
      if (l1.atoms.size == 1 && l1.c == 0) {
        val (varId, k) = l1.atoms.head
        if (meta.isRefinable(varId) && !meta.occurs(varId, l2) && Level.geq(l2, k)) {
          val other = Level.addOffset(l2, -k)
          Some(meta.addLink(varId, other))
        } else None
      } else None
    }

    // A kind that is one refinable variable may be solved as any kind it does not occur in.
    private def unifyKinds(k1: Kind, k2: Kind, meta: EqStore): Option[EqStore] =
      if (!k1.lin && k1.vars.size == 1) {
        val varId = k1.vars.head
        if (meta.isRefinable(varId) && !k2.vars.contains(varId)) Some(meta.addLink(varId, k2)) else None
      } else None

    /** Different constant kinds are apart; a kind that is one refinable variable may be solved. */
    private def unifyKindValues(k1: Kind, k2: Kind, meta: EqStore): Result =
      if (k1 == k2) Right(meta)
      else if (k1.vars.isEmpty && k2.vars.isEmpty) Left(Contradiction(k1, k2))
      else unifyKinds(k1, k2, meta).orElse(unifyKinds(k2, k1, meta)).toRight(Stuck(k1, k2))

    private def tryLinkVar(v: Var, other: Value, meta: EqStore): Result = {
      // A variable is linked only to a value of its own type, which may solve the type's levels.
      val m1 =
        tryUnify(v.tpe, other.tpe, meta) match {
          case Right(next)  => next
          case Left(failed) => return Left(failed)
        }
      m1.linkable(v.id, other) match {
        case Some(target) => Right(m1.addLink(v.id, target))
        case None         => Left(Stuck(v, other))
      }
    }

    /**
     * Prefer named vars because anonymous fields lack local slots for quotation.
     */
    private def tryLinkVarToPreferredRepresentative(v1: Var, v2: Var, meta: EqStore): Result = {
      val v1Anonymous = v1.name == "_"
      val v2Anonymous = v2.name == "_"
      val (toLink, representative) =
        if (v1Anonymous && !v2Anonymous) (v1, v2)
        else if (v2Anonymous && !v1Anonymous) (v2, v1)
        else if (v1.id > v2.id) (v1, v2)
        else (v2, v1)

      tryLinkVar(toLink, representative, meta)
    }

    private def tryUnifyPairs(pairs: Vector[(Value, Value)], meta: EqStore): Result = {
      var current = meta
      val iter = pairs.iterator
      while (iter.hasNext) {
        val (left, right) = iter.next()
        tryUnify(left, right, current) match {
          case Left(failure) => return Left(failure)
          case Right(next)   => current = next
        }
      }
      Right(current)
    }

    private def sameInductiveFamily(left: Value, right: Value): Boolean =
      (left, right) match {
        case (InductiveFamilyValue(f1), InductiveFamilyValue(f2)) => f1.head.name == f2.head.name
        case _                                                    => false
      }

    private sealed trait RigidForm
    private case object DataConstructor extends RigidForm
    private case object TypeFamily extends RigidForm
    private case object FunctionType extends RigidForm
    private case object TypeUniverse extends RigidForm

    // Exhaustive over Value: adding a representation requires deciding whether
    // it supplies no-confusion evidence. Partial family/constructor heads are
    // functions; ordinary applications, symbols and blocked matches are opaque.
    private def rigidForm(value: Value): Option[RigidForm] = value match {
      case VCtor(_, _, _) if !isProof(value) => Some(DataConstructor)
      // A list-shaped family is never a proposition family, so a word is never a proof.
      case _: VWord => Some(DataConstructor)
      // Families of every kind are nominal.
      case InductiveFamilyValue(_) if value.tpe.isInstanceOf[VUniv] => Some(TypeFamily)
      case pi: VPi  => if (pi.tpe == PropTpe) None else Some(FunctionType)
      case _: VUniv => Some(TypeUniverse)
      // A suspended proof is a proof, as `VCtor` proofs above are no rigid form either.
      case _: Var | _: NeutralThunk | _: VLam | _: VConst | _: VApp | _: ConstructorHead | _: VNatPoly |
          _: VSuspendedProof =>
        None
      // Level and kind arithmetic and these primitive forms have no nominal apartness rule.
      case _: Level | LevelTpe | _: Kind | KindTpe | PropTpe | KernelObject => None
    }

    private def isConstructorData(value: Value): Boolean =
      value match {
        case VCtor(_, _, _) => true
        case _: VWord       => true
        case _              => false
      }

    /**
     * Constructor against constructor, both materialized and not both words: different constructors of one family
     * contradict, and the same constructor unifies its stored fields in order, then the result types. A cons is always
     * a word, so a word here meets a different constructor.
     */
    private def unifyConstructors(a: Value, b: Value, meta: EqStore): Result = {
      val (h1, fields1) = ConstructorValue.unapply(a).get
      val (h2, fields2) = ConstructorValue.unapply(b).get
      if (h1.name != h2.name) {
        if (sameInductiveFamily(a.tpe, b.tpe)) Left(Contradiction(a, b)) else stuck(a, b)
      } else if (fields1.length != fields2.length) stuck(a, b)
      else {
        val types = if (a.tpe eq b.tpe) Vector.empty else Vector(a.tpe -> b.tpe)
        tryUnifyPairs(fields1.zip(fields2) ++ types, meta)
      }
    }

    /**
     * Two words, both materialized, in one loop over their aligned layers (`Words.zip`), so a word of many layers does
     * not recurse. Two layers of different constructors contradict when they belong to one family, which can only
     * happen at the first pair. Two layers of one constructor unify the payloads before the recursive field at once;
     * the payloads after it and the layers' types wait on a stack until the rests are done, preserving the order of the
     * constructor rule. The walk stops at rests with equal keys, which convert, and rests where either word ended are
     * unified as usual. Rests of materialized words are materialized too.
     */
    private def unifyWords(left: VWord, right: VWord, meta: EqStore): Result = {
      val deferred = scala.collection.mutable.ArrayBuffer.empty[Vector[(Value, Value)]]
      var store = meta
      var failure: UnificationFailure = null
      def record(result: Result): Boolean =
        result match {
          case Left(failed) =>
            failure = failed
            false
          case Right(next) =>
            store = next
            true
        }
      def pairs(l: Token, r: Token, from: Int, until: Int): Vector[(Value, Value)] =
        (from until until).map(index => l.payload(index) -> r.payload(index)).toVector
      val rests = Words.zip(left, right)((l, r) =>
        if (l.head.name != r.head.name) {
          failure = if (sameInductiveFamily(l.tpe, r.tpe)) Contradiction(l.rest, r.rest) else Stuck(l.rest, r.rest)
          false
        } else
          record(tryUnifyPairs(pairs(l, r, 0, l.recursiveIndex), store)) && {
            val types = if (l.tpe eq r.tpe) Vector.empty else Vector(l.tpe -> r.tpe)
            val after = pairs(l, r, l.recursiveIndex, l.payloadWidth) ++ types
            if (after.nonEmpty) deferred += after
            true
          }
      )
      val restsUnify = rests match {
        case Zipped.Refused      => false
        case Zipped.Agreed       => true
        case rests: Zipped.Rests => record(tryUnify(rests.left, rests.right, store))
      }
      if (!restsUnify) return Left(failure)
      var index = deferred.length - 1
      while (index >= 0) {
        if (!record(tryUnifyPairs(deferred(index), store))) return Left(failure)
        index -= 1
      }
      Right(store)
    }

    private object EtaPairs {
      def unapply(pair: (Value, Value)): Option[Vector[(Value, Value)]] = StructEta.fieldPairs(pair._1, pair._2)
    }

    def tryUnify(v1: Value, v2: Value, meta: EqStore): Result = {
      val a = ValueOps.materialize(v1, meta)
      val b = ValueOps.materialize(v2, meta)

      if (DefEq.defEq(a, b)) return Right(meta)
      if (isProof(a) && isProof(b)) return tryUnify(a.tpe, b.tpe, meta)

      (a, b) match {

        case (l: VWord, r: VWord) => unifyWords(l, r, meta)

        case _ if isConstructorData(a) && isConstructorData(b) => unifyConstructors(a, b, meta)

        case (InductiveFamilyValue(f1), InductiveFamilyValue(f2)) =>
          if (a.tpe == PropTpe || b.tpe == PropTpe) stuck(a, b)
          else if (f1.head.name != f2.head.name || f1.args.length != f2.args.length) Left(Contradiction(a, b))
          else tryUnifyPairs(f1.args.zip(f2.args) :+ (a.tpe -> b.tpe), meta)

        case (k1: Kind, k2: Kind) => unifyKindValues(k1, k2, meta)

        // Universes whose kinds are different constants are apart; a kind variable may be solved, and then the levels
        // unify as before kinds.
        case (VUniv(k1, l1), VUniv(k2, l2)) =>
          unifyKindValues(k1, k2, meta).flatMap { next =>
            if (defEq(l1, l2)) Right(next)
            else
              unifyLevels(l1, l2, next)
                .orElse(unifyLevels(l2, l1, next))
                .toRight(Stuck(l1, l2))
          }

        case (v1: Var, v2: Var) if meta.isRefinable(v1.id) && meta.isRefinable(v2.id) =>
          tryLinkVarToPreferredRepresentative(v1, v2, meta)

        // Link unlinked Var (left) to a non-Var value
        case (v: Var, other) if meta.isRefinable(v.id) => tryLinkVar(v, other, meta)

        // Symmetric: link unlinked Var (right) to non-Var value
        case (other, v: Var) if meta.isRefinable(v.id) => tryLinkVar(v, other, meta)

        case (_: VNatPoly, _) | (_, _: VNatPoly) => NatNormalForm.unifySuccessorPrefixes(a, b, meta)

        // Structure eta: a constructor and a value that is not unify field by field with its projections. The types
        // come first: a matched constructor's type solves its witnesses of the family parameters, which its fields'
        // types mention, so a field of an opaque type such as `Protocol.Inst(P, init)` then meets its projection at
        // one type instead of being stuck.
        case EtaPairs(pairs) => tryUnifyPairs((a.tpe -> b.tpe) +: pairs, meta)

        case _ =>
          (rigidForm(a), rigidForm(b)) match {
            case (None, _) | (_, None) => stuck(a, b)
            // Two Pis have no injectivity rule. Other equal-form pairs were
            // handled structurally above; classification alone cannot refute them.
            case (Some(left), Some(right)) if left == right => stuck(a, b)
            // The remaining canonical forms are disjoint by no-confusion/N3.
            case (Some(_), Some(_)) => Left(Contradiction(a, b))
          }
      }
    }
  }
}
