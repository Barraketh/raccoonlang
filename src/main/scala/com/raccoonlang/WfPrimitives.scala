package com.raccoonlang

import com.raccoonlang.CoreAst.{Binder, Decl, LocalRef, Term}
import com.raccoonlang.Value._
import com.raccoonlang.telescope.BinderOps

/** K2's validated, uniformly sealed accessibility recursor and its propositional constructor equation. */
object WfPrimitives {
  val SealedRecName: String = "Acc.rec"
  val EquationName: String = "$raccoon.wf.Acc.rec_eq"
  val reservedNames: Set[String] = Set(SealedRecName, EquationName)

  sealed trait UniverseRole
  object UniverseRole {
    case object MotiveResult extends UniverseRole
    case object Carrier extends UniverseRole
  }

  final case class ProducerVersion(lean4Export: String, lean: String, leanCommit: String)
  val SupportedProducer: ProducerVersion =
    ProducerVersion("3.1.0", "4.24.0-rc1", "919e297292280cdb27598edd4e03437be5850221")

  final case class RecursorRule(constructorName: String, fieldCount: Int) {
    require(fieldCount >= 0, "Recursor rule field count must be non-negative")
  }

  /** Redundant Lean metadata retained by T1 and compared with facts derived from the checked declaration. */
  final case class AccExportMetadata(
      producer: ProducerVersion,
      familyName: String,
      constructorNames: Vector[String],
      numParams: Int,
      numIndices: Int,
      isRecursive: Boolean
  )

  final case class EqualityExportMetadata(
      producer: ProducerVersion,
      familyName: String,
      constructorNames: Vector[String],
      numParams: Int,
      numIndices: Int,
      isRecursive: Boolean
  )

  /** The exported type is validation input only; the installed type is always rebuilt from AccRecursorShape. */
  final case class ExportedRecursor(
      universeOrder: Vector[UniverseRole],
      tpe: Term,
      rules: Vector[RecursorRule],
      span: Span
  )

  final class ValidatedEquality private[WfPrimitives] (
      val family: VConst,
      val constructor: ConstructorHead
  )

  final class AccRecursorShape private[WfPrimitives] (
      val family: VConst,
      val constructor: ConstructorHead
  )

  final case class Installed(env: Env, recursorType: Term, equationType: Term)

  private val NoSpan = Span(0, 0)
  private final class RefSupply {
    // Generated terms are checked in environments containing elaborator locals; negative ids keep these synthetic
    // binders disjoint without depending on the process-global fresh-variable supply.
    private var nextId = -1
    def fresh(name: String): LocalRef = {
      val result = LocalRef(nextId, name)
      nextId -= 1
      result
    }
  }

  private def fail(declaration: String, reason: String, span: Span): Nothing =
    throw UnsupportedWfExportShape(declaration, reason, Some(span))

  private def concise(value: Value): String = {
    def render(current: Value, depth: Int): String =
      current match {
        case pi: VPi if depth > 0 =>
          val fresh = BinderOps.freshen(pi)
          val binders = pi.binders.map { binder =>
            val marking = if (binder.isImplicit) "implicit" else "explicit"
            s"$marking ${binder.name}: ${render(fresh(binder.localRef).tpe, depth - 1)}"
          }
          s"Pi(${binders.mkString(", ")}) -> ${render(pi.codomain(fresh), depth - 1)}"
        case pi: VPi =>
          val markings = pi.binders.map(binder => if (binder.isImplicit) "i" else "e").mkString
          s"Pi/${pi.binders.length}[$markings]"
        case VApp(head, args, _, _) if depth > 0 =>
          s"${render(head, depth - 1)}(${args.map(render(_, depth - 1)).mkString(", ")})"
        case VApp(head, args, _, _) => s"application of ${render(head, depth)} with ${args.length} arguments"
        case other                  => String.valueOf(other)
      }

    val rendered = render(value, depth = 2)
    val limit = 240
    if (rendered.length <= limit) rendered else rendered.take(limit - 3) + "..."
  }

  private def same(declaration: String, description: String, actual: Value, expected: Value, span: Span): Unit =
    if (!ValueEquivalence.defEq(actual, expected))
      fail(declaration, s"$description: expected ${concise(expected)}, got ${concise(actual)}", span)

  private def checkedType(declaration: String, description: String, term: Term, env: Env, span: Span): Value =
    try TypeChecker.getType(term, env)
    catch {
      case error: TypeError => fail(declaration, s"$description did not typecheck: ${error.msg}", span)
    }

  private def checkedGlobal(declaration: String, name: String, env: Env, span: Span): Value =
    try env(name)
    catch {
      case _: NotFound =>
        fail(declaration, s"validated dependency $name is absent from the installation environment", span)
    }

  private def pi(declaration: String, description: String, value: Value, arity: Int, span: Span): VPi =
    value match {
      case result: VPi if result.binders.length == arity => result
      case result: VPi => fail(declaration, s"$description has ${result.binders.length} binders, expected $arity", span)
      case other       => fail(declaration, s"$description must be a Pi, got $other", span)
    }

  private def requireImplicitness(
      declaration: String,
      description: String,
      actual: Vector[Boolean],
      expected: Vector[Boolean],
      span: Span
  ): Unit =
    if (actual != expected) {
      def render(markings: Vector[Boolean]): String =
        markings.map(if (_) "implicit" else "explicit").mkString("[", ", ", "]")
      fail(declaration, s"$description binder markings must be ${render(expected)}, got ${render(actual)}", span)
    }

  private def requireImplicitness(
      declaration: String,
      description: String,
      pi: VPi,
      expected: Vector[Boolean],
      span: Span
  ): Unit =
    requireImplicitness(declaration, description, pi.binders.map(_.isImplicit), expected, span)

  private def installedFamily(decl: Decl.InductiveDecl, env: Env): VConst =
    checkedGlobal(decl.header.name, decl.header.name, env, decl.span) match {
      case family @ VConst(_, Inductive(meta), _) =>
        if (meta.familyArity != decl.header.arity)
          fail(decl.header.name, s"installed family arity ${meta.familyArity} disagrees with declaration", decl.span)
        if (meta.constructorNames != decl.ctors.map(_.canonicalName))
          fail(
            decl.header.name,
            s"installed constructor order ${meta.constructorNames} disagrees with the declaration",
            decl.span
          )
        family
      case other => fail(decl.header.name, s"installed family head is not inductive: $other", decl.span)
    }

  private def installedConstructor(decl: Decl.InductiveDecl, env: Env): ConstructorHead = {
    val name = decl.ctors.head.canonicalName
    checkedGlobal(decl.header.name, name, env, decl.span) match {
      case constructor: ConstructorHead => constructor
      case other => fail(decl.header.name, s"$name is not an installed constructor: $other", decl.span)
    }
  }

  def validateEquality(
      decl: Decl.InductiveDecl,
      installedEnv: Env,
      exported: EqualityExportMetadata
  ): ValidatedEquality = {
    val declaration = "Eq"
    if (decl.header.name != declaration) fail(declaration, s"family identity is ${decl.header.name}", decl.span)
    if (decl.header.params.length != 2 || decl.header.indices.length != 2)
      fail(declaration, "expected universe and carrier parameters followed by two indices", decl.span)
    requireImplicitness(
      declaration,
      "translated family",
      decl.header.binders.map(_.isImplicit),
      Vector(true, false, false, false),
      decl.header.span
    )
    if (decl.ctors.map(_.canonicalName) != Vector("Eq.refl"))
      fail(
        declaration,
        s"expected sole constructor Eq.refl, got ${decl.ctors.map(_.canonicalName).mkString(", ")}",
        decl.span
      )
    if (decl.ctors.head.binders.length != 1)
      fail(declaration, "Eq.refl must bind only its diagonal value", decl.ctors.head.span)
    requireImplicitness(
      declaration,
      "translated Eq.refl fields",
      decl.ctors.head.binders.map(_.isImplicit),
      Vector(false),
      decl.ctors.head.span
    )
    if (
      exported != EqualityExportMetadata(
        producer = SupportedProducer,
        familyName = "Eq",
        constructorNames = Vector("Eq.refl"),
        numParams = 2,
        numIndices = 1,
        isRecursive = false
      )
    ) fail(declaration, s"exported block metadata disagrees with the checked equality shape: $exported", decl.span)

    val family = installedFamily(decl, installedEnv)
    val familyPi = pi(declaration, "family type", family.tpe, 4, decl.header.span)
    requireImplicitness(
      declaration,
      "installed family",
      familyPi,
      Vector(true, false, false, false),
      decl.header.span
    )
    val familyEnv = BinderOps.freshen(familyPi)
    val Vector(u, carrier, left, right) = familyPi.binders.map(binder => familyEnv(binder.localRef))
    same(declaration, "universe parameter type", u.tpe, LevelTpe, decl.header.span)
    val level = u match {
      case value: Level => value
      case other        => fail(declaration, s"universe parameter is not a level: $other", decl.header.span)
    }
    same(declaration, "carrier parameter type", carrier.tpe, VSort(level), decl.header.span)
    same(declaration, "left index type", left.tpe, carrier, decl.header.span)
    same(declaration, "right index type", right.tpe, carrier, decl.header.span)
    same(declaration, "result universe", familyPi.codomain(familyEnv), PropTpe, decl.header.resultTy.span)

    val constructor = installedConstructor(decl, installedEnv)
    if (constructor.numErasedFamilyArgs != 2 || constructor.totalArity != 3 || !constructor.noConfusion)
      fail(declaration, "Eq.refl ownership, arity, or no-confusion metadata disagrees with the declaration", decl.span)
    val constructorPi = pi(declaration, "Eq.refl type", constructor.tpe, 3, decl.ctors.head.span)
    requireImplicitness(
      declaration,
      "installed Eq.refl",
      constructorPi,
      Vector(true, true, false),
      decl.ctors.head.span
    )
    val constructorEnv = BinderOps.freshen(constructorPi)
    val Vector(cu, cCarrier, value) = constructorPi.binders.map(binder => constructorEnv(binder.localRef))
    same(declaration, "Eq.refl universe type", cu.tpe, LevelTpe, decl.ctors.head.span)
    val cLevel = cu match {
      case v: Level => v
      case other    => fail(declaration, s"Eq.refl universe parameter is not a level: $other", decl.ctors.head.span)
    }
    same(declaration, "Eq.refl carrier type", cCarrier.tpe, VSort(cLevel), decl.ctors.head.span)
    same(declaration, "Eq.refl value type", value.tpe, cCarrier, decl.ctors.head.span)
    val expectedResult = Interpreter.evalApply(family, Vector(cu, cCarrier, value, value))
    same(
      declaration,
      "Eq.refl diagonal result",
      constructorPi.codomain(constructorEnv),
      expectedResult,
      decl.ctors.head.span
    )
    new ValidatedEquality(family, constructor)
  }

  def validateAcc(
      decl: Decl.InductiveDecl,
      installedEnv: Env,
      exported: AccExportMetadata
  ): AccRecursorShape = {
    val declaration = "Acc"
    if (decl.header.name != declaration) fail(declaration, s"family identity is ${decl.header.name}", decl.span)
    if (decl.header.params.length != 3 || decl.header.indices.length != 1)
      fail(declaration, "expected universe, carrier, and relation parameters followed by one index", decl.span)
    requireImplicitness(
      declaration,
      "translated family",
      decl.header.binders.map(_.isImplicit),
      Vector(true, false, false, false),
      decl.header.span
    )
    if (decl.ctors.map(_.canonicalName) != Vector("Acc.intro"))
      fail(
        declaration,
        s"expected sole constructor Acc.intro, got ${decl.ctors.map(_.canonicalName).mkString(", ")}",
        decl.span
      )
    if (decl.ctors.head.binders.length != 2)
      fail(declaration, "Acc.intro must bind x and its accessibility child function", decl.ctors.head.span)
    requireImplicitness(
      declaration,
      "translated Acc.intro fields",
      decl.ctors.head.binders.map(_.isImplicit),
      Vector(false, false),
      decl.ctors.head.span
    )
    if (
      exported != AccExportMetadata(
        producer = SupportedProducer,
        familyName = "Acc",
        constructorNames = Vector("Acc.intro"),
        numParams = 2,
        numIndices = 1,
        isRecursive = true
      )
    ) fail(declaration, s"exported block metadata disagrees with the checked singleton shape: $exported", decl.span)

    val family = installedFamily(decl, installedEnv)
    val familyPi = pi(declaration, "family type", family.tpe, 4, decl.header.span)
    requireImplicitness(
      declaration,
      "installed family",
      familyPi,
      Vector(true, false, false, false),
      decl.header.span
    )
    val familyEnv = BinderOps.freshen(familyPi)
    val Vector(u, carrier, relation, index) = familyPi.binders.map(binder => familyEnv(binder.localRef))
    same(declaration, "universe parameter type", u.tpe, LevelTpe, decl.header.span)
    val level = u match {
      case value: Level => value
      case other        => fail(declaration, s"universe parameter is not a level: $other", decl.header.span)
    }
    same(declaration, "carrier parameter type", carrier.tpe, VSort(level), decl.header.span)
    val relationPi = pi(declaration, "relation parameter type", relation.tpe, 2, decl.header.span)
    requireImplicitness(declaration, "relation parameter", relationPi, Vector(false, false), decl.header.span)
    val relationEnv = BinderOps.freshen(relationPi)
    relationPi.binders.foreach(binder =>
      same(declaration, "relation argument type", relationEnv(binder.localRef).tpe, carrier, decl.header.span)
    )
    same(declaration, "relation result", relationPi.codomain(relationEnv), PropTpe, decl.header.span)
    same(declaration, "index type", index.tpe, carrier, decl.header.span)
    same(declaration, "result universe", familyPi.codomain(familyEnv), PropTpe, decl.header.resultTy.span)

    val constructor = installedConstructor(decl, installedEnv)
    if (constructor.numErasedFamilyArgs != 3 || constructor.totalArity != 5 || !constructor.noConfusion)
      fail(
        declaration,
        "Acc.intro ownership, arity, or no-confusion metadata disagrees with the declaration",
        decl.span
      )
    val constructorPi = pi(declaration, "Acc.intro type", constructor.tpe, 5, decl.ctors.head.span)
    requireImplicitness(
      declaration,
      "installed Acc.intro",
      constructorPi,
      Vector(true, true, false, false, false),
      decl.ctors.head.span
    )
    val constructorEnv = BinderOps.freshen(constructorPi)
    val Vector(cu, cCarrier, cRelation, x, children) =
      constructorPi.binders.map(binder => constructorEnv(binder.localRef))
    same(declaration, "Acc.intro universe type", cu.tpe, LevelTpe, decl.ctors.head.span)
    val cLevel = cu match {
      case value: Level => value
      case other => fail(declaration, s"Acc.intro universe parameter is not a level: $other", decl.ctors.head.span)
    }
    same(declaration, "Acc.intro carrier type", cCarrier.tpe, VSort(cLevel), decl.ctors.head.span)
    val cRelationPi = pi(declaration, "Acc.intro relation type", cRelation.tpe, 2, decl.ctors.head.span)
    requireImplicitness(
      declaration,
      "Acc.intro relation",
      cRelationPi,
      Vector(false, false),
      decl.ctors.head.span
    )
    val cRelationEnv = BinderOps.freshen(cRelationPi)
    cRelationPi.binders.foreach(binder =>
      same(
        declaration,
        "Acc.intro relation argument",
        cRelationEnv(binder.localRef).tpe,
        cCarrier,
        decl.ctors.head.span
      )
    )
    same(declaration, "Acc.intro relation result", cRelationPi.codomain(cRelationEnv), PropTpe, decl.ctors.head.span)
    same(declaration, "Acc.intro index type", x.tpe, cCarrier, decl.ctors.head.span)
    val childrenPi = pi(declaration, "Acc.intro child function", children.tpe, 2, decl.ctors.head.span)
    requireImplicitness(
      declaration,
      "Acc.intro child function",
      childrenPi,
      Vector(false, false),
      decl.ctors.head.span
    )
    val childrenEnv = BinderOps.freshen(childrenPi)
    val Vector(y, proof) = childrenPi.binders.map(binder => childrenEnv(binder.localRef))
    same(declaration, "child index type", y.tpe, cCarrier, decl.ctors.head.span)
    val expectedRelation = Interpreter.evalApply(cRelation, Vector(y, x))
    same(declaration, "child relation proof type", proof.tpe, expectedRelation, decl.ctors.head.span)
    val expectedChild = Interpreter.evalApply(family, Vector(cu, cCarrier, cRelation, y))
    same(declaration, "recursive child result", childrenPi.codomain(childrenEnv), expectedChild, decl.ctors.head.span)
    val expectedResult = Interpreter.evalApply(family, Vector(cu, cCarrier, cRelation, x))
    same(declaration, "Acc.intro result", constructorPi.codomain(constructorEnv), expectedResult, decl.ctors.head.span)

    family.constType match {
      case Inductive(meta)
          if meta.proofRecovery.exists(_.definitelyComplete) &&
            meta.projectionInfo.exists(info => !info.etaEligible) =>
      case _ =>
        fail(
          declaration,
          "checked Acc lacks complete proof recovery or incorrectly permits structure eta",
          decl.span
        )
    }
    new AccRecursorShape(family, constructor)
  }

  def install(
      equality: ValidatedEquality,
      acc: AccRecursorShape,
      exported: ExportedRecursor,
      env: Env
  ): Installed = {
    if (exported.universeOrder != Vector(UniverseRole.MotiveResult, UniverseRole.Carrier))
      fail(
        SealedRecName,
        s"universe order must be motive-result then carrier, got ${exported.universeOrder}",
        exported.span
      )
    if (exported.rules != Vector(RecursorRule(acc.constructor.name, fieldCount = 2)))
      fail(
        SealedRecName,
        s"expected the sole Acc.intro rule with two constructor fields, got ${exported.rules}",
        exported.span
      )
    checkedGlobal(EquationName, equality.family.name, env, exported.span) match {
      case family: VConst if family eq equality.family =>
      case _ => fail(EquationName, "validated equality does not belong to the installation environment", exported.span)
    }
    checkedGlobal(SealedRecName, acc.family.name, env, exported.span) match {
      case family: VConst if family eq acc.family =>
      case _ => fail(SealedRecName, "validated Acc does not belong to the installation environment", exported.span)
    }

    val recursorType = buildRecursorType(acc)
    val derived = checkedType(SealedRecName, "derived recursor type", recursorType, env, exported.span)
    val exportedType = checkedType(SealedRecName, "exported recursor type", exported.tpe, env, exported.span)
    same(SealedRecName, "exported recursor type", exportedType, derived, exported.span)
    val withRecursor = Interpreter.evalDecl(
      Decl.AxiomDecl(SealedRecName, recursorType, exported.span),
      env,
      ReservedNamePermit.wellFounded
    )

    val equationType = buildEquationType(equality, acc)
    val equationValue =
      checkedType(EquationName, "generated constructor equation", equationType, withRecursor, exported.span)
    if (!Value.isPropositionType(equationValue))
      fail(EquationName, s"generated constructor equation is not a proposition: $equationValue", exported.span)
    val installed = Interpreter.evalDecl(
      Decl.AxiomDecl(EquationName, equationType, exported.span),
      withRecursor,
      ReservedNamePermit.wellFounded
    )
    Installed(installed, recursorType, equationType)
  }

  /** Mechanically derived validation target for the export importer; installation rebuilds it independently. */
  def expectedRecursorType(acc: AccRecursorShape): Term = buildRecursorType(acc)

  private def local(ref: LocalRef): Term = Term.LocalRef(ref, NoSpan)
  private def global(name: String): Term = Term.GlobalRef(name, NoSpan)
  private def app(fn: Term, args: Term*): Term = Term.App(fn, args.toVector, NoSpan)
  private def binder(ref: LocalRef, tpe: Term, implicitBinder: Boolean): Binder =
    Binder(ref, tpe, NoSpan, isImplicit = implicitBinder)
  private def pi(binders: Vector[Binder], out: Term): Term.Pi = Term.Pi(binders, out, NoSpan)

  private final case class RecursorPrefix(
      binders: Vector[Binder],
      carrier: LocalRef,
      relation: LocalRef,
      motive: LocalRef,
      minor: LocalRef
  )

  private def recursorPrefix(acc: AccRecursorShape)(implicit refs: RefSupply): RecursorPrefix = {
    val v = refs.fresh("v")
    val u = refs.fresh("u")
    val carrier = refs.fresh("α")
    val relation = refs.fresh("r")
    val motive = refs.fresh("motive")
    val minor = refs.fresh("intro")
    val left = refs.fresh("left")
    val right = refs.fresh("right")
    val relationType = pi(
      Vector(
        binder(left, local(carrier), implicitBinder = false),
        binder(right, local(carrier), implicitBinder = false)
      ),
      global("Prop")
    )
    def accAt(value: Term): Term = app(global(acc.family.name), local(carrier), local(relation), value)
    val motiveIndex = refs.fresh("a")
    val motiveProof = refs.fresh("proof")
    val motiveType = pi(
      Vector(
        binder(motiveIndex, local(carrier), implicitBinder = false),
        binder(motiveProof, accAt(local(motiveIndex)), implicitBinder = false)
      ),
      app(global("Sort"), local(v))
    )
    val x = refs.fresh("x")
    val h = refs.fresh("h")
    val childIndex = refs.fresh("y")
    val childRelation = refs.fresh("hr")
    val hType = pi(
      Vector(
        binder(childIndex, local(carrier), implicitBinder = false),
        binder(childRelation, app(local(relation), local(childIndex), local(x)), implicitBinder = false)
      ),
      accAt(local(childIndex))
    )
    val y = refs.fresh("y")
    val hr = refs.fresh("hr")
    val ihType = pi(
      Vector(
        binder(y, local(carrier), implicitBinder = false),
        binder(hr, app(local(relation), local(y), local(x)), implicitBinder = false)
      ),
      app(local(motive), local(y), app(local(h), local(y), local(hr)))
    )
    val introValue = app(global(acc.constructor.name), local(relation), local(x), local(h))
    val motiveAtIntro = app(local(motive), local(x), introValue)
    val minorType = pi(
      Vector(
        binder(x, local(carrier), implicitBinder = false),
        binder(h, hType, implicitBinder = false),
        binder(refs.fresh("ih"), ihType, implicitBinder = false)
      ),
      motiveAtIntro
    )
    val binders = Vector(
      binder(v, global("Level"), implicitBinder = true),
      binder(u, global("Level"), implicitBinder = true),
      binder(carrier, app(global("Sort"), local(u)), implicitBinder = true),
      // Proof collapse makes r and motive unforceable from later proof-bearing types. The fully explicit export
      // therefore lowers them to ordinary Core arguments; T3 retains those arguments at every occurrence.
      binder(relation, relationType, implicitBinder = false),
      binder(motive, motiveType, implicitBinder = false),
      binder(minor, minorType, implicitBinder = false)
    )
    RecursorPrefix(binders, carrier, relation, motive, minor)
  }

  private def buildRecursorType(acc: AccRecursorShape): Term = {
    implicit val refs: RefSupply = new RefSupply
    val prefix = recursorPrefix(acc)
    val a = refs.fresh("a")
    val t = refs.fresh("t")
    val accAtA = app(global(acc.family.name), local(prefix.carrier), local(prefix.relation), local(a))
    val binders = prefix.binders ++ Vector(
      binder(a, local(prefix.carrier), implicitBinder = true),
      binder(t, accAtA, implicitBinder = false)
    )
    pi(binders, app(local(prefix.motive), local(a), local(t)))
  }

  private def buildEquationType(equality: ValidatedEquality, acc: AccRecursorShape): Term = {
    implicit val refs: RefSupply = new RefSupply
    val prefix = recursorPrefix(acc)
    val x = refs.fresh("x")
    val h = refs.fresh("h")
    val childIndex = refs.fresh("y")
    val childRelation = refs.fresh("hr")
    val hType = pi(
      Vector(
        binder(childIndex, local(prefix.carrier), implicitBinder = false),
        binder(
          childRelation,
          app(local(prefix.relation), local(childIndex), local(x)),
          implicitBinder = false
        )
      ),
      app(global(acc.family.name), local(prefix.carrier), local(prefix.relation), local(childIndex))
    )
    val ihIndex = refs.fresh("y")
    val ihRelation = refs.fresh("hr")
    val ihType = pi(
      Vector(
        binder(ihIndex, local(prefix.carrier), implicitBinder = false),
        binder(ihRelation, app(local(prefix.relation), local(ihIndex), local(x)), implicitBinder = false)
      ),
      app(local(prefix.motive), local(ihIndex), app(local(h), local(ihIndex), local(ihRelation)))
    )
    val recursiveCall = app(
      global(SealedRecName),
      local(prefix.relation),
      local(prefix.motive),
      local(prefix.minor),
      app(local(h), local(ihIndex), local(ihRelation))
    )
    val ih = Term.Lam(ihType, recursiveCall, NoSpan, name = None, recursion = None)
    val introValue = app(global(acc.constructor.name), local(prefix.relation), local(x), local(h))
    val resultType = app(local(prefix.motive), local(x), introValue)
    val lhs = app(
      global(SealedRecName),
      local(prefix.relation),
      local(prefix.motive),
      local(prefix.minor),
      introValue
    )
    val rhs = app(local(prefix.minor), local(x), local(h), ih)
    val conclusion = app(global(equality.family.name), resultType, lhs, rhs)
    val equationBinders = prefix.binders ++ Vector(
      binder(x, local(prefix.carrier), implicitBinder = false),
      binder(h, hType, implicitBinder = false)
    )
    pi(equationBinders, conclusion)
  }
}
