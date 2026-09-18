package com.raccoonlang

import com.raccoonlang.CoreAst.{Term => CTerm}
import com.raccoonlang.Value._

/** The positional eta view of a checked, one-constructor, unindexed, nonrecursive family. */
object StructEta {
  private def anyInstance(tpe: Value): Option[(InductiveFamilyInstance, ProjectionInfo)] =
    tpe match {
      case InductiveFamilyValue(inst) => inst.meta.projectionInfo.filter(_.etaEligible).map(inst -> _)
      case _                          => None
    }

  def eligibleInstance(tpe: Value): Option[(InductiveFamilyInstance, ProjectionInfo)] =
    anyInstance(tpe).filterNot { case _ => tpe.tpe == PropTpe }

  def fields(value: Value): Option[Vector[Value]] = value match {
    case _ =>
      eligibleInstance(value.tpe).map { case (inst, info) =>
        value match {
          case ConstructorForm(name, stored) if name == info.ctorName =>
            if (stored.length != info.fieldCount)
              throw WTF(s"Constructor $name supplied ${stored.length} fields, expected ${info.fieldCount}")
            stored
          case _ => Vector.tabulate(info.fieldCount)(i => fieldProjection(value, inst, info, i))
        }
      }
  }

  def fieldProjection(base: Value, inst: InductiveFamilyInstance, info: ProjectionInfo, idx: Int): Value = {
    if (idx < 0 || idx >= info.fieldCount)
      throw WTF(s"Projection ${inst.head.name}.$idx is out of range (${info.fieldCount} fields)")
    base match {
      case ConstructorForm(name, stored) if name == info.ctorName => stored(idx)
      case _ =>
        val program = info.projectors(idx)
        val env = Env.empty.putGlobal(info.ctorHead.name, info.ctorHead).putLocal(program.self, base)
        val blocked = Blocker.unapply(base).getOrElse(DepSet.empty)
        NeutralThunk(
          program.term,
          env,
          ValueId.LocalId(program.term.nodeId, Vector(base)),
          fieldType(base, inst, info, idx),
          blocked
        )
    }
  }

  private def fieldType(base: Value, inst: InductiveFamilyInstance, info: ProjectionInfo, idx: Int): Value = {
    val head = info.ctorHead
    if (info.fieldCount > 0 && head.pi.isEmpty)
      throw WTF(s"Constructor ${head.name} has fields but non-Pi type ${head.tpe}")
    val binders = head.fieldBinders
    var env = head.fieldEnv(inst.args)
    val deps = info.fieldDependencies(idx)
    var i = 0
    while (i < idx) {
      if (deps.contains(i)) env = env.putLocal(binders(i).localRef, fieldProjection(base, inst, info, i))
      i += 1
    }
    Interpreter.evalTerm(binders(idx).ty, env)
  }

  final case class Projector(self: CoreAst.LocalRef, term: CTerm.Match)

  private[raccoonlang] def buildProjector(ctorName: String, fieldCount: Int, idx: Int): Projector = {
    def fresh(name: String): CoreAst.LocalRef = CoreAst.LocalRef(AstNodeId.synthetic().start, name)
    val self = fresh("self")
    val fields = Vector.tabulate(fieldCount)(i => fresh(s"x$i"))
    val span = Span.synthetic()
    val branch =
      CoreAst.Case(ctorName, isFullyQualified = true, fields.map(Some(_)), CTerm.LocalRef(fields(idx), span), span)
    Projector(self, CTerm.Match(CTerm.LocalRef(self, span), None, Vector(branch), span))
  }
}
