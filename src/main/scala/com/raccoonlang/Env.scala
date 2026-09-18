package com.raccoonlang

import scala.collection.immutable.VectorMap

sealed trait GlobalBinding { def value(env: Env): Value }
object GlobalBinding {
  final case class Strict(value0: Value) extends GlobalBinding {
    override def value(env: Env): Value = value0
  }
  final class Lazy(force: () => Value) extends GlobalBinding {
    private[this] var cached: Option[Value] = None
    override def value(env: Env): Value = cached match {
      case Some(value) => value
      case None =>
        val value = force()
        Env.assertClosedGlobal(value)
        Env.assertCanonicalProof(value)
        cached = Some(value)
        value
    }
  }
}

object Env {
  val empty: Env = Env(Map.empty, VectorMap.empty, Set.empty)

  private val assertionsEnabled: Boolean =
    java.lang.Boolean.parseBoolean(System.getProperty("raccoon.envAssertions", "true"))

  private[raccoonlang] def assertClosedGlobal(value: Value): Unit =
    if (assertionsEnabled && value.synDeps.nonEmpty)
      throw CoreInvariant(s"Global value must be closed, but has free vars ${value.synDeps}")

  private[raccoonlang] def assertCanonicalProof(value: Value): Unit =
    if (assertionsEnabled && !(Value.canonicalizeProof(value) eq value))
      throw CoreInvariant(s"Non-canonical proof bound into env: $value")
}

final case class Env(
    globals: Map[String, GlobalBinding],
    locals: VectorMap[CoreAst.LocalRef, Value],
    private[raccoonlang] val localRefs: Set[CoreAst.LocalRef]
) {
  require(localRefs.size == locals.size, "local-ref index size disagrees with locals")

  def apply(name: String): Value = globals.get(name).map(_.value(this)).getOrElse(throw NotFound(name))
  def apply(ref: CoreAst.LocalRef): Value = locals.getOrElse(ref, throw NotFound(ref.name))

  def putGlobal(name: String, value: Value): Env = {
    Env.assertClosedGlobal(value)
    Env.assertCanonicalProof(value)
    if (globals.contains(name)) throw AlreadyDefined(name)
    else if (name == "_") throw WTF("Wildcards not allowed in global names")
    else copy(globals = globals.updated(name, GlobalBinding.Strict(value)))
  }

  def putOpaque(name: String, ty: Value): Env = {
    if (globals.contains(name)) throw AlreadyDefined(name)
    putGlobal(name, Value.canonicalizeProof(Value.VConst(name, Value.Symbol, ty)))
  }

  def putLocal(ref: CoreAst.LocalRef, value: Value): Env = {
    Env.assertCanonicalProof(value)
    if (locals.contains(ref)) throw AlreadyDefined(ref.name)
    copy(locals = locals.updated(ref, value), localRefs = localRefs + ref)
  }

  private[raccoonlang] def putRecursiveGroup(names: Vector[String], build: Env => Vector[Value.VLam]): Env = {
    if (names.isEmpty) throw WTF("Recursive group must not be empty")
    if (names.distinct.length != names.length) throw WTF("Recursive group names must be distinct")
    names.foreach { name =>
      if (globals.contains(name)) throw AlreadyDefined(name)
      if (name == "_") throw WTF("Wildcards not allowed in global names")
    }
    var result: Env = null
    lazy val values: Vector[Value.VLam] = {
      val built = build(result)
      if (built.length != names.length)
        throw WTF(s"Recursive group built ${built.length} values for ${names.length} members")
      built
    }
    val bindings = names.zipWithIndex.map { case (name, index) =>
      name -> new GlobalBinding.Lazy(() => values(index))
    }
    result = copy(globals = globals ++ bindings)
    result
  }

  def closeForEval(capturedRefs: Set[CoreAst.LocalRef]): Env = {
    val missing = capturedRefs.filterNot(locals.contains)
    if (missing.nonEmpty)
      throw CoreInvariant(
        s"Cannot close evaluation environment; missing refs: ${missing.map(_.name).toVector.sorted.mkString(", ")}"
      )
    copy(
      locals = locals.filter { case (ref, _) => capturedRefs.contains(ref) },
      localRefs = capturedRefs
    )
  }

  def dependencies: DepSet = locals.values.foldLeft(DepSet.empty)(_ ++ _.synDeps)
}
