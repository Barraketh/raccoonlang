package com.raccoonlang

import com.raccoonlang.Util.NEL

object ArgumentOps {
  def reorder[A](
      args: NEL[AppArg[A]],
      binders: NEL[CoreAst.Binder],
      appSpan: Option[Span] = None
  ): NEL[A] = {
    val rawArgs = args.toVector
    val binderVec = binders.toVector
    val bindersByName = binderVec.zipWithIndex.groupMap(_._1.name)(_._2)

    var seenNamed = false
    var nextPositional = 0
    var supplied = Vector.fill[Option[A]](binderVec.length)(None)
    val namedArgs = collection.mutable.Set.empty[String]

    rawArgs.foreach {
      case AppArg.Pos(value, span) =>
        if (seenNamed) throw PositionalArgumentAfterNamed(Some(span))
        if (nextPositional >= binderVec.length)
          throw ArityMismatch(binderVec.length, rawArgs.length, Some(span))

        supplied = supplied.updated(nextPositional, Some(value))
        nextPositional += 1

      case AppArg.Named(name, value, span) =>
        seenNamed = true
        if (name == "_") throw CannotCallAnonymousArgument(Some(span))
        if (namedArgs.contains(name)) throw DuplicateNamedArgument(name, Some(span))

        val matches = bindersByName.getOrElse(name, Vector.empty)
        if (matches.isEmpty) throw UnknownNamedArgument(name, Some(span))
        if (matches.length > 1) throw AmbiguousNamedArgument(name, Some(span))

        val idx = matches.head
        if (supplied(idx).isDefined) throw NamedArgumentAlreadySupplied(name, Some(span))

        supplied = supplied.updated(idx, Some(value))
        namedArgs += name
    }

    if (rawArgs.length != binderVec.length)
      throw ArityMismatch(binderVec.length, rawArgs.length, appSpan)

    NEL.mk(supplied.map {
      case Some(arg) => arg
      case None      => throw ArityMismatch(binderVec.length, rawArgs.length, appSpan)
    })
  }
}
