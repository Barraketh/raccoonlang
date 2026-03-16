package com.raccoonlang

// Environment: tracks lexical scope
final case class Env(globals: Map[String, Value], locals: Map[String, Value], parent: Option[Env]) {
  def find(name: String): Option[Value] =
    locals.get(name).orElse(globals.get(name)).orElse(parent.flatMap(_.find(name)))

  def findLocal(name: String): Option[Value] =
    locals.get(name).orElse(parent.flatMap(_.findLocal(name)))

  def putGlobal(name: String, value: Value): Env = {
    if (globals.contains(name))
      throw AlreadyDefined(name)
    else if (name == "_") this
    else Env(globals + (name -> value), locals, parent)
  }

  def putLocal(name: String, value: Value): Env = {
    if (locals.contains(name) || globals.contains(name))
      throw AlreadyDefined(name)
    else if (name == "_") this
    else Env(globals, locals + (name -> value), parent)
  }

  def newScope: Env = Env(Map.empty, Map.empty, Some(this))
}

object Env {
  val empty: Env = Env(globals = Map(), locals = Map(), parent = None)
}
