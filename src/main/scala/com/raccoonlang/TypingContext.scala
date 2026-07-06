package com.raccoonlang

final case class TypingContext(env: Env[Value], instances: Instances) {
  def putGlobal(name: String, value: Value, isInstance: Boolean = false): TypingContext = {
    val nextEnv = env.putGlobal(name, value)
    val nextInstances =
      if (isInstance) instances.putGlobal(name, value)
      else instances
    copy(env = nextEnv, instances = nextInstances)
  }

  def putLazyGlobal(name: String, force: () => Value): TypingContext =
    copy(env = env.putLazyGlobal(name, force))

  def putLocal(ref: CoreAst.LocalRef, value: Value, isInstance: Boolean = false): TypingContext = {
    val nextEnv = env.putLocal(ref, value)
    val nextInstances =
      if (isInstance) instances.putLocal(ref, value)
      else instances
    copy(env = nextEnv, instances = nextInstances)
  }

  def registerLocalInstance(ref: CoreAst.LocalRef): TypingContext =
    copy(instances = instances.putLocal(ref, env(ref)))

  def withEnv(nextEnv: Env[Value]): TypingContext =
    copy(env = nextEnv)
}

object TypingContext {
  def envOnly(env: Env[Value]): TypingContext =
    TypingContext(env, Instances.empty)
}
