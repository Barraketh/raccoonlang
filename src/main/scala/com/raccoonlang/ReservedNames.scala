package com.raccoonlang

/** Kernel-owned authority to publish a narrow set of otherwise reserved global identities. */
final class ReservedNamePermit private (private[raccoonlang] val names: Set[String])

object ReservedNamePermit {
  val empty: ReservedNamePermit = new ReservedNamePermit(Set.empty)

  private[raccoonlang] val nativePrelude: ReservedNamePermit = new ReservedNamePermit(Packed.reservedNames)
  private[raccoonlang] val wellFounded: ReservedNamePermit = new ReservedNamePermit(WfPrimitives.reservedNames)
}

object ReservedNames {
  val all: Set[String] = Packed.reservedNames ++ WfPrimitives.reservedNames

  def unauthorized(names: Iterable[String], permit: ReservedNamePermit): Option[String] =
    names.find(name => all(name) && !permit.names(name))
}
