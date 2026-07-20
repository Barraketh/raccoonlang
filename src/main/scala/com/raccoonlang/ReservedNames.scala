package com.raccoonlang

/** Kernel-owned authority to publish a narrow set of otherwise reserved global identities. */
final class ReservedNamePermit private (private[raccoonlang] val names: Set[String])

object ReservedNamePermit {
  val empty: ReservedNamePermit = new ReservedNamePermit(Set.empty)

  private[raccoonlang] val nativePrelude: ReservedNamePermit = new ReservedNamePermit(Packed.reservedNames)
  private[raccoonlang] val wellFounded: ReservedNamePermit = new ReservedNamePermit(WfPrimitives.reservedNames)
}

/** Complete authority for building a prelude environment; invalid permit/profile combinations are unrepresentable. */
sealed trait BootstrapAuthority

object BootstrapAuthority {
  case object Unprivileged extends BootstrapAuthority

  private[raccoonlang] final class Native private[BootstrapAuthority] (val profile: Packed.NativeBootstrapProfile)
    extends BootstrapAuthority

  private[raccoonlang] val bundledSourcePrelude = new Native(Packed.BundledSourcePrelude)
  private[raccoonlang] val pinnedTranslatedInit = new Native(Packed.PinnedTranslatedInit)
  private[raccoonlang] val syntheticFullK3 = new Native(Packed.SyntheticFullK3)
}

object ReservedNames {
  val all: Set[String] = Packed.reservedNames ++ WfPrimitives.reservedNames

  def unauthorized(names: Iterable[String], permit: ReservedNamePermit): Option[String] =
    names.find(name => all(name) && !permit.names(name))
}
