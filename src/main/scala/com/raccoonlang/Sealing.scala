package com.raccoonlang

/**
 * Sealed families (spec §7.1). A sealed family exports its head, parameters, indices and classifier, but its
 * constructors and selectors only to its module, the `.rac` file that declares it. Sealing restricts what a program may
 * write, never what the checker knows (§7.2): kinds, scopes, coverage, apartness and conversion read the full
 * declaration everywhere, and evaluation compares no module. A seal shapes values in two places only: a sealed family
 * has no structure eta (InductiveMeta), and a proof of a sealed proposition is never reconstructed
 * (ProofReconstruction), so no `match` in the module opens a value it never built.
 *
 * `accessible` is the one decision. The checker asks it where a name is resolved to a constructor or selector (a global
 * reference, a selected field) and for a match's scrutinee family, which also covers a case's `.short` form, since that
 * resolves only against the scrutinee's family. Implicit projection asks it before reading a constructor's field. A
 * module is compared nowhere else.
 */
object Sealing {

  /** A sealed family, by name, and its module: the source its declaration was read from. */
  final case class Seal(family: String, module: Option[SourceId])

  /**
   * Whether code written at `site` may use the constructors and selectors of a family sealed by `seal`, if it is
   * sealed: only inside its module. A term the checker fabricates belongs to no module and is exempt.
   */
  def accessible(seal: Option[Seal], site: Span): Boolean =
    seal.forall(s => site.source == s.module || site.source.contains(AstNodeId.syntheticSource))

  /**
   * A use at `site` of a sealed family's constructors or selectors: `member` names the constructor or selector the
   * position names, and is absent for a match on a value of the family. Outside its module it is `SealedConstructor`.
   */
  def requireAccessible(seal: Option[Seal], member: Option[String], site: Span): Unit =
    seal.foreach(s => if (!accessible(seal, site)) fail(SealedConstructor(s.family, member)))
}
