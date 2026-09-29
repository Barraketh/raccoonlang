package com.raccoonlang

/**
 * Sealed families (spec §7.1). A sealed family exports its head, parameters, indices and classifier, but its
 * constructors and selectors only to its module, the `.rac` file that declares it. Sealing restricts what a program may
 * write, never what the checker knows (§7.2): kinds, scopes, coverage, apartness and conversion read the full
 * declaration everywhere, and evaluation compares no module. A seal shapes no value: structure eta and proof
 * reconstruction apply to a sealed family as to any other, since only the trusted prelude declares axioms and the
 * bundled one declares no sealed family (§7.3), so every value of one was built from its constructors.
 *
 * `accessible` is the one decision. The checker asks it where a name is resolved to a constructor or selector (a global
 * reference, a selected field) and for a match's scrutinee family, which also covers a case's `.short` form, since that
 * resolves only against the scrutinee's family. Implicit projection asks it before reading a constructor's field. A
 * module is compared nowhere else, and no site is exempt.
 */
object Sealing {

  /**
   * A sealed family, by name, and its module: the source its declaration was read from. `Elaborator.familySeal` makes
   * the seal of a family's constructors and of its selectors alike.
   */
  final case class Seal(family: String, module: SourceId)

  /**
   * Whether code written at `site` may use the constructors and selectors of a family sealed by `seal`, if it is
   * sealed: only inside its module. A site without a source lies in no module.
   */
  def accessible(seal: Option[Seal], site: Span): Boolean =
    seal.forall(s => site.source.contains(s.module))

  /**
   * A use at `site` of a sealed family's constructors or selectors: `member` names the constructor or selector the
   * position names, and is absent for a match on a value of the family. Outside its module it is `SealedConstructor`.
   */
  def requireAccessible(seal: Option[Seal], member: Option[String], site: Span): Unit =
    seal.foreach(s => if (!accessible(seal, site)) fail(SealedConstructor(s.family, member)))

  /** A reference at `site` to the global `name`, which may be a sealed family's constructor or selector. */
  def requireAccessibleGlobal(name: String, site: Span, env: Env): Unit =
    requireAccessible(env.sealedMembers.get(name), Some(name), site)
}
