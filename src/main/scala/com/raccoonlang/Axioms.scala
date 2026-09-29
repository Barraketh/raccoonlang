package com.raccoonlang

import com.raccoonlang.AxiomMintsToken.Part
import com.raccoonlang.Value._
import com.raccoonlang.telescope.BinderOps

/**
 * What an axiom may state (spec §7.3). An axiom's result is a neutral, so an axiom whose type mentions a token could
 * make or consume one without its module, and one that binds a lifetime or kind could state an equation between them
 * that no program can refute, since none are apart, and refinement along it would retype a value across scopes or
 * kinds. Sealing needs no rule here: no `match` opens a value of a sealed family its module did not build (§7.1). The
 * trusted prelude is exempt: its `Quot` and `Quot.sound` bind lifetimes.
 */
object Axioms {

  /**
   * Walk the value of the checked type `tpe` of the axiom `name` once, in order, and refuse the first part that is a
   * binder of a kind or lifetime, a kind or lifetime other than `Kind.unr` and `Lifetime.empty` (sort and closure
   * fields included), or a linear type. The walk reads the type as a value, never a subterm's type:
   *   - a function type: its closure, then each binder's type under fresh values for the earlier binders, then its
   *     codomain under fresh values for all of them;
   *   - an application, a family instance included: its head, then its arguments;
   *   - a lambda: its type and its captures; a blocked `match`: its captures, since its branches are code;
   *   - a proof: its proposition, which is all it holds.
   *
   * A family head's own declared type is not part of the axiom's, so `List(Nat)`, whose `List` binds a lifetime, is
   * admitted: its arguments are `Lifetime.empty` and `Nat`. Level binders are admitted.
   */
  def requireMintsNoToken(name: String, tpe: Value): Unit = {
    def reject(part: Part): Nothing = fail(AxiomMintsToken(name, part))

    // A linear type is read off its sort (Linearity), so only a value whose type is a sort is asked.
    def requireUnrestricted(value: Value): Unit =
      value.tpe match {
        case _: VSort => if (Linearity.isLinear(value)) reject(Part.LinearType(value))
        case _        =>
      }

    def walk(value: Value): Unit =
      value match {
        case kind: Kind         => if (!kind.isUnr) reject(Part.Parameter(kind))
        case lifetime: Lifetime => if (!lifetime.isEmpty) reject(Part.Parameter(lifetime))
        case sort: VSort =>
          walk(sort.kind)
          walk(sort.scope)
        // A function type is linear exactly when its closure kind is, which the closure's walk refuses.
        case pi: VPi =>
          walk(pi.closureKind)
          walk(pi.closureScope)
          val fresh = BinderOps.freshen(pi)
          pi.binders.foreach { binder =>
            fresh(binder.localRef).tpe match {
              case LevelTpe                =>
              case parameter: ParameterTpe => reject(Part.Binder(binder.name, parameter))
              case binderTpe               => walk(binderTpe)
            }
          }
          walk(pi.codomain(fresh))
        case lam: VLam =>
          walk(lam.tpe)
          lam.id match {
            case ValueId.LocalId(_, captures) => captures.foreach(walk)
            case ValueId.Const(_)             =>
          }
        case app: VApp =>
          walk(app.head)
          requireUnrestricted(app)
          app.args.foreach(walk)
        case thunk: NeutralThunk =>
          requireUnrestricted(thunk)
          thunk.id.captures.foreach(walk)
        case proof: VProof      => walk(proof.tpe)
        case _: VConst | _: Var => requireUnrestricted(value)
        case _: VPacked | _: ConstructorHead | _: Level | _: ParameterTpe | SortParameter | Large =>
      }

    walk(tpe)
  }
}
