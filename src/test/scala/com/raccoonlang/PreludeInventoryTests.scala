package com.raccoonlang

import com.raccoonlang.Value._

import java.nio.file.Paths

/**
 * A prelude's trusted surface (docs/kernel.md, Trusted bootstrap and native values): what the kernel takes on trust
 * rather than checks. The obligations T1–T5 it keeps are audited, not checked, so the bundled prelude's surface is a
 * golden, and any change to it is reviewed against them. Every other prelude declaration is checked as one in any
 * module, a linear, kind-polymorphic or sealed one included.
 */
class PreludeInventoryTests extends munit.FunSuite with TestSupport with Goldens {

  /**
   * The trusted surface of `prelude`, one section per part, each in declaration order: its axioms and builtins with
   * their types as declared, the declarations the kernel attached a native operation to, the native literal layouts it
   * installed, and its sealed families, which the obligations name. A native operation or sealed family is listed under
   * its own name only, not under a definition that merely evaluates to it.
   */
  private def inventory(prelude: Prelude.Config): String = {
    val env = prelude.checkedEnv
    val decls = prelude.core.decls
    val axioms = decls.collect { case CoreAst.Decl.AxiomDecl(name, ty, _) =>
      s"$name : ${PrettyPrinter.printTerm(ty)}"
    }
    val builtins = decls.collect { case CoreAst.Decl.ConstDecl(name, ty, CoreAst.ConstBody.Builtin(_), _, _) =>
      s"$name : ${PrettyPrinter.printTerm(ty)}"
    }
    val checkedNames = decls.flatMap {
      case _: CoreAst.Decl.AxiomDecl                                        => Vector.empty
      case CoreAst.Decl.ConstDecl(_, _, CoreAst.ConstBody.Builtin(_), _, _) => Vector.empty
      case other                                                            => other.definedNames
    }
    val nativeOps = checkedNames.filter(name =>
      Packed.opNames(name) && (env(name) match {
        case VLam(_, _, _: LamBody.Native) => true
        case _                             => false
      })
    )
    val layouts =
      env.nativeLiterals.natLayout.map(layout => PrettyPrinter.print(layout.natTpe)).toVector ++
        env.nativeLiterals.stringLayout.map(layout => PrettyPrinter.print(layout.stringTpe))
    val sealedFamilies = checkedNames.filter(name =>
      env(name) match {
        case VConst(family, Inductive(meta), _) => family == name && meta.seal.nonEmpty
        case _                                  => false
      }
    )
    Vector(
      "axioms" -> axioms,
      "builtins" -> builtins,
      "native operations" -> nativeOps,
      "native literal layouts" -> layouts,
      "sealed families" -> sealedFamilies
    ).map { case (part, entries) =>
      (part +: (if (entries.isEmpty) Vector("none") else entries).map("  " + _)).mkString("\n")
    }.mkString("", "\n", "\n")
  }

  test("the bundled prelude's trusted surface is its golden inventory") {
    assertGolden(Paths.get("src", "test", "resources", "prelude-inventory.txt"), inventory(Prelude.default))
  }

  /**
   * Linear and kind-polymorphic families and definitions, a linear closure, a sealed family, a definition that is it,
   * and an axiom.
   */
  private val custom =
    """
      |inductive Unit : Type
      | | unit : Unit
      |
      |inductive Tok : Type { kind = lin }
      | | mk : Tok
      |
      |inductive Box {k: Kind}(A: Type { kind = k }) : Type { kind = k }
      | | mk (held: A) : Box(A)
      |
      |def keep {k: Kind}{A: Type { kind = k }}(x: A): A := x
      |
      |def unbox {k: Kind}{A: Type { kind = k }}(b: Box(A)): A := match b returning A with
      | | Box.mk held => held
      |
      |def spend (t: Tok): Unit := match t returning Unit with
      | | Tok.mk => Unit.unit
      |
      |def apply (f: { kind = lin } Unit -> Unit): Unit := f(Unit.unit)
      |
      |sealed inductive Permit : Prop
      | | mk : Permit
      |
      |axiom Carrier : Type
      |
      |def Sealed : Prop := Permit
      |""".stripMargin

  test(
    "a prelude may declare linear, kind-polymorphic and sealed families, and only its trusted surface is inventoried"
  ) {
    val prelude = Prelude.fromSource("custom", custom)
    assertNoDiff(
      inventory(prelude),
      """axioms
        |  Carrier : Type
        |builtins
        |  none
        |native operations
        |  none
        |native literal layouts
        |  none
        |sealed families
        |  Permit
        |""".stripMargin
    )
    val spent = runProgram("{ spend(unbox(keep(Box.mk(Tok.mk)))) }", prelude)
    assert(ValueEquivalence.defEq(spent, runProgram("{ Unit.unit }", prelude)))
  }

  test("a prelude's own declarations are checked as any module's, so one that drops a token is refused") {
    val dropping = Prelude.fromSource("dropping", custom + "\ndef drop (t: Tok): Unit := Unit.unit\n")
    assertEquals(interceptError[LinearUnused](dropping.checkedEnv), LinearUnused("t"))
  }
}
