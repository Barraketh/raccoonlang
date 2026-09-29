package com.raccoonlang

import com.raccoonlang.CoreAst.{Decl, Term}

import java.nio.file.{Files, Path, Paths}
import scala.jdk.CollectionConverters._

/**
 * A Pi's, lambda's, match's or `scope` term's node identity is where its span starts, and the keys built from it decide
 * conversion and name atoms (docs/kernel.md#value-identity). So two such nodes of one kind may share an identity only
 * when they are the same syntax, as a selector's result type is both where its header and its match's motive use it.
 * This holds the elaborator to that across every program at hand: the bundled preludes, the examples and each
 * diagnostic fixture's program.
 */
class NodeIdentityTests extends munit.FunSuite {

  /** The identity-bearing nodes of a term, at any depth. */
  private def identityNodes(term: Term): Vector[Term] = {
    val own = term match {
      case _: Term.Pi | _: Term.Lam | _: Term.Match | _: Term.Scope => Vector(term)
      case _                                                        => Vector.empty
    }
    own ++ CoreAst.children(term).flatMap(identityNodes)
  }

  /** Every term a declaration elaborates to, with the family and constructor types the inductive checks build. */
  private def declTerms(decl: Decl): Vector[Term] =
    decl match {
      case d: Decl.ConstDecl =>
        d.ty +: (d.body match {
          case CoreAst.ConstBody.TermBody(term) => Vector(term)
          case _: CoreAst.ConstBody.Builtin     => Vector.empty
        })
      case d: Decl.AxiomDecl => Vector(d.ty)
      case d: Decl.InductiveDecl =>
        InductiveChecks.familyTypeTerm(d) +: d.ctors.map(InductiveChecks.constructorTypeTerm(d.header, _))
      case block: Decl.InductiveBlock => block.families.flatMap(declTerms)
      case block: Decl.RecursiveDefBlock =>
        block.definitions.flatMap { definition =>
          val measure = definition.decreases match {
            case CoreAst.DecreaseSpec.Measure(term, _) => Vector(term)
            case _: CoreAst.DecreaseSpec.Lexicographic => Vector.empty
          }
          Vector(definition.ty, definition.body) ++ measure
        }
    }

  private def programTerms(program: CoreAst.Program): Vector[Term] =
    program.decls.flatMap(declTerms) ++ program.body

  private def localRefs(part: Any): Set[CoreAst.LocalRef] =
    part match {
      case ref: CoreAst.LocalRef => Set(ref)
      case many: Iterable[_]     => many.iterator.flatMap(localRefs).toSet
      case product: Product      => product.productIterator.flatMap(localRefs).toSet
      case _                     => Set.empty
    }

  /**
   * A node's syntax, spans included, up to the naming of its locals: each is numbered by the order it was bound in,
   * which is its id's. A node's captures are listed in that order too, so two nodes with one identity and one syntax
   * denote the same thing under the same captures.
   */
  private def syntax(node: Term): String = {
    val number = localRefs(node).toVector.sortBy(_.id).zipWithIndex.toMap
    def render(part: Any): String =
      part match {
        case ref: CoreAst.LocalRef => s"#${number(ref)}"
        case many: Iterable[_]     => many.map(render).mkString("[", ",", "]")
        case product: Product => product.productIterator.map(render).mkString(s"${product.productPrefix}(", ",", ")")
        case other            => other.toString
      }
    render(node)
  }

  private def racFiles(root: Path): Vector[Path] =
    Files.walk(root).iterator().asScala.filter(_.toString.endsWith(".rac")).toVector.sorted

  /** A program's Core, or none when it does not load or elaborate: a fixture may exist to fail there. */
  private def elaborated(entry: Path): Option[CoreAst.Program] =
    try {
      val loaded = ModuleLoader.load(entry, ModuleLoader.LoadConfig(Vector(entry.getParent), Prelude.default))
      Some(Elaborator.elab(loaded.program, Prelude.default))
    } catch {
      case _: ModuleLoader.LoadFailure | _: Diagnostic => None
    }

  test("no two identity-bearing nodes of one kind with different syntax share a node identity") {
    val fixtures =
      racFiles(Paths.get("src", "test", "resources", "diagnostics")).filter(_.getFileName.toString == "main.rac")
    val programs =
      Vector(Prelude.default.core, Prelude.test.core) ++ (racFiles(Paths.get("examples")) ++ fixtures)
        .flatMap(elaborated)
    assert(programs.length > fixtures.length / 2, s"only ${programs.length} programs elaborated")

    val nodes = programs.flatMap(programTerms).flatMap(identityNodes)
    val clashes =
      nodes
        .groupBy(node => (node.getClass.getSimpleName, node.span.nodeId))
        .toVector
        .collect {
          case ((kind, id), sharing) if sharing.length > 1 && sharing.map(syntax).distinct.length > 1 =>
            s"$kind ${id.stableName}: ${sharing.map(_.toString).distinct.mkString(" | ")}"
        }
    assertEquals(clashes, Vector.empty[String])
  }
}
