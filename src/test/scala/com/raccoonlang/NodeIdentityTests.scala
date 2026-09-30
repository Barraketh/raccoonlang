package com.raccoonlang

import com.raccoonlang.CoreAst.{Decl, Term}

import java.nio.file.{Files, Path, Paths}
import scala.jdk.CollectionConverters._

/**
 * A Pi's, lambda's, match's or `scope` term's node identity is a field of its own, and the keys built from it decide
 * conversion and name atoms (docs/kernel.md#value-identity). So two nodes may share an identity only when one is the
 * other rebuilt, and a residual keeps the identity of the node it rebuilds. This holds the elaborator and the checker
 * to that across every program at hand: the bundled preludes, the examples and each diagnostic fixture's program.
 */
class NodeIdentityTests extends munit.FunSuite {

  private def identity(term: Term): Option[NodeId] =
    term match {
      case pi: Term.Pi       => Some(pi.id)
      case lam: Term.Lam     => Some(lam.id)
      case m: Term.Match     => Some(m.id)
      case scope: Term.Scope => Some(scope.id)
      case _                 => None
    }

  /** The identity-bearing nodes of a term, at any depth. */
  private def identityNodes(term: Term): Vector[Term] =
    identity(term).map(_ => term).toVector ++ CoreAst.children(term).flatMap(identityNodes)

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

  /** The bundled preludes. They are checked from the kernel's initial environment, the other programs after one. */
  private lazy val preludes: Vector[CoreAst.Program] = Vector(Prelude.default.core, Prelude.test.core)

  private lazy val programs: Vector[CoreAst.Program] = {
    val fixtures =
      racFiles(Paths.get("src", "test", "resources", "diagnostics")).filter(_.getFileName.toString == "main.rac")
    val programs = (racFiles(Paths.get("examples")) ++ fixtures).flatMap(elaborated)
    assert(programs.length > fixtures.length / 2, s"only ${programs.length} programs elaborated")
    programs
  }

  test("distinct identity-bearing nodes never share a node identity") {
    val nodes = (preludes ++ programs).flatMap(program => program.decls.flatMap(declTerms) ++ program.body)
    val clashes =
      nodes
        .flatMap(identityNodes)
        .groupBy(node => identity(node).get)
        .toVector
        .collect {
          case (id, sharing) if !sharing.forall(_ eq sharing.head) =>
            s"$id: ${sharing.map(_.toString).distinct.mkString(" | ")}"
        }
    assertEquals(clashes, Vector.empty[String])
  }

  /**
   * Where a residual rebuilds an identity-bearing node, whether it keeps that node's identity. A residual has its
   * source's shape, except that a selected field `base.f` checks to the call `P.f(base)`.
   */
  private def rebuildMismatches(source: Term, residual: Term): Vector[String] =
    (source, residual) match {
      case (Term.Select(base, _, _), Term.App(_, Vector(checkedBase), _, _)) => rebuildMismatches(base, checkedBase)
      case _ =>
        val (sourceChildren, residualChildren) = (CoreAst.children(source), CoreAst.children(residual))
        if (source.getClass != residual.getClass || sourceChildren.length != residualChildren.length)
          Vector(s"$source was rebuilt as $residual")
        else if (identity(source) != identity(residual)) Vector(s"$source was rebuilt with another identity")
        else sourceChildren.zip(residualChildren).flatMap { case (s, r) => rebuildMismatches(s, r) }
    }

  /**
   * Each of a declaration's terms paired with the checker's residual of it, checked where the declaration stands. A
   * recursive group's member is checked to a lambda, which rebuilds the member. The inductive checks keep no residual.
   */
  private def residuals(decl: Decl, env: Env): Vector[(Term, Term)] =
    decl match {
      case d: Decl.ConstDecl =>
        val ty = TypeChecker.checkDeclType(d.ty, env)
        (d.ty -> ty.residual) +: (d.body match {
          case CoreAst.ConstBody.TermBody(term) => Vector(term -> TypeChecker.checkTerm(term, ty.value, env).residual)
          case _: CoreAst.ConstBody.Builtin     => Vector.empty
        })
      case d: Decl.AxiomDecl => Vector(d.ty -> TypeChecker.checkDeclType(d.ty, env).residual)
      case _: Decl.InductiveDecl | _: Decl.InductiveBlock => Vector.empty
      case block: Decl.RecursiveDefBlock =>
        block.definitions.zip(TypeChecker.checkRecursiveDefBlock(block, env)).map { case (definition, checked) =>
          val member =
            Term.Lam(definition.ty, definition.body, definition.span, definition.id, Some(definition.name), None)
          member -> checked.residual
        }
    }

  /** A program's residuals, declaration by declaration, up to its first failure: a fixture may exist to fail. */
  private def programResiduals(program: CoreAst.Program, initial: Env, trusted: Boolean): Vector[(Term, Term)] = {
    val found = Vector.newBuilder[(Term, Term)]
    try {
      val env = program.decls.foldLeft(initial) { (env, decl) =>
        found ++= residuals(decl, env)
        Interpreter.evalDecl(decl, env, trusted)
      }
      program.body.foreach(body => found += body -> TypeChecker.checkTerm(body, env).residual)
    } catch { case _: Diagnostic => }
    found.result()
  }

  test("every residual node keeps the identity of the node it rebuilds") {
    val pairs =
      preludes.flatMap(programResiduals(_, Interpreter.preludeInitialEnv, trusted = true)) ++
        programs.flatMap(programResiduals(_, Prelude.default.checkedEnv, trusted = false))
    val compared = pairs.flatMap(pair => identityNodes(pair._2)).length
    assert(compared > 500, s"only $compared residual nodes were compared")
    assertEquals(pairs.flatMap { case (source, residual) => rebuildMismatches(source, residual) }, Vector.empty[String])
  }

  // The F2 class: `(Nat -> Nat) -> Nat` and its domain `Nat -> Nat`, written at one span. When a span's start was a
  // node's identity they had one key, which decided that they were convertible.
  test("two function types written at one span with different syntax have different identities and keys") {
    val env = Prelude.default.checkedEnv
    val span = Span(0, 0, None)
    val nat = Term.GlobalRef("Nat", span)
    def arrow(domain: Term, ref: Int): Term.Pi =
      Term.Pi(
        Vector(
          CoreAst.Binder(CoreAst.LocalRef(ref, "x"), domain, span, CoreAst.BinderSite.Function, BinderMode.Explicit)
        ),
        nat,
        CoreAst.Closure.unrestricted(span),
        span,
        NodeId.fresh()
      )
    val domain = arrow(nat, 0)
    val outer = arrow(domain, 1)
    assertNotEquals(domain.id, outer.id)

    val (checkedDomain, checkedOuter) = (TypeChecker.checkTerm(domain, env), TypeChecker.checkTerm(outer, env))
    assertEquals(identity(checkedDomain.residual), Some(domain.id))
    assertEquals(identity(checkedOuter.residual), Some(outer.id))
    assertNotEquals(checkedDomain.value.key, checkedOuter.value.key)
    assert(!ValueEquivalence.defEq(checkedDomain.value, checkedOuter.value))
  }
}
