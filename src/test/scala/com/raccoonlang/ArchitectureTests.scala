package com.raccoonlang

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path, Paths}
import scala.jdk.CollectionConverters._
import scala.util.matching.Regex

/**
 * Kernel invariants the compiler cannot enforce, stated as source patterns forbidden in `src/main`. A rule names the
 * invariant, the pattern that would break it, and the files (by name) where the pattern belongs. Adding an invariant is
 * adding one rule.
 */
class ArchitectureTests extends munit.FunSuite {
  import ArchitectureTests.Rule

  private val kernelObjects = "(LevelTpe|KindTpe|SortParameter|Large)"

  private val rules = Vector(
    Rule("sorts are built through Sorts, not the removed PropTpe/TypeTpe", raw"\b(PropTpe|TypeTpe)\b".r, Set.empty),
    Rule("only Sorts builds a sort", raw"\bnew\s+VSort\b".r, Set("Sorts.scala")),
    Rule(
      "only Sorts asks whether a sort is Prop",
      raw"[=!]=\s*Level\.zero\b|\bLevel\.zero\s*[=!]=".r,
      Set("Sorts.scala")
    ),
    Rule(
      "sort formers and the sort parameters' forms are syntax the kernel owns, never names of globals or builtins",
      "\"(Sort|Type|Prop|Level\\.(zero|one|succ|max|imax)|Kind\\.(unr|lin|join))\"".r,
      Set("IdentifierSyntax.scala", "LanguageParser.scala", "PrettyPrinter.scala")
    ),
    Rule(
      "lifetime scope support is absent from the compiler API and kernel",
      raw"\b(LifetimeTpe|LifetimeEscapes|LifetimeEmpty|LifetimeUnion|ScopeField|closureScope|mentionedScope|openAtoms)\b".r,
      Set.empty
    ),
    Rule(
      "where a sort parameter, an expression of one or a large type may stand is decided only by the checker's " +
        "position rules and the Pi classifier",
      raw"(\beq|[=!]=)\s*$kernelObjects\b|\b$kernelObjects\s*(\beq\b|[=!]=)".r,
      Set("TypeChecker.scala", "Interpreter.scala")
    ),
    Rule(
      "a function type's value is built only by evaluating its syntax, so its closure is always its syntax's",
      raw"\bVPi\(".r,
      Set("Value.scala", "Interpreter.scala")
    ),
    Rule(
      "checking is synthesis plus equality: only TypeChecker.check takes an optional expected type",
      raw"\bexpected\w*\s*:\s*Option\[".r,
      Set("TypeChecker.scala")
    ),
    Rule(
      "the ledger's walk has no wildcard arm, so a new Core term is a compile error there until it is counted",
      raw"\bcase\s+(_|[a-z]\w*)\s*(=>|\bif\b)".r,
      _ != "Ledger.scala"
    ),
    Rule(
      "tokens stay out of types and proofs by one test, TypeChecker.tokenInTypeOrProof, which alone raises LinearInType",
      raw"\bLinearInType\(".r,
      Set("TypeChecker.scala", "Errors.scala", "ErrorRendering.scala")
    ),
    Rule(
      "uses of a linear local are counted only by the ledger",
      raw"\bLinear(Unused|Reused)\(".r,
      Set("Ledger.scala", "Errors.scala", "ErrorRendering.scala")
    ),
    Rule(
      "sealing is one decision, Sealing.accessible, and only Sealing raises SealedConstructor",
      raw"\bSealedConstructor\(".r,
      Set("Sealing.scala", "Errors.scala", "ErrorRendering.scala")
    ),
    Rule(
      "only the trusted prelude declares axioms, decided by Interpreter.evalDecl's bootstrap privilege alone",
      raw"\bUntrustedAxiom\(".r,
      Set("Interpreter.scala", "Errors.scala", "ErrorRendering.scala")
    ),
    Rule(
      "a module is a source file, and only Sealing compares a span's source",
      raw"\.source\s*[=!]=|\.source\.contains\b|[=!]=\s*[\w.]*\.source\b|\bsyntheticSource\b".r,
      Set("Sealing.scala", "Parser.scala")
    ),
    Rule(
      "sealing is asked only where a name resolves to a constructor or selector, of a match's scrutinee family or " +
        "a destructured value's, before evidence is discharged with a constructor, and by implicit projection before " +
        "it reads a constructor's field",
      raw"\bSealing\.(accessible|requireAccessible)\(".r,
      Set("TypeChecker.scala", "MatchChecker.scala", "Discharge.scala", "Projection.scala")
    ),
    Rule(
      "a proof's recovery plan is read only by ProofReconstruction, the one place a proof is reconstructed",
      raw"\.proofRecovery\b".r,
      Set("ProofReconstruction.scala")
    )
  )

  private val mainRoot: Path = Paths.get("src", "main").toAbsolutePath.normalize

  test("src/main breaks no architecture rule") {
    val sources = Files.walk(mainRoot).iterator().asScala.filter(_.toString.endsWith(".scala")).toVector.sorted
    val violations = for {
      source <- sources
      rule <- rules if !rule.allowedIn(source.getFileName.toString)
      (line, index) <- Files.readAllLines(source, StandardCharsets.UTF_8).asScala.zipWithIndex
      if rule.forbidden.findFirstIn(line).nonEmpty
    } yield s"${mainRoot.relativize(source)}:${index + 1}: ${rule.invariant}: ${line.trim}"
    assert(sources.nonEmpty, s"no Scala sources under $mainRoot")
    assert(violations.isEmpty, violations.mkString("\n"))
  }
}

object ArchitectureTests {
  private final case class Rule(invariant: String, forbidden: Regex, allowedIn: String => Boolean)
}
