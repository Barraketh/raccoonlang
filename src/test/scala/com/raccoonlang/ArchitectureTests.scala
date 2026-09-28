package com.raccoonlang

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path, Paths}
import scala.jdk.CollectionConverters._
import scala.util.matching.Regex

/**
 * Kernel invariants the compiler cannot enforce, stated as source patterns forbidden in `src/main`. A rule names the
 * invariant, the pattern that would break it, and the only files (by name) where the pattern belongs. Adding an
 * invariant is adding one rule.
 */
class ArchitectureTests extends munit.FunSuite {
  import ArchitectureTests.Rule

  private val rules = Vector(
    Rule("sorts are built through Sorts, not the removed PropTpe/TypeTpe", raw"\b(PropTpe|TypeTpe)\b".r, Set.empty),
    Rule("only Sorts builds a sort", raw"\bnew\s+VSort\b".r, Set("Sorts.scala")),
    Rule(
      "only Sorts asks whether a sort is Prop",
      raw"[=!]=\s*Level\.zero\b|\bLevel\.zero\s*[=!]=".r,
      Set("Sorts.scala")
    ),
    Rule(
      "checking is synthesis plus equality: only TypeChecker.check takes an optional expected type",
      raw"\bexpected\w*\s*:\s*Option\[".r,
      Set("TypeChecker.scala")
    )
  )

  private val mainRoot: Path = Paths.get("src", "main").toAbsolutePath.normalize

  test("src/main breaks no architecture rule") {
    val sources = Files.walk(mainRoot).iterator().asScala.filter(_.toString.endsWith(".scala")).toVector.sorted
    val violations = for {
      source <- sources
      rule <- rules if !rule.allowedIn.contains(source.getFileName.toString)
      (line, index) <- Files.readAllLines(source, StandardCharsets.UTF_8).asScala.zipWithIndex
      if rule.forbidden.findFirstIn(line).nonEmpty
    } yield s"${mainRoot.relativize(source)}:${index + 1}: ${rule.invariant}: ${line.trim}"
    assert(sources.nonEmpty, s"no Scala sources under $mainRoot")
    assert(violations.isEmpty, violations.mkString("\n"))
  }
}

object ArchitectureTests {
  private final case class Rule(invariant: String, forbidden: Regex, allowedIn: Set[String])
}
