package com.raccoonlang

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path}

/**
 * Golden files: expected outputs kept under `src/test/resources` and compared verbatim. Regenerate every golden with
 * `sbt -batch -Draccoon.goldens.regenerate=true test`, then read the diff: it is the review artifact for the change.
 */
trait Goldens { this: munit.FunSuite =>
  private val regenerate: Boolean = sys.props.get("raccoon.goldens.regenerate").contains("true")

  /** `actual` is the content of the golden `file`, or becomes it when regenerating. */
  protected def assertGolden(file: Path, actual: String)(implicit loc: munit.Location): Unit =
    if (regenerate) Files.write(file, actual.getBytes(StandardCharsets.UTF_8))
    else {
      assert(Files.isRegularFile(file), s"missing golden $file; regenerate the goldens")
      assertNoDiff(actual, Files.readString(file))
    }
}
