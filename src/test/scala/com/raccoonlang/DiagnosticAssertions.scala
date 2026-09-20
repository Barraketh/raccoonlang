package com.raccoonlang

/**
 * Asserting on what the kernel rejected.
 *
 * An error is plain data now, so a test cannot intercept one directly: what travels is the `Diagnostic` carrying it.
 * These keep the assertion on the payload, which is the part a test means, and return it so the test can go on to check
 * its fields.
 *
 * Checking a whole program reports every independent failure at once, so what it raises is a `CheckFailure` carrying
 * them. A test that asserts on "the error" means the first one, and `interceptDiagnostics` is there for the tests that
 * mean all of them.
 */
trait DiagnosticAssertions { this: munit.FunSuite =>

  /** Run `body`, require it to fail with an `E`, and hand back that error. */
  protected def interceptError[E <: TypeError](
      body: => Any
  )(implicit tag: reflect.ClassTag[E], loc: munit.Location): E = {
    val error = interceptDiagnostic(body).error
    if (tag.runtimeClass.isInstance(error)) error.asInstanceOf[E]
    else fail(s"expected ${tag.runtimeClass.getSimpleName}, got $error")
  }

  /** Run `body` and require it to fail, whatever the error is; the first diagnostic when there are several. */
  protected def interceptDiagnostic(body: => Any)(implicit loc: munit.Location): Diagnostic =
    interceptDiagnostics(body).head

  /** Run `body` and require it to fail, handing back every diagnostic the run collected, in source order. */
  protected def interceptDiagnostics(body: => Any)(implicit loc: munit.Location): Vector[Diagnostic] =
    try {
      body
      fail("expected the program to be rejected, but it was accepted")
    } catch {
      case Execution.CheckFailure(diagnostics) => diagnostics
      case diagnostic: Diagnostic              => Vector(diagnostic)
    }
}
