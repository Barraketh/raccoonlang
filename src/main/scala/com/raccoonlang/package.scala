package com

/** Raising and locating diagnostics; see `Errors.scala`. */
package object raccoonlang {

  /** Raise an unlocated error; the nearest enclosing boundary supplies the span. */
  def fail(error: TypeError): Nothing = throw Diagnostic(error, None, Vector.empty)

  /** Raise a broken kernel invariant. Not a program error: it keeps its stack trace and is reported as a kernel bug. */
  def wtf(reason: String): Nothing = throw new InternalError(reason)

  /**
   * Locate anything raised inside `body` at `span` unless already located. For sites that know a more specific node
   * than the enclosing term; everything else is located by the checker boundaries.
   */
  def at[A](span: Span)(body: => A): A =
    try body
    catch {
      case diagnostic: Diagnostic if diagnostic.span.isEmpty => throw diagnostic.copy(span = Some(span))
      case internal: InternalError =>
        internal.locate(span)
        throw internal
    }

  /** Append `frame` to a failure passing through. By-name, so it costs nothing unless something was caught. */
  def framed[A](frame: => Frame)(body: => A): A =
    try body
    catch {
      case diagnostic: Diagnostic => throw diagnostic.copy(frames = diagnostic.frames :+ frame)
    }
}
