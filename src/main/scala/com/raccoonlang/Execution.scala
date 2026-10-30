package com.raccoonlang

/** Where checking and evaluation run (docs/kernel.md, "Evaluation depth"). */
object Execution {

  /**
   * `body` run on a thread of its own whose stack is `stackBytes` bytes, as `Thread` takes it (the JVM may round it,
   * and zero leaves it to the JVM's default); the caller waits for it. What `body` returns is returned, and what it
   * throws, a stack overflow included, is rethrown here: nothing is caught on the way.
   *
   * Checking and evaluation recurse on the host stack, so this is how a caller chooses their depth: the CLI runs its
   * whole pipeline on one, of `--stack` bytes.
   */
  def onStack[A](stackBytes: Long)(body: => A): A = {
    var outcome: Either[Throwable, A] = Left(new IllegalStateException("the checking thread did not finish"))
    val thread = new Thread(
      null,
      () =>
        outcome =
          try Right(body)
          catch { case thrown: Throwable => Left(thrown) },
      "raccoon-check",
      stackBytes
    )
    thread.start()
    thread.join()
    outcome.fold(throw _, identity)
  }
}
