package com.raccoonlang

import java.util.concurrent.atomic.AtomicLong

/**
 * Process-local unique semantic identity for closure-producing syntax, distinct from diagnostic source locations. New
 * or code-changing syntax gets a fresh ID; checked residuals preserve the ID. An ID may be shared only by
 * representations of the same code.
 */
final class NodeId private (val value: Long) extends AnyVal {
  override def toString: String = s"NodeId($value)"
}

object NodeId {
  private val nextValue = new AtomicLong(0L)

  def fresh(): NodeId = new NodeId(nextValue.updateAndGet(n => Math.incrementExact(n)))
}
