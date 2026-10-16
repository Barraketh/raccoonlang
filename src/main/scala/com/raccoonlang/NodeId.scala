package com.raccoonlang

/** A stable identity for a function type, lambda or match; rebuilding a checked node preserves its identity. */
final class NodeId private (val value: Int) extends AnyVal {
  override def toString: String = s"NodeId($value)"
}

object NodeId {
  // Like FreshVar, allocation assumes a single checking thread.
  private var next = 0

  def fresh(): NodeId = {
    val result = new NodeId(next)
    next += 1
    result
  }
}
