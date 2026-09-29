package com.raccoonlang

/**
 * The identity of a Pi, lambda, match or `scope` node (docs/kernel.md#value-identity): what a closure's or stuck
 * match's key and a `scope` term's atom are made from. Only `fresh` makes one, so two nodes share an identity exactly
 * when one is the other rebuilt: whoever makes a node allocates it a fresh identity, and whoever rebuilds one, as the
 * checker does with its residual, carries the identity over. A span is only where a node was written.
 */
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
