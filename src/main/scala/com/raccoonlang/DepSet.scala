package com.raccoonlang

import org.roaringbitmap.RoaringBitmap

final class DepSet private (private val bitmap: RoaringBitmap) {
  def contains(id: Int): Boolean = bitmap.contains(id)

  def isEmpty: Boolean = bitmap.isEmpty

  def nonEmpty: Boolean = !isEmpty

  def +(id: Int): DepSet = {
    val next = bitmap.clone()
    next.add(id)
    new DepSet(next)
  }

  def ++(other: DepSet): DepSet =
    if (other.isEmpty) this
    else if (isEmpty) other
    else {
      val next = bitmap.clone()
      next.or(other.bitmap)
      new DepSet(next)
    }

  def &(other: DepSet): DepSet =
    if (isEmpty || other.isEmpty) DepSet.empty
    else {
      val next = bitmap.clone()
      next.and(other.bitmap)
      new DepSet(next)
    }

  def --(other: DepSet): DepSet =
    if (isEmpty || other.isEmpty) this
    else {
      val next = bitmap.clone()
      next.andNot(other.bitmap)
      new DepSet(next)
    }

  def foreach(f: Int => Unit): Unit = {
    val it = bitmap.getIntIterator
    while (it.hasNext) f(it.next())
  }

  def toRoaringBitmap: RoaringBitmap = bitmap.clone()

  override def equals(obj: Any): Boolean =
    obj match {
      case other: DepSet => bitmap == other.bitmap
      case _             => false
    }

  override def hashCode(): Int = bitmap.hashCode()

  override def toString: String = {
    val ids = Vector.newBuilder[Int]
    foreach(ids += _)
    ids.result().mkString("DepSet(", ", ", ")")
  }
}

object DepSet {
  val empty: DepSet = new DepSet(new RoaringBitmap)

  def apply(ids: Int*): DepSet = from(ids)

  def unionAll(sets: DepSet*): DepSet = {
    val builder = newBuilder
    sets.foreach(builder.unionInPlace)
    builder.result()
  }

  def from(ids: IterableOnce[Int]): DepSet = {
    val builder = newBuilder
    ids.iterator.foreach(builder.add)
    builder.result()
  }

  def newBuilder: Builder = new Builder

  def newBuilder(ids: DepSet): Builder = new Builder().unionInPlace(ids)

  final class Builder private[DepSet] {
    private val bitmap = new RoaringBitmap

    def isEmpty: Boolean = bitmap.isEmpty

    def add(id: Int): this.type = {
      bitmap.add(id)
      this
    }

    def unionInPlace(ids: DepSet): this.type = {
      bitmap.or(ids.bitmap)
      this
    }

    def unionInPlace(ids: Builder): this.type = {
      bitmap.or(ids.bitmap)
      this
    }

    def diffInPlace(ids: Builder): this.type = {
      bitmap.andNot(ids.bitmap)
      this
    }

    def result(): DepSet = new DepSet(bitmap.clone())
  }
}
