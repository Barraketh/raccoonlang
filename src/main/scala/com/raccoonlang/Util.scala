package com.raccoonlang

object Util {
  case class NEL[+A](head: A, tail: List[A]) {
    def apply(idx: Int): A = {
      if (idx == 0) head
      else tail(idx - 1)
    }
    def ::[B >: A](elem: B): NEL[B] = NEL(elem, toList)

    def :::[B >: A](prefix: NEL[B]): NEL[B] = NEL(prefix.head, prefix.tail ::: toList)

    def :::[B >: A](prefix: Vector[B]): NEL[B] =
      if (prefix.isEmpty) this else NEL(prefix.head, prefix.tail.toList ::: toList)

    def :+[B >: A](elem: B): NEL[B] = NEL(head, tail :+ elem)

    def :++[B >: A](next: Vector[B]): NEL[B] = NEL(head, tail :++ next)

    def map[B](f: A => B): NEL[B] = NEL(f(head), tail.map(f))

    def take(toTake: Int): NEL[A] = {
      if (toTake == 0) throw new RuntimeException("Cannot take 0 args")
      NEL(head, tail.take(toTake - 1))
    }

    def length: Int = tail.length + 1

    def zip[B](others: NEL[B]): NEL[(A, B)] = NEL((head, others.head), tail.zip(others.tail))

    def foldLeft[B](z: B)(op: (B, A) => B): B = toList.foldLeft(z)(op)

    def foreach(f: A => Unit): Unit = {
      f(head)
      tail.foreach(f)
    }

    def forall(op: A => Boolean): Boolean = op(head) && tail.forall(op)

    def exists(op: A => Boolean): Boolean = op(head) || tail.exists(op)

    def toList: List[A] = head :: tail

    def toVector: Vector[A] = Vector(head) :++ tail

    override def toString: String = (head :: tail).toString()
  }
  case object NEL {
    def mk[A](vector: Vector[A]): NEL[A] = NEL(vector.head, vector.tail.toList)
    def mk[A](list: List[A]): NEL[A] = NEL(list.head, list.tail)

    def mkOpt[A](list: List[A]): Option[NEL[A]] = if (list.isEmpty) None else Some(NEL(list.head, list.tail))

    def one[A](elem: A): NEL[A] = NEL(elem, Nil)
  }

}
