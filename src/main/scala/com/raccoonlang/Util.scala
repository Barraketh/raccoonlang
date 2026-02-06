package com.raccoonlang

import scala.annotation.tailrec

object Util {
  case class NEL[+A](head: A, tail: List[A]) {
    def ::[B >: A](elem: B): NEL[B] = NEL(elem, toList)

    def :::[B >: A](prefix: NEL[B]): NEL[B] = NEL(prefix.head, prefix.tail ::: toList)

    def :::[B >: A](prefix: Vector[B]): NEL[B] =
      if (prefix.isEmpty) this else NEL(prefix.head, prefix.tail.toList ::: toList)

    def :+[B >: A](elem: B): NEL[B] = NEL(head, tail :+ elem)

    def :++[B >: A](next: Vector[B]): NEL[B] = NEL(head, tail :++ next)

    def map[B](f: A => B): NEL[B] = NEL(f(head), tail.map(f))

    def length: Int = tail.length + 1

    def splitAt(idx: Int): (NEL[A], Option[NEL[A]]) = {
      val (headL, tailL) = (head :: tail).splitAt(idx)
      (NEL.mk(headL), NEL.mkOpt(tailL))
    }

    def zip[B](others: NEL[B]): NEL[(A, B)] = NEL((head, others.head), tail.zip(others.tail))

    def foldLeft[B](z: B)(op: (B, A) => B): B = toList.foldLeft(z)(op)

    def foldWhile[B](z: B)(op: (B, A) => (B, Boolean)): B = {
      @tailrec
      def loop(l: List[A], curB: B): B = {
        if (l.isEmpty) curB
        else {
          val (nextB, isDone) = op(curB, l.head)
          if (isDone) nextB
          else loop(l.tail, nextB)
        }
      }

      loop(toList, z)
    }

    def forall(op: A => Boolean): Boolean = op(head) && tail.forall(op)

    def toList: List[A] = head :: tail
  }
  case object NEL {
    def mk[A](vector: Vector[A]): NEL[A] = NEL(vector.head, vector.tail.toList)
    def mk[A](list: List[A]): NEL[A] = NEL(list.head, list.tail)

    def mkOpt[A](list: List[A]): Option[NEL[A]] = if (list.isEmpty) None else Some(NEL(list.head, list.tail))

    def one[A](elem: A): NEL[A] = NEL(elem, Nil)
  }

}
