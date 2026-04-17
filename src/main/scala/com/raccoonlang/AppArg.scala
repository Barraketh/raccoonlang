package com.raccoonlang

sealed trait AppArg[+A] {
  def value: A
  def span: Span

  def map[B](f: A => B): AppArg[B]
}

object AppArg {
  final case class Pos[A](value: A, span: Span) extends AppArg[A] {
    override def map[B](f: A => B): AppArg[B] = Pos(f(value), span)
  }

  final case class Named[A](name: String, value: A, span: Span) extends AppArg[A] {
    override def map[B](f: A => B): AppArg[B] = Named(name, f(value), span)
  }
}
