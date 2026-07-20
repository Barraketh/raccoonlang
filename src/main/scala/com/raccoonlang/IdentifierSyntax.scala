package com.raccoonlang

private[raccoonlang] object IdentifierSyntax {
  val keywords: Set[String] = Set(
    "fun",
    "let",
    "match",
    "as",
    "returning",
    "with",
    "opaque",
    "axiom",
    "def",
    "inductive",
    "struct",
    "namespace",
    "open",
    "import",
    "builtin",
    "decreases",
    "structural",
    "lexicographic",
    "measure",
    "indices",
    "in"
  )

  def isStart(char: Char): Boolean = char.isLetter
  def isContinue(char: Char): Boolean = char.isLetterOrDigit || char == '_'

  def isAtom(value: String): Boolean =
    value.nonEmpty && isStart(value.head) && value.tail.forall(isContinue) && !keywords(value)
}
