package com.raccoonlang

/**
 * Parse errors, each reached at every position its syntax can stand in: a definition's header, a lambda's header, a
 * function type's binder in a type and in a term position, and a constructor's field. An error inside a binder is
 * reported as itself, not swallowed into a generic failure of the enclosing type.
 *
 * A fragment marks where its error is reported with `@`, which the program does not contain.
 */
class ParseErrorTests extends munit.FunSuite {

  /** The positions a type stands in, each as the program that puts a type there. */
  private val typePositions: Vector[String => String] = Vector(
    t => s"def f (x: $t): Nat := 0\n", // a definition's parameter
    t => s"def f (n: Nat): $t := n\n", // a definition's result
    t => s"def f : Nat := (fun (x: $t): Nat => 0)(0)\n", // a lambda's parameter
    t => s"def f : Nat := (fun (n: Nat): $t => n)(0)\n", // a lambda's result
    t => s"def f (h: (x: $t) -> Nat): Nat := 0\n", // a function type's binder in a type position
    t => s"def f (h: {x: $t} -> Nat): Nat := 0\n", // its implicit binder
    t => s"def f : Type := (x: $t) -> Nat\n", // a function type's binder in a term position
    t => s"inductive W : Type\n | mk (x: $t) : W\n" // a constructor's field
  )

  /** The message and offset of the parse error `marked` reports where its `@` stands. */
  private def expectParseError(marked: String, message: String)(implicit loc: munit.Location): Unit = {
    val at = marked.indexOf('@')
    assert(at >= 0, s"no @ in $marked")
    val source = marked.patch(at, "", 1)
    LanguageParser.parseProgram(source) match {
      case Failure(_, curIdx, reported) =>
        assertEquals(reported, message, source)
        assertEquals(source.substring(curIdx), source.substring(at), source)
      case _: Success[_] => fail(s"expected a parse error in:\n$source")
    }
  }

  private def expectParses(source: String)(implicit loc: munit.Location): Unit =
    LanguageParser.parseProgram(source) match {
      case _: Success[_]                => ()
      case Failure(_, curIdx, reported) => fail(s"$reported at ${source.substring(curIdx)} in:\n$source")
    }

  private def everywhere(fragment: String, message: String)(implicit loc: munit.Location): Unit =
    typePositions.foreach(program => expectParseError(program(fragment), message))

  test("each position parses a well-formed sort and function type") {
    Vector("Type", "Sort { level = Level.one }", " Nat -> Nat").foreach { t =>
      typePositions.foreach(program => expectParses(program(t)))
    }
  }

  test("a sort's field list is nonempty and names each known field once") {
    everywhere("Sort @{}", "Empty field list")
    everywhere("Type @{}", "Empty field list")
    everywhere("Sort { level = Level.one, @size = 1 }", "Unknown field size")
    everywhere("Sort { level = Level.one, @level = Level.one }", "Repeated field level")
  }

  test("Sort requires its level, bare or applied, and Type and Prop fix theirs") {
    everywhere("@Sort", "Sort requires a level field")
    everywhere("@Sort(Level.one)", "Sort requires a level field")
    everywhere("Type { @level = Level.one }", "Misplaced field level: Type fixes the level")
    everywhere("Prop { @level = Level.zero }", "Misplaced field level: Prop fixes the level")
  }

  // A match stands only where a term does: a type's grammar has none, so a header, a binder or a field cannot hold one.
  test("a match without returning is a parse error in a definition's body and a lambda's") {
    val cases = " with\n | .zero => 0\n | .succ k => k\n"
    val positions = Vector(
      s"def f (n: Nat): Nat := match n@$cases",
      s"def f : Nat -> Nat := fun (n: Nat): Nat => match n@$cases",
      s"def f (n: Nat): Nat := {\n  let m := match n@$cases  m\n}\n"
    )
    positions.foreach(expectParseError(_, "Failed to parse returning clause"))
  }

  // `returning` continues the match header, as an arrow continues a function type.
  test("a match's returning clause may start the next line") {
    expectParses("def f (n: Nat): Nat := match n\n  returning Nat with\n | .zero => 0\n | .succ k => k\n")
    expectParses(
      "def f (n: Nat): Nat := match n\n  // the motive\n  returning Nat with\n | .zero => 0\n | .succ k => k\n"
    )
  }

  test("a parse failure names what was expected, never a parser object") {
    expectParseError("def f : Nat := 0\n@)\n", "Failed to parse end of input")
    expectParseError("def f (n: Nat): Nat := Nat.add(n@\n", "Failed to parse LayoutSymTight())")
  }
}
