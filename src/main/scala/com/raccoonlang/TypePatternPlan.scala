package com.raccoonlang

final case class TypePatternPlan(
    pattern: ElabAst.TypePattern,
    expected: ElabAst.TypeTerm,
    captures: Vector[Value.VCapture]
)
