package com.raccoonlang

/** Core sort terms for suites that build Core syntax by hand. */
object CoreTestTerms {
  private def nullary(form: CoreAst.Form, span: Span): CoreAst.Term = CoreAst.Term.FormOp(form, Vector.empty, span)

  def sortAt(level: CoreAst.Form, span: Span): CoreAst.Term.Sort = sortAt(nullary(level, span), span)

  def sortAt(level: CoreAst.Term, span: Span): CoreAst.Term.Sort =
    CoreAst.Term.Sort(level, span)
}
