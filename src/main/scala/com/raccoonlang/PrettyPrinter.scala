package com.raccoonlang

object PrettyPrinter {
  def printTerm(term: CoreAst.Ast): String = term match {
    case CoreAst.Term.GlobalRef(name, _)          => name
    case CoreAst.Term.LocalRef(ref, _)            => ref.name
    case CoreAst.Term.NatLit(value, _)            => value.toString
    case CoreAst.Term.StrLit(scalars, _)          => UnicodeScalarString.renderQuoted(scalars)
    case CoreAst.Term.Select(base, field, _)      => s"${printTerm(base)}.$field"
    case CoreAst.Term.Pi(binders, out, _, _)      => binders.map(printBinder).mkString + s" -> ${printTerm(out)}"
    case CoreAst.Term.App(fn, args, _)            => s"${printTerm(fn)}(${args.map(printTerm).mkString(", ")})"
    case CoreAst.Term.Lam(_, body, _, name, _, _) => s"fun ${name.getOrElse("")} => ${printTerm(body)}"
    case CoreAst.Term.Body(lets, res, _) =>
      (lets.map(l => s"let ${l.name} := ${printTerm(l.value)}") :+ printTerm(res)).mkString("{ ", "; ", " }")
    case CoreAst.Term.Match(scrut, _, cases, _) =>
      s"match ${printTerm(scrut)} { ${cases.map(c => s"${c.ctorName} => ${printTerm(c.body)}").mkString("; ")} }"
    case _: CoreAst.DecreaseSpec => "<decrease>"
  }

  def printBinder(binder: CoreAst.Binder): String = {
    val braces = if (binder.isImplicit) ("{", "}") else ("(", ")")
    s"${braces._1}${binder.name}: ${printTerm(binder.ty)}${braces._2}"
  }

  def print(value: Value): String = value match {
    case Value.VSort(level)                      => if (level == 0) "Type" else s"Sort($level)"
    case Value.LevelTpe                          => "Level"
    case Value.VPi(_, _, _, _, _, _, _)          => "Pi"
    case Value.VLam(_, _, _)                     => "<lambda>"
    case Value.VApp(head, args, _, _)            => s"${print(head)}(${args.map(print).mkString(", ")})"
    case Value.VConst(name, _, _)                => name
    case Value.NeutralThunk(_, _, _, _, _)       => "<match>"
    case Value.Var(name, id, _)                  => s"$name#$id"
    case Value.ConstructorHead(name, _, _, _, _) => name
  }
}
