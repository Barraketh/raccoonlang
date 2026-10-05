package com.raccoonlang

import com.raccoonlang.Value._
import com.raccoonlang.telescope.BinderOps

import scala.collection.mutable

/** The one exact trusted Prelude boundary for running generic serialized byte-buffer programs. */
private[raccoonlang] object NativeBufferBuiltins {
  val Name = "Buffer.Native.executeEncoded"

  private final case class Layout(
      nat: Value,
      listNat: Value,
      listListNat: Value,
      result: Value,
      listNil: ConstructorHead,
      listCons: ConstructorHead,
      pairMk: ConstructorHead,
      natZero: ConstructorHead,
      natSucc: ConstructorHead
  )

  private sealed trait Decoded[+A]
  private final case class Ready[A](value: A) extends Decoded[A]
  private case object NonCanonical extends Decoded[Nothing]
  private case object InvalidInput extends Decoded[Nothing]
  private case object ResourceExceeded extends Decoded[Nothing]

  def instantiate(name: String, tpe: Value, env: Env): Value = {
    if (name != Name) wtf(s"Unexpected native buffer builtin $name")
    val layout = validateType(tpe, env)
    val pi = tpe.asInstanceOf[VPi]
    lazy val self: VLam =
      VLam(
        pi,
        ValueId.Const(name),
        LamBody.Native(
          (args, _) => run(self, args, layout),
          Env.empty,
          isRawRecursive = false,
          scalarCapability = None,
          equation = None
        )
      )
    self
  }

  private def validateType(tpe: Value, env: Env): Layout = {
    def reject(reason: String): Nothing = fail(NativeOperationDeclarationMismatch(Name, reason))
    def global(name: String): Value = env.globals.get(name).map(_.value(env)).getOrElse(reject(s"missing `$name`"))

    val nat = Packed.validateNatFamily(env).natTpe
    val listFamily = global("List") match {
      case value @ VConst("List", Inductive(meta), _)
          if meta.familyArity >= 1 && meta.constructorNames == Vector("List.nil", "List.cons") && meta.seal.isEmpty =>
        value
      case _ => reject("`List` is not the ordinary unary list family")
    }
    val pairFamily = global("Pair") match {
      case value @ VConst("Pair", Inductive(meta), _)
          if meta.familyArity >= 2 && meta.constructorNames == Vector("Pair.mk") && meta.seal.isEmpty =>
        value
      case _ => reject("`Pair` is not the ordinary two-parameter pair family")
    }
    val listNat = applyType("List", Vector(CoreAst.Term.GlobalRef("Nat", Span(0, 0))), env)
    val listListNat = applyType(
      "List",
      Vector(
        CoreAst.Term.App(
          CoreAst.Term.GlobalRef("List", Span(0, 0)),
          Vector(CoreAst.Term.GlobalRef("Nat", Span(0, 0))),
          Vector.empty,
          Span(0, 0)
        )
      ),
      env
    )
    val result = applyType(
      "Pair",
      Vector(
        CoreAst.Term.GlobalRef("Nat", Span(0, 0)),
        CoreAst.Term.App(
          CoreAst.Term.GlobalRef("List", Span(0, 0)),
          Vector(
            CoreAst.Term.App(
              CoreAst.Term.GlobalRef("List", Span(0, 0)),
              Vector(CoreAst.Term.GlobalRef("Nat", Span(0, 0))),
              Vector.empty,
              Span(0, 0)
            )
          ),
          Vector.empty,
          Span(0, 0)
        )
      ),
      env
    )
    if (listFamily.synDeps.nonEmpty || pairFamily.synDeps.nonEmpty)
      reject("standard collection families are not closed")

    def familyArgs(instance: Value, family: Value, label: String): Vector[Value] = {
      val arity = family match {
        case VConst(_, Inductive(meta), _) => meta.familyArity
        case _                             => -1
      }
      instance match {
        case ConstSpine(head, args) if (head eq family) && args.length == arity => args
        case _ => reject(s"`$label` is not the expected closed family instance")
      }
    }
    val listNatArgs = familyArgs(listNat, listFamily, "List Nat")
    val listListNatArgs = familyArgs(listListNat, listFamily, "List (List Nat)")
    val resultArgs = familyArgs(result, pairFamily, "Pair Nat (List (List Nat))")
    Vector(listNat, listListNat, result).foreach { value =>
      if (!ValueEquivalence.defEq(value.tpe, Sorts.Type))
        reject("collection instances must be closed unrestricted types")
    }

    val nil = constructor(global("List.nil"), "List.nil", reject)
    val cons = constructor(global("List.cons"), "List.cons", reject)
    val pairMk = constructor(global("Pair.mk"), "Pair.mk", reject)
    val zero = constructor(global("Nat.zero"), "Nat.zero", reject)
    val succ = constructor(global("Nat.succ"), "Nat.succ", reject)

    requireConstructorShape(nil, listNatArgs, Vector.empty, listNat, reject)
    requireConstructorShape(cons, listNatArgs, Vector(nat, listNat), listNat, reject)
    requireConstructorShape(nil, listListNatArgs, Vector.empty, listListNat, reject)
    requireConstructorShape(cons, listListNatArgs, Vector(listNat, listListNat), listListNat, reject)
    requireConstructorShape(pairMk, resultArgs, Vector(nat, listListNat), result, reject)
    requireConstructorShape(zero, Vector.empty, Vector.empty, nat, reject)
    requireConstructorShape(succ, Vector.empty, Vector(nat), nat, reject)

    tpe match {
      case pi: VPi if pi.binders.length == 2 =>
        if (
          pi.closureKind != Kind.unr || pi.closureScope != Lifetime.empty || pi.mentionedScope != Lifetime.empty || pi.isPropValued
        )
          reject("the native function must be an unrestricted closed function into Type")
        var telescopeEnv = pi.env
        Vector(listNat, listListNat).zip(pi.binders).foreach { case (expected, binder) =>
          if (binder.mode != BinderMode.Explicit) reject("expected two explicit arguments")
          val domain = Interpreter.evalTerm(binder.ty, telescopeEnv)
          if (!ValueEquivalence.defEq(domain, expected)) reject("expected List Nat and List (List Nat) arguments")
          telescopeEnv = BinderOps.freshen(Vector(binder), telescopeEnv)
        }
        if (!ValueEquivalence.defEq(pi.codomain(telescopeEnv), result))
          reject("expected Pair Nat (List (List Nat)) result")
      case _ => reject("expected a two-argument native buffer declaration")
    }

    Layout(nat, listNat, listListNat, result, nil, cons, pairMk, zero, succ)
  }

  private def applyType(name: String, arguments: Vector[CoreAst.Term], env: Env): Value = {
    val span = Span(0, 0)
    TypeChecker
      .checkTerm(
        CoreAst.Term.App(CoreAst.Term.GlobalRef(name, span), arguments, Vector.empty, span),
        env
      )
      .value
  }

  private def constructor(value: Value, expectedName: String, reject: String => Nothing): ConstructorHead =
    value match {
      case head: ConstructorHead if head.name == expectedName && head.noConfusion => head
      case _ => reject(s"`$expectedName` is not the expected constructor")
    }

  private def requireConstructorShape(
      head: ConstructorHead,
      familyArgs: Vector[Value],
      expectedFields: Vector[Value],
      expectedResult: Value,
      reject: String => Nothing
  ): Unit = {
    if (head.numErasedFamilyArgs != familyArgs.length || head.fieldBinders.length != expectedFields.length)
      reject(s"`${head.name}` has an unexpected arity")
    head.pi match {
      case Some(pi) =>
        var current = BinderOps.instantiateFull(head.paramBinders, pi.env, familyArgs)
        head.fieldBinders.zip(expectedFields).foreach { case (binder, expected) =>
          if (binder.mode != BinderMode.Explicit) reject(s"`${head.name}` has a non-explicit field")
          val actual = Interpreter.evalTerm(binder.ty, current)
          if (!ValueEquivalence.defEq(actual, expected)) reject(s"`${head.name}` has an unexpected field type")
          current = current.putLocal(binder.localRef, BinderOps.freshBinderValue(binder.name, actual))
        }
        if (!ValueEquivalence.defEq(pi.codomain(current), expectedResult))
          reject(s"`${head.name}` has an unexpected result type")
      case None if expectedFields.isEmpty && familyArgs.isEmpty =>
        if (!ValueEquivalence.defEq(head.tpe, expectedResult)) reject(s"`${head.name}` has an unexpected result type")
      case None => reject(s"`${head.name}` has no expected telescope")
    }
  }

  private def run(self: VLam, args: Vector[Value], layout: Layout): Value = {
    val resultType = layout.result
    val malformed = resultValue(layout, NativeBufferProgram.MalformedProgram.code, Vector.empty)
    if (args.length != 2) return malformed
    val blockedOn = dependencies(args)
    if (blockedOn.nonEmpty) return Value.canonicalizeProof(VBlockedApp(self, args, resultType, blockedOn))

    readList[BigInt](args(0), layout.listNat, layout, NativeBufferProgram.MaxProgramWords) { value =>
      natValue(value, layout)
    } match {
      case NonCanonical     => neutral(self, args, resultType)
      case InvalidInput     => resultValue(layout, NativeBufferProgram.InvalidArgument.code, Vector.empty)
      case ResourceExceeded => resultValue(layout, NativeBufferProgram.ResourceLimit.code, Vector.empty)
      case Ready(programWords) =>
        NativeBufferProgram.prepare(programWords) match {
          case Left(error) => resultValue(layout, error.code, Vector.empty)
          case Right(prepared) =>
            if (prepared.outputByteCount > NativeBufferProgram.MaxSourceOutputBytes)
              return resultValue(layout, NativeBufferProgram.ResourceLimit.code, Vector.empty)
            var inputIndex = 0
            val expectedInputExtents = prepared.inputExtents
            val decodedInputs: Decoded[Vector[Vector[Byte]]] = readList[Vector[Byte]](
              args(1),
              layout.listListNat,
              layout,
              expectedInputExtents.length,
              overLimit = InvalidInput
            ) { value =>
              val extent = expectedInputExtents(inputIndex)
              inputIndex += 1
              readList[Byte](value, layout.listNat, layout, extent, overLimit = InvalidInput) { cell =>
                natValue(cell, layout) match {
                  case Ready(n) if n <= 255 => Ready(n.toByte)
                  case Ready(_)             => InvalidInput
                  case NonCanonical         => NonCanonical
                  case InvalidInput         => InvalidInput
                  case ResourceExceeded     => ResourceExceeded
                }
              } match {
                case Ready(bytes) if bytes.length == extent => Ready(bytes)
                case Ready(_)                               => InvalidInput
                case other                                  => other
              }
            }
            decodedInputs match {
              case Ready(inputBuffers) =>
                val result = prepared.run(inputBuffers)
                result.error match {
                  case Some(error) => resultValue(layout, error.code, Vector.empty)
                  case None        => resultValue(layout, 0, result.outputs)
                }
              case NonCanonical     => neutral(self, args, resultType)
              case InvalidInput     => resultValue(layout, NativeBufferProgram.InvalidArgument.code, Vector.empty)
              case ResourceExceeded => resultValue(layout, NativeBufferProgram.ResourceLimit.code, Vector.empty)
            }
        }
    }
  }

  private def dependencies(values: Vector[Value]): DepSet = {
    val pending = mutable.ArrayDeque.from(values)
    val seen = new java.util.IdentityHashMap[Value, java.lang.Boolean]()
    var result = DepSet.empty
    while (pending.nonEmpty) {
      val value = pending.removeHead()
      if (!seen.containsKey(value)) {
        seen.put(value, java.lang.Boolean.TRUE)
        result = result ++ value.synDeps
        Blocker.unapply(value).foreach(deps => result = result ++ deps)
        value match {
          case app: VApp =>
            pending.append(app.head)
            pending.appendAll(app.determiningArgs)
          case _ =>
        }
      }
    }
    result
  }

  private def neutral(self: VLam, args: Vector[Value], resultType: Value): Value =
    Value.canonicalizeProof(VApp(VConst(Name, Symbol, self.tpe), args, resultType))

  private def readList[A](
      value: Value,
      expectedType: Value,
      layout: Layout,
      maximum: Int,
      overLimit: Decoded[Nothing] = ResourceExceeded
  )(read: Value => Decoded[A]): Decoded[Vector[A]] = {
    val result = Vector.newBuilder[A]
    var rest = value
    var length = 0
    while (length <= maximum) {
      rest match {
        case VCtor(head, Vector(), tpe) if (head eq layout.listNil) && ValueEquivalence.defEq(tpe, expectedType) =>
          return Ready(result.result())
        case VCtor(head, Vector(element, tail), tpe) if head eq layout.listCons =>
          if (!ValueEquivalence.defEq(tpe, expectedType)) return NonCanonical
          if (length == maximum) return overLimit
          read(element) match {
            case Ready(item)      => result += item
            case NonCanonical     => return NonCanonical
            case InvalidInput     => return InvalidInput
            case ResourceExceeded => return ResourceExceeded
          }
          rest = tail
          length += 1
        case _ => return NonCanonical
      }
    }
    InvalidInput
  }

  private def natValue(value: Value, layout: Layout): Decoded[BigInt] = {
    var rest = value
    var unary = BigInt(0)
    while (true) {
      rest match {
        case packed: VPacked if (packed.codec eq NatCodec) && ValueEquivalence.defEq(packed.tpe, layout.nat) =>
          val n = packed.natValue.get
          val total = unary + n
          return if (total.bitLength > 64) InvalidInput else Ready(total)
        case VCtor(head, Vector(), tpe) if (head eq layout.natZero) && ValueEquivalence.defEq(tpe, layout.nat) =>
          return Ready(unary)
        case VCtor(head, Vector(previous), tpe)
            if (head eq layout.natSucc) && ValueEquivalence.defEq(tpe, layout.nat) =>
          unary += 1
          if (unary.bitLength > 64) return InvalidInput
          rest = previous
        case _ => return NonCanonical
      }
    }
    NonCanonical
  }

  private def resultValue(layout: Layout, status: Int, outputs: Vector[Vector[Byte]]): Value = {
    def list(values: Vector[Value], resultType: Value): Value = {
      var tail: Value = VCtor(layout.listNil, Vector.empty, resultType)
      var index = values.length - 1
      while (index >= 0) {
        tail = VCtor(layout.listCons, Vector(values(index), tail), resultType)
        index -= 1
      }
      tail
    }
    val outputRows = outputs.map { output =>
      val bytes = output.map(byte => VPacked.nat(BigInt(byte & 0xff), layout.nat): Value)
      list(bytes, layout.listNat)
    }
    val outputValue = list(outputRows, layout.listListNat)
    VCtor(
      layout.pairMk,
      Vector(VPacked.nat(BigInt(status), layout.nat), outputValue),
      layout.result
    )
  }
}
