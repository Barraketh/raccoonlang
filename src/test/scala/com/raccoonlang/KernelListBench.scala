package com.raccoonlang

import com.raccoonlang.Value._
import com.raccoonlang.packed.Storage

/**
 * CPU time of kernel list operations across sizes, to show their growth: left and right accumulation by the native
 * append, the prelude's `List.reverse`, and `length` of a closed list. Run with `Test/runMain`.
 */
object KernelListBench {
  @volatile private var sink: AnyRef = _

  private val threads = java.lang.management.ManagementFactory.getThreadMXBean

  private lazy val env: Env = {
    val src = "def rev (xs: List(Nat)): List(Nat) := List.reverse(xs)\n"
    val parsed = LanguageParser.parseProgram(src) match {
      case Success(program, _, _) => program
      case failure: Failure       => throw new IllegalStateException(failure.toString)
    }
    Elaborator.elab(parsed, Prelude.default).decls.foldLeft(Interpreter.initialEnv(Prelude.default)) {
      case (env, decl) => Interpreter.evalDecl(decl, env)
    }
  }
  private lazy val cons: ConstructorHead = env("List.cons").asInstanceOf[ConstructorHead]
  private lazy val listNat: Value = Interpreter.evalApply(env("List"), Vector(Kernel.natType))
  private lazy val nilNat: Value = Interpreter.evalApply(env("List.nil"), Vector(Kernel.natType))

  private def nat(n: Int): Value = NatNormalForm.literal(BigInt(n))

  private def build(elements: Seq[Value]): Value =
    elements.foldRight(nilNat)((element, tail) => ConstructorValue(cons, Vector(element, tail), listNat))

  private def append(l: Value, r: Value): Value = Interpreter.evalApply(env("List.append"), Vector(l, r))

  private def accumulateLeft(n: Int): Value = {
    val piece = build(Vector(nat(1), nat(2), nat(3)))
    var acc = nilNat
    (0 until n).foreach(_ => acc = append(acc, piece))
    acc
  }

  private def accumulateRight(n: Int): Value = {
    var acc = nilNat
    (0 until n).foreach(_ => acc = append(build(Vector(nat(1), nat(2), nat(3))), acc))
    acc
  }

  /** Best of five CPU times after warming at the size, in milliseconds. */
  private def measure(label: String, sizes: Vector[Int])(prepare: Int => () => AnyRef): Unit = {
    val results = sizes.map { n =>
      val run = prepare(n)
      (0 until 3).foreach(_ => sink = run())
      val best = (0 until 5).map { _ =>
        val started = threads.getCurrentThreadCpuTime
        sink = run()
        threads.getCurrentThreadCpuTime - started
      }.min
      n -> best / 1e6
    }
    val base = results.head
    val line = results.map { case (n, ms) => f"n=$n%-8d $ms%9.3f ms (x${ms / base._2}%.2f)" }.mkString("  ")
    println(f"$label%-22s $line")
  }

  def main(args: Array[String]): Unit = {
    val worker = new Thread(null, () => run(), "bench", 1L << 30)
    worker.start()
    worker.join()
  }

  private def run(): Unit = {
    val sizes = Vector(10000, 20000, 40000, 80000, 160000)
    measure("left accumulation", sizes)(n => () => accumulateLeft(n))
    measure("right accumulation", sizes)(n => () => accumulateRight(n))
    val rev = env("rev")
    measure("prelude reverse", Vector(5000, 10000, 20000, 40000, 80000)) { n =>
      val list = build((0 until n).map(i => nat(i % 7)))
      () => Interpreter.evalApply(rev, Vector(list))
    }
    measure("length (closed)", Vector(1000, 10000, 100000, 1000000)) { n =>
      val list = build((0 until n).map(i => nat(i % 7)))
      () => Interpreter.evalApply(env("List.length"), Vector(list))
    }
    val left = accumulateLeft(100000)
    val right = accumulateRight(100000)
    println(
      s"segments after 100000 steps: left=${Storage.segments(left).length} right=${Storage.segments(right).length}"
    )
  }
}
