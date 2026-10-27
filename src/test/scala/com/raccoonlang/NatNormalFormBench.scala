package com.raccoonlang

import com.raccoonlang.NatFixtures._
import com.raccoonlang.Value._

/** Warmed operation timings and thread allocation counts; run on a JVM with allocation tracking. */
object NatNormalFormBench {
  @volatile private var sink: AnyRef = _

  private val allocations = java.lang.management.ManagementFactory.getThreadMXBean
    .asInstanceOf[com.sun.management.ThreadMXBean]

  /** Warm for at least `warmup` iterations and 200 ms, so fast workloads reach compiled code before measurement. */
  private def benchmark(label: String, warmup: Int, iterations: Int)(body: => AnyRef): Unit = {
    var iteration = 0
    val warmupStarted = System.nanoTime()
    while (iteration < warmup || System.nanoTime() - warmupStarted < 200000000L) {
      sink = body
      iteration += 1
    }
    val threadId = Thread.currentThread().threadId()
    val samples = Vector.fill(5) {
      val beforeBytes = allocations.getThreadAllocatedBytes(threadId)
      val started = System.nanoTime()
      iteration = 0
      while (iteration < iterations) {
        sink = body
        iteration += 1
      }
      val micros = (System.nanoTime() - started).toDouble / iterations / 1000.0
      val bytes = (allocations.getThreadAllocatedBytes(threadId) - beforeBytes).toDouble / iterations
      (micros, bytes)
    }
    val micros = samples.map(_._1).sorted
    val kibibytes = samples.map(_._2 / 1024).sorted
    println(
      f"$label%-36s median=${micros(2)}%10.3f us range=${micros.head}%.3f..${micros.last}%.3f alloc=${kibibytes(2)}%.3f KiB/op"
    )
  }

  def main(args: Array[String]): Unit = {
    require(allocations.isThreadAllocatedMemorySupported, "This benchmark requires thread allocation tracking")
    allocations.setThreadAllocatedMemoryEnabled(true)

    val n = fresh("n")
    val m = fresh("m")
    val zero = constant(0)
    val one = constant(1)
    benchmark("add zero to atom", warmup = 200000, iterations = 10000) { add(n, zero) }
    benchmark("successor of atom", warmup = 200000, iterations = 10000) {
      ConstructorValue(Kernel.succ, Vector(n), Kernel.natType)
    }
    benchmark("isZero of atom", warmup = 200000, iterations = 10000) { NatNormalForm.isZero(n) }
    benchmark("multiply atoms", warmup = 200000, iterations = 10000) { mul(n, m) }
    val nPlusOne = add(n, one)
    val mPlusTwo = add(m, constant(2))
    benchmark("(n+1)*(m+2)", warmup = 200000, iterations = 10000) { mul(nPlusOne, mPlusTwo) }

    Vector(512, 2048).foreach { count =>
      val variables = Vector.tabulate(count)(index => fresh(s"v$index"))
      // The one superlinear pattern: each addition merges into an ever-longer term sequence.
      benchmark(s"$count terms: sum one term at a time", warmup = 5, iterations = 5) {
        variables.foldLeft(zero)((total, variable) => add(total, variable))
      }
      benchmark(s"$count terms: balanced sum", warmup = 20, iterations = 20) { sum(variables) }
      benchmark(s"$count factors: product one factor at a time", warmup = 5, iterations = 5) {
        variables.foldLeft(one)((total, variable) => mul(total, variable))
      }
      benchmark(s"$count factors: balanced product", warmup = 20, iterations = 20) { product(variables) }

      val poly = sum(variables).asInstanceOf[VNatPoly]
      benchmark(s"$count terms: fresh successor deps and key", warmup = 20, iterations = 100) {
        val successor = NatNormalForm.successor(poly)
        successor.synDeps
        successor.key
      }
      benchmark(s"$count terms: multiply two", warmup = 20, iterations = 100) { mul(poly, constant(2)) }
      benchmark(s"$count terms: native sub and ble", warmup = 20, iterations = 100) {
        NatNormalForm.ble(NatNormalForm.sub(add(poly, constant(5)), poly), constant(5))
      }
      benchmark(s"$count terms: peel 64 successors", warmup = 20, iterations = 20) {
        var current: Value = add(poly, constant(64))
        var steps = 0
        while (steps < 64) {
          val ConstructorValue(_, fields) = current
          current = fields.head
          current.key
          steps += 1
        }
        current
      }
      val replaced = variables.take(2).map(_.key).toSet
      val replacement = add(n, m)
      benchmark(s"$count terms: substitute two atoms by a sum", warmup = 10, iterations = 20) {
        NatNormalForm.substituteAtoms(poly, atom => if (replaced(atom.key)) replacement else atom)
      }
      val wideProduct = product(variables).asInstanceOf[VNatPoly]
      benchmark(s"$count factors: substitute one atom by a sum", warmup = 10, iterations = 20) {
        NatNormalForm.substituteAtoms(wideProduct, atom => if (atom.key == variables.head.key) replacement else atom)
      }
    }

    Vector(64, 256).foreach { count =>
      val sums = Vector.tabulate(count)(index => add(fresh(s"x$index"), fresh(s"y$index")))
      benchmark(s"$count sums: balanced product", warmup = 20, iterations = 20) { product(sums) }
      val sumProduct = product(sums)
      benchmark(s"$count sums: product squared", warmup = 20, iterations = 20) { mul(sumProduct, sumProduct) }
      val bases = form(sumProduct).operands.map(base => form(base).operands.head.key).toSet
      benchmark(s"$count sums: substitute one atom per sum by one", warmup = 10, iterations = 20) {
        NatNormalForm.substituteAtoms(sumProduct.asInstanceOf[VNatPoly], atom => if (bases(atom.key)) one else atom)
      }
    }

    // Observations of lambdas from different programs are convertible atoms with different keys, so conversion aligns
    // them before comparing.
    def observer(parameter: String): Value =
      LanguageParser.parseProgram(
        s"""
           |axiom observe (f: Nat -> Nat)(k: Nat): Nat
           |{ fun (k: Nat): Nat => observe(fun ($parameter: Nat): Nat => $parameter, k) }
           |""".stripMargin
      ) match {
        case Success(parsed, _, _) =>
          Interpreter.run(Elaborator.elab(parsed, Prelude.default), Prelude.default).get
        case failure: Failure => throw new IllegalStateException(s"Failed to parse: $failure")
      }
    val first = observer("p")
    val second = observer("q")
    val observedAtoms = Vector.tabulate(64)(index => fresh(s"observed$index"))
    def observed(observe: Value): Vector[Value] =
      observedAtoms.map(atom => Interpreter.evalApply(observe, Vector(atom)))
    val firstSum = sum(observed(first))
    val secondSum = sum(observed(second))
    require(firstSum.key != secondSum.key && ValueEquivalence.defEq(firstSum, secondSum))
    benchmark("64 terms: structural atom conversion", warmup = 20, iterations = 20) {
      java.lang.Boolean.valueOf(ValueEquivalence.defEq(firstSum, secondSum))
    }
    val shared = fresh("shared")
    val firstSums = product(observed(first).map(add(_, shared)))
    val secondSums = product(observed(second).map(add(_, shared)))
    require(firstSums.key != secondSums.key && ValueEquivalence.defEq(firstSums, secondSums))
    benchmark("64 sums: structural atom conversion", warmup = 20, iterations = 20) {
      java.lang.Boolean.valueOf(ValueEquivalence.defEq(firstSums, secondSums))
    }

    val huge = (BigInt(1) << 65535) + 123
    benchmark("64K-bit constant: fresh value key", warmup = 10, iterations = 100) { constant(huge).key }
  }
}
