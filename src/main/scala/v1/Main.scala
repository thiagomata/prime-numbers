package v1

import stainless.annotation.extern
import v1.chapter2.div.DivMod

object Main {

  @extern
  def println(message: String): Unit = {
    scala.Predef.println(message)
  }

  @extern
  def main(args: Array[String]): Unit = {
    val argLenght = args.length

    try {
      if (argLenght == 1 && args(0) == "help") {
        println("Usage:")
        println("  just run <a> <b>           — compute div/mod of a and b")
        println("  just check <a> <b> <d> <m> — verify div/mod with explicit values")
        println("  just show <steps> <count>  — show Spec = Canonical = Cycle apply values")
        return
      }
      if (argLenght == 1 && args(0) == "show") {
        println("Usage: just show <steps> <count>")
        return
      }
      if (argLenght == 3 && args(0) == "show") {
        showEquivalence(args(1).toInt, args(2).toInt)
        return
      }
      if (argLenght == 2) {
        with2Args(args)
        return
      }
      if (argLenght == 4) {
        with4Args(args)
        return
      }
      println("Usage: sbt 'runMain v1.DivMain <a> <b> [<div> <mod>]'")
      println("       just show <steps> <count>")
    } catch {
      case e: NumberFormatException => {
        println("Invalid integer numbers " + args.toList.mkString(", "))
      }
      case e: IllegalArgumentException => {
        println("Invalid div mod numbers " + args.toList.mkString(", "))
      }
    }
  }

  @extern
  private def with2Args(args: Array[String]): Unit = {
    val a = BigInt(args(0))
    val b = BigInt(args(1))
    val divMod = DivMod(a, b, 0, a)
    val result = divMod.solve
    println(s"div: ${result.div.toString()}, mod: ${result.mod.toString()}")
  }

  @extern
  private def with4Args(args: Array[String]): Unit = {
    val a = BigInt(args(0))
    val b = BigInt(args(1))
    val div = BigInt(args(2))
    val mod = BigInt(args(3))
    val divMod = DivMod(a, b, div, mod)
    val result = divMod.solve
    println(s"div: ${result.div.toString()}, mod: ${result.mod.toString()}")
  }

  @extern
  private def computePeriod(spec: v1.chapter6.seq.sieve.SpecSieveSequence): BigInt = {
    val target = spec.head.value + spec.tailPrimorial
    var k = BigInt(1)
    while (spec(k) != target) {
      k += 1
    }
    k
  }

  @extern
  private def showEquivalence(steps: Int, count: Int): Unit = {
    import stainless.collection.List
    import v1.chapter5.prime.{AllPrimesSoFarList, Prime, SortedPrimeList}
    import v1.chapter6.seq.sieve.{CycleSieveSequence, SpecDerivedSieveSequence, SpecSieveSequence}

    val spec0 = SpecSieveSequence(
      AllPrimesSoFarList(SortedPrimeList(List(Prime(BigInt(3)), Prime(BigInt(2))))))

    var spec = spec0
    var derived = SpecDerivedSieveSequence(spec, computePeriod(spec))
    var cycle = CycleSieveSequence.S_1()

    for (stage <- 0 to steps) {
      println(s"\n=== Stage $stage (head = ${spec.head.value}) ===")
      val sVals = (0 until count).map(k => spec(k).toString).mkString(", ")
      val cVals = (0 until count).map(k => derived.cycle(k).toString).mkString(", ")
      val cyVals = (0 until count).map(k => cycle(k).toString).mkString(", ")
      println(s"  Spec      [$sVals]")
      println(s"  Canonical [$cVals]")
      println(s"  Cycle     [$cyVals]")
      val ok = (0 until count).forall(k =>
        spec(k) == derived.cycle(k) && derived.cycle(k) == cycle(k))
      println(if (ok) "  \u2713 all match" else "  \u2717 MISMATCH")

      if (stage < steps) {
        val np = computePeriod(spec.next)
        val nextCanonical = SpecDerivedSieveSequence(spec.next, np)
        spec = spec.next
        cycle = nextCanonical.cycle
        derived = nextCanonical
      }
    }
  }
}
