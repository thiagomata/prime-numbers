package v1.chapter6.seq.sieve.empirical

import stainless.annotation.extern

@extern
object EmpiricalRunner {

  private val outputPath = "data/empirical/results.csv"

  def main(args: Array[String]): Unit = {
    val maxPrime = if (args.length >= 1) args(0).toInt else 1000
    println(s"Max prime: $maxPrime")

    val primes = primesUpTo(maxPrime)
    println(s"Generated ${primes.length} primes up to $maxPrime")

    CsvWriter.init(outputPath)

    for (i <- 0 until primes.length - 1) {
      val p = primes(i)
      if (p >= BigInt(3)) {
        val hi = p * p
        val lo = p

        val sievePrimes = primes.take(i) // all primes less than p
        val survivors = SegmentedSieve.survivorsInRange(lo, hi, sievePrimes)
        val gLocal = GapAnalyzer.countTwoGaps(survivors)
        val delta = gLocal - p
        val extinction = delta <= 0

        val row = OutputRow(
          k = i + 1,
          p = p,
          pNext = primes(i + 1),
          gLocal = gLocal,
          delta = delta,
          extinction = extinction
        )
        CsvWriter.append(outputPath, row)

        if (i % 50 == 0 || p <= 30) {
          println(f"p=$p%4s  G_local=$gLocal%4s  delta=$delta%4s  extinct=$extinction")
        }
      }
    }

    println(s"\nDone. Results written to $outputPath")
  }

  private def primesUpTo(limit: Int): Array[BigInt] = {
    if (limit < 2) return Array.empty
    val isPrime = Array.fill(limit + 1)(true)
    isPrime(0) = false
    isPrime(1) = false
    var i = 2
    while (i * i <= limit) {
      if (isPrime(i)) {
        var j = i * i
        while (j <= limit) {
          isPrime(j) = false
          j += i
        }
      }
      i += 1
    }
    (2 to limit).filter(isPrime).map(BigInt(_)).toArray
  }
}
