package v1.seq.sieve.empirical

import stainless.annotation.extern

@extern
object SegmentedSieve {

  def survivorsInRange(lo: BigInt, hi: BigInt, primes: Array[BigInt]): List[BigInt] = {
    val size = (hi - lo + 1).toInt
    if (size <= 0) return Nil

    val isCandidate = Array.fill(size)(true)

    for (p <- primes if p * p <= hi) {
      if (p > 0) {
        val firstMultiple = {
          val rem = lo % p
          if (rem == 0) lo else lo + (p - rem)
        }
        var m = firstMultiple
        while (m <= hi) {
          isCandidate((m - lo).toInt) = false
          m += p
        }
      }
    }

    val builder = List.newBuilder[BigInt]
    for (i <- 0 until size) {
      if (isCandidate(i)) {
        builder += lo + i
      }
    }
    builder.result()
  }
}
