package v1.chapter6.seq.sieve.empirical

import stainless.annotation.extern

@extern
object GapAnalyzer {

  def countTwoGaps(survivors: List[BigInt]): BigInt = {
    if (survivors.length < 2) return BigInt(0)

    var count = BigInt(0)
    var i = 0
    while (i < survivors.length - 1) {
      if (survivors(i + 1) - survivors(i) == BigInt(2)) {
        count += BigInt(1)
      }
      i += 1
    }
    count
  }
}
