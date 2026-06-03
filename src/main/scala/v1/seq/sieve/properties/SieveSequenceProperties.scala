package v1.seq.sieve.properties

import stainless.lang.*
import v1.Calc
import v1.div.properties.ConsecutiveIntegers
import v1.seq.sieve.SieveSequence
import verification.Helper.{assert}

object SieveSequenceProperties {

  /**
   * Lemma: For S_0 where apply(i) = i + 2,
   * among p consecutive values starting at position start,
   * at least one is divisible by p.
   */
  def atLeastOneMultiplePerBlock(start: BigInt, p: BigInt): Boolean = {
    require(p > 1)
    require(start >= 0)
    ConsecutiveIntegers.existsZero(start + 2, p)
  }.holds
}
