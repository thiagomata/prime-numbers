package v1.seq.sieve.properties

import stainless.lang.*
import v1.seq.sieve.SieveSequence

object SieveSequenceProperties {

  def assertS1HeadIsThree(): Boolean = {
    val s1 = SieveSequence.S_1()
    s1.head == BigInt(3)
  }.holds

  def assertS1PrimesLength(): Boolean = {
    val s1 = SieveSequence.S_1()
    s1.primes.size == BigInt(2)
  }.holds

}
