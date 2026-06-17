package v1.seq.sieve

import org.scalatest.flatspec.*
import org.scalatest.matchers.should.*
import stainless.collection.List
import v1.prime.{AllPrimesSoFarList, Prime, SortedPrimeList}

class SieveSequenceV0Test extends FlatSpec with Matchers  {

  private def allPrimesSoFar(values: List[Prime]): AllPrimesSoFarList =
    AllPrimesSoFarList(SortedPrimeList(values))

  private def shouldAccept(sequence: SieveSequenceV0, values: Seq[BigInt]) = {
    values.foreach(value => sequence.accepts(value) should be(true))
    succeed
  }

  private def shouldReject(sequence: SieveSequenceV0, values: Seq[BigInt]) = {
    values.foreach(value => sequence.accepts(value) should be(false))
    succeed
  }

  "SieveSequenceV0" should "use the first prime as the generator head" in {
    val s1 = SieveSequenceV0(allPrimesSoFar(List(Prime(3), Prime(2))))
    val s2 = SieveSequenceV0(allPrimesSoFar(List(Prime(5), Prime(3), Prime(2))))
    val s3 = SieveSequenceV0(allPrimesSoFar(List(Prime(7), Prime(5), Prime(3), Prime(2))))

    s1.head.value should be(BigInt(3))
    s2.head.value should be(BigInt(5))
    s3.head.value should be(BigInt(7))
  }

  it should "filter only by the tail primes" in {
    val s1 = SieveSequenceV0(allPrimesSoFar(List(Prime(3), Prime(2))))
    val s2 = SieveSequenceV0(allPrimesSoFar(List(Prime(5), Prime(3), Prime(2))))
    val s3 = SieveSequenceV0(allPrimesSoFar(List(Prime(7), Prime(5), Prime(3), Prime(2))))

    s1.filterPrimes.map(_.value) should be(List(BigInt(2)))
    s2.filterPrimes.map(_.value) should be(List(BigInt(3), BigInt(2)))
    s3.filterPrimes.map(_.value) should be(List(BigInt(5), BigInt(3), BigInt(2)))
  }

  it should "accept concrete values that are not multiples of the tail primes" in {
    val s1 = SieveSequenceV0(allPrimesSoFar(List(Prime(3), Prime(2))))
    val s2 = SieveSequenceV0(allPrimesSoFar(List(Prime(5), Prime(3), Prime(2))))
    val s3 = SieveSequenceV0(allPrimesSoFar(List(Prime(7), Prime(5), Prime(3), Prime(2))))

    shouldAccept(s1, Seq(BigInt(3), BigInt(5), BigInt(7), BigInt(9), BigInt(11), BigInt(13), BigInt(15)))
    shouldAccept(s2, Seq(BigInt(5), BigInt(7), BigInt(11), BigInt(13), BigInt(17), BigInt(19), BigInt(23), BigInt(25), BigInt(29), BigInt(31)))
    shouldAccept(s3, Seq(BigInt(7), BigInt(11), BigInt(13), BigInt(17), BigInt(19), BigInt(23), BigInt(29), BigInt(31), BigInt(37), BigInt(41)))
  }

  it should "reject concrete values that are multiples of at least one tail prime" in {
    val s1 = SieveSequenceV0(allPrimesSoFar(List(Prime(3), Prime(2))))
    val s2 = SieveSequenceV0(allPrimesSoFar(List(Prime(5), Prime(3), Prime(2))))
    val s3 = SieveSequenceV0(allPrimesSoFar(List(Prime(7), Prime(5), Prime(3), Prime(2))))

    shouldReject(s1, Seq(BigInt(4), BigInt(6), BigInt(8), BigInt(10), BigInt(12)))
    shouldReject(s2, Seq(BigInt(6), BigInt(8), BigInt(9), BigInt(10), BigInt(12), BigInt(14), BigInt(15), BigInt(16), BigInt(18)))
    shouldReject(s3, Seq(BigInt(10), BigInt(12), BigInt(14), BigInt(15), BigInt(18), BigInt(20), BigInt(21), BigInt(22), BigInt(24), BigInt(25)))
  }

  it should "accept head plus any checked multiple of the tail product" in {
    val s = SieveSequenceV0(allPrimesSoFar(List(Prime(5), Prime(3), Prime(2))))

    shouldAccept(
      s,
      Seq(
        s.head.value,
        s.head.value + s.filterModulus,
        s.head.value + BigInt(2) * s.filterModulus,
        s.head.value + BigInt(3) * s.filterModulus
      )
    )
  }

  it should "generate the expected tail-filtered prefixes with apply" in {
    val s1 = SieveSequenceV0(allPrimesSoFar(List(Prime(3), Prime(2))))
    val s2 = SieveSequenceV0(allPrimesSoFar(List(Prime(5), Prime(3), Prime(2))))
    val s3 = SieveSequenceV0(allPrimesSoFar(List(Prime(7), Prime(5), Prime(3), Prime(2))))

    (0 to 6).map(i => s1(BigInt(i))) should be(
      Seq(BigInt(3), BigInt(5), BigInt(7), BigInt(9), BigInt(11), BigInt(13), BigInt(15))
    )
    (0 to 9).map(i => s2(BigInt(i))) should be(
      Seq(BigInt(5), BigInt(7), BigInt(11), BigInt(13), BigInt(17), BigInt(19), BigInt(23), BigInt(25), BigInt(29), BigInt(31))
    )
    (0 to 9).map(i => s3(BigInt(i))) should be(
      Seq(BigInt(7), BigInt(11), BigInt(13), BigInt(17), BigInt(19), BigInt(23), BigInt(29), BigInt(31), BigInt(37), BigInt(41))
    )
  }

  it should "find an apply index for accepted values" in {
    val s1 = SieveSequenceV0(allPrimesSoFar(List(Prime(3), Prime(2))))
    val s2 = SieveSequenceV0(allPrimesSoFar(List(Prime(5), Prime(3), Prime(2))))

    Seq(BigInt(3), BigInt(5), BigInt(7), BigInt(9), BigInt(11), BigInt(15)).foreach { value =>
      s1(s1.indexOfAccepted(value)) should be(value)
    }

    Seq(BigInt(5), BigInt(7), BigInt(11), BigInt(13), BigInt(17), BigInt(19), BigInt(25), BigInt(31)).foreach { value =>
      s2(s2.indexOfAccepted(value)) should be(value)
    }

    succeed
  }

}
