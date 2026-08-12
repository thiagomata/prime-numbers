package v1.seq.sieve

import org.scalatest.flatspec.*
import org.scalatest.matchers.should.*
import stainless.collection.List
import v1.chapter5.prime.{AllPrimesSoFarList, Prime, SortedPrimeList}
import v1.chapter6.sieve.seq.spec.SpecSieveSequence
import v1.chapter6.sieve.seq.spec.properties.{SpecSieveSeqNextStageProperties, SpecSieveSeqPeriodProperties, SpecSieveSeqSurvivorCountProperties}
import v1.tags.SlowLemmaTest

class SpecSieveSequenceTest extends FlatSpec with Matchers  {

  private def allPrimesSoFar(values: List[Prime]): AllPrimesSoFarList =
    AllPrimesSoFarList(SortedPrimeList(values))

  private def shouldAccept(sequence: SpecSieveSequence, values: Seq[BigInt]) = {
    values.foreach(value => sequence.accepts(value) should be(true))
    succeed
  }

  private def shouldReject(sequence: SpecSieveSequence, values: Seq[BigInt]) = {
    values.foreach(value => sequence.accepts(value) should be(false))
    succeed
  }

  "SpecSieveSequence" should "use the first prime as the generator head" in {
    val s1 = SpecSieveSequence(allPrimesSoFar(List(Prime(3), Prime(2))))
    val s2 = SpecSieveSequence(allPrimesSoFar(List(Prime(5), Prime(3), Prime(2))))
    val s3 = SpecSieveSequence(allPrimesSoFar(List(Prime(7), Prime(5), Prime(3), Prime(2))))

    s1.head.value should be(BigInt(3))
    s2.head.value should be(BigInt(5))
    s3.head.value should be(BigInt(7))
  }

  it should "filter only by the tail primes" in {
    val s1 = SpecSieveSequence(allPrimesSoFar(List(Prime(3), Prime(2))))
    val s2 = SpecSieveSequence(allPrimesSoFar(List(Prime(5), Prime(3), Prime(2))))
    val s3 = SpecSieveSequence(allPrimesSoFar(List(Prime(7), Prime(5), Prime(3), Prime(2))))

    s1.filterPrimes.map(_.value) should be(List(BigInt(2)))
    s2.filterPrimes.map(_.value) should be(List(BigInt(3), BigInt(2)))
    s3.filterPrimes.map(_.value) should be(List(BigInt(5), BigInt(3), BigInt(2)))
  }

  it should "accept concrete values that are not multiples of the tail primes" in {
    val s1 = SpecSieveSequence(allPrimesSoFar(List(Prime(3), Prime(2))))
    val s2 = SpecSieveSequence(allPrimesSoFar(List(Prime(5), Prime(3), Prime(2))))
    val s3 = SpecSieveSequence(allPrimesSoFar(List(Prime(7), Prime(5), Prime(3), Prime(2))))

    shouldAccept(s1, Seq(BigInt(3), BigInt(5), BigInt(7), BigInt(9), BigInt(11), BigInt(13), BigInt(15)))
    shouldAccept(s2, Seq(BigInt(5), BigInt(7), BigInt(11), BigInt(13), BigInt(17), BigInt(19), BigInt(23), BigInt(25), BigInt(29), BigInt(31)))
    shouldAccept(s3, Seq(BigInt(7), BigInt(11), BigInt(13), BigInt(17), BigInt(19), BigInt(23), BigInt(29), BigInt(31), BigInt(37), BigInt(41)))
  }

  it should "reject concrete values that are multiples of at least one tail prime" in {
    val s1 = SpecSieveSequence(allPrimesSoFar(List(Prime(3), Prime(2))))
    val s2 = SpecSieveSequence(allPrimesSoFar(List(Prime(5), Prime(3), Prime(2))))
    val s3 = SpecSieveSequence(allPrimesSoFar(List(Prime(7), Prime(5), Prime(3), Prime(2))))

    shouldReject(s1, Seq(BigInt(4), BigInt(6), BigInt(8), BigInt(10), BigInt(12)))
    shouldReject(s2, Seq(BigInt(6), BigInt(8), BigInt(9), BigInt(10), BigInt(12), BigInt(14), BigInt(15), BigInt(16), BigInt(18)))
    shouldReject(s3, Seq(BigInt(10), BigInt(12), BigInt(14), BigInt(15), BigInt(18), BigInt(20), BigInt(21), BigInt(22), BigInt(24), BigInt(25)))
  }

  it should "accept head plus any checked multiple of the tail product" taggedAs(SlowLemmaTest) in {
    val s = SpecSieveSequence(allPrimesSoFar(List(Prime(5), Prime(3), Prime(2))))

    shouldAccept(
      s,
      Seq(
        s.head.value,
        s.head.value + s.tailPrimorial,
        s.head.value + BigInt(2) * s.tailPrimorial,
        s.head.value + BigInt(3) * s.tailPrimorial
      )
    )
  }

  it should "generate the expected tail-filtered prefixes with apply" taggedAs(SlowLemmaTest) in {
    val s1 = SpecSieveSequence(allPrimesSoFar(List(Prime(3), Prime(2))))
    val s2 = SpecSieveSequence(allPrimesSoFar(List(Prime(5), Prime(3), Prime(2))))
    val s3 = SpecSieveSequence(allPrimesSoFar(List(Prime(7), Prime(5), Prime(3), Prime(2))))

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

  it should "find an apply index for accepted values" taggedAs(SlowLemmaTest) in {
    val s1 = SpecSieveSequence(allPrimesSoFar(List(Prime(3), Prime(2))))
    val s2 = SpecSieveSequence(allPrimesSoFar(List(Prime(5), Prime(3), Prime(2))))

    Seq(BigInt(3), BigInt(5), BigInt(7), BigInt(9), BigInt(11), BigInt(15)).foreach { value =>
      s1(s1.indexOfAccepted(value)) should be(value)
    }

    Seq(BigInt(5), BigInt(7), BigInt(11), BigInt(13), BigInt(17), BigInt(19), BigInt(25), BigInt(31)).foreach { value =>
      s2(s2.indexOfAccepted(value)) should be(value)
    }

    succeed
  }

  // === Bridge-critical lemma tests for V0-V2 equivalence ===

  it should "extract correct gapList for S_1" taggedAs(SlowLemmaTest) in {
    val s1 = SpecSieveSequence(allPrimesSoFar(List(Prime(3), Prime(2))))
    // apply: 3, 5, 7, 9, 11, 13, 15, ... → gaps: 2 repeated
    SpecSieveSeqPeriodProperties.gapList(s1, BigInt(0), BigInt(4)) should be(
      stainless.collection.List(BigInt(2), BigInt(2), BigInt(2), BigInt(2))
    )
  }

  it should "extract correct gapList for S_2" taggedAs(SlowLemmaTest) in {
    val s2 = SpecSieveSequence(allPrimesSoFar(List(Prime(5), Prime(3), Prime(2))))
    // apply: 5, 7, 11, 13, 17, 19, 23, 25, ... → gaps: 2, 4, 2, 4, ...
    SpecSieveSeqPeriodProperties.gapList(s2, BigInt(0), BigInt(4)) should be(
      stainless.collection.List(BigInt(2), BigInt(4), BigInt(2), BigInt(4))
    )
  }

  it should "prove assertGapListPositive for S_1" taggedAs(SlowLemmaTest) in {
    val s1 = SpecSieveSequence(allPrimesSoFar(List(Prime(3), Prime(2))))
    SpecSieveSeqPeriodProperties.assertGapListPositive(s1, BigInt(0), BigInt(4)) should be(true)
  }

  it should "prove assertGapListSize matches count" taggedAs(SlowLemmaTest) in {
    val s1 = SpecSieveSequence(allPrimesSoFar(List(Prime(3), Prime(2))))
    SpecSieveSeqPeriodProperties.assertGapListSize(s1, BigInt(0), BigInt(4)) should be(true)
  }

  it should "prove apply(k) equals head plus the telescoped gap sum for S_1" taggedAs(SlowLemmaTest) in {
    val s1 = SpecSieveSequence(allPrimesSoFar(List(Prime(3), Prime(2))))
    Seq(BigInt(0), BigInt(1), BigInt(5)).foreach { k =>
      SpecSieveSeqPeriodProperties.assertSumGapTelescopes(s1, BigInt(0), k) should be(true)
      SpecSieveSeqPeriodProperties.sumGap(s1, BigInt(0), k) should be(s1(k) - s1.head.value)
    }
    succeed
  }

  it should "prove each gap is positive via assertGapPositive" taggedAs(SlowLemmaTest) in {
    val s1 = SpecSieveSequence(allPrimesSoFar(List(Prime(3), Prime(2))))
    s1.assertGapPositive(BigInt(0)) should be(true)
    s1.assertGapPositive(BigInt(1)) should be(true)
    s1.assertGapPositive(BigInt(5)) should be(true)
  }

  it should "prove gap periodicity for S_1" taggedAs(SlowLemmaTest) in {
    val s1 = SpecSieveSequence(allPrimesSoFar(List(Prime(3), Prime(2))))
    // For S_1: head=3, tailPrimorial=2 → head+M=5, indexOfAccepted(5)=1
    val p = BigInt(1)
    SpecSieveSeqPeriodProperties.assertGapPeriodic(s1, BigInt(0), p) should be(true)
    SpecSieveSeqPeriodProperties.assertGapPeriodic(s1, BigInt(1), p) should be(true)
    SpecSieveSeqPeriodProperties.assertGapPeriodic(s1, BigInt(5), p) should be(true)
  }

  it should "prove gap periodicity for S_2" taggedAs(SlowLemmaTest) in {
    val s2 = SpecSieveSequence(allPrimesSoFar(List(Prime(5), Prime(3), Prime(2))))
    // For S_2: head=5, tailPrimorial=6 → head+M=11, indexOfAccepted(11)=2
    val p = BigInt(2)
    SpecSieveSeqPeriodProperties.assertGapPeriodic(s2, BigInt(0), p) should be(true)
    SpecSieveSeqPeriodProperties.assertGapPeriodic(s2, BigInt(1), p) should be(true)
    SpecSieveSeqPeriodProperties.assertGapPeriodic(s2, BigInt(5), p) should be(true)
  }

  it should "prove sum of one period equals tailPrimorial" taggedAs(SlowLemmaTest) in {
    val s1 = SpecSieveSequence(allPrimesSoFar(List(Prime(3), Prime(2))))
    // For S_1: head=3, tailPrimorial=2, p=1, sumGap(0,p)=2 which equals tailPrimorial
    val p = BigInt(1)
    SpecSieveSeqPeriodProperties.assertSumGapTelescopes(s1, BigInt(0), p) should be(true)
    SpecSieveSeqPeriodProperties.sumGap(s1, BigInt(0), p) should be(s1.tailPrimorial)
  }

  // === Same-head extended filter size theorem tests ===

  it should "prove same-head filter size for S_1 [3,2]" taggedAs(SlowLemmaTest) in {
    val s1 = SpecSieveSequence(allPrimesSoFar(List(Prime(3), Prime(2))))
    // head=3, tailPrimorial=2, M=2, period=1
    // mod(M, head) = mod(2,3) = 2 != 0 ✓
    // ─── The theorem ───
    // countAcceptedHeadNonMultiplesBetween(3, 9) == 1 * (3-1) == 2
    SpecSieveSeqSurvivorCountProperties.assertSameHeadExtendedFilterCount(s1, BigInt(1)) should be(true)
  }

  it should "prove same-head filter size for S_2 [5,3,2]" taggedAs(SlowLemmaTest) in {
    val s2 = SpecSieveSequence(allPrimesSoFar(List(Prime(5), Prime(3), Prime(2))))
    // head=5, tailPrimorial=6, M=6, period=2
    // mod(M, head) = mod(6,5) = 1 != 0 ✓
    // ─── The theorem ───
    // countAcceptedHeadNonMultiplesBetween(5, 35) == 2 * (5-1) == 8
    SpecSieveSeqSurvivorCountProperties.assertSameHeadExtendedFilterCount(s2, BigInt(2)) should be(true)
  }

  // === Same-head survivor count (body computes actual count) ===

  it should "compute same-head survivor count for S_1 [3,2]" taggedAs(SlowLemmaTest) in {
    val s1 = SpecSieveSequence(allPrimesSoFar(List(Prime(3), Prime(2))))
    // head=3, M=2, period=1 → survivors in [3,9): 5,7 → count=2
    SpecSieveSeqSurvivorCountProperties.sameHeadSurvivorCount(s1, BigInt(1)) should be(BigInt(2))
  }

  it should "compute same-head survivor count for S_2 [5,3,2]" taggedAs(SlowLemmaTest) in {
    val s2 = SpecSieveSequence(allPrimesSoFar(List(Prime(5), Prime(3), Prime(2))))
    // head=5, M=6, period=2 → survivors in [5,35): 7,11,13,17,19,23,29,31 → count=8
    SpecSieveSeqSurvivorCountProperties.sameHeadSurvivorCount(s2, BigInt(2)) should be(BigInt(8))
  }

  // === Next period via SpecSieveSeqNextStageProperties ===

  it should "compute nextPeriod for S_1 [3,2]" taggedAs(SlowLemmaTest) in {
    val s1 = SpecSieveSequence(allPrimesSoFar(List(Prime(3), Prime(2))))
    // period=1, head=3 → nextPeriod == 1 * (3-1) == 2
    SpecSieveSeqNextStageProperties.verifiedNextPeriod(s1, BigInt(1)) should be(BigInt(2))
  }

  it should "compute nextPeriod for S_2 [5,3,2]" taggedAs(SlowLemmaTest) in {
    val s2 = SpecSieveSequence(allPrimesSoFar(List(Prime(5), Prime(3), Prime(2))))
    // period=2, head=5 → nextPeriod == 2 * (5-1) == 8
    SpecSieveSeqNextStageProperties.verifiedNextPeriod(s2, BigInt(2)) should be(BigInt(8))
  }

}
