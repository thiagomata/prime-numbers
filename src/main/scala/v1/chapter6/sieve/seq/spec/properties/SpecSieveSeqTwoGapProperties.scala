package v1.chapter6.sieve.seq.spec.properties

import stainless.lang.*
import v1.chapter2.div.Calc
import v1.chapter2.div.properties.{ModOperations, ModSmallDividend}
import v1.chapter5.prime.BezoutUtils
import v1.chapter6.sieve.seq.spec.{SieveUtils, SpecSieveSequence}

object SpecSieveSeqTwoGapProperties {

  /**
   * The two endpoints of a real sieve-sequence 2-gap have different forbidden
   * lift offsets under the incoming odd head.
   *
   * For step M = seq.tailPrimorial and p = seq.head.value, each endpoint has a
   * unique offset in [0,p) whose lifted value is divisible by p. If those
   * offsets were equal, p would divide two values differing by 2. Since p > 2,
   * mod(2,p) == 2, which is impossible.
   */
  def assertForbiddenLiftOffsetsDistinct(
    seq: SpecSieveSequence,
    k: BigInt
  ): Boolean = {
    require(k >= BigInt(0))
    require(seq.head.value > BigInt(2))
    require(Calc.mod(seq.tailPrimorial, seq.head.value) != BigInt(0))
    require(seq.apply(k + BigInt(1)) - seq.apply(k) == BigInt(2))

    val p = seq.head.value
    val step = seq.tailPrimorial
    val left = seq.apply(k)
    val right = seq.apply(k + BigInt(1))
    val leftOffset = BezoutUtils.coprimeStepZeroOffset(left, step, p)
    val rightOffset = BezoutUtils.coprimeStepZeroOffset(right, step, p)

    assert(right == left + BigInt(2))
    assert(Calc.mod(left + leftOffset * step, p) == BigInt(0))
    assert(Calc.mod(right + rightOffset * step, p) == BigInt(0))

    if (leftOffset == rightOffset) {
      val leftCopy = left + leftOffset * step
      val rightCopy = right + rightOffset * step
      assert(rightCopy == leftCopy + BigInt(2))
      assert(Calc.mod(leftCopy, p) == BigInt(0))
      assert(Calc.mod(rightCopy, p) == BigInt(0))
      assert(ModOperations.modZeroPlusC(leftCopy, p, BigInt(2)))
      assert(Calc.mod(rightCopy, p) == Calc.mod(BigInt(2), p))
      assert(ModSmallDividend.modSmallDividend(BigInt(2), p))
      assert(Calc.mod(BigInt(2), p) == BigInt(2))
      assert(Calc.mod(rightCopy, p) != BigInt(0))
      leftOffset != rightOffset
    } else {
      leftOffset != rightOffset
    }
  }.holds

  /** Exactly two copies of a real 2-gap are destroyed in one full lift block. */
  def assertExactlyTwoDestroyedCopies(
    seq: SpecSieveSequence,
    k: BigInt
  ): Boolean = {
    require(k >= BigInt(0))
    require(seq.head.value > BigInt(2))
    require(Calc.mod(seq.tailPrimorial, seq.head.value) != BigInt(0))
    require(seq.apply(k + BigInt(1)) - seq.apply(k) == BigInt(2))

    val p = seq.head.value
    val step = seq.tailPrimorial
    val left = seq.apply(k)
    val right = seq.apply(k + BigInt(1))
    val leftWitness = BezoutUtils.coprimeStepZeroOffset(left, step, p)
    val rightWitness = BezoutUtils.coprimeStepZeroOffset(right, step, p)

    assert(right == left + BigInt(2))
    assert(assertForbiddenLiftOffsetsDistinct(seq, k))
    assert(leftWitness != rightWitness)
    assert(assertDestroyedCountEqualsEndpointCounts(
      left,
      step,
      p,
      BigInt(0),
      leftWitness,
      rightWitness
    ))
    assert(SieveUtils.assertCountZeroOffsetsOne(left, step, p))
    assert(SieveUtils.countZeroOffsets(left, step, p, BigInt(0)) == BigInt(1))
    assert(SieveUtils.assertCountZeroOffsetsOne(right, step, p))
    assert(SieveUtils.countZeroOffsets(right, step, p, BigInt(0)) == BigInt(1))

    countDestroyedTwoGapCopies(left, step, p, BigInt(0)) == BigInt(2)
  }.holds

  /** Exactly p - 2 copies survive after the incoming head p is installed. */
  def assertExactlyHeadMinusTwoCopiesSurvive(
    seq: SpecSieveSequence,
    k: BigInt
  ): Boolean = {
    require(k >= BigInt(0))
    require(seq.head.value > BigInt(2))
    require(Calc.mod(seq.tailPrimorial, seq.head.value) != BigInt(0))
    require(seq.apply(k + BigInt(1)) - seq.apply(k) == BigInt(2))

    val p = seq.head.value
    val step = seq.tailPrimorial
    val left = seq.apply(k)

    assert(assertExactlyTwoDestroyedCopies(seq, k))
    p - countDestroyedTwoGapCopies(left, step, p, BigInt(0)) == p - BigInt(2)
  }.holds

  /** Counts lift indices whose copied 2-gap loses at least one endpoint. */
  def countDestroyedTwoGapCopies(
    left: BigInt,
    step: BigInt,
    p: BigInt,
    i: BigInt
  ): BigInt = {
    require(left >= BigInt(0))
    require(step >= BigInt(0))
    require(p > BigInt(2))
    require(i >= BigInt(0))
    require(i <= p)
    decreases(p - i)

    if (i == p) {
      BigInt(0)
    } else {
      val rest = countDestroyedTwoGapCopies(left, step, p, i + BigInt(1))
      assert(rest >= BigInt(0))
      assert(rest <= p - (i + BigInt(1)))

      if (
        Calc.mod(left + i * step, p) == BigInt(0) ||
        Calc.mod(left + BigInt(2) + i * step, p) == BigInt(0)
      ) {
        assert(rest + BigInt(1) <= p - i)
        rest + BigInt(1)
      } else {
        assert(rest <= p - i)
        rest
      }
    }
  }.ensuring(result => result >= BigInt(0) && result <= p - i)

  /** The two endpoint hit sets are disjoint, so their counts add. */
  def assertDestroyedCountEqualsEndpointCounts(
    left: BigInt,
    step: BigInt,
    p: BigInt,
    i: BigInt,
    leftWitness: BigInt,
    rightWitness: BigInt
  ): Boolean = {
    require(left >= BigInt(0))
    require(step >= BigInt(0))
    require(p >= BigInt(2))
    require(v1.chapter5.prime.Prime.isPrime(p))
    require(Calc.mod(step, p) != BigInt(0))
    require(i >= BigInt(0))
    require(i <= p)
    require(leftWitness >= BigInt(0) && leftWitness < p)
    require(rightWitness >= BigInt(0) && rightWitness < p)
    require(leftWitness != rightWitness)
    require(Calc.mod(left + leftWitness * step, p) == BigInt(0))
    require(Calc.mod(left + BigInt(2) + rightWitness * step, p) == BigInt(0))
    decreases(p - i)

    if (i == p) {
      countDestroyedTwoGapCopies(left, step, p, i) ==
        SieveUtils.countZeroOffsets(left, step, p, i) +
          SieveUtils.countZeroOffsets(left + BigInt(2), step, p, i)
    } else {
      assert(assertDestroyedCountEqualsEndpointCounts(
        left,
        step,
        p,
        i + BigInt(1),
        leftWitness,
        rightWitness
      ))

      val leftHit = Calc.mod(left + i * step, p) == BigInt(0)
      val rightHit = Calc.mod(left + BigInt(2) + i * step, p) == BigInt(0)

      if (leftHit && rightHit) {
        BezoutUtils.assertCoprimeStepAtMostOneZero(left, step, p, i, leftWitness)
        BezoutUtils.assertCoprimeStepAtMostOneZero(
          left + BigInt(2), step, p, i, rightWitness
        )
        assert(i == leftWitness)
        assert(i == rightWitness)
        assert(leftWitness == rightWitness)
      }

      countDestroyedTwoGapCopies(left, step, p, i) ==
        SieveUtils.countZeroOffsets(left, step, p, i) +
          SieveUtils.countZeroOffsets(left + BigInt(2), step, p, i)
    }
  }.holds
}
