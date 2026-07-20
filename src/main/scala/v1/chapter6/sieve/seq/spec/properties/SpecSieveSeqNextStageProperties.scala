package v1.chapter6.sieve.seq.spec.properties

import stainless.collection.List
import stainless.lang.*
import v1.chapter2.div.Calc
import v1.chapter2.div.properties.AdditionAndMultiplication
import v1.chapter6.sieve.seq.spec.SpecSieveSequence

/**
 * Assembly lemmas that wire the individual step proofs into
 * Goal 3: the next stage's integral cycle reconstructs the next spec.
 *
 * The leaf proofs live in:
 * - NextProperties: filter bridge, gap merge, skip characterization
 * - SurvivorCountProperties: T' = T*(h-1)
 * - PeriodProperties: assertSpecGapCycleIntegralMatchesApply (cycle = spec)
 *
 * This object adds the assembly that connects them.
 */
object SpecSieveSeqNextStageProperties {

  // ── Headline theorems ─────────────────────────────────────────────────

  /**
   * Goal 3 headline: the next stage's integral cycle reconstructs the next spec.
   *
   * Given that:
   * (1) the current stage has period `period`,
   * (2) nextPeriod is the verified survivor count T*(h-1),
   * (3) the next stage's period boundary holds,
   *
   * then for every k > 0:
   *   spec.next.specGapCycle(nextPeriod).integral(k - 1) == spec.next(k)
   *
   * The proof delegates to assertSpecGapCycleIntegralMatchesApply on spec.next,
   * which is a generic lemma valid for any SpecSieveSequence with a valid period.
   */
  def assertNextCycleReconstructsNextSpec(
    seq: SpecSieveSequence,
    period: BigInt,
    nextPeriod: BigInt,
    k: BigInt
  ): Boolean = {
    require(period > BigInt(0))
    require(nextPeriod > BigInt(0))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)
    require(seq.primes.nextPrime.value < seq.head.value * seq.head.value)
    require(seq.next.apply(nextPeriod) == seq.next.head.value + seq.next.tailPrimorial)
    require(k > BigInt(0))

    val nextSeq = seq.next
    SpecSieveSeqPeriodProperties.assertSpecGapCycleIntegralMatchesApply(nextSeq, nextPeriod, k)
  }.holds

  /**
   * The next stage's gap list has exactly `nextPeriod` gaps.
   */
  def assertNextGapListHasCorrectSize(
    seq: SpecSieveSequence,
    period: BigInt,
    nextPeriod: BigInt
  ): Boolean = {
    require(period > BigInt(0))
    require(nextPeriod > BigInt(0))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)
    require(seq.primes.nextPrime.value < seq.head.value * seq.head.value)
    require(seq.next.apply(nextPeriod) == seq.next.head.value + seq.next.tailPrimorial)

    val nextSeq = seq.next
    SpecSieveSeqPeriodProperties.assertGapListSize(nextSeq, BigInt(0), nextPeriod)
  }.holds

  /**
   * The next stage's gap cycle integral base case: integral(0) == nextSeq(1).
   */
  def assertNextCycleIntegralBase(
    seq: SpecSieveSequence,
    period: BigInt,
    nextPeriod: BigInt
  ): Boolean = {
    require(period > BigInt(0))
    require(nextPeriod > BigInt(0))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)
    require(seq.primes.nextPrime.value < seq.head.value * seq.head.value)
    require(seq.next.apply(nextPeriod) == seq.next.head.value + seq.next.tailPrimorial)

    val nextSeq = seq.next
    SpecSieveSeqPeriodProperties.assertSpecGapCycleIntegralBase(nextSeq, nextPeriod)
  }.holds

  // ── Supporting assembly ───────────────────────────────────────────────

  /**
   * The verified next-period count is T*(h-1).
   */
  def verifiedNextPeriod(
    seq: SpecSieveSequence,
    period: BigInt
  ): BigInt = {
    require(period > BigInt(0))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)
    require(Calc.mod(seq.tailPrimorial, seq.head.value) != BigInt(0))

    SpecSieveSeqSurvivorCountProperties.sameHeadSurvivorCount(seq, period)
  }.ensuring(nextPeriod =>
    nextPeriod == period * (seq.head.value - BigInt(1))
  )

  /**
   * The pipeline-constructed merged gap prefix matches the next spec's gap list.
   *
   * Takes nextSeq explicitly to avoid Stainless unfolding seq.next through
   * many layers. The caller must ensure nextSeq == seq.next and the
   * structural invariants (filterValues.head == seq.head.value, etc.).
   */
  def assertPipelineOutputMatchesNextGapList(
    seq: SpecSieveSequence,
    nextSeq: SpecSieveSequence,
    period: BigInt,
    nextPeriod: BigInt
  ): Boolean = {
    require(period > BigInt(0))
    require(nextPeriod > BigInt(0))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)
    require(nextPeriod == period * (seq.head.value - BigInt(1)))
    require(Calc.mod(seq.tailPrimorial, seq.head.value) != BigInt(0))
    require(seq.primes.nextPrime.value < seq.head.value * seq.head.value)
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.head == seq.head.value)
    require(nextSeq.filterValues.tail == seq.filterValues)
    require(nextSeq.head.value == seq.apply(BigInt(1)))
    require(seq.head.value < nextSeq.head.value)
    require(nextSeq.accepts(seq.apply(BigInt(1))))
    require(nextSeq(BigInt(0)) == seq.apply(BigInt(1)))
    require(Calc.mod(seq.head.value + seq.tailPrimorial, seq.head.value) != BigInt(0))

    SpecSieveSeqNextProperties.assertMergedGapPrefixMatchesNext(
      seq, nextSeq, BigInt(1), BigInt(0), nextPeriod, period
    )
  }.holds

  /**
   * The pipeline-constructed next stage has the correct head.
   */
  def assertNextHeadIsCorrect(
    seq: SpecSieveSequence,
    period: BigInt
  ): Boolean = {
    require(period > BigInt(0))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)
    require(seq.primes.nextPrime.value < seq.head.value * seq.head.value)

    val nextSeq = seq.next
    assert(SpecSieveSeqHeadIsPrime.assertApplyOneEqualsNextPrime(seq))
    assert(nextSeq.head.value == seq.apply(BigInt(1)))

    nextSeq.head.value == seq.apply(BigInt(1))
  }.holds
}
