package v1.chapter60.sieve.seq.spec.properties

import stainless.collection.List
import stainless.lang.*
import v1.chapter2.div.Calc
import v1.chapter2.div.properties.AdditionAndMultiplication
import v1.chapter3.list.{ListBoundUtils, ListUtils}
import v1.chapter5.prime.*
import v1.chapter6.seq.sieve.SieveUtils
import v1.chapter60.sieve.seq.spec.SpecSieveSequence

object SpecSieveSeqNextProperties {

  def assertNextValueAcceptedByThis(seq: SpecSieveSequence, k: BigInt): Boolean = {
    require(k >= BigInt(0))
    require(seq.primes.nextPrime.value < seq.head.value * seq.head.value)

    val nextSeq = seq.next
    val value = nextSeq(k)

    assert(value >= nextSeq.head.value)
    assert(nextSeq.head.value > seq.head.value)
    assert(value >= seq.head.value)
    assert(nextSeq.filterPrimes == seq.primes.list.list)
    assert(nextSeq.filterValues == PrimeUtils.primeValues(seq.primes.list.list))
    assert(nextSeq.filterValues.tail == PrimeUtils.primeValues(seq.primes.list.tail.list))
    assert(seq.filterValues == PrimeUtils.primeValues(seq.primes.list.tail.list))
    assert(nextSeq.filterValues.tail == seq.filterValues)
    assert(nextSeq.accepts(value))
    assert(CoprimeUtils.isCoprime(value, nextSeq.filterValues))
    assert(SieveUtils.assertIsCoprimeSound(value, nextSeq.filterValues))
    assert(CoprimeUtils.isCoprime(value, nextSeq.filterValues.tail))
    assert(CoprimeUtils.isCoprime(value, seq.filterValues))
    seq.accepts(value)
  }.holds

  /**
   * Reverse direction: a value accepted by the current filters and not
   * divisible by the head is accepted by the next stage.
   *
   * The next stage's filter is `head :: filterValues`. Since
   * `isCoprime(v, p :: rest) = mod(v, p) != 0 && isCoprime(v, rest)`,
   * this follows directly from the definition.
   */
  def assertSurvivorAcceptedByNext(seq: SpecSieveSequence,v: BigInt): Boolean = {
    require(v >= seq.head.value)
    require(seq.accepts(v))
    require(Calc.mod(v, seq.head.value) != BigInt(0))
    require(seq.primes.nextPrime.value < seq.head.value * seq.head.value)

    val nextSeq = seq.next
    assert(nextSeq.filterValues.head == seq.head.value)
    assert(nextSeq.filterValues.tail == seq.filterValues)
    nextSeq.passesFilter(v)
  }.holds

  def assertOldAcceptedHeadNonMultipleAcceptedByNext(seq: SpecSieveSequence, v: BigInt): Boolean = {
    require(seq.primes.nextPrime.value < seq.head.value * seq.head.value)
    require(v >= seq.next.head.value)
    require(seq.accepts(v))
    require(Calc.mod(v, seq.head.value) != BigInt(0))

    val nextSeq = seq.next

    assert(v >= seq.head.value)
    assert(assertSurvivorAcceptedByNext(seq,v))
    assert(nextSeq.passesFilter(v))

    nextSeq.accepts(v)
  }.holds

  def assertOldAcceptedRejectedByNextIsHeadMultiple(seq: SpecSieveSequence, v: BigInt): Boolean = {
    require(seq.primes.nextPrime.value < seq.head.value * seq.head.value)
    require(v >= seq.next.head.value)
    require(seq.accepts(v))
    require(!seq.next.accepts(v))

    val nextSeq = seq.next

    assert(assertNextAcceptsMatchesHeadFilterForAcceptedValue(seq,v))
    assert(nextSeq.accepts(v) == (Calc.mod(v, seq.head.value) != BigInt(0)))
    assert(Calc.mod(v, seq.head.value) == BigInt(0))

    Calc.mod(v, seq.head.value) == BigInt(0)
  }.holds

  def assertOldGeneratedValueBetweenNextValuesIsHeadMultiple(seq: SpecSieveSequence, k: BigInt, oldIndex: BigInt): Boolean = {
    require(k >= BigInt(0))
    require(oldIndex >= BigInt(0))
    require(seq.primes.nextPrime.value < seq.head.value * seq.head.value)
    require(seq.apply(oldIndex) > seq.next(k))
    require(seq.apply(oldIndex) < seq.next(k + BigInt(1)))

    val nextSeq = seq.next
    val value = seq.apply(oldIndex)

    assert(nextSeq.assertApplyMonotonic(BigInt(0), k))
    assert(nextSeq(BigInt(0)) == nextSeq.head.value)
    assert(nextSeq.head.value <= nextSeq(k))
    assert(value >= nextSeq.head.value)
    assert(seq.accepts(value))
    assert(nextSeq.assertNoAcceptedValueBetweenGeneratedValues(k, value))
    assert(!nextSeq.accepts(value))
    assert(assertOldAcceptedRejectedByNextIsHeadMultiple(seq, value))

    Calc.mod(value, seq.head.value) == BigInt(0)
  }.holds

  def assertNextAcceptsMatchesHeadFilterForAcceptedValue(seq: SpecSieveSequence, v: BigInt): Boolean = {
    require(seq.primes.nextPrime.value < seq.head.value * seq.head.value)
    require(v >= seq.next.head.value)
    require(seq.accepts(v))

    val nextSeq = seq.next
    assert(nextSeq.filterValues.head == seq.head.value)
    assert(nextSeq.filterValues.tail == seq.filterValues)

    if (Calc.mod(v, seq.head.value) == BigInt(0)) {
      assert(Calc.mod(v, nextSeq.filterValues.head) == BigInt(0))
      assert(!CoprimeUtils.isCoprime(v, nextSeq.filterValues))
      assert(!nextSeq.passesFilter(v))
      assert(!nextSeq.accepts(v))
    } else {
      assert(assertSurvivorAcceptedByNext(seq,v))
      assert(nextSeq.passesFilter(v))
      assert(nextSeq.accepts(v))
    }

    nextSeq.accepts(v) == (Calc.mod(v, seq.head.value) != BigInt(0))
  }.holds

  // APPROACH 2: prove via count of next-accepted values in [head, nextBoundary).
  //
  // The counting lemma proves `expected` survivors in [head, head+h*M).
  // The gap argument (block shift + no-accepted-between) proves 0 survivors
  // in [head+h*M, nextBoundary).
  // Total next-accepted values in [head, nextBoundary) = expected.
  // Since next.apply is 0-indexed and strictly increasing,
  // indexOfAccepted(nextBoundary) == expected.
  //
  // Key bridge: "no next-accepted values in [head+h*M, nextBoundary)"
  // follows from:
  //   seq.apply(h*period) == seq.head+h*M (block shift)
  //   seq.apply(h*period+1) == nextBoundary (block shift + seq.apply(1)==next.head)
  //   noAcceptedBetween(seq.apply(h*period)+1, seq.apply(h*period+1)) (by nextDoesNotPassAcceptedValue)
  //   head+h*M is head-multiple → not next-accepted
  //
  // STUCK: the minimality postcondition on indexOfAccepted (seq.apply(k) < value for k < result)
  // was added and verified. All 34 body assertions pass (block shift, gap, counting, coprimality).
  // But the postcondition `next.period() == expected` still times out because Stainless
  // cannot connect "count of survivors = expected" to "indexOfAccepted returns expected".
  // The minimality postcondition helps Stainless reason about indexOfAccepted but is not
  // sufficient to close the gap without the circular `next.apply(expected) == nextBoundary`.
  //
  // What was tried:
  //   1. Direct assertion of next.apply(expected) == nextBoundary → times out (SMT can't bridge this.apply to next.apply)
  //   2. Minimality postcondition on indexOfAccepted → verified but insufficient alone
  //   3. assertApplyInjective(period, expected) → circular (requires the very fact being proved)
  //   4. Coprimality + gap + block shift → all verified, but SMT can't compose them into the postcondition
  //
  // Remaining options:
  //   A. Add a quantified postcondition to indexOfAccepted (forall k < res, seq.apply(k) < value)
  //   B. Prove next.apply(expected) == nextBoundary via gap-preservation induction
  //   C. Add a dedicated count-index bridge lemma
  //
  // def assertNextPeriodEqualsExpected(): Boolean = {
  //   require(Calc.mod(seq.tailPrimorial, seq.head.value) != BigInt(0))
  //   require(primes.nextPrime.value < seq.head.value * seq.head.value)
  //   val p = period()
  //   val h = seq.head.value
  //   val expected = p * (h - BigInt(1))
  //   val M = seq.tailPrimorial
  //   val nextSeq = next
  //   val nextBoundary = nextSeq.head.value + nextSeq.tailPrimorial
  //   assert(nextSeq.tailPrimorial == h * M)
  //   assert(assertApplyOneEqualsNextPrime())
  //   assert(nextSeq.head.value == seq.apply(BigInt(1)))
  //   assert(sameHeadSurvivorCount(p) == expected)
  //   assert(assertBlockShiftMultiple(BigInt(0), h, p))
  //   assert(seq.apply(h * p) == seq.head.value + h * M)
  //   assert(assertBlockShiftMultiple(BigInt(1), h, p))
  //   assert(seq.apply(h * p + BigInt(1)) == nextBoundary)
  //   assert(nextDoesNotPassAcceptedValue(h * p, nextBoundary))
  //   assert(nextSeq.apply(nextSeq.period()) == nextBoundary)
  //   assert(nextSeq.passesFilter(nextBoundary))
  //   nextSeq.period() == expected
  // }.holds

  /**
   * The first value of this generator.
   *
   * `AllPrimesSoFarList` stores primes in descending order, so the list head is
   * the newest/largest prime in the current sieve stage. V0 starts enumerating
   * at this value. It does not use the previous V2 gap-cycle history to jump
   * around; it will eventually walk forward through ordinary consecutive
   * integers from here.
   */
  def assertSingletonFilterDecision(seq: SpecSieveSequence, value: BigInt, p: BigInt): Boolean = {
    require(p > BigInt(0))
    require(seq.filterValues == List(p))

    seq.passesFilter(value) == (Calc.mod(value, p) != BigInt(0))
  }.holds

  /**
   * Lifts acceptance from this sequence to a sequence with one extra front filter.
   *
   * `assertSkipUntilNonMultiple` needs to reason about a value found in the old
   * stream after skipping one or more values that are multiples of the newly
   * introduced filter. The old stream already proves that the value survives
   * `filterValues`. The extra assumption here proves the missing piece: the
   * same value is not a multiple of `nextSeq.filterValues.head`.
   *
   * When `nextSeq.filterValues.tail == seq.filterValues`, those two facts are
   * exactly the definition of `nextSeq.accepts(value)`. Naming the bridge keeps
   * the main gap-merge proof focused on index ordering instead of repeatedly
   * unfolding the list-shaped coprimality predicate.
   */
  private def assertAcceptedByNextWhenOldAcceptedAndNewHeadNonMultiple(
    seq: SpecSieveSequence,
    nextSeq: SpecSieveSequence,
    value: BigInt
  ): Boolean = {
    require(value >= seq.head.value)
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.tail == seq.filterValues)
    require(nextSeq.head.value == seq.head.value)
    require(seq.accepts(value))
    require(Calc.mod(value, nextSeq.filterValues.head) != BigInt(0))

    assert(value >= nextSeq.head.value)
    assert(SieveUtils.isCoprime(value, seq.filterValues))
    assert(SieveUtils.isCoprime(value, nextSeq.filterValues.tail))
    assert(SieveUtils.isCoprime(value, nextSeq.filterValues))
    nextSeq.accepts(value)
  }.holds

  /**
   * Projects acceptance by an extended next filter back to this sequence.
   *
   * The skip proof also needs the reverse direction for the candidate produced
   * by `nextSeq`: if the extended filter accepts `value`, then `value` must
   * survive both parts of that extended filter. The head of
   * `nextSeq.filterValues` gives the new non-multiple fact, and the tail is
   * exactly this sequence's `filterValues`, so the same value is accepted by
   * this sequence as well.
   *
   * This lemma is deliberately paired with
   * `assertAcceptedByNextWhenOldAcceptedAndNewHeadNonMultiple`. Together they
   * make the filter relationship explicit in both directions, leaving the main
   * gap-merge proof to focus on finding and ordering the first survivor.
   */
  private def assertNextAcceptedImpliesOldAcceptedAndNewHeadNonMultiple(
     seq: SpecSieveSequence,
     nextSeq: SpecSieveSequence,
     value: BigInt
   ): Boolean = {
    require(value >= nextSeq.head.value)
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.tail == seq.filterValues)
    require(nextSeq.head.value == seq.head.value)
    require(nextSeq.accepts(value))

    assert(value >= seq.head.value)
    assert(SieveUtils.isCoprime(value, nextSeq.filterValues))
    assert(SieveUtils.assertIsCoprimeSound(value, nextSeq.filterValues))
    assert(Calc.mod(value, nextSeq.filterValues.head) != BigInt(0))
    assert(SieveUtils.isCoprime(value, nextSeq.filterValues.tail))
    assert(SieveUtils.isCoprime(value, seq.filterValues))
    seq.accepts(value) && Calc.mod(value, nextSeq.filterValues.head) != BigInt(0)
  }.holds

  /**
   * Proves rejection by the extended next filter when the new front filter divides.
   *
   * This is the negative companion to the two acceptance bridge lemmas above.
   * During gap merging, the old stream may contain values that still satisfy this
   * sequence's tail filter, but are multiples of the newly inserted front filter
   * in `nextSeq`. Such values must not appear in `nextSeq`.
   *
   * The proof is intentionally direct. `nextSeq.accepts(value)` is just
   * `nextSeq.passesFilter(value)` once the value is above the shared head, and
   * `passesFilter` is `SieveUtils.isCoprime` over `nextSeq.filterValues`. If the
   * head of that filter list is `p` and `value` has zero remainder modulo `p`,
   * the first branch of `isCoprime` rejects the value immediately.
   */
  private def assertRejectedByNextWhenNewHeadMultiple(
                                                       seq: SpecSieveSequence,
                                                       nextSeq: SpecSieveSequence,
                                                       value: BigInt,
                                                       p: BigInt
                                                     ): Boolean = {
    require(value >= nextSeq.head.value)
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.head == p)
    require(Calc.mod(value, p) == BigInt(0))

    assert(Calc.mod(value, nextSeq.filterValues.head) == BigInt(0))
    assert(!SieveUtils.isCoprime(value, nextSeq.filterValues))
    assert(!nextSeq.passesFilter(value))
    !nextSeq.accepts(value)
  }.holds

  /**
   * Exposes the skipped-interval fact for a non-initial generated value.
   *
   * The postcondition of `searchNext` says the bounded linear scan returns the
   * first accepted candidate in its window. `apply(k)` uses that helper for
   * every `k > 0`, starting immediately after `apply(k - 1)`. This lemma names
   * that fact at the `apply` level: between the previous generated value and
   * the current generated value, there is no accepted value left behind.
   */
  private def assertFilterPreservesNextPosition(
                                                 seq: SpecSieveSequence,
                                                 nextSeq: SpecSieveSequence,
                                                 k: BigInt
                                               ): Boolean = {
    require(k >= BigInt(0))
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.tail == seq.filterValues)
    require(nextSeq.head.value == seq.head.value)
    require(nextSeq.accepts(seq.apply(k)))
    require(Calc.mod(seq.apply(k + BigInt(1)), nextSeq.filterValues.head) != BigInt(0))
    true
  }.ensuring(res => {
    val V = seq.apply(k)
    val W = seq.apply(k + BigInt(1))
    val vIdx = nextSeq.indexOfAccepted(V)

    assert(seq.accepts(W))
    assert(nextSeq.accepts(W))

    assert(seq.applySkipsNoAcceptedBetween(k + BigInt(1)))
    assert(seq.noAcceptedBetween(V + BigInt(1), W))

    assert(nextSeq.applyStrictlyIncreases(vIdx))
    assert(nextSeq(vIdx + BigInt(1)) > V)
    val z = nextSeq(vIdx + BigInt(1))
    assert(SieveUtils.isCoprime(z, seq.filterValues))
    assert(seq.accepts(z))
    assert(seq.nextDoesNotPassAcceptedValue(k, z))
    assert(W <= z)

    assert(nextSeq.accepts(W))
    assert(nextSeq.nextDoesNotPassAcceptedValue(vIdx, W))
    assert(z <= W)

    res && nextSeq(vIdx + BigInt(1)) == W
  })

  /**
   * Proves the copied-gap corollary for the immediate-survivor case.
   *
   * The old sequence filters by `filterValues`; `nextSeq` filters by one
   * additional front value followed by the same tail. If `apply(k)` is accepted
   * by `nextSeq`, it has an index there. If the old immediate successor
   * `apply(k + 1)` is also not a multiple of the new front filter, then
   * `nextSeq` must place that successor immediately after `apply(k)`.
   *
   * Therefore the gap is copied unchanged:
   *
   * nextSeq(vIdx + 1) - nextSeq(vIdx) == seq.apply(k + 1) - seq.apply(k)
   *
   * This is the local copy case used by gap-merge proofs. It deliberately
   * says nothing about the branch where `apply(k + 1)` is removed by the new
   * front filter; that branch is handled by merge/skip lemmas.
   */
  def assertFilterPreservesNextGap(
                                    seq: SpecSieveSequence,
                                    nextSeq: SpecSieveSequence,
                                    k: BigInt
                                  ): Boolean = {
    require(k >= BigInt(0))
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.tail == seq.filterValues)
    require(nextSeq.head.value == seq.head.value)
    require(nextSeq.accepts(seq.apply(k)))
    require(Calc.mod(seq.apply(k + BigInt(1)), nextSeq.filterValues.head) != BigInt(0))

    val v = seq.apply(k)
    val w = seq.apply(k + BigInt(1))
    val vIdx = nextSeq.indexOfAccepted(v)

    assert(nextSeq(vIdx) == v)
    assert(assertFilterPreservesNextPosition(seq, nextSeq, k))
    assert(nextSeq(vIdx + BigInt(1)) == w)

    nextSeq(vIdx + BigInt(1)) - nextSeq(vIdx) == w - v
  }.holds

  /**
   * Proves that accepting two consecutive old values copies their gap.
   *
   * Unlike `assertFilterPreservesNextGap`, this lemma does not require the two
   * sequences to have the same seq.head. That makes it applicable to the actual
   * `next` stage, whose head is strictly greater than the current seq.head.
   *
   * The next sequence must use this sequence's filters as its tail and must
   * accept both `apply(k)` and `apply(k + 1)`. The first value therefore has an
   * index in `nextSeq`. Its immediate next value cannot be below
   * `apply(k + 1)`, because every next-sequence value also passes the old tail
   * filters and the old sequence has no accepted value between consecutive
   * generated values. It cannot be above `apply(k + 1)` because that value is
   * itself accepted by `nextSeq`. The two bounds force equality, so the gap is
   * copied unchanged.
   */
  def assertConsecutiveAcceptedByNextPreservesGap(
     seq: SpecSieveSequence,
     nextSeq: SpecSieveSequence,
    k: BigInt
  ): Boolean = {
    require(k >= BigInt(0))
    require(nextSeq.filterValues.tail == seq.filterValues)
    require(nextSeq.head.value >= seq.head.value)
    require(seq.apply(k) >= nextSeq.head.value)
    require(seq.apply(k + BigInt(1)) >= nextSeq.head.value)
    require(nextSeq.accepts(seq.apply(k)))
    require(nextSeq.accepts(seq.apply(k + BigInt(1))))
    require(ListUtils.checkAllPositive(nextSeq.filterValues))

    val v = seq.apply(k)
    val w = seq.apply(k + BigInt(1))
    val vIdx = nextSeq.indexOfAccepted(v)

    assert(nextSeq(vIdx) == v)
    assert(nextSeq.applyStrictlyIncreases(vIdx))
    val z = nextSeq(vIdx + BigInt(1))
    assert(z > v)
    assert(z >= nextSeq.head.value)
    assert(z >= seq.head.value)
    assert(CoprimeUtils.isCoprime(z, nextSeq.filterValues))
    assert(CoprimeUtils.assertIsCoprimeForAll(z, nextSeq.filterValues))
    assert(CoprimeUtils.isCoprime(z, nextSeq.filterValues.tail))
    assert(CoprimeUtils.isCoprime(z, seq.filterValues))
    assert(seq.accepts(z))
    assert(seq.nextDoesNotPassAcceptedValue(k, z))
    assert(w <= z)

    assert(nextSeq.accepts(w))
    assert(nextSeq.nextDoesNotPassAcceptedValue(vIdx, w))
    assert(z <= w)
    assert(z == w)

    nextSeq(vIdx + BigInt(1)) - nextSeq(vIdx) == w - v
  }.holds

  /**
   * Finds the first old index > k whose value is not a multiple of p, within bound.
   * Returns `k+1` if `apply(k+1)` is not a multiple, otherwise recurses forward.
   * The postcondition guarantees the result is in `[k+1, bound]` and that its
   * value is not a multiple of p.
   */
  def findFirstNonMultipleAfter(
                                 seq: SpecSieveSequence,
                                 k: BigInt, p: BigInt,
                                 bound: BigInt): BigInt = {
    require(k >= BigInt(0))
    require(p > BigInt(0))
    require(bound > k)
    require(Calc.mod(seq.apply(bound), p) != BigInt(0))
    decreases(bound - k)
    if (Calc.mod(seq.apply(k + BigInt(1)), p) != BigInt(0)) k + BigInt(1)
    else {
      assert(bound > k + BigInt(1))
      findFirstNonMultipleAfter(seq, k + BigInt(1), p, bound)
    }
  }.ensuring(res => res >= k + BigInt(1) && res <= bound && Calc.mod(seq.apply(res), p) != BigInt(0))

  /**
   * Proves `apply(k + n * period) == seq.apply(k) + n * seq.tailPrimorial` for any n >= 0.
   * Induction on n: base `n=0` is trivial, step uses `assertBlockShift(k + (n-1)*period, period)`
   * to propagate the shift equality one period at a time.
   */
  private def assertFirstNonMultipleIsAtOrBefore(
                                                  seq: SpecSieveSequence,
                                                  k: BigInt,
                                                  zIdx: BigInt,
                                                  p: BigInt,
                                                  bound: BigInt
                                                ): Boolean = {
    require(k >= BigInt(0))
    require(zIdx > k)
    require(zIdx <= bound)
    require(p > BigInt(0))
    require(Calc.mod(seq.apply(zIdx), p) != BigInt(0))
    require(Calc.mod(seq.apply(bound), p) != BigInt(0))
    decreases(bound - k)
    val m = findFirstNonMultipleAfter(seq, k, p, bound)
    if (k + BigInt(1) == m) {
      m <= zIdx
    } else {
      assert(k + BigInt(1) < m)
      assert(Calc.mod(seq.apply(k + BigInt(1)), p) == BigInt(0))
      assert(zIdx > k + BigInt(1))
      assert(assertFirstNonMultipleIsAtOrBefore(seq, k + BigInt(1), zIdx, p, bound))
      m <= zIdx
    }
  }.holds

  /**
   * Proves the recursive skip invariant for the old stream.
   *
   * Let `m` be the first old-stream index after `k` whose value is not a
   * multiple of the new filter `p`. Every old-stream index strictly between
   * `k` and `m` must therefore be a multiple of `p`.
   *
   * This is the recursive gap-merging backbone: when the next sequence cannot
   * copy `apply(k + 1)`, it is not because the value disappeared mysteriously;
   * it is because the new filter consumes that old gap. Repeating this fact
   * index by index accounts for exactly the run of old gaps merged before the
   * first surviving value.
   */
  private def assertSkippedIndexBeforeFirstIsMultiple(
                                                       seq: SpecSieveSequence,
                                                       k: BigInt,
                                                       idx: BigInt,
                                                       p: BigInt,
                                                       bound: BigInt
                                                     ): Boolean = {
    require(k >= BigInt(0))
    require(p > BigInt(0))
    require(bound > k)
    require(Calc.mod(seq.apply(bound), p) != BigInt(0))
    require(idx > k)
    require(idx < findFirstNonMultipleAfter(seq, k, p, bound))
    decreases(idx - k)

    val m = findFirstNonMultipleAfter(seq, k, p, bound)
    assert(k + BigInt(1) <= idx)
    assert(k + BigInt(1) < m)

    if (Calc.mod(seq.apply(k + BigInt(1)), p) != BigInt(0)) {
      assert(m == k + BigInt(1))
      assert(false)
      Calc.mod(seq.apply(idx), p) == BigInt(0)
    } else if (idx == k + BigInt(1)) {
      Calc.mod(seq.apply(idx), p) == BigInt(0)
    } else {
      assert(idx > k + BigInt(1))
      assert(bound > k + BigInt(1))
      val nextM = findFirstNonMultipleAfter(seq, k + BigInt(1), p, bound)
      assert(m == nextM)
      assert(idx < nextM)
      assert(assertSkippedIndexBeforeFirstIsMultiple(seq, k + BigInt(1), idx, p, bound))
      Calc.mod(seq.apply(idx), p) == BigInt(0)
    }
  }.holds

  /**
   * Anchors the next-sequence index before the first old-stream survivor.
   *
   * The full gap-merge proof starts from an alignment point:
   * `nextSeq(vIdx) == seq.apply(k)`, where `vIdx` is the next-sequence index for
   * the old value `apply(k)`. The first old value that survives the new filter
   * is `apply(m)`, with `m = findFirstNonMultipleAfter(seq, k, p, bound)`.
   *
   * This lemma proves the ordering fact needed by
   * `nextSeq.nextDoesNotPassAcceptedValue`: the aligned next value is strictly
   * before the first old survivor. Keeping this fact separate avoids asking
   * Stainless to rediscover strict old-stream monotonicity inside the larger
   * filter/gap proof.
   */
  private def assertNextAnchorBeforeFirstSurvivor(
                                                   seq: SpecSieveSequence,
                                                   nextSeq: SpecSieveSequence,
                                                   k: BigInt,
                                                   p: BigInt,
                                                   bound: BigInt
                                                 ): Boolean = {
    require(k >= BigInt(0))
    require(p > BigInt(0))
    require(bound > k)
    require(Calc.mod(seq.apply(bound), p) != BigInt(0))
    require(nextSeq.head.value == seq.head.value)
    require(nextSeq.accepts(seq.apply(k)))

    val vIdx = nextSeq.indexOfAccepted(seq.apply(k))
    val m = findFirstNonMultipleAfter(seq, k, p, bound)

    assert(m >= k + BigInt(1))
    assert(m > k)
    assert(seq.applyIndexStrictlyPreservesValues(k, m))
    assert(seq.apply(k) < seq.apply(m))
    assert(nextSeq(vIdx) == seq.apply(k))
    nextSeq(vIdx) < seq.apply(m)
  }.holds

  /**
   * Connects the recursive old-stream skip invariant to next-sequence rejection.
   *
   * `assertSkippedIndexBeforeFirstIsMultiple` proves that every old index between
   * the aligned point `k` and the first old survivor `m` is a multiple of the new
   * filter `p`. This lemma translates that arithmetic fact into the sequence
   * language used by gap merging: those skipped old values are not accepted by
   * `nextSeq`, because `p` is the newly added front filter in `nextSeq`.
   *
   * Separating this bridge keeps the eventual `assertSkipUntilNonMultiple` proof
   * from needing to unfold both the recursive search and the next-sequence filter
   * definition in the same verification condition.
   */
  private def assertSkippedOldValueRejectedByNext(
                                                   seq: SpecSieveSequence,
                                                   nextSeq: SpecSieveSequence,
                                                   k: BigInt,
                                                   idx: BigInt,
                                                   p: BigInt,
                                                   bound: BigInt
                                                 ): Boolean = {
    require(k >= BigInt(0))
    require(p > BigInt(0))
    require(bound > k)
    require(Calc.mod(seq.apply(bound), p) != BigInt(0))
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.head == p)
    require(nextSeq.head.value == seq.head.value)
    require(idx > k)
    require(idx < findFirstNonMultipleAfter(seq, k, p, bound))

    assert(assertSkippedIndexBeforeFirstIsMultiple(seq, k, idx, p, bound))
    assert(Calc.mod(seq.apply(idx), p) == BigInt(0))
    assert(seq.apply(idx) >= seq.head.value)
    assert(seq.apply(idx) >= nextSeq.head.value)
    assert(assertRejectedByNextWhenNewHeadMultiple(seq, nextSeq, seq.apply(idx), p))
    !nextSeq.accepts(seq.apply(idx))
  }.holds

  /**
   * Proves the upper inequality for the skip-to-first-survivor equality.
   *
   * Let `m` be the first old-stream index after `k` whose value is not a
   * multiple of the new front filter `p`. This lemma proves that the next value
   * emitted by `nextSeq` after the aligned old value cannot pass `apply(m)`.
   *
   * The proof deliberately avoids the reverse-index/minimality argument. It only
   * packages the local completeness fact for `nextSeq`: once `apply(m)` is known
   * to be accepted by `nextSeq`, and the aligned next-sequence value is strictly
   * before `apply(m)`, `nextSeq.nextDoesNotPassAcceptedValue` gives
   * `nextSeq(vIdx + 1) <= seq.apply(m)`.
   */
  private def assertNextValueAtOrBeforeFirstSurvivor(
                                                      seq: SpecSieveSequence,
                                                      nextSeq: SpecSieveSequence,
                                                      k: BigInt,
                                                      p: BigInt,
                                                      bound: BigInt
                                                    ): Boolean = {
    require(k >= BigInt(0))
    require(p > BigInt(0))
    require(bound > k)
    require(Calc.mod(seq.apply(bound), p) != BigInt(0))
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.head == p)
    require(nextSeq.filterValues.tail == seq.filterValues)
    require(nextSeq.head.value == seq.head.value)
    require(nextSeq.accepts(seq.apply(k)))

    val vIdx = nextSeq.indexOfAccepted(seq.apply(k))
    val m = findFirstNonMultipleAfter(seq, k, p, bound)

    assert(m >= k + BigInt(1))
    assert(m >= BigInt(0))
    assert(Calc.mod(seq.apply(m), p) != BigInt(0))
    assert(Calc.mod(seq.apply(m), nextSeq.filterValues.head) != BigInt(0))
    assert(seq.accepts(seq.apply(m)))
    assert(assertAcceptedByNextWhenOldAcceptedAndNewHeadNonMultiple(seq, nextSeq, seq.apply(m)))
    assert(nextSeq.accepts(seq.apply(m)))
    assert(assertNextAnchorBeforeFirstSurvivor(seq, nextSeq, k, p, bound))
    assert(nextSeq.nextDoesNotPassAcceptedValue(vIdx, seq.apply(m)))
    nextSeq(vIdx + BigInt(1)) <= seq.apply(m)
  }.holds

  /**
   * Maps the next-sequence successor back to an old-stream index after `k`.
   *
   * In the reverse half of the skip-to-first-survivor equality, we start with
   * the value emitted by `nextSeq` immediately after the aligned old value
   * `apply(k)`. Call that value `z`. Because `nextSeq` strictly increases,
   * `z` is strictly greater than `apply(k)`.
   *
   * The reverse filter bridge then tells us that `z` is also accepted by this
   * old sequence, so `indexOfAccepted(z)` is a valid old-stream index. This
   * lemma proves that the old index cannot be at or before `k`: if it were, old
   * stream monotonicity would give `z = seq.apply(zIdx) <= seq.apply(k)`, contradicting
   * the strict next-sequence step.
   *
   * The lemma intentionally proves only the index-order fact `zIdx > k`. The
   * later reverse inequality proof will separately use this index together with
   * `assertFirstNonMultipleIsAtOrBefore` and `applyIndexOrderPreservesValues`.
   */
  private def assertNextSuccessorOldIndexAfterAnchor(
                                                      seq: SpecSieveSequence,
                                                      nextSeq: SpecSieveSequence,
                                                      k: BigInt
                                                    ): Boolean = {
    require(k >= BigInt(0))
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.tail == seq.filterValues)
    require(nextSeq.head.value == seq.head.value)
    require(nextSeq.accepts(seq.apply(k)))

    val vIdx = nextSeq.indexOfAccepted(seq.apply(k))
    assert(vIdx >= BigInt(0))
    assert(nextSeq(vIdx) == seq.apply(k))
    assert(nextSeq.applyStrictlyIncreases(vIdx))

    val z = nextSeq(vIdx + BigInt(1))
    assert(z > seq.apply(k))
    assert(nextSeq.accepts(z))
    assert(assertNextAcceptedImpliesOldAcceptedAndNewHeadNonMultiple(seq, nextSeq, z))
    assert(seq.accepts(z))

    val zIdx = seq.indexOfAccepted(z)
    assert(zIdx >= BigInt(0))
    assert(seq.apply(zIdx) == z)

    if (zIdx > k) {
      true
    } else {
      assert(zIdx <= k)
      assert(seq.applyIndexOrderPreservesValues(zIdx, k))
      assert(seq.apply(zIdx) <= seq.apply(k))
      assert(z <= seq.apply(k))
      zIdx > k
    }
  }.holds

  /**
   * Bounds the old-stream index of the next-sequence successor.
   *
   * The reverse half of the skip proof needs to call
   * `assertFirstNonMultipleIsAtOrBefore(seq, k, zIdx, p, bound)`, so the old-stream
   * index `zIdx` for the next-sequence successor must be inside the same finite
   * search window. This lemma proves that bound without involving the
   * first-non-multiple minimality argument.
   *
   * The proof first reuses the upper inequality helper:
   * `z = nextSeq(vIdx + 1) <= seq.apply(m)`. The search helper already guarantees
   * `m <= bound`, and old-stream monotonicity turns that into
   * `apply(m) <= seq.apply(bound)`. Therefore `z <= seq.apply(bound)`. Since
   * `indexOfAccepted(z)` is the old-stream index that emits `z`,
   * `valueBoundImpliesIndexBound` converts the value bound back into
   * `zIdx <= bound`.
   */
  private def assertNextSuccessorOldIndexWithinBound(
                                                      seq: SpecSieveSequence,
                                                      nextSeq: SpecSieveSequence,
                                                      k: BigInt,
                                                      p: BigInt,
                                                      bound: BigInt
                                                    ): Boolean = {
    require(k >= BigInt(0))
    require(p > BigInt(0))
    require(bound > k)
    require(Calc.mod(seq.apply(bound), p) != BigInt(0))
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.head == p)
    require(nextSeq.filterValues.tail == seq.filterValues)
    require(nextSeq.head.value == seq.head.value)
    require(nextSeq.accepts(seq.apply(k)))

    val vIdx = nextSeq.indexOfAccepted(seq.apply(k))
    val z = nextSeq(vIdx + BigInt(1))
    val zIdx = seq.indexOfAccepted(z)
    val m = findFirstNonMultipleAfter(seq, k, p, bound)

    assert(assertNextValueAtOrBeforeFirstSurvivor(seq, nextSeq, k, p, bound))
    assert(z <= seq.apply(m))
    assert(m <= bound)
    assert(m >= BigInt(0))
    assert(seq.applyIndexOrderPreservesValues(m, bound))
    assert(seq.apply(m) <= seq.apply(bound))
    assert(z <= seq.apply(bound))
    assert(seq.apply(zIdx) == z)
    assert(seq.valueBoundImpliesIndexBound(zIdx, bound))
    zIdx <= bound
  }.holds

  /**
   * Proves the reverse ordering between the first old survivor and the next value.
   *
   * The forward helper already proves that the next sequence cannot pass the
   * first old-stream value after `k` that is not a multiple of `p`. This lemma
   * proves the opposite inequality.
   *
   * Let `z` be the value emitted by `nextSeq` immediately after `apply(k)`.
   * Because `z` is accepted by `nextSeq`, it is also accepted by this old
   * sequence and is not a multiple of the new filter `p`. The previous two
   * connector lemmas place the old-stream index of `z` strictly after `k` and
   * at or before `bound`. Therefore the first non-multiple found by
   * `findFirstNonMultipleAfter` must occur at or before that old index, and
   * old-stream monotonicity gives `apply(m) <= z`.
   */
  private def assertFirstSurvivorAtOrBeforeNextValue(
                                                      seq: SpecSieveSequence,
                                                      nextSeq: SpecSieveSequence,
                                                      k: BigInt,
                                                      p: BigInt,
                                                      bound: BigInt
                                                    ): Boolean = {
    require(k >= BigInt(0))
    require(p > BigInt(0))
    require(bound > k)
    require(Calc.mod(seq.apply(bound), p) != BigInt(0))
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.head == p)
    require(nextSeq.filterValues.tail == seq.filterValues)
    require(nextSeq.head.value == seq.head.value)
    require(nextSeq.accepts(seq.apply(k)))

    val vIdx = nextSeq.indexOfAccepted(seq.apply(k))
    val z = nextSeq(vIdx + BigInt(1))
    val zIdx = seq.indexOfAccepted(z)
    val m = findFirstNonMultipleAfter(seq, k, p, bound)

    assert(assertNextSuccessorOldIndexAfterAnchor(seq, nextSeq, k))
    assert(zIdx > k)
    assert(assertNextSuccessorOldIndexWithinBound(seq, nextSeq, k, p, bound))
    assert(zIdx <= bound)
    assert(assertNextAcceptedImpliesOldAcceptedAndNewHeadNonMultiple(seq, nextSeq, z))
    assert(seq.accepts(z))
    assert(Calc.mod(z, p) != BigInt(0))
    assert(seq.apply(zIdx) == z)
    assert(Calc.mod(seq.apply(zIdx), p) != BigInt(0))
    assert(assertFirstNonMultipleIsAtOrBefore(seq, k, zIdx, p, bound))
    assert(m <= zIdx)
    assert(seq.applyIndexOrderPreservesValues(m, zIdx))
    assert(seq.apply(m) <= seq.apply(zIdx))
    seq.apply(m) <= z
  }.holds

  /**
   * Connects both ordering directions into the skip-to-first-survivor equality.
   *
   * Starting from an old value `apply(k)` that also exists in `nextSeq`, the
   * next value in `nextSeq` is exactly the first later old-stream value that is
   * not a multiple of the new filter `p`. Earlier old values may still satisfy
   * this sequence's tail filter, but they are skipped precisely because `p`
   * divides them.
   *
   * This lemma is intentionally only the bounded equality. It does not choose
   * the bound; callers remain responsible for proving a finite search window
   * whose endpoint is itself not a multiple of `p`.
   */
  private def assertNextSuccessorIsFirstSurvivor(
                                                  seq: SpecSieveSequence,
                                                  nextSeq: SpecSieveSequence,
                                                  k: BigInt,
                                                  p: BigInt,
                                                  bound: BigInt
                                                ): Boolean = {
    require(k >= BigInt(0))
    require(p > BigInt(0))
    require(bound > k)
    require(Calc.mod(seq.apply(bound), p) != BigInt(0))
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.head == p)
    require(nextSeq.filterValues.tail == seq.filterValues)
    require(nextSeq.head.value == seq.head.value)
    require(nextSeq.accepts(seq.apply(k)))

    val vIdx = nextSeq.indexOfAccepted(seq.apply(k))
    val m = findFirstNonMultipleAfter(seq, k, p, bound)

    assert(assertNextValueAtOrBeforeFirstSurvivor(seq, nextSeq, k, p, bound))
    assert(nextSeq(vIdx + BigInt(1)) <= seq.apply(m))
    assert(assertFirstSurvivorAtOrBeforeNextValue(seq, nextSeq, k, p, bound))
    assert(seq.apply(m) <= nextSeq(vIdx + BigInt(1)))
    nextSeq(vIdx + BigInt(1)) == seq.apply(m)
  }.holds

  /**
   * Exposes the finite endpoint used by the period-based merge proof.
   *
   * The skipped-successor merge needs a bounded search for the first old-stream
   * value after `k` that survives the new front filter `p`. The endpoint
   * `k + p * period` is useful because one old period adds `tailPrimorial`, so
   * `p` whole periods add `p * seq.tailPrimorial`. That shift preserves the
   * remainder modulo `p`, which means the endpoint survives whenever `apply(k)`
   * survives.
   *
   * This lemma packages those endpoint facts for callers: the bound is after
   * `k`, the divisor `p` is positive, and `apply(bound)` is not a multiple of
   * `p`.
   */
  private def assertPeriodBoundIsNonMultiple(
                                              seq: SpecSieveSequence,
                                              nextSeq: SpecSieveSequence,
                                              k: BigInt, period: BigInt
                                            ): Boolean = {
    require(k >= BigInt(0))
    require(period > BigInt(0))
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.tail == seq.filterValues)
    require(nextSeq.head.value == seq.head.value)
    require(nextSeq.accepts(seq.apply(k)))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)
    require(Calc.mod(seq.head.value + seq.tailPrimorial, nextSeq.filterValues.head) != BigInt(0))

    val p = nextSeq.filterValues.head
    val bound = k + p * period

    seq.primorialMatchesSieveProduct(seq.filterPrimes)
    assert(seq.tailPrimorial == SieveUtils.product(seq.filterValues))
    assert(p > BigInt(0))
    assert(bound > k)
    assert(seq.assertBlockShiftMultiple(k, p, period))
    assert(seq.apply(bound) == seq.apply(k) + p * seq.tailPrimorial)
    assert(assertNextAcceptedImpliesOldAcceptedAndNewHeadNonMultiple(seq, nextSeq, seq.apply(k)))
    assert(Calc.mod(seq.apply(k), p) != BigInt(0))
    assert(AdditionAndMultiplication.ATimesBSameMod(seq.apply(k), p, seq.tailPrimorial))
    assert(Calc.mod(seq.apply(k) + p * seq.tailPrimorial, p) == Calc.mod(seq.apply(k), p))

    Calc.mod(seq.apply(bound), p) != BigInt(0)
  }.ensuring(res => {
    val p = nextSeq.filterValues.head
    val bound = k + p * period
    res && p > BigInt(0) && bound > k && Calc.mod(seq.apply(bound), p) != BigInt(0)
  })

  /**
   * Period-based gap merge for a skipped immediate old successor.
   *
   * This is the public wrapper around the bounded merge lemma. The bounded
   * lemma needs a finite endpoint whose old-stream value is not a multiple of
   * the new front filter `p`. The period witness supplies exactly that endpoint:
   * shifting `k` by `p` whole old periods moves the value from `apply(k)` to
   * `apply(k) + p * seq.tailPrimorial`, which has the same remainder modulo `p`.
   *
   * The precondition `Calc.mod(seq.apply(k + 1), p) == 0` describes the interesting
   * merge case: the next old value is rejected by the new filter, so the next
   * sequence must skip forward. The result says it skips no more and no less
   * than the first old value after `k` that is not a multiple of `p`.
   */
  private def assertSkipUntilNonMultiple(seq: SpecSieveSequence, nextSeq: SpecSieveSequence, k: BigInt, period: BigInt): Boolean = {
    require(k >= BigInt(0))
    require(period > BigInt(0))
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.tail == seq.filterValues)
    require(nextSeq.head.value == seq.head.value)
    require(nextSeq.accepts(seq.apply(k)))
    require(Calc.mod(seq.apply(k + BigInt(1)), nextSeq.filterValues.head) == BigInt(0))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)
    require(Calc.mod(seq.head.value + seq.tailPrimorial, nextSeq.filterValues.head) != BigInt(0))

    val p = nextSeq.filterValues.head
    val vIdx = nextSeq.indexOfAccepted(seq.apply(k))
    val bound = k + p * period

    seq.primorialMatchesSieveProduct(seq.filterPrimes)
    assert(seq.tailPrimorial == SieveUtils.product(seq.filterValues))
    assert(p > BigInt(0))
    assert(bound > k)
    assert(seq.assertBlockShiftMultiple(k, p, period))
    assert(seq.apply(bound) == seq.apply(k) + p * seq.tailPrimorial)
    assert(assertNextAcceptedImpliesOldAcceptedAndNewHeadNonMultiple(seq, nextSeq, seq.apply(k)))
    assert(Calc.mod(seq.apply(k), p) != BigInt(0))
    assert(AdditionAndMultiplication.ATimesBSameMod(seq.apply(k), p, seq.tailPrimorial))
    assert(Calc.mod(seq.apply(k) + p * seq.tailPrimorial, p) == Calc.mod(seq.apply(k), p))
    assert(Calc.mod(seq.apply(bound), p) != BigInt(0))
    val m = findFirstNonMultipleAfter(seq, k, p, bound)
    assert(assertNextSuccessorIsFirstSurvivor(seq, nextSeq, k, p, bound))

    nextSeq(vIdx + BigInt(1)) == seq.apply(m)
  }.holds

  /**
   * Obvious property-name alias for the merge landing point.
   *
   * This lemma intentionally restates `assertSkipUntilNonMultiple` with a name
   * that matches the gap-cycle proof ladder: when the immediate old successor
   * `apply(k + 1)` is removed by the newly added front filter, the next sequence
   * lands exactly on the first later old-stream value that survives that new
   * filter.
   *
   * Keeping this public alias makes the merge proof easier to find from the
   * mathematical property name without forcing callers to remember the helper
   * implementation name.
   */
  private def assertMergeLandsOnFirstSurvivor(seq: SpecSieveSequence, nextSeq: SpecSieveSequence, k: BigInt, period: BigInt): Boolean = {
    require(k >= BigInt(0))
    require(period > BigInt(0))
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.tail == seq.filterValues)
    require(nextSeq.head.value == seq.head.value)
    require(nextSeq.accepts(seq.apply(k)))
    require(Calc.mod(seq.apply(k + BigInt(1)), nextSeq.filterValues.head) == BigInt(0))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)
    require(Calc.mod(seq.head.value + seq.tailPrimorial, nextSeq.filterValues.head) != BigInt(0))

    val p = nextSeq.filterValues.head
    val vIdx = nextSeq.indexOfAccepted(seq.apply(k))
    val bound = k + p * period

    assert(assertPeriodBoundIsNonMultiple(seq, nextSeq, k, period))
    val m = findFirstNonMultipleAfter(seq, k, p, bound)
    assert(assertSkipUntilNonMultiple(seq, nextSeq, k, period))

    nextSeq(vIdx + BigInt(1)) == seq.apply(m)
  }.holds

  /**
   * Proves the merged-gap corollary for the skipped-successor case.
   *
   * When the immediate old successor `apply(k + 1)` is removed by the new front
   * filter, `nextSeq` lands on the first later old-stream survivor `apply(m)`.
   * The new gap is therefore not a new arithmetic object; it is exactly the
   * telescope of the old adjacent gaps from `k` up to `m`.
   *
   * This is the gap-list merge shape needed by the prefix transformer: copied
   * gaps use `assertFilterPreservesNextGap`, while skipped runs use this lemma
   * to replace several old gaps with their sum.
   */
  private def assertMergeGapEqualsOldGapSum(seq: SpecSieveSequence, nextSeq: SpecSieveSequence, k: BigInt, period: BigInt): Boolean = {
    require(k >= BigInt(0))
    require(period > BigInt(0))
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.tail == seq.filterValues)
    require(nextSeq.head.value == seq.head.value)
    require(nextSeq.accepts(seq.apply(k)))
    require(Calc.mod(seq.apply(k + BigInt(1)), nextSeq.filterValues.head) == BigInt(0))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)
    require(Calc.mod(seq.head.value + seq.tailPrimorial, nextSeq.filterValues.head) != BigInt(0))

    val p = nextSeq.filterValues.head
    val vIdx = nextSeq.indexOfAccepted(seq.apply(k))
    val bound = k + p * period

    assert(assertPeriodBoundIsNonMultiple(seq, nextSeq, k, period))
    val m = findFirstNonMultipleAfter(seq, k, p, bound)
    assert(m >= k)
    assert(assertMergeLandsOnFirstSurvivor(seq, nextSeq, k, period))
    assert(nextSeq(vIdx) == seq.apply(k))
    assert(nextSeq(vIdx + BigInt(1)) == seq.apply(m))
    assert(seq.assertSumGapTelescopes(k, m))

    nextSeq(vIdx + BigInt(1)) - nextSeq(vIdx) == seq.sumGap(k, m)
  }.holds

  /**
   * Advances one output position in the merged old-index view.
   *
   * The future gap-prefix transformer should not scan natural numbers again;
   * it should walk this sequence's already-filtered indices and decide whether
   * each adjacent old gap is copied or whether several old gaps are merged.
   *
   * This helper performs exactly one such step from an old index `k` whose value
   * is already known to appear in `nextSeq`. If the immediate old successor
   * `apply(k + 1)` survives the new front filter, the next old index is simply
   * `k + 1`. Otherwise the step uses the bounded period witness to find the
   * first later old value that is not a multiple of the new front filter. In
   * both cases the returned index is strictly after `k`. Its value is still
   * accepted by this sequence, is not a multiple of the new front filter, and
   * is accepted by `nextSeq`. Exporting all three facts is important: callers
   * cannot rely on the internal proof assertions, so the bridge-shape invariant
   * must appear in the post condition.
   *
   * The post condition also exports two gap equalities:
   *  - The **value equality** `nextSeq(nextSeqIndex + 1) == seq.apply(result)`:
   *    the next sequence's next value equals the old sequence's value at the
   *    returned index.
   *  - The **difference equality** `nextSeq(nextSeqIndex + 1) - nextSeq(nextSeqIndex) == sumGap(k, result)`:
   *    the next sequence's gap equals the telescoped sum of old gaps.
   *    Both are needed by callers: the difference equality for gap-level reasoning
   *    (`assertMergedGapPrefixHeadMatchesNext`) and the value equality for
   *    cross-sequence index matching (`assertMergedGapPrefixMatchesNext`).
   */
  def nextMergedGapOldIndex(seq: SpecSieveSequence, nextSeq: SpecSieveSequence, k: BigInt, period: BigInt): BigInt = {
    require(k >= BigInt(0))
    require(period > BigInt(0))
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.tail == seq.filterValues)
    require(nextSeq.head.value == seq.head.value)
    require(nextSeq.accepts(seq.apply(k)))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)
    require(Calc.mod(seq.head.value + seq.tailPrimorial, nextSeq.filterValues.head) != BigInt(0))

    val frontFilterPrime = nextSeq.filterValues.head
    val nextSeqIndex = nextSeq.indexOfAccepted(seq.apply(k))

    if (Calc.mod(seq.apply(k + BigInt(1)), frontFilterPrime) != BigInt(0)) {
      assert(seq.accepts(seq.apply(k + BigInt(1))))
      assert(assertAcceptedByNextWhenOldAcceptedAndNewHeadNonMultiple(seq, nextSeq, seq.apply(k + BigInt(1))))
      assert(assertFilterPreservesNextGap(seq, nextSeq, k))
      assert(nextSeq(nextSeqIndex + BigInt(1)) == seq.apply(k + BigInt(1)))
      k + BigInt(1)
    } else {
      val searchUpperBound = k + frontFilterPrime * period

      assert(assertPeriodBoundIsNonMultiple(seq, nextSeq, k, period))
      val firstSurvivorOldIndex = findFirstNonMultipleAfter(seq, k, frontFilterPrime, searchUpperBound)
      assert(firstSurvivorOldIndex > k)
      assert(seq.accepts(seq.apply(firstSurvivorOldIndex)))
      assert(Calc.mod(seq.apply(firstSurvivorOldIndex), frontFilterPrime) != BigInt(0))
      assert(assertAcceptedByNextWhenOldAcceptedAndNewHeadNonMultiple(seq, nextSeq, seq.apply(firstSurvivorOldIndex)))
      assert(assertMergeGapEqualsOldGapSum(seq, nextSeq, k, period))
      assert(seq.assertSumGapTelescopes(k, firstSurvivorOldIndex))
      assert(nextSeq(nextSeqIndex + BigInt(1)) == seq.apply(firstSurvivorOldIndex))
      firstSurvivorOldIndex
    }
  }.ensuring(result =>
    result > k &&
      seq.accepts(seq.apply(result)) &&
      Calc.mod(seq.apply(result), nextSeq.filterValues.head) != BigInt(0) &&
      nextSeq.accepts(seq.apply(result)) && {
      val computedNextSeqIndex = nextSeq.indexOfAccepted(seq.apply(k))
      nextSeq(computedNextSeqIndex + BigInt(1)) == seq.apply(result) &&
        nextSeq(computedNextSeqIndex + BigInt(1)) - nextSeq(computedNextSeqIndex) == seq.sumGap(k, result)
    }
  )

  /**
   * Public wrapper for the old-index step used by the next-stage filter.
   *
   * This exposes the already-verified `nextMergedGapOldIndex` result without
   * exposing the private search helpers. Starting from an old index `k` whose
   * value appears in `nextSeq`, the returned old index is the next value
   * emitted by `nextSeq`. It is strictly after `k`, survives the newly added
   * front filter, and its value equals `nextSeq(indexOfAccepted(seq.apply(k)) + 1)`.
   *
   * Math:
   *
   *   j = nextAcceptedOldIndex(nextSeq, k, period)
   *   nextSeq(indexOfAccepted(seq.apply(k)) + 1) = seq.apply(j)
   *   j > k
   *   mod(seq.apply(j), nextSeq.filterValues.head) != 0
   */
  def nextAcceptedOldIndex(
                            seq: SpecSieveSequence,
                            nextSeq: SpecSieveSequence,
    k: BigInt,
    period: BigInt
  ): BigInt = {
    require(k >= BigInt(0))
    require(period > BigInt(0))
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.tail == seq.filterValues)
    require(nextSeq.head.value == seq.head.value)
    require(nextSeq.accepts(seq.apply(k)))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)
    require(Calc.mod(seq.head.value + seq.tailPrimorial, nextSeq.filterValues.head) != BigInt(0))

    nextMergedGapOldIndex(seq, nextSeq, k, period)
  }.ensuring(result =>
    result > k &&
      seq.accepts(seq.apply(result)) &&
      Calc.mod(seq.apply(result), nextSeq.filterValues.head) != BigInt(0) &&
      nextSeq.accepts(seq.apply(result)) && {
      val computedNextSeqIndex = nextSeq.indexOfAccepted(seq.apply(k))
      nextSeq(computedNextSeqIndex + BigInt(1)) == seq.apply(result)
    }
  )

  /**
   * Every old index skipped by `nextAcceptedOldIndex` is removed by the new
   * front filter.
   *
   * This is the public, caller-friendly form of the private
   * `assertSkippedIndexBeforeFirstIsMultiple` recursion. It is the fact needed
   * to feed `GapProperties.allMultiplesInRange` on the cycle side: the new
   * sequence did not skip arbitrary values; it skipped exactly a prefix whose
   * old values are multiples of `nextSeq.filterValues.head`.
   *
   * Math:
   *
   *   k < idx < nextAcceptedOldIndex(nextSeq, k, period)
   *   ------------------------------------------------------------
   *   mod(seq.apply(idx), nextSeq.filterValues.head) = 0
   */
  def assertSkippedBeforeNextAcceptedOldIndexIsMultiple(
                                                         seq: SpecSieveSequence,
                                                         nextSeq: SpecSieveSequence,
    k: BigInt,
    idx: BigInt,
    period: BigInt
  ): Boolean = {
    require(k >= BigInt(0))
    require(idx > k)
    require(period > BigInt(0))
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.tail == seq.filterValues)
    require(nextSeq.head.value == seq.head.value)
    require(nextSeq.accepts(seq.apply(k)))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)
    require(Calc.mod(seq.head.value + seq.tailPrimorial, nextSeq.filterValues.head) != BigInt(0))
    require(idx < nextAcceptedOldIndex(seq, nextSeq, k, period))

    val p = nextSeq.filterValues.head
    val nextOldIndex = nextAcceptedOldIndex(seq, nextSeq, k, period)

    val skippedIsMultiple = if (Calc.mod(seq.apply(k + BigInt(1)), p) != BigInt(0)) {
      assert(nextOldIndex == k + BigInt(1))
      assert(idx < k + BigInt(1))
      false
    } else {
      val bound = k + p * period

      assert(assertPeriodBoundIsNonMultiple(seq, nextSeq, k, period))
      val firstSurvivor = findFirstNonMultipleAfter(seq, k, p, bound)
      assert(nextOldIndex == firstSurvivor)
      assert(idx < firstSurvivor)
      assert(assertSkippedIndexBeforeFirstIsMultiple(seq, k, idx, p, bound))
      assert(Calc.mod(seq.apply(idx), p) == BigInt(0))
      Calc.mod(seq.apply(idx), p) == BigInt(0)
    }

    skippedIsMultiple
  }.holds

  /**
   * Builds a bounded prefix of the copied-or-merged gap list.
   *
   * This is the executable shape of the gap-merge process. The parameter
   * `remaining` says how many next-sequence gaps to emit, so termination is
   * independent of how many old indices are skipped in each merge. The parameter
   * `k` is the current old index whose value is already aligned with the current
   * next-sequence value; that alignment is represented by
   * `nextSeq.accepts(seq.apply(k))`.
   *
   * Each recursive step asks `nextMergedGapOldIndex` for the next old index
   * whose value survives the new front filter. The emitted gap is the telescoped
   * old distance from `k` to that returned index. A one-index move is a copied
   * gap. A longer move is a merged gap. The returned list is therefore not
   * produced by scanning natural numbers again; it is produced by walking the
   * old sequence's accepted values and merging exactly the runs removed by the
   * new filter.
   */
  def mergedGapPrefix(
                       seq: SpecSieveSequence,
                       nextSeq: SpecSieveSequence,
                               k: BigInt,
                               remaining: BigInt,
                               period: BigInt
                             ): List[BigInt] = {
    require(k >= BigInt(0))
    require(remaining >= BigInt(0))
    require(period > BigInt(0))
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.tail == seq.filterValues)
    require(nextSeq.head.value == seq.head.value)
    require(nextSeq.accepts(seq.apply(k)))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)
    require(Calc.mod(seq.head.value + seq.tailPrimorial, nextSeq.filterValues.head) != BigInt(0))
    decreases(remaining)

    if (remaining == BigInt(0)) {
      List.empty[BigInt]
    } else {
      val nextK = nextMergedGapOldIndex(seq, nextSeq, k, period)

      assert(nextK > k)
      assert(nextK >= k)
      assert(nextK >= BigInt(0))
      assert(nextSeq.accepts(seq.apply(nextK)))
      seq.sumGap(k, nextK) :: mergedGapPrefix(seq, nextSeq, nextK, remaining - BigInt(1), period)
    }
  }

  /**
   * Proves every gap emitted by `mergedGapPrefix` is strictly positive.
   *
   * This is the list-level lift of `assertSumGapPositive`. Each emitted gap is
   * `sumGap(currentOldIndex, nextOldIndex)`, where `nextMergedGapOldIndex`
   * guarantees `nextOldIndex > currentOldIndex`. By `assertSumGapPositive`,
   * that single gap is strictly positive, and by induction on `remaining`,
   * the entire emitted list satisfies `allGreaterThan(_, 0)`.
   *
   * The inductive step makes the head/tail split explicit via
   * `ListBoundUtils.assertGreaterThanHeadTail`, so the solver sees both the
   * head positivity (from the single-step lemma) and the tail positivity
   * (from the inductive hypothesis) as separate facts before being asked to
   * combine them.
   */
  private def assertMergedGapPrefixAllPositive(
                                                seq: SpecSieveSequence,
                                                nextSeq: SpecSieveSequence,
    k: BigInt,
    remaining: BigInt,
    period: BigInt
  ): Boolean = {
    require(k >= BigInt(0))
    require(remaining >= BigInt(0))
    require(period > BigInt(0))
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.tail == seq.filterValues)
    require(nextSeq.head.value == seq.head.value)
    require(nextSeq.accepts(seq.apply(k)))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)
    require(Calc.mod(seq.head.value + seq.tailPrimorial, nextSeq.filterValues.head) != BigInt(0))
    decreases(remaining)

    val prefix = mergedGapPrefix(seq, nextSeq, k, remaining, period)
    if (remaining == BigInt(0)) {
      ListBoundUtils.allGreaterThan(prefix, BigInt(0))
    } else {
      val nextOldIndex = nextMergedGapOldIndex(seq, nextSeq, k, period)
      val tailPrefix = mergedGapPrefix(seq, nextSeq, nextOldIndex, remaining - BigInt(1), period)

      assert(seq.assertSumGapPositive(k, nextOldIndex))
      assert(assertMergedGapPrefixAllPositive(seq, nextSeq, nextOldIndex, remaining - BigInt(1), period))
      assert(ListBoundUtils.assertGreaterThanHeadTail(prefix, BigInt(0)))
      ListBoundUtils.allGreaterThan(prefix, BigInt(0))
    }
  }.holds

  /**
   * Proves that the first gap emitted by `mergedGapPrefix(nextSeq, k, 1, period)`
   * equals the corresponding next-sequence gap.
   *
   * The next-sequence gap at the position of `apply(k)` is
   * `nextSeq(vIdx + 1) - nextSeq(vIdx)` where `vIdx` is the next-sequence index
   * of `apply(k)`. The prefix emits `sumGap(k, nextK)` for the next old index
   * `nextK = nextMergedGapOldIndex(nextSeq, k, period)`. The `.ensuring`
   * post condition of `nextMergedGapOldIndex` directly equates these two gaps
   * (both as difference and as value equality).
   *
   * This is the inductive base for `assertMergedGapPrefixMatchesNext`.
   */
  private def assertMergedGapPrefixHeadMatchesNext(
                                                    seq: SpecSieveSequence,
                                                    nextSeq: SpecSieveSequence,
    k: BigInt,
    period: BigInt
  ): Boolean = {
    require(k >= BigInt(0))
    require(period > BigInt(0))
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.tail == seq.filterValues)
    require(nextSeq.head.value == seq.head.value)
    require(nextSeq.accepts(seq.apply(k)))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)
    require(Calc.mod(seq.head.value + seq.tailPrimorial, nextSeq.filterValues.head) != BigInt(0))

    val prefix = mergedGapPrefix(seq, nextSeq, k, BigInt(1), period)
    val nextSeqIndex = nextSeq.indexOfAccepted(seq.apply(k))

    prefix.head == nextSeq(nextSeqIndex + BigInt(1)) - nextSeq(nextSeqIndex)
  }.holds

  /**
   * Proves that the prefix built by `mergedGapPrefix(nextSeq, k, remaining, period)`
   * equals the gap list `nextSeq.gapList(seqIndex, remaining)` where `seqIndex`
   * is the next-sequence index of `apply(k)`.
   *
   * The proof proceeds by induction on `remaining`:
   *  - **Base case** (`remaining == 0`): both sides are empty lists.
   *  - **Inductive step** (`remaining > 0`):
   *    1. `assertMergedGapPrefixHeadMatchesNext` proves the first gap matches.
   *       2. `assertMergedGapPrefixMatchesNext` (recursive) proves the tail matches
   *       by the inductive hypothesis, using `seqIndex + 1` as the new position.
   *       3. `nextSeq.assertApplyInjective` bridges the gap between the parameter
   *       `seqIndex` and `nextSeq.indexOfAccepted(seq.apply(k))`, which is needed
   *       to connect the `.ensuring` post condition of `nextMergedGapOldIndex`
   *       to this lemma's parameter.
   *
   * This is shape (a) of the prefix equality — the list-level statement. Shape (b)
   * (partial sums reconstruct nextSeq.apply) follows as a corollary because
   * gapList's cumulative sums reconstruct nextSeq.apply by construction.
   */
  def assertMergedGapPrefixMatchesNext(
                                        seq: SpecSieveSequence,
                                        nextSeq: SpecSieveSequence,
    k: BigInt,
    seqIndex: BigInt,
    remaining: BigInt,
    period: BigInt
  ): Boolean = {
    require(k >= BigInt(0))
    require(seqIndex >= BigInt(0))
    require(remaining >= BigInt(0))
    require(period > BigInt(0))
    require(nextSeq.filterValues.nonEmpty)
    require(nextSeq.filterValues.tail == seq.filterValues)
    require(nextSeq.head.value == seq.head.value)
    require(nextSeq.accepts(seq.apply(k)))
    require(nextSeq(seqIndex) == seq.apply(k))
    require(seq.apply(period) == seq.head.value + seq.tailPrimorial)
    require(Calc.mod(seq.head.value + seq.tailPrimorial, nextSeq.filterValues.head) != BigInt(0))
    decreases(remaining)

    val prefix = mergedGapPrefix(seq, nextSeq, k, remaining, period)

    if (remaining == BigInt(0)) {
      prefix == nextSeq.gapList(seqIndex, BigInt(0))
    } else {
      val nextOldIndex = nextMergedGapOldIndex(seq, nextSeq, k, period)
      val computedSeqIndex = nextSeq.indexOfAccepted(seq.apply(k))

      assert(nextSeq.assertApplyInjective(seqIndex, computedSeqIndex))
      assert(assertMergedGapPrefixHeadMatchesNext(seq, nextSeq, k, period))
      assert(assertMergedGapPrefixMatchesNext(seq, nextSeq, nextOldIndex, seqIndex + BigInt(1), remaining - BigInt(1), period))

      prefix == nextSeq.gapList(seqIndex, remaining)
    }
  }.holds
}
