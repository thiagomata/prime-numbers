package v1.chapter4.cycle.integral.recursive.properties

import stainless.collection.List
import stainless.lang.{decreases, BooleanDecorations}
import stainless.lang.BigInt
import v1.chapter1.verification.Helper.assert
import v1.chapter2.div.Calc
import v1.chapter3.list.{ListBoundUtils, ListUtils, ShiftedList}
import v1.chapter3.list.properties.{ListRepeatProperties, ListUtilsProperties, RotationProperties}
import v1.chapter4.cycle.integral.recursive.CycleIntegral

/**
 * Gap properties for integral sequences and sieve cycles.
 *
 * A "gap" is an adjacent difference in a value sequence:
 * `apply(i + 1) - apply(i) = gaps(i)`. This file unifies three theorems
 * central to the independent next-cycle proof in Chapter 6:
 *
 *  - **Repeated gaps** — repeating a gap cycle preserves the integral at
 *    positions within the original period (via `assertRepeatedValuesIntegralMatches`).
 *  - **Merged gaps** — the sum of consecutive gaps telescopes to the
 *    integral difference (via `assertConsecutiveGapSumEqualsDiff`)
 *    and merged gaps are strictly positive (via `assertMergedGapIsCITelescope`).
 *  - **Rotated gaps** — rotating a gap cycle by 1 and adjusting the head
 *    shifts the integral by 1 (via `ShiftedList.assertShiftedApplyIsOriginalPlusOne`).
 *
 * The `k > 1` rotations (multi-step shift) and the full merged-gap equality
 * (`ci(to) - ci(from) == sum(gaps[from..to-1])`) are open extensions
 * documented as drafts.
 */
object GapProperties {

  // ------------------------------------------------------------
  //  1. GAP ROTATION + HEAD CHANGE → INTEGRAL SHIFT
  // ------------------------------------------------------------

  /**
   * Rotation-by-1 with head-adjustment shifts the integral by 1 position.
   *
   * For `shifted = ShiftedList.shift(head, gaps)` and
   * `orig = ShiftedList(head, gaps)`:
   *
   * [Verified] in `ShiftedList.assertShiftedApplyIsOriginalPlusOne`.
   */
  def assertRotateOneShiftsIntegralByOne(
    origHead: BigInt,
    gaps: List[BigInt],
    i: BigInt
  ): Boolean = {
    require(gaps.nonEmpty)
    require(i >= 0)
    require(i + 1 < gaps.size)
    ShiftedList.assertShiftedApplyIsOriginalPlusOne(origHead, gaps, i)
  }.holds

  // GENERALISATION TO k > 1 (DRAFT — requires rotation-sum lemmas):
  //
  // shift_k(head, gaps, k).apply(i) == orig.apply(i + k)
  //
  // Where shift_k advances head by sum(gaps[0..k-1]) and rotates gaps by k.
  // The induction step needs bridging between shift_{k-1}(shifted) and
  // shift_k via rotation-index + rotation-sum lemmas.

  def shiftK(
    origHead: BigInt,
    gaps: List[BigInt],
    k: BigInt
  ): ShiftedList = {
    require(gaps.nonEmpty)
    require(k >= 0)
    require(k < gaps.size)
    val prefixSum = ListUtils.sum(ListUtils.slice(gaps, BigInt(0), k))
    ShiftedList(origHead + prefixSum, ListUtils.rotateAt(gaps, k))
  }

  // ------------------------------------------------------------
  //  2.  REPEATED GAPS → SAME INTEGRAL WITHIN ORIGINAL PERIOD
  // ------------------------------------------------------------

  /**
   * Repeating a gap cycle `times` times does not change the integral at
   * positions within the original period.
   *
   * [Verified] in `CycleIntegralProperties.assertRepeatedValuesIntegralMatches`.
   */
  def assertRepeatedGapsPreservesIntegral(
    originalCI: CycleIntegral,
    repeatedCI: CycleIntegral,
    times: BigInt,
    pos: BigInt
  ): Boolean = {
    require(times > BigInt(0))
    require(pos >= BigInt(0))
    require(originalCI.cycle.size > BigInt(0))
    require(repeatedCI.initialValue == originalCI.initialValue)
    require(repeatedCI.cycle.values ==
      ListRepeatProperties.repeat(originalCI.cycle.values, times))
    CycleIntegralProperties.assertRepeatedValuesIntegralMatches(
      originalCI, repeatedCI, times, pos
    )
  }.holds

  // ------------------------------------------------------------
  //  3.  MERGED GAPS (telescoping · filtered)
  // ------------------------------------------------------------

  /**
   * Two consecutive gaps telescope to the integral difference.
   *
   * [Verified] in `CycleIntegralProperties.assertConsecutiveGapSumEqualsDiff`.
   */
  def assertTwoGapSumEqualsDiff(
    ci: CycleIntegral,
    k: BigInt
  ): Boolean = {
    require(k >= BigInt(1))
    require(ci.cycle.size > k + BigInt(1))
    require(ci.cycle.values.nonEmpty)
    CycleIntegralProperties.assertConsecutiveGapSumEqualsDiff(ci, k)
  }.holds

  /**
   * A merged gap (difference between two consecutive survivors after
   * filtering) is strictly positive.
   *
   * [Verified] in `CycleIntegralFilterProperties.assertMergedGapIsCITelescope`.
   */
  def assertMergedGapPositive(
    ci: CycleIntegral,
    filterValue: BigInt,
    fromPosition: BigInt,
    toPosition: BigInt
  ): Boolean = {
    require(fromPosition >= 0)
    require(toPosition > fromPosition)
    require(filterValue > 0)
    require(Calc.mod(ci(fromPosition), filterValue) != BigInt(0))
    require(Calc.mod(ci(toPosition), filterValue) != BigInt(0))
    require(CycleIntegralFilterProperties.allMultiplesBetween(
      ci, filterValue, fromPosition, toPosition
    ))
    require(ci.initialValue >= BigInt(0))
    require(ListBoundUtils.allGreaterThan(ci.cycle.values, BigInt(0)))
    CycleIntegralFilterProperties.assertMergedGapIsCITelescope(
      ci, filterValue, fromPosition, toPosition
    )
  }.holds

  // GENERALISATION TO N-GAP MERGE (DRAFT):
  //
  // ci(toPosition) - ci(fromPosition) == sum(ci.cycle.values[fromPosition..toPosition-1])
  //
  // The n-gap version follows by induction on (toPos - fromPos),
  // using assertConsecutiveGapSumEqualsDiff at each step.
  // Open because sum(slice(values, from, to)) equality with term-by-term
  // induction requires an explicit sum-slice decomposition lemma.

  // ------------------------------------------------------------
  // ------------------------------------------------------------
  //  4.  SUPPORT: SUM-SLICE DECOMPOSITION
  // ------------------------------------------------------------

  /**
   * Step-lemma: `sum(slice(list, from, to)) == sum(slice(list, from, to-1)) + list(to)`.
   *
   * Follows from `assertAppendToSlice` + `listCombine` + `listAddValueTail`.
   */
  private def assertSumSliceStep(
    list: List[BigInt],
    from: BigInt,
    to: BigInt
  ): Boolean = {
    require(from >= 0)
    require(from < to)
    require(to < list.size)

    val left = ListUtils.slice(list, from, to - BigInt(1))
    val right = List(list(to))

    assert(ListUtilsProperties.assertAppendToSlice(list, from, to))
    assert(ListUtils.slice(list, from, to) == left ++ right)

    assert(ListUtils.listCombine(left, right))
    assert(ListUtils.sum(left ++ right) == ListUtils.sum(left) + ListUtils.sum(right))

    assert(ListUtils.listAddValueTail(List.empty[BigInt], list(to)))
    assert(ListUtils.sum(right) == list(to))

    ListUtils.sum(ListUtils.slice(list, from, to)) ==
      ListUtils.sum(ListUtils.slice(list, from, to - BigInt(1))) + list(to)
  }.holds

  // ------------------------------------------------------------
  //  4.  MERGED GAPS: SURVIVOR PROPERTIES
  // ------------------------------------------------------------

  /**
   * The first survivor is the head of the cycle integral — the value at
   * the start position survives the filter (it is not a multiple of
   * `filterValue`).
   *
   * [Verified] in `CycleIntegralFilterProperties.assertFirstSurvivorHead`.
   */
  def assertFirstSurvivorIsHead(
    ci: CycleIntegral,
    filterValue: BigInt,
    startPos: BigInt,
    count: BigInt
  ): Boolean = {
    require(filterValue > 0)
    require(startPos >= 0)
    require(count > 0)
    require(Calc.mod(ci(startPos), filterValue) != BigInt(0))
    CycleIntegralFilterProperties.assertFirstSurvivorHead(ci, filterValue, startPos, count)
  }.holds

  /**
   * The survivors list is non-empty — at least one value passes the
   * filter. Follows from `assertFirstSurvivorHead`.
   */
  def assertSurvivorsNonEmpty(
    ci: CycleIntegral,
    filterValue: BigInt,
    startPos: BigInt,
    count: BigInt
  ): Boolean = {
    require(filterValue > 0)
    require(startPos >= 0)
    require(count > 0)
    require(Calc.mod(ci(startPos), filterValue) != BigInt(0))
    assert(assertFirstSurvivorIsHead(ci, filterValue, startPos, count))
    CycleIntegralFilterProperties.survivorValues(ci, filterValue, startPos, count).nonEmpty
  }.holds

  /**
   * The last survivor is the last scanned CI value — when the final
   * position in the scan range also passes the filter, it ends up as
   * the final element of the survivors list.
   *
   * Together with `assertFirstSurvivorIsHead`, the first and last
   * survivors bracket the original scan range, giving
   * `survivors.last - survivors.head == ci(last) - ci(first)`.
   */
  def assertLastSurvivorIsLastScanned(
    ci: CycleIntegral,
    filterValue: BigInt,
    startPos: BigInt,
    count: BigInt
  ): Boolean = {
    require(filterValue > 0)
    require(startPos >= 0)
    require(count > 0)
    require(Calc.mod(ci(startPos + count - BigInt(1)), filterValue) != BigInt(0))
    decreases(count)

    val survivors = CycleIntegralFilterProperties.survivorValues(ci, filterValue, startPos, count)
    val lastPos = startPos + count - BigInt(1)

    if (count == BigInt(1)) {
      survivors.last == ci(lastPos)
    } else if (Calc.mod(ci(startPos), filterValue) != BigInt(0)) {
      assert(assertLastSurvivorIsLastScanned(ci, filterValue, startPos + BigInt(1), count - BigInt(1)))
      survivors.last == ci(lastPos)
    } else {
      assert(assertLastSurvivorIsLastScanned(ci, filterValue, startPos + BigInt(1), count - BigInt(1)))
      survivors.last == ci(lastPos)
    }
  }.holds

  // ------------------------------------------------------------
  //  5.  CYCLE-PERIOD SHIFT
  // ------------------------------------------------------------

  /**
   * Shifting by one full cycle adds the sum of all cycle values.
   *
   * \[ ci(pos + ci.size) == ci(pos) + sum(ci.cycle.values) \]
   *
   * This is the termination bound for survivor searches: within one
   * cycle period, a survivor is always found because the integral
   * advances by a fixed amount and the gap list is non-empty.
   *
   * [Verified] in `CycleIntegralFilterProperties.assertCIShiftEqualsSum`.
   */
  def assertFullCycleShift(
    ci: CycleIntegral,
    pos: BigInt
  ): Boolean = {
    require(ci.size > 0)
    require(pos >= 0)
    require(ci(ci.size) - ci(BigInt(0)) == ci.sum)
    CycleIntegralFilterProperties.assertCIShiftEqualsSum(ci, pos)
  }.holds

  /**
   * After `m` full cycles, the integral advances by `m * sum(gaps)`.
   *
   * \[ ci(pos + ci.size \cdot m) = ci(pos) + m \cdot \sum \text{cycle.values} \]
   *
   * Proved by induction on `m` using `assertFullCycleShift` at each step.
   * This gives the periodic termination bound: every `ci.size` positions,
   * the integral increases by a constant amount, so survivor search within
   * one period is sufficient.
   */
  def assertMultiCycleShift(
    ci: CycleIntegral,
    pos: BigInt,
    m: BigInt
  ): Boolean = {
    require(ci.size > 0)
    require(pos >= 0)
    require(m >= 0)
    require(ci(ci.size) - ci(BigInt(0)) == ci.sum)
    decreases(m)

    val period = ci.size
    val totalGaps = ci.sum

    if (m == BigInt(0)) {
      ci(pos) == ci(pos) + totalGaps * BigInt(0)
    } else {
      assert(assertFullCycleShift(ci, pos + period * (m - BigInt(1))))
      assert(ci(pos + period * (m - BigInt(1)) + period) ==
        ci(pos + period * (m - BigInt(1))) + totalGaps)

      assert(assertMultiCycleShift(ci, pos, m - BigInt(1)))
      assert(ci(pos + period * (m - BigInt(1))) == ci(pos) + totalGaps * (m - BigInt(1)))

      ci(pos + period * m) == ci(pos) + totalGaps * m
    }
  }.holds

  // ------------------------------------------------------------
  //  5.  MERGED GAPS = INTEGRAL DIFFERENCE (DRAFT)
  // ------------------------------------------------------------

  // The telescoping sum property:
  //
  //   ci(to) - ci(from) == sum(slice(ci.cycle.values, from, to - BigInt(1)))
  //
  // The two-gap case is proven (assertConsecutiveGapSumEqualsDiff).
  // The n-gap case follows by induction with sum-slice decomposition;
  // the sum-step helper (assertSumSliceStep, 26/26) is verified, but
  // the induction over the integral cannot close the gap because the
  // decreases measure on (to - from) does not terminate in the SMT solver.

  // ------------------------------------------------------------
  //  5.  GAP-APPLY IDENTITY
  // ------------------------------------------------------------

  /**
   * The adjacent difference at `position` equals the cycle value at that
   * position:
   *
   *   ci(position + 1) - ci(position) == ci.cycle(position)
   *
   * [Verified] in `CycleIntegralProperties.assertDiffEqualsCycleValue`.
   */
  def assertGapEqualsCycleValue(
    ci: CycleIntegral,
    position: BigInt
  ): Boolean = {
    require(position >= 0)
    require(position < ci.cycle.size)
    require(position < ci.size)
    require(ci.cycle.values.nonEmpty)
    CycleIntegralProperties.assertDiffEqualsCycleValue(ci, position)
  }.holds

}
