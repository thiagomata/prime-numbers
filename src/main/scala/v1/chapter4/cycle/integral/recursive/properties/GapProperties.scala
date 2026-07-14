package v1.chapter4.cycle.integral.recursive.properties

import stainless.collection.List
import stainless.lang.{decreases, BooleanDecorations}
import stainless.lang.BigInt
import v1.chapter1.verification.Helper.assert
import v1.chapter2.div.Calc
import v1.chapter2.div.properties.{AdditionAndMultiplication, ModIdempotence, ModOperations, ModSmallDividend}
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
 * (`ci(to) - ci(from) == sum(gaps[from..to-1])`) are open extensions.
 */
object GapProperties {

  /* ---- GAP ROTATION + HEAD CHANGE (integral shift) ---- */

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

  /**
   * Rotating the backing cycle by one position and advancing the initial value
   * by the original first gap shifts the recursive cycle integral by one
   * position within the stored period.
   */
  def assertRotateOneCycleIntegralShiftsByOne(
    originalCI: CycleIntegral,
    shiftedCI: CycleIntegral,
    i: BigInt
  ): Boolean = {
    require(i >= 0)
    require(i + 1 < originalCI.period)
    require(shiftedCI.initialValue == originalCI.initialValue + originalCI.cycle(0))
    require(shiftedCI.cycle.values == ListUtils.rotateAt(originalCI.cycle.values, BigInt(1)))
    decreases(i)

    assert(originalCI.cycle.values.nonEmpty)
    assert(RotationProperties.assertRotateSameSize(originalCI.cycle.values, BigInt(1)))
    assert(shiftedCI.period == originalCI.period)
    assert(RotationProperties.assertRotatedAtIndexPlusOne(originalCI.cycle.values, i))
    assert(shiftedCI.cycle(i) == originalCI.cycle(i + 1))

    if (i == BigInt(0)) {
      assert(shiftedCI(i) == shiftedCI.initialValue + shiftedCI.cycle(0))
      assert(originalCI(i + 1) == originalCI(i) + originalCI.cycle(i + 1))
      assert(originalCI(i) == originalCI.initialValue + originalCI.cycle(0))
      assert(shiftedCI(i) == originalCI(i + 1))
    } else {
      assert(assertRotateOneCycleIntegralShiftsByOne(originalCI, shiftedCI, i - BigInt(1)))
      assert(shiftedCI(i - BigInt(1)) == originalCI(i))
      assert(shiftedCI(i) == shiftedCI(i - BigInt(1)) + shiftedCI.cycle(i))
      assert(originalCI(i + 1) == originalCI(i) + originalCI.cycle(i + 1))
      assert(shiftedCI(i) == originalCI(i + 1))
    }

    shiftedCI(i) == originalCI(i + 1)
  }.holds

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

  /* ---- REPEATED GAPS (same integral within original period) ---- */

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
    require(originalCI.cycle.period > BigInt(0))
    require(repeatedCI.initialValue == originalCI.initialValue)
    require(repeatedCI.cycle.values ==
      ListRepeatProperties.repeat(originalCI.cycle.values, times))
    CycleIntegralProperties.assertRepeatedValuesIntegralMatches(
      originalCI, repeatedCI, times, pos
    )
  }.holds

  /* ---- MERGED GAPS (telescoping, filtered) ---- */

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
    require(ci.cycle.period > k + BigInt(1))
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

  /* GENERALISATION TO N-GAP MERGE (open extension):
   *
   *   ci(toPosition) - ci(fromPosition) == sum(ci.cycle.values[fromPosition..toPosition-1])
   *
   *   The n-gap version follows by induction on (toPos - fromPos),
   *   using assertConsecutiveGapSumEqualsDiff at each step.
   *   Open because sum(slice(values, from, to)) equality with term-by-term
   *   induction requires an explicit sum-slice decomposition lemma.
   */

  /* ---- SUPPORT: SUM-SLICE DECOMPOSITION ---- */

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

  /* ---- MERGED GAPS: SURVIVOR PROPERTIES ---- */

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
   * Prefix predicate for survivor scans.
   *
   * `allMultiplesInRange(ci, f, from, until)` means every scanned value in the
   * half-open range `[from, until)` is removed by the filter `f`.
   *
   * Math:
   *
   *   \forall i. from <= i < until => mod(ci(i), f) = 0
   *
   * This shape is intentionally different from
   * `CycleIntegralFilterProperties.allMultiplesBetween`, whose endpoints are
   * exclusive for merged-gap telescoping. Survivor head proofs need the
   * inclusive-left prefix `[start, pos)` so they can show that no earlier
   * scanned position was retained.
   */
  def allMultiplesInRange(
    ci: CycleIntegral,
    filterValue: BigInt,
    fromPos: BigInt,
    untilPos: BigInt
  ): Boolean = {
    require(filterValue > 0)
    require(fromPos >= 0)
    require(untilPos >= fromPos)
    decreases(untilPos - fromPos)

    if (fromPos == untilPos) true
    else Calc.mod(ci(fromPos), filterValue) == BigInt(0) &&
      allMultiplesInRange(ci, filterValue, fromPos + BigInt(1), untilPos)
  }

  /**
   * Tail of a non-empty all-multiple prefix is still an all-multiple prefix.
   *
   * Math:
   *
   *   allMultiplesInRange(ci, f, from, until)
   *   from < until
   *   ------------------------------------------------------------
   *   allMultiplesInRange(ci, f, from + 1, until)
   */
  def assertAllMultiplesInRangeTail(
    ci: CycleIntegral,
    filterValue: BigInt,
    fromPos: BigInt,
    untilPos: BigInt
  ): Boolean = {
    require(filterValue > 0)
    require(fromPos >= 0)
    require(untilPos > fromPos)
    require(allMultiplesInRange(ci, filterValue, fromPos, untilPos))

    allMultiplesInRange(ci, filterValue, fromPos + BigInt(1), untilPos)
  }.holds

  /**
   * First retained value when all earlier scanned values are multiples.
   *
   * If every value in `[start, pos)` is removed by the filter and `ci(pos)` is
   * not removed, then the head of `survivorValues` over a scan range including
   * `pos` is exactly `ci(pos)`.
   *
   * Math:
   *
   *   start <= pos < start + count
   *   allMultiplesInRange(ci, filterValue, start, pos)
   *   mod(ci(pos), filterValue) != 0
   *   ------------------------------------------------------------
   *   survivorValues(ci, filterValue, start, count).head = ci(pos)
   *
   * This is the ordered companion to the membership/exclusion lemmas below:
   * membership says `ci(pos)` is somewhere in the survivor list; this lemma
   * says it is the first survivor when the prefix before it was filtered out.
   */
  def assertFirstSurvivorAtPosition(
    ci: CycleIntegral,
    filterValue: BigInt,
    startPos: BigInt,
    count: BigInt,
    pos: BigInt
  ): Boolean = {
    require(filterValue > 0)
    require(startPos >= 0)
    require(count > 0)
    require(pos >= startPos)
    require(pos < startPos + count)
    require(allMultiplesInRange(ci, filterValue, startPos, pos))
    require(Calc.mod(ci(pos), filterValue) != BigInt(0))
    decreases(count)

    val survivors = CycleIntegralFilterProperties.survivorValues(
      ci, filterValue, startPos, count)

    if (pos == startPos) {
      assert(Calc.mod(ci(startPos), filterValue) != BigInt(0))
      assert(assertFirstSurvivorIsHead(ci, filterValue, startPos, count))
      survivors.head == ci(pos)
    } else {
      assert(pos > startPos)
      assert(Calc.mod(ci(startPos), filterValue) == BigInt(0))
      assert(pos >= startPos + BigInt(1))
      assert(pos < startPos + BigInt(1) + (count - BigInt(1)))
      assert(assertAllMultiplesInRangeTail(
        ci, filterValue, startPos, pos))
      assert(allMultiplesInRange(
        ci, filterValue, startPos + BigInt(1), pos))
      assert(assertFirstSurvivorAtPosition(
        ci, filterValue, startPos + BigInt(1), count - BigInt(1), pos))
      survivors.head == ci(pos)
    }
  }.holds

  /**
   * Structural split at the first retained position.
   *
   * If `[start, pos)` is removed by the filter and `pos` survives, then the
   * whole survivor scan is exactly `ci(pos)` followed by the survivor scan that
   * starts after `pos`.
   *
   * Math:
   *
   *   remaining = start + count - pos - 1
   *   allMultiplesInRange(ci, f, start, pos)
   *   mod(ci(pos), f) != 0
   *   ------------------------------------------------------------
   *   survivorValues(ci, f, start, count)
   *     = ci(pos) :: survivorValues(ci, f, pos + 1, remaining)
   *
   * This is the ordered-list version of `assertFirstSurvivorAtPosition`.
   * Later chapter 6 bridges can use it to peel one survivor at a time without
   * forcing Stainless to rediscover how the skipped prefix was filtered out.
   */
  def assertSurvivorValuesSplitAtFirstPosition(
    ci: CycleIntegral,
    filterValue: BigInt,
    startPos: BigInt,
    count: BigInt,
    pos: BigInt
  ): Boolean = {
    require(filterValue > 0)
    require(startPos >= 0)
    require(count > 0)
    require(pos >= startPos)
    require(pos < startPos + count)
    require(allMultiplesInRange(ci, filterValue, startPos, pos))
    require(Calc.mod(ci(pos), filterValue) != BigInt(0))
    decreases(count)

    val survivors = CycleIntegralFilterProperties.survivorValues(
      ci, filterValue, startPos, count)
    val remaining = startPos + count - pos - BigInt(1)
    val afterPos = CycleIntegralFilterProperties.survivorValues(
      ci, filterValue, pos + BigInt(1), remaining)

    if (pos == startPos) {
      assert(Calc.mod(ci(startPos), filterValue) != BigInt(0))
      survivors == ci(pos) :: afterPos
    } else {
      assert(pos > startPos)
      assert(Calc.mod(ci(startPos), filterValue) == BigInt(0))
      assert(pos >= startPos + BigInt(1))
      assert(pos < startPos + BigInt(1) + (count - BigInt(1)))
      assert(assertAllMultiplesInRangeTail(
        ci, filterValue, startPos, pos))
      assert(allMultiplesInRange(
        ci, filterValue, startPos + BigInt(1), pos))
      assert(startPos + BigInt(1) + (count - BigInt(1)) - pos - BigInt(1) ==
        remaining)
      assert(assertSurvivorValuesSplitAtFirstPosition(
        ci, filterValue, startPos + BigInt(1), count - BigInt(1), pos))
      survivors == ci(pos) :: afterPos
    }
  }.holds

  /**
   * Survivor scan completeness for one original position.
   *
   * If a scanned CI value is not a multiple of the filter value, then the
   * survivor list contains that value. This is the first half of the exactness
   * statement for filtering: non-multiples are not removed.
   *
   * Math:
   *
   *   start <= pos < start + count
   *   mod(ci(pos), filterValue) != 0
   *   ------------------------------------------------------------
   *   ci(pos) in survivorValues(ci, filterValue, start, count)
   */
  def assertSurvivorValuesContainsNonMultipleAtPosition(
    ci: CycleIntegral,
    filterValue: BigInt,
    startPos: BigInt,
    count: BigInt,
    pos: BigInt
  ): Boolean = {
    require(filterValue > 0)
    require(startPos >= 0)
    require(count >= 0)
    require(pos >= startPos)
    require(pos < startPos + count)
    require(Calc.mod(ci(pos), filterValue) != BigInt(0))
    decreases(count)

    val survivors = CycleIntegralFilterProperties.survivorValues(
      ci, filterValue, startPos, count)

    if (count == BigInt(0)) {
      false
    } else if (pos == startPos) {
      assert(Calc.mod(ci(startPos), filterValue) != BigInt(0))
      survivors.contains(ci(pos))
    } else {
      assert(pos > startPos)
      assert(pos >= startPos + BigInt(1))
      assert(pos < startPos + BigInt(1) + (count - BigInt(1)))
      assert(assertSurvivorValuesContainsNonMultipleAtPosition(
        ci, filterValue, startPos + BigInt(1), count - BigInt(1), pos))
      CycleIntegralFilterProperties.survivorValues(
        ci, filterValue, startPos + BigInt(1), count - BigInt(1)
      ).contains(ci(pos))
      survivors.contains(ci(pos))
    }
  }.holds

  /**
   * Survivor scan soundness for one retained value.
   *
   * If a value appears in the survivor list, then it is not a multiple of the
   * filter value. This is the second half of the exactness statement for
   * filtering: the scan only keeps non-multiples.
   *
   * Math:
   *
   *   value in survivorValues(ci, filterValue, start, count)
   *   ------------------------------------------------------------
   *   mod(value, filterValue) != 0
   */
  def assertSurvivorValuesContainsOnlyNonMultiples(
    ci: CycleIntegral,
    filterValue: BigInt,
    startPos: BigInt,
    count: BigInt,
    value: BigInt
  ): Boolean = {
    require(filterValue > 0)
    require(startPos >= 0)
    require(count >= 0)
    require(CycleIntegralFilterProperties.survivorValues(
      ci, filterValue, startPos, count).contains(value))
    decreases(count)

    val survivors = CycleIntegralFilterProperties.survivorValues(
      ci, filterValue, startPos, count)

    if (count == BigInt(0)) {
      false
    } else {
      val tailSurvivors = CycleIntegralFilterProperties.survivorValues(
        ci, filterValue, startPos + BigInt(1), count - BigInt(1))

      if (Calc.mod(ci(startPos), filterValue) != BigInt(0)) {
        if (ci(startPos) == value) {
          assert(Calc.mod(value, filterValue) != BigInt(0))
        } else {
          assert(tailSurvivors.contains(value))
          assert(assertSurvivorValuesContainsOnlyNonMultiples(
            ci, filterValue, startPos + BigInt(1), count - BigInt(1), value))
        }
      } else {
        assert(tailSurvivors.contains(value))
        assert(assertSurvivorValuesContainsOnlyNonMultiples(
          ci, filterValue, startPos + BigInt(1), count - BigInt(1), value))
      }
    }

    Calc.mod(value, filterValue) != BigInt(0)
  }.holds

  /**
   * Survivor scan excludes a scanned multiple.
   *
   * This corollary packages the soundness lemma in the direct "removed value"
   * shape: if the CI value at a scanned position is a multiple of the filter
   * value, then that value is absent from the survivor list.
   *
   * Math:
   *
   *   start <= pos < start + count
   *   mod(ci(pos), filterValue) == 0
   *   ------------------------------------------------------------
   *   ci(pos) notin survivorValues(ci, filterValue, start, count)
   */
  def assertSurvivorValuesExcludesMultipleAtPosition(
    ci: CycleIntegral,
    filterValue: BigInt,
    startPos: BigInt,
    count: BigInt,
    pos: BigInt
  ): Boolean = {
    require(filterValue > 0)
    require(startPos >= 0)
    require(count >= 0)
    require(pos >= startPos)
    require(pos < startPos + count)
    require(Calc.mod(ci(pos), filterValue) == BigInt(0))

    val value = ci(pos)
    val survivors = CycleIntegralFilterProperties.survivorValues(
      ci, filterValue, startPos, count)

    if (survivors.contains(value)) {
      assert(assertSurvivorValuesContainsOnlyNonMultiples(
        ci, filterValue, startPos, count, value))
      assert(Calc.mod(value, filterValue) != BigInt(0))
      false
    } else {
      true
    }

    !survivors.contains(value)
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

  /* ---- DIV/MOD FORMULA ---- */

  /**
   * Decompose the integral at any position using div and mod:
   *
   *   ci(pos) == ci(pos % size) + (pos / size) * ci.sum
   *
   * This makes large-position evaluations O(1) instead of O(pos).
   * Wraps `assertCycleIntegralEqualsSumOfModValuesAsList`.
   */
  def assertCIModDivFormula(
    ci: CycleIntegral,
    pos: BigInt
  ): Boolean = {
    require(ci.period > 0)
    require(pos >= 0)
    CycleIntegralProperties.assertCycleIntegralEqualsSumOfModValuesAsList(ci, pos)
  }.holds

  /**
   * Filtering one full period preserves the total gap sum.
   * Scans `ci.size + 1` positions (one more than the cycle size
   * to cover all gaps exactly once).
   *
   *   survivors.last - survivors.head == ci.sum
   */
  def assertFilteredSumEqualsOriginalSum(
    ci: CycleIntegral,
    filterValue: BigInt
  ): Boolean = {
    require(filterValue > 0)
    require(ci.period > 0)
    require(ci(ci.period) - ci(BigInt(0)) == ci.sum)
    require(Calc.mod(ci(BigInt(0)), filterValue) != BigInt(0))
    require(Calc.mod(ci(ci.period), filterValue) != BigInt(0))

    val totalPositions = ci.period + BigInt(1)

    val survivors = CycleIntegralFilterProperties.survivorValues(
      ci, filterValue, BigInt(0), totalPositions
    )

    assert(assertCIModDivFormula(ci, ci.period))
    assert(ci(ci.period) == ci(BigInt(0)) + ci.sum)

    assert(assertFirstSurvivorIsHead(ci, filterValue, BigInt(0), totalPositions))
    assert(survivors.head == ci(BigInt(0)))

    assert(assertLastSurvivorIsLastScanned(ci, filterValue, BigInt(0), totalPositions))
    assert(survivors.last == ci(ci.period))

    survivors.last - survivors.head == ci.sum
  }.holds

  private def assertAddZeroModValuePreservesMod(
    value: BigInt,
    zeroModValue: BigInt,
    m: BigInt
  ): Boolean = {
    require(m > 0)
    require(Calc.mod(zeroModValue, m) == BigInt(0))

    assert(ModOperations.modAdd(value, m, zeroModValue))
    assert(Calc.mod(value + zeroModValue, m) ==
      Calc.mod(Calc.mod(value, m) + Calc.mod(zeroModValue, m), m))
    assert(Calc.mod(value + zeroModValue, m) ==
      Calc.mod(Calc.mod(value, m), m))
    assert(ModIdempotence.modIdempotence(value, m))
    assert(Calc.mod(Calc.mod(value, m), m) == Calc.mod(value, m))

    Calc.mod(value + zeroModValue, m) == Calc.mod(value, m)
  }.holds

  /**
   * The residue modulo `m` repeats with period `ci.size` when the
   * cycle sum is a multiple of `m`:
   *
   *   mod(ci(pos), m) == mod(ci(pos % ci.size), m)
   *
   * Corollary: if mod(ci(k), m) != 0 for all k in [0, ci.size],
   * then no position is ever a multiple of m.
   *
   * Proof decreases `pos` by one full cycle at a time via
   * ci(k + ci.size) == ci(k) + ci.sum. Since ci.sum is 0 mod m,
   * adding one full cycle does not change the residue.
   */
  def assertModIsPeriodic(
    ci: CycleIntegral,
    m: BigInt,
    pos: BigInt
  ): Boolean = {
    require(ci.period > 0)
    require(m > 0)
    require(pos >= 0)
    require(Calc.mod(ci.sum, m) == BigInt(0))
    require(ci(ci.period) - ci(BigInt(0)) == ci.sum)
    decreases(pos)

    val size = ci.period
    val r = Calc.mod(pos, size)

    if (pos < size) {
      assert(ModSmallDividend.modSmallDividend(pos, size))
      assert(r == pos)
      assert(Calc.mod(ci(pos), m) == Calc.mod(ci(r), m))
    } else {
      val previous = pos - size
      val previousR = Calc.mod(previous, size)

      assert(previous >= BigInt(0))
      assert(previous < pos)
      assert(previous + size == pos)
      assert(AdditionAndMultiplication.APlusBSameModPlusDiv(previous, size))
      assert(Calc.mod(previous + size, size) == Calc.mod(previous, size))
      assert(r == previousR)

      assert(assertModIsPeriodic(ci, m, previous))
      assert(Calc.mod(ci(previous), m) == Calc.mod(ci(previousR), m))

      assert(CycleIntegralFilterProperties.assertCIShiftEqualsSum(ci, previous))
      assert(ci(previous + size) - ci(previous) == ci.sum)
      assert(ci(pos) - ci(previous) == ci.sum)
      assert(ci(pos) == ci(previous) + ci.sum)

      assert(assertAddZeroModValuePreservesMod(ci(previous), ci.sum, m))
      assert(Calc.mod(ci(previous) + ci.sum, m) == Calc.mod(ci(previous), m))
      assert(Calc.mod(ci(pos), m) == Calc.mod(ci(previous), m))
      assert(Calc.mod(ci(pos), m) == Calc.mod(ci(previousR), m))
      assert(Calc.mod(ci(pos), m) == Calc.mod(ci(r), m))
    }

    Calc.mod(ci(pos), m) == Calc.mod(ci(r), m)
  }.holds

  /* ---- CYCLE-PERIOD SHIFT ---- */

  /**
   * After one full cycle from any position, the integral advances by
   * the cycle sum. Pure gap arithmetic — no filter dependency.
   *
   *   ci(k + ci.size) - ci(k) == ci.sum
   */
  def assertPeriodicShift(
    ci: CycleIntegral,
    k: BigInt
  ): Boolean = {
    require(ci.period > 0)
    require(k >= 0)
    require(ci(ci.period) - ci(BigInt(0)) == ci.sum)
    CycleIntegralFilterProperties.assertCIShiftEqualsSum(ci, k)
  }.holds

  /**
   * Shifting by one full cycle adds the sum of all cycle values.
   *
   *   ci(pos + ci.size) == ci(pos) + ci.sum
   *
   * This is the termination bound: within one cycle period, a survivor
   * is always found because the integral advances by a fixed amount.
   *
   * [Verified] in `CycleIntegralFilterProperties.assertCIShiftEqualsSum`.
   */
  def assertFullCycleShift(
    ci: CycleIntegral,
    pos: BigInt
  ): Boolean = {
    require(ci.period > 0)
    require(pos >= 0)
    require(ci(ci.period) - ci(BigInt(0)) == ci.sum)
    CycleIntegralFilterProperties.assertCIShiftEqualsSum(ci, pos)
  }.holds

  /**
   * After `m` full cycles, the integral advances by `m * ci.sum`.
   *
   *   ci(pos + ci.size * m) == ci(pos) + m * ci.sum
   *
   * Proved by induction on `m` using `assertFullCycleShift`.
   */
  def assertMultiCycleShift(
    ci: CycleIntegral,
    pos: BigInt,
    m: BigInt
  ): Boolean = {
    require(ci.period > 0)
    require(pos >= 0)
    require(m >= 0)
    require(ci(ci.period) - ci(BigInt(0)) == ci.sum)
    decreases(m)

    val period = ci.period
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

}
