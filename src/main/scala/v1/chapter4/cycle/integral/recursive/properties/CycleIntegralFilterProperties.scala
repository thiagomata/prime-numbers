package v1.chapter4.cycle.integral.recursive.properties

import stainless.collection.List
import stainless.lang.*
import v1.chapter1.verification.Helper.assert
import v1.chapter2.div.Calc
import v1.chapter2.div.properties.ModOperations
import v1.chapter3.list.ListBoundUtils
import v1.chapter4.cycle.integral.recursive.CycleIntegral
import v1.chapter4.cycle.integral.recursive.properties.CycleIntegralProperties
import v1.chapter4.cycle.memory.properties.MemCycleProperties

object CycleIntegralFilterProperties {

  /**
   * Telescoping recurrence for CycleIntegral differences.
   *
   * The difference between any two positions decomposes into the cycle value
   * at the upper position plus the difference of the remaining span.
   *
   * @param cycleIntegral the cycle integral
   * @param fromPosition  starting position, `fromPosition >= 0`
   * @param toPosition    ending position, `toPosition > fromPosition`
   * @return the recurrence identity
   *
   * ```math
   * \begin{aligned}
   * CI(to) - CI(from) = Cycle(to) + \big(CI(to - 1) - CI(from)\big)
   * \end{aligned}
   * ```
   */
  def assertCITelescopeRecurrence(
    cycleIntegral: CycleIntegral,
    fromPosition: BigInt,
    toPosition: BigInt
  ): Boolean = {
    require(fromPosition >= 0)
    require(toPosition > fromPosition)
    decreases(toPosition - fromPosition)
    if (toPosition == fromPosition + 1) {
      CycleIntegralProperties.assertDiffEqualsCycleValue(
        cycleIntegral, fromPosition)
    } else {
      assertCITelescopeRecurrence(
        cycleIntegral, fromPosition, toPosition - 1)
      CycleIntegralProperties.assertDiffEqualsCycleValue(
        cycleIntegral, toPosition - 1)
    }
    cycleIntegral(toPosition) - cycleIntegral(fromPosition) ==
      cycleIntegral.cycle(toPosition) +
        (cycleIntegral(toPosition - 1) - cycleIntegral(fromPosition))
  }.holds

  /**
   * Modulo periodicity at position zero when the full-cycle sum is a
   * multiple of the filter value.
   *
   * If adding one full cycle sum does not change the remainder modulo
   * `filterValue` (because the sum itself is a multiple), then the residue
   * at position `size` equals the residue at position `0`.
   *
   * @param cycleIntegral the cycle integral
   * @param filterValue   the filter value, `filterValue > 0`
   * @return preserved-modulo equality
   *
   * ```math
   * \begin{aligned}
   * CI(size) - CI(0) &= \sum\text{Cycle} \\
   * \sum\text{Cycle} \bmod v &= 0 \;\Longrightarrow\;
   * CI(size) \bmod v = CI(0) \bmod v
   * \end{aligned}
   * ```
   */
  def assertModPeriodicWithMultipleSum(
    cycleIntegral: CycleIntegral,
    filterValue: BigInt
  ): Boolean = {
    require(cycleIntegral.size > 0)
    require(filterValue > 0)
    require(cycleIntegral(0) >= 0)
    require(cycleIntegral(cycleIntegral.size) - cycleIntegral(0) ==
      cycleIntegral.sum)
    require(Calc.mod(cycleIntegral.sum, filterValue) == BigInt(0))
    require(Calc.mod(cycleIntegral(0), filterValue) != BigInt(0))
    assert(cycleIntegral(cycleIntegral.size) ==
      cycleIntegral(0) + cycleIntegral.sum)
    ModOperations.modZeroPlusC(
      cycleIntegral.sum, filterValue, cycleIntegral(0))
    Calc.mod(cycleIntegral(cycleIntegral.size), filterValue) ==
      Calc.mod(cycleIntegral(0), filterValue)
  }.holds

  /**
   * Bounded forward search for the next survivor position.
   *
   * Starting from `fromPosition`, scans at most `bound` steps forward
   * and returns the first position whose CycleIntegral value is not a
   * multiple of `filterValue`. If no survivor is found within the bound,
   * returns `fromPosition` itself.
   *
   * @param cycleIntegral the cycle integral
   * @param filterValue   the filter value, `filterValue > 0`
   * @param fromPosition  starting position of the search
   * @param bound         maximum number of steps to scan forward
   * @return the next survivor position, at least `fromPosition`
   */
  def findNextSurvivor(
    cycleIntegral: CycleIntegral,
    filterValue: BigInt,
    fromPosition: BigInt,
    bound: BigInt
  ): BigInt = {
    require(fromPosition >= 0)
    require(bound >= 0)
    require(filterValue > 0)
    decreases(bound)
    if (bound == 0) fromPosition
    else if (Calc.mod(cycleIntegral(fromPosition + 1), filterValue) !=
      BigInt(0)) fromPosition + 1
    else findNextSurvivor(
      cycleIntegral, filterValue, fromPosition + 1, bound - 1)
  }.ensuring(result => result >= fromPosition)

  /**
   * Full-cycle shift invariance.
   *
   * For every position, shifting by one full cycle adds exactly the
   * total sum of the cycle values.
   *
   * @param cycleIntegral the cycle integral
   * @param position      the position, `position >= 0`
   * @return the shift identity
   *
   * ```math
   * \begin{aligned}
   * CI(pos + size) - CI(pos) = \sum_{j=0}^{size-1} \text{Cycle}_j
   * \end{aligned}
   * ```
   */
  def assertCIShiftEqualsSum(
    cycleIntegral: CycleIntegral,
    position: BigInt
  ): Boolean = {
    require(cycleIntegral.size > 0)
    require(position >= 0)
    require(cycleIntegral(cycleIntegral.size) - cycleIntegral(0) ==
      cycleIntegral.sum)
    decreases(position)
    if (position == 0) true
    else {
      assertCIShiftEqualsSum(cycleIntegral, position - 1)
      assert(cycleIntegral(position - 1 + cycleIntegral.size) -
        cycleIntegral(position - 1) == cycleIntegral.sum)
      MemCycleProperties.valueMatchAfterManyLoopsInBoth(
        cycleIntegral.cycle, position, BigInt(0), BigInt(1))
      assert(cycleIntegral.cycle(position + cycleIntegral.size) ==
        cycleIntegral.cycle(position))
      CycleIntegralProperties.assertDiffEqualsCycleValue(
        cycleIntegral, position + cycleIntegral.size - 1)
      assert(cycleIntegral(position + cycleIntegral.size) ==
        cycleIntegral.cycle(position + cycleIntegral.size) +
          cycleIntegral(position + cycleIntegral.size - 1))
      assert(cycleIntegral(position + cycleIntegral.size) ==
        cycleIntegral.cycle(position) +
          cycleIntegral(position - 1 + cycleIntegral.size))
      CycleIntegralProperties.assertDiffEqualsCycleValue(
        cycleIntegral, position - 1)
      assert(cycleIntegral(position) - cycleIntegral(position - 1) ==
        cycleIntegral.cycle(position))
      assert(cycleIntegral(position - 1 + cycleIntegral.size) -
        cycleIntegral(position) ==
        (cycleIntegral(position - 1 + cycleIntegral.size) -
          cycleIntegral(position - 1)) +
          (cycleIntegral(position - 1) - cycleIntegral(position)))
      assert(cycleIntegral(position - 1 + cycleIntegral.size) -
        cycleIntegral(position) ==
        cycleIntegral.sum - cycleIntegral.cycle(position))
      assert(cycleIntegral(position + cycleIntegral.size) -
        cycleIntegral(position) ==
        cycleIntegral.cycle(position) +
          (cycleIntegral(position - 1 + cycleIntegral.size) -
            cycleIntegral(position)))
      assert(cycleIntegral(position + cycleIntegral.size) -
        cycleIntegral(position) ==
        cycleIntegral.cycle(position) +
          cycleIntegral.sum - cycleIntegral.cycle(position))
    }
    cycleIntegral(position + cycleIntegral.size) -
      cycleIntegral(position) == cycleIntegral.sum
  }.holds

  /**
   * Recursive construction of the merged gap list.
   *
   * Starting from a survivor position, repeatedly finds the next survivor
   * and emits the gap (CI difference) between them.
   *
   * @param cycleIntegral the cycle integral
   * @param filterValue   the filter value
   * @param fromPosition  current survivor position
   * @param count         number of gaps to produce
   * @return the list of merged gaps
   */
  def mergedGaps(
    cycleIntegral: CycleIntegral,
    filterValue: BigInt,
    fromPosition: BigInt,
    count: BigInt
  ): List[BigInt] = {
    require(fromPosition >= 0)
    require(count >= 0)
    require(filterValue > 0)
    require(cycleIntegral.size > 0)
    decreases(count)
    if (count == 0) List.empty[BigInt]
    else {
      val nextSurvivor = findNextSurvivor(
        cycleIntegral, filterValue, fromPosition, cycleIntegral.size)
      assert(nextSurvivor >= fromPosition)
      assert(nextSurvivor >= 0)
      val gap = cycleIntegral(nextSurvivor) -
        cycleIntegral(fromPosition)
      gap :: mergedGaps(
        cycleIntegral, filterValue, nextSurvivor, count - 1)
    }
  }

  /**
   * Predicate: all positions strictly between `fromPosition` and
   * `toPosition` have CycleIntegral values that are multiples of
   * `filterValue`.
   *
   * @param cycleIntegral the cycle integral
   * @param filterValue   the filter value
   * @param fromPosition  lower bound (exclusive)
   * @param toPosition    upper bound (exclusive)
   * @return true iff every position in `(from, to)` is a multiple
   */
  def allMultiplesBetween(
    cycleIntegral: CycleIntegral,
    filterValue: BigInt,
    fromPosition: BigInt,
    toPosition: BigInt
  ): Boolean = {
    require(toPosition > fromPosition)
    require(fromPosition >= 0)
    require(filterValue > 0)
    decreases(toPosition - fromPosition)
    if (toPosition == fromPosition + 1) true
    else Calc.mod(cycleIntegral(fromPosition + 1), filterValue) ==
      BigInt(0) &&
      allMultiplesBetween(
        cycleIntegral, filterValue, fromPosition + 1, toPosition)
  }

  /**
   * Merged-gap positivity.
   *
   * When two positions are both survivors and every intermediate position
   * is a multiple, the difference between them is positive (the CI is
   * strictly increasing).
   *
   * @param cycleIntegral the cycle integral
   * @param filterValue   the filter value
   * @param fromPosition  the first survivor
   * @param toPosition    the next survivor (after all skipped multiples)
   * @return positivity of the merged gap
   */
  def assertMergedGapIsCITelescope(
    cycleIntegral: CycleIntegral,
    filterValue: BigInt,
    fromPosition: BigInt,
    toPosition: BigInt
  ): Boolean = {
    require(fromPosition >= 0)
    require(toPosition > fromPosition)
    require(filterValue > 0)
    require(Calc.mod(cycleIntegral(fromPosition), filterValue) != BigInt(0))
    require(Calc.mod(cycleIntegral(toPosition), filterValue) != BigInt(0))
    require(allMultiplesBetween(
      cycleIntegral, filterValue, fromPosition, toPosition))
    require(cycleIntegral.initialValue >= BigInt(0))
    require(ListBoundUtils.allGreaterThan(
      cycleIntegral.cycle.values, BigInt(0)))
    CycleIntegralProperties.assertCycleIntegralIncreasing(
      cycleIntegral, fromPosition, toPosition)
    cycleIntegral(toPosition) - cycleIntegral(fromPosition) > BigInt(0)
  }.holds

  /**
   * Collects all survivor values within a bounded range.
   *
   * Scans `count` consecutive positions starting at `startPosition`,
   * retaining only those CycleIntegral values that are **not** multiples
   * of `filterValue`.
   *
   * @param cycleIntegral the cycle integral
   * @param filterValue   the filter value
   * @param startPosition first position to scan
   * @param count         number of positions to examine
   * @return the list of survivor values in order
   */
  def survivorValues(
    cycleIntegral: CycleIntegral,
    filterValue: BigInt,
    startPosition: BigInt,
    count: BigInt
  ): List[BigInt] = {
    require(startPosition >= 0)
    require(count >= 0)
    require(filterValue > 0)
    decreases(count)
    if (count == 0) List.empty[BigInt]
    else if (Calc.mod(cycleIntegral(startPosition), filterValue) !=
      BigInt(0))
      cycleIntegral(startPosition) ::
        survivorValues(cycleIntegral, filterValue,
          startPosition + 1, count - 1)
    else
      survivorValues(cycleIntegral, filterValue,
        startPosition + 1, count - 1)
  }

  /**
   * Computes pairwise gaps between consecutive values.
   *
   * Given an ordered list of survivor values, returns the list of
   * differences between each consecutive pair.
   *
   * @param survivorValues non-empty list of survivor values
   * @return the list of gaps, one fewer element than input
   */
  def gapsFromValues(valuesList: List[BigInt]): List[BigInt] = {
    require(!valuesList.isEmpty)
    decreases(valuesList.size)
    if (valuesList.tail.isEmpty) List.empty[BigInt]
    else (valuesList.tail.head - valuesList.head) ::
      gapsFromValues(valuesList.tail)
  }

  /**
   * Correctness of `gapsFromValues`.
   *
   * The gap at index `index` equals the difference between consecutive
   * elements of the source list.
   *
   * ```math
   * \text{gapsFromValues}(S)_i = S_{i+1} - S_i
   * ```
   *
   * @param sourceList  the list of values
   * @param index       the gap index, `0 <= index < sourceList.size - 1`
   * @return the identity `gaps(sourceList)[index] == sourceList[index+1] - sourceList[index]`
   */
  def assertGapsFromValuesAtIndex(
    sourceList: List[BigInt],
    index: BigInt
  ): Boolean = {
    require(!sourceList.isEmpty)
    require(index >= 0)
    require(index + 1 < sourceList.size)
    decreases(index)
    if (index == 0) {
      assert(gapsFromValues(sourceList).head ==
        sourceList.tail.head - sourceList.head)
    } else {
      assertGapsFromValuesAtIndex(sourceList.tail, index - 1)
    }
    gapsFromValues(sourceList)(index) ==
      sourceList(index + 1) - sourceList(index)
  }.holds

  /**
   * Predicate: the new cycle's gaps match the differences between
   * consecutive survivor values, for all positions `0` through `maxIndex`.
   *
   * ```math
   * \begin{aligned}
   * \forall\, i \in [0, maxIndex]:\;
   * \text{FilteredCycle}_i = S_{i+1} - S_i
   * \end{aligned}
   * ```
   * where `S` is the list of survivor values from the old cycle integral.
   *
   * @param filteredIntegral  the new (filtered) cycle integral
   * @param survivorValues    survivor values from the old cycle integral
   * @param maxIndex          the largest index to check
   * @return true iff all gaps match
   */
  def allGapsMatch(
    filteredIntegral: CycleIntegral,
    survivorList: List[BigInt],
    maxIndex: BigInt
  ): Boolean = {
    require(maxIndex >= -1)
    require(survivorList.size > maxIndex + 1)
    decreases(maxIndex + 1)
    if (maxIndex < 0) true
    else filteredIntegral.cycle(maxIndex) ==
      survivorList(maxIndex + 1) - survivorList(maxIndex) &&
      allGapsMatch(filteredIntegral, survivorList, maxIndex - 1)
  }

  /**
   * Main filter-merge theorem.
   *
   * Given a new cycle integral whose initial value equals the first
   * survivor and whose cycle values equal the differences between
   * consecutive survivors, the new integral at position `position`
   * matches the `(position + 1)`-th survivor value from the old
   * integral.
   *
   * @param filteredIntegral  the new (filtered) cycle integral
   * @param survivorList      ordered survivor values from the old integral
   * @param position          the position in the new integral
   * @return equality of the filtered integral with the survivor sequence
   *
   * ```math
   * \begin{aligned}
   * \text{CI}_\text{new}(0) &= S_0 \\
   * \forall\, i \in [0, k]:\;
   * \text{Cycle}_\text{new}(i) &= S_{i+1} - S_i \\
   * &\Longrightarrow
   * \text{CI}_\text{new}(k) = S_{k+1}
   * \end{aligned}
   * ```
   */
  def assertNewCIGeneratesFiltered(
    filteredIntegral: CycleIntegral,
    survivorList: List[BigInt],
    position: BigInt
  ): Boolean = {
    require(survivorList.size > position + 1)
    require(filteredIntegral.size > position)
    require(position >= 0)
    require(filteredIntegral.initialValue == survivorList.head)
    require(allGapsMatch(filteredIntegral, survivorList, position))
    decreases(position)
    if (position == 0) {
      assert(filteredIntegral(0) ==
        filteredIntegral.initialValue + filteredIntegral.cycle(0))
    } else {
      assert(allGapsMatch(filteredIntegral, survivorList, position - 1))
      assertNewCIGeneratesFiltered(
        filteredIntegral, survivorList, position - 1)
      assert(filteredIntegral(position - 1) ==
        survivorList(position))
      assert(filteredIntegral(position) ==
        filteredIntegral(position - 1) + filteredIntegral.cycle(position))
    }
    filteredIntegral(position) == survivorList(position + 1)
  }.holds

  def allGapsMatchBeforeMerge(
    oldIntegral: CycleIntegral,
    newIntegral: CycleIntegral,
    mergeIndex: BigInt,
    until: BigInt
  ): Boolean = {
    require(until >= -1)
    require(until < mergeIndex)
    decreases(until + 1)
    if (until < 0) true
    else newIntegral.cycle(until) == oldIntegral.cycle(until) &&
      allGapsMatchBeforeMerge(
        oldIntegral, newIntegral, mergeIndex, until - 1)
  }

  def allGapsMatchAfterMerge(
    oldIntegral: CycleIntegral,
    newIntegral: CycleIntegral,
    mergeIndex: BigInt,
    until: BigInt
  ): Boolean = {
    require(mergeIndex >= 0)
    require(until >= mergeIndex)
    require(until < newIntegral.size)
    decreases(until - mergeIndex + 1)
    if (until <= mergeIndex) true
    else newIntegral.cycle(until) ==
      oldIntegral.cycle(until + 1) &&
      allGapsMatchAfterMerge(
        oldIntegral, newIntegral, mergeIndex, until - 1)
  }

  def assertSameBeforeMerge(
    oldIntegral: CycleIntegral,
    newIntegral: CycleIntegral,
    mergeIndex: BigInt,
    position: BigInt
  ): Boolean = {
    require(mergeIndex >= 0)
    require(mergeIndex + 1 < oldIntegral.size)
    require(newIntegral.size == oldIntegral.size - 1)
    require(oldIntegral.initialValue == newIntegral.initialValue)
    require(position >= 0)
    require(position < mergeIndex)
    require(allGapsMatchBeforeMerge(
      oldIntegral, newIntegral, mergeIndex, position))
    decreases(position)
    if (position == 0) true
    else {
      assert(allGapsMatchBeforeMerge(
        oldIntegral, newIntegral, mergeIndex, position - 1))
      assertSameBeforeMerge(
        oldIntegral, newIntegral, mergeIndex, position - 1)
      assert(newIntegral(position - 1) == oldIntegral(position - 1))
      assert(newIntegral(position) ==
        newIntegral(position - 1) + newIntegral.cycle(position))
      assert(oldIntegral(position) ==
        oldIntegral(position - 1) + oldIntegral.cycle(position))
    }
    newIntegral(position) == oldIntegral(position)
  }.holds

  def assertShiftAtMerge(
    oldIntegral: CycleIntegral,
    newIntegral: CycleIntegral,
    mergeIndex: BigInt
  ): Boolean = {
    require(mergeIndex >= 0)
    require(mergeIndex + 1 < oldIntegral.size)
    require(newIntegral.size == oldIntegral.size - 1)
    require(oldIntegral.initialValue == newIntegral.initialValue)
    require(newIntegral.cycle(mergeIndex) ==
      oldIntegral.cycle(mergeIndex) +
        oldIntegral.cycle(mergeIndex + 1))
    require(allGapsMatchBeforeMerge(
      oldIntegral, newIntegral, mergeIndex, mergeIndex - 1))
    if (mergeIndex == 0) {
      assert(newIntegral(0) ==
        newIntegral.initialValue + newIntegral.cycle(0))
      assert(oldIntegral(1) ==
        oldIntegral.cycle(0) + oldIntegral.cycle(1) +
          oldIntegral.initialValue)
    } else {
      assertSameBeforeMerge(
        oldIntegral, newIntegral, mergeIndex, mergeIndex - 1)
      assert(newIntegral(mergeIndex - 1) ==
        oldIntegral(mergeIndex - 1))
      assert(newIntegral(mergeIndex) ==
        newIntegral(mergeIndex - 1) +
          newIntegral.cycle(mergeIndex))
      assert(oldIntegral(mergeIndex + 1) ==
        oldIntegral(mergeIndex) +
          oldIntegral.cycle(mergeIndex + 1))
    }
    newIntegral(mergeIndex) == oldIntegral(mergeIndex + 1)
  }.holds

  /**
   * Case: position is after the merge point.
   * All cycle values are shifted back by one, so
   * newCI(position) = oldCI(position + 1).
   */
  def assertShiftAfterMerge(
    oldIntegral: CycleIntegral,
    newIntegral: CycleIntegral,
    mergeIndex: BigInt,
    position: BigInt
  ): Boolean = {
    require(mergeIndex >= 0)
    require(mergeIndex + 1 < oldIntegral.size)
    require(newIntegral.size == oldIntegral.size - 1)
    require(oldIntegral.initialValue == newIntegral.initialValue)
    require(position > mergeIndex)
    require(position < newIntegral.size)
    require(newIntegral.cycle(position) ==
      oldIntegral.cycle(position + 1))
    require(allGapsMatchAfterMerge(
      oldIntegral, newIntegral, mergeIndex, position))
    require(allGapsMatchBeforeMerge(
      oldIntegral, newIntegral, mergeIndex, mergeIndex - 1))
    require(newIntegral.cycle(mergeIndex) ==
      oldIntegral.cycle(mergeIndex) +
        oldIntegral.cycle(mergeIndex + 1))
    decreases(position - mergeIndex)
    if (position == mergeIndex + 1) {
      assertShiftAtMerge(oldIntegral, newIntegral, mergeIndex)
      assert(newIntegral(mergeIndex) == oldIntegral(mergeIndex + 1))
      assert(newIntegral(position) ==
        newIntegral(mergeIndex) + newIntegral.cycle(position))
      assert(oldIntegral(position + 1) ==
        oldIntegral(mergeIndex + 1) +
          oldIntegral.cycle(position + 1))
    } else {
      assertShiftAfterMerge(
        oldIntegral, newIntegral, mergeIndex, position - 1)
      assert(newIntegral(position - 1) ==
        oldIntegral(position))
      assert(newIntegral(position) ==
        newIntegral(position - 1) + newIntegral.cycle(position))
      assert(oldIntegral(position + 1) ==
        oldIntegral(position) + oldIntegral.cycle(position + 1))
    }
    newIntegral(position) == oldIntegral(position + 1)
  }.holds

}
