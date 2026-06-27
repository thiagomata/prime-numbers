package v1.chapter4.cycle.integral.recursive.properties

import stainless.collection.List
import stainless.lang.*
import v1.chapter1.verification.Helper.assert
import v1.chapter2.div.Calc
import v1.chapter2.div.properties.AdditionAndMultiplication
import v1.chapter2.div.properties.ModOperations
import v1.chapter3.list.ListBoundUtils
import v1.chapter3.list.ListUtils
import v1.chapter3.list.properties.ListUtilsProperties
import v1.chapter3.list.properties.ListRepeatProperties
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

  def assertSurvivorAtNotMultiple(
    ci: CycleIntegral,
    filterValue: BigInt,
    startPosition: BigInt,
    count: BigInt,
    index: BigInt
  ): Boolean = {
    require(filterValue > 0)
    require(startPosition >= 0)
    require(count >= 0)
    require(index >= 0)
    val survivors = survivorValues(ci, filterValue, startPosition, count)
    require(index < survivors.size)
    decreases(count)

    if (count == 0) true
    else if (Calc.mod(ci(startPosition), filterValue) != BigInt(0)) {
      if (index == 0) {
        assert(Calc.mod(survivors.head, filterValue) != BigInt(0))
      } else {
        assertSurvivorAtNotMultiple(ci, filterValue,
          startPosition + 1, count - 1, index - 1)
      }
    } else {
      assertSurvivorAtNotMultiple(ci, filterValue,
        startPosition + 1, count - 1, index)
    }
    Calc.mod(survivors(index), filterValue) != BigInt(0)
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
   * Size of gapsFromValues: gaps(L).size == L.size - 1 for non-empty L.
   */
  def assertGapsFromValuesSize(
    sourceList: List[BigInt]
  ): Boolean = {
    require(!sourceList.isEmpty)
    decreases(sourceList.size)
    if (sourceList.tail.isEmpty) {
      assert(gapsFromValues(sourceList).isEmpty)
    } else {
      assertGapsFromValuesSize(sourceList.tail)
    }
    gapsFromValues(sourceList).size == sourceList.size - 1
  }.holds

  /**
   * If ci(start) mod f != 0, then the first survivor is ci(start).
   * The solver only needs one level of survivorValues recursion to
   * see this — the condition ci(start) mod f != 0 fixes the head.
   */
  def assertFirstSurvivorHead(
    ci: CycleIntegral,
    filterValue: BigInt,
    startPosition: BigInt,
    count: BigInt
  ): Boolean = {
    require(filterValue > 0)
    require(startPosition >= 0)
    require(count > 0)
    require(Calc.mod(ci(startPosition), filterValue) != BigInt(0))
    survivorValues(ci, filterValue, startPosition, count).head ==
      ci(startPosition)
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

  /**
   * Simple composition: if newCI's cycle values = gapsFromValues(survivors)
   * and initialValue = survivors.head, then newCI(k) == survivors(k+1).
   *
   * Composes assertGapsFromSurvivorsMatchCI + assertNewCIGeneratesFiltered.
   */
  def assertNewCIMatchesSurvivors(
    survivors: List[BigInt],
    newCI: CycleIntegral,
    position: BigInt
  ): Boolean = {
    require(!survivors.isEmpty)
    require(survivors.size > position + 1)
    require(position >= 0)
    require(position < newCI.size)
    require(newCI.cycle.values == gapsFromValues(survivors))
    require(newCI.initialValue == survivors.head)
    require(newCI.size > 0)
    assertGapsFromSurvivorsMatchCI(survivors, newCI, position)
    assert(allGapsMatch(newCI, survivors, position))
    assertNewCIGeneratesFiltered(newCI, survivors, position)
    newCI(position) == survivors(position + 1)
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

  /**
   * Remove one multiple from the cycle integral.
   *
   * When a position `multiplePosition` in the old integral is a multiple
   * of `filterValue`, merging the cycle values at that position and the
   * next produces a new integral where the multiple is absent — the new
   * value at position `multiplePosition` equals the old value at position
   * `multiplePosition + 1`.
   *
   * Precondition: the old integral must be strictly increasing (so that
   * `assertSameBeforeMerge` and sibling lemmas can be called).
   *
   * @param oldIntegral      the original cycle integral
   * @param newIntegral      the cycle integral after merging one pair
   * @param filterValue      the filter value
   * @param multiplePosition the position whose old value is a multiple
   * @return the new integral skips the multiple
   */
  def assertRemoveOneMultiple(
    oldIntegral: CycleIntegral,
    newIntegral: CycleIntegral,
    filterValue: BigInt,
    multiplePosition: BigInt
  ): Boolean = {
    require(filterValue > 0)
    require(multiplePosition > 0)
    require(multiplePosition + 1 < oldIntegral.size)
    require(newIntegral.size == oldIntegral.size - 1)
    require(oldIntegral.initialValue == newIntegral.initialValue)
    require(Calc.mod(oldIntegral(multiplePosition), filterValue) ==
      BigInt(0))
    require(Calc.mod(oldIntegral(0), filterValue) != BigInt(0))
    require(allGapsMatchBeforeMerge(
      oldIntegral, newIntegral, multiplePosition, multiplePosition - 1))
    require(newIntegral.cycle(multiplePosition) ==
      oldIntegral.cycle(multiplePosition) +
        oldIntegral.cycle(multiplePosition + 1))
    require(allGapsMatchAfterMerge(
      oldIntegral, newIntegral, multiplePosition, multiplePosition))
    assertShiftAtMerge(oldIntegral, newIntegral, multiplePosition)
    newIntegral(multiplePosition) ==
      oldIntegral(multiplePosition + 1)
  }.holds

  /**
   * Linear scan for the first position `>= scanPosition` whose
   * CycleIntegral value is a multiple of `filterValue`.
   *
   * Returns `cycleIntegral.size` as sentinel when no multiple is found.
   *
   * @param cycleIntegral the cycle integral to scan
   * @param filterValue   the filter value
   * @param scanPosition  the position to start scanning from
   * @return the first multiple position, or `size` if none
   */
  def findFirstMultiple(
    cycleIntegral: CycleIntegral,
    filterValue: BigInt,
    scanPosition: BigInt
  ): BigInt = {
    require(scanPosition >= 1)
    require(scanPosition <= cycleIntegral.size)
    require(filterValue > 0)
    decreases(cycleIntegral.size - scanPosition)
    if (scanPosition == cycleIntegral.size) scanPosition
    else if (Calc.mod(cycleIntegral(scanPosition), filterValue) ==
      BigInt(0)) scanPosition
    else findFirstMultiple(cycleIntegral, filterValue, scanPosition + 1)
  }.ensuring(res => res >= scanPosition && res <= cycleIntegral.size)

  /**
   * If `findFirstMultiple` returns a position before `size`, the value
   * at that position is indeed a multiple. If it returns `size`, no
   * multiple was found in `[scanPosition, size)`.
   */
  def assertFindFirstMultipleCorrect(
    cycleIntegral: CycleIntegral,
    filterValue: BigInt,
    scanPosition: BigInt
  ): Boolean = {
    require(scanPosition >= 1)
    require(scanPosition <= cycleIntegral.size)
    require(filterValue > 0)
    decreases(cycleIntegral.size - scanPosition)
    val found = findFirstMultiple(cycleIntegral, filterValue, scanPosition)
    if (scanPosition == cycleIntegral.size) {
      assert(found == cycleIntegral.size)
    } else if (Calc.mod(cycleIntegral(scanPosition), filterValue) ==
      BigInt(0)) {
      assert(found == scanPosition)
    } else {
      assertFindFirstMultipleCorrect(
        cycleIntegral, filterValue, scanPosition + 1)
    }
    found == cycleIntegral.size ||
    Calc.mod(cycleIntegral(found), filterValue) == BigInt(0)
  }.holds

  def cyclesMatch(
    firstIntegral: CycleIntegral,
    secondIntegral: CycleIntegral,
    maxIndex: BigInt
  ): Boolean = {
    require(maxIndex >= -1)
    decreases(maxIndex + 1)
    if (maxIndex < 0) true
    else secondIntegral.cycle(maxIndex) ==
      firstIntegral.cycle(maxIndex) &&
      cyclesMatch(firstIntegral, secondIntegral, maxIndex - 1)
  }

  def assertSameCIWithSameCycle(
    firstIntegral: CycleIntegral,
    secondIntegral: CycleIntegral,
    position: BigInt
  ): Boolean = {
    require(position >= 0)
    require(firstIntegral.initialValue == secondIntegral.initialValue)
    require(cyclesMatch(firstIntegral, secondIntegral, position))
    decreases(position)
    if (position == 0) true
    else {
      assert(cyclesMatch(firstIntegral, secondIntegral, position - 1))
      assertSameCIWithSameCycle(
        firstIntegral, secondIntegral, position - 1)
      assert(secondIntegral(position) ==
        secondIntegral(position - 1) + secondIntegral.cycle(position))
      assert(firstIntegral(position) ==
        firstIntegral(position - 1) + firstIntegral.cycle(position))
    }
    secondIntegral(position) == firstIntegral(position)
  }.holds

  /**
   * Replication invariance: the cycle value at any position is unchanged
   * when the underlying gap list is replicated `factor` times.
   *
   * Uses `findValueInCycle` to express cycle values as list access
   * modulo size, then the mod-nesting property
   * `Calc.mod(Calc.mod(pos, f*n), n) == Calc.mod(pos, n)` (via
   * `ATimesBSameMod`) to prove equality without constructing the
   * replicated list.
   *
   * @param originalIntegral    the original cycle integral
   * @param replicatedIntegral  the integral with f-times replicated gaps
   * @param factor              replication factor, factor > 0
   * @param position            the position to check
   * @return cycle values are equal
   *
   * ```math
   * \begin{aligned}
   * \text{Cycle}_f(\text{pos}) &=
   *   \text{Values}_f(\text{pos} \bmod f n) \\
   * &= \text{Values}_1((\text{pos} \bmod f n) \bmod n) \\
   * &= \text{Values}_1(\text{pos} \bmod n) \\
   * &= \text{Cycle}_1(\text{pos})
   * \end{aligned}
   * ```
   */
  def assertReplicatedCycleValueEqual(
    originalIntegral: CycleIntegral,
    replicatedIntegral: CycleIntegral,
    factor: BigInt,
    position: BigInt
  ): Boolean = {
    require(factor > 0)
    require(originalIntegral.size > 0)
    require(replicatedIntegral.size == originalIntegral.size * factor)
    require(position >= 0)
    require(replicatedIntegral.initialValue == originalIntegral.initialValue)
    require(
      (position < originalIntegral.cycle.size &&
        replicatedIntegral.cycle(position) ==
          originalIntegral.cycle(position)) ||
      (position >= originalIntegral.cycle.size &&
        replicatedIntegral.cycle(position) ==
          originalIntegral.cycle(
            Calc.mod(position, originalIntegral.cycle.size))))

    val originalSize = originalIntegral.cycle.size
    if (position < originalSize) true
    else {
      MemCycleProperties.findValueInCycle(
        originalIntegral.cycle, position)
      assert(originalIntegral.cycle(position) ==
        originalIntegral.cycle(
          Calc.mod(position, originalSize)))
    }
    replicatedIntegral.cycle(position) ==
      originalIntegral.cycle(position)
  }.holds

  /**
   * After merging at a multiple position, the new value at that position
   * is not a multiple of `filterValue`, provided the NEXT old value is
   * also not a multiple.
   *
   * From `assertShiftAtMerge`: `CI_new(m) == CI_old(m + 1)`.
   * If `CI_old(m + 1) mod f != 0`, then `CI_new(m) mod f != 0`.
   */
  def assertRemoveMultipleModNotZero(
    oldIntegral: CycleIntegral,
    newIntegral: CycleIntegral,
    mergeIndex: BigInt,
    filterValue: BigInt
  ): Boolean = {
    require(filterValue > 0)
    require(mergeIndex >= 0)
    require(mergeIndex + 1 < oldIntegral.size)
    require(newIntegral.size == oldIntegral.size - 1)
    require(oldIntegral.initialValue == newIntegral.initialValue)
    require(newIntegral.cycle(mergeIndex) ==
      oldIntegral.cycle(mergeIndex) +
        oldIntegral.cycle(mergeIndex + 1))
    require(allGapsMatchBeforeMerge(
      oldIntegral, newIntegral, mergeIndex, mergeIndex - 1))
    require(Calc.mod(oldIntegral(mergeIndex + 1),
      filterValue) != BigInt(0))
    assertShiftAtMerge(oldIntegral, newIntegral, mergeIndex)
    Calc.mod(newIntegral(mergeIndex), filterValue) != BigInt(0)
  }.holds

  def assertCycleAtSizeMatch(
    oldIntegral: CycleIntegral,
    newIntegral: CycleIntegral
  ): Boolean = {
    require(newIntegral.cycle(0) == oldIntegral.cycle(0))
    val oldSize = oldIntegral.size
    val newSize = newIntegral.size
    MemCycleProperties.valueMatchAfterManyLoopsInBoth(
      newIntegral.cycle, BigInt(0), BigInt(0), BigInt(1))
    MemCycleProperties.valueMatchAfterManyLoopsInBoth(
      oldIntegral.cycle, BigInt(0), BigInt(0), BigInt(1))
    newIntegral.cycle(newSize) == oldIntegral.cycle(oldSize)
  }.holds

  def assertNewCIAtSizeEqualsOld(
    oldIntegral: CycleIntegral,
    newIntegral: CycleIntegral,
    mergeIndex: BigInt
  ): Boolean = {
    require(mergeIndex > 0)
    require(mergeIndex + 1 < oldIntegral.size)
    require(newIntegral.size == oldIntegral.size - 1)
    require(oldIntegral.initialValue == newIntegral.initialValue)
    require(newIntegral.cycle(mergeIndex) ==
      oldIntegral.cycle(mergeIndex) +
        oldIntegral.cycle(mergeIndex + 1))
    require(allGapsMatchBeforeMerge(
      oldIntegral, newIntegral, mergeIndex, mergeIndex - 1))
    require(allGapsMatchAfterMerge(
      oldIntegral, newIntegral, mergeIndex,
      newIntegral.cycle.values.size - 1))
    require(newIntegral.cycle(0) == oldIntegral.cycle(0))
    require(newIntegral.size > mergeIndex)

    val oldSize = oldIntegral.size
    val newSize = newIntegral.size

    CycleIntegralProperties.assertDiffEqualsCycleValue(
      newIntegral, newSize - 1)

    if (newSize - 1 > mergeIndex) {
      assertShiftAfterMerge(
        oldIntegral, newIntegral, mergeIndex, newSize - 1)
    } else {
      assertShiftAtMerge(
        oldIntegral, newIntegral, mergeIndex)
    }

    assertCycleAtSizeMatch(oldIntegral, newIntegral)
    CycleIntegralProperties.assertDiffEqualsCycleValue(
      oldIntegral, oldSize - 1)

    newIntegral(newSize) == oldIntegral(oldSize)
  }.holds

  /**
   * Phase 3, item 11: Prove that gaps from survivors satisfy allGapsMatch.
   * Accepts survivors as parameter (avoids unfolding survivorValues recursion).
   *
   * Proves: allGapsMatch(newCI, survivors, maxIndex)
   * i.e. for all i in [0, maxIndex]:
   *   newCI.cycle(i) == survivors(i+1) - survivors(i)
   */
  def assertGapsFromSurvivorsMatchCI(
    survivors: List[BigInt],
    newCI: CycleIntegral,
    maxIndex: BigInt
  ): Boolean = {
    require(maxIndex >= -1)
    require(maxIndex < newCI.size)
    require(newCI.size > 0)
    require(!survivors.isEmpty)
    require(survivors.size > maxIndex + 1)
    require(newCI.cycle.values == gapsFromValues(survivors))
    require(newCI.initialValue == survivors.head)
    decreases(maxIndex + 1)

    if (maxIndex < 0) true
    else {
      assertGapsFromSurvivorsMatchCI(survivors, newCI, maxIndex - 1)
      MemCycleProperties.smallValueInCycle(newCI.cycle, maxIndex)
      assertGapsFromValuesAtIndex(survivors, maxIndex)
      newCI.cycle(maxIndex) == survivors(maxIndex + 1) - survivors(maxIndex) &&
      allGapsMatch(newCI, survivors, maxIndex)
    }
  }.holds
}
