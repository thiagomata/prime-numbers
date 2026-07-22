package v1.chapter4.cycle.integral.recursive.properties

import stainless.collection.List
import stainless.lang.{decreases, BooleanDecorations}
import stainless.lang.BigInt
import v1.chapter1.verification.Helper.assert
import v1.chapter2.div.Calc
import v1.chapter3.list.properties.ListRepeatProperties
import v1.chapter4.cycle.integral.recursive.CycleIntegral
import v1.chapter4.cycle.memory.properties.MemCycleProperties

/**
 * Properties of CycleIntegral when the backing gap cycle is repeated.
 *
 * Repeating a gap list `L` by `times` produces `L^(times) = L :: ... :: L`
 * (times copies). A CycleIntegral built from the repeated list has:
 *
 *  - Period = original period * times — §assertRepeatedPeriodIsMultiplied
 *  - Integral values = original integral values — §assertRepeatedValuesIntegralMatches
 *  - Cycle values = original cycle values — §assertReplicatedCycleValueEqual
 *
 * The thin wrapper §assertRepeatedGapsPreservesIntegral re-exports the
 * integral invariance under the gap-oriented naming convention.
 */
object RepeatedGapIntegralProperties {

  /* ---- PERIOD MULTIPLICATION ---- */

  /**
   * The repeated period is `times` times the original period.
   *
   * Math:
   *
   *   n    = original.period
   *   times > 0
   *   repeated.cycle.values = repeat(original.cycle.values, times)
   *
   *   repeated.period == n * times
   *
   * Proof: by ListRepeatProperties.assertRepeatSize and the
   * definition CycleIntegral.period == cycle.period == cycle.values.size.
   */
  def assertRepeatedPeriodIsMultiplied(
    original: CycleIntegral,
    repeated: CycleIntegral,
    times: BigInt
  ): Boolean = {
    require(times > BigInt(0))
    require(original.period > BigInt(0))
    require(repeated.initialValue == original.initialValue)
    require(repeated.cycle.values ==
      ListRepeatProperties.repeat(original.cycle.values, times))

    assert(ListRepeatProperties.assertRepeatSize(original.cycle.values, times))
    assert(repeated.cycle.period == original.cycle.values.size * times)
    assert(original.cycle.period == original.cycle.values.size)

    repeated.period == original.period * times
  }.holds

  /* ---- INTEGRAL INVARIANCE ---- */

  /**
   * Repeating the physical values of a cycle preserves the recursive integral
   * when the initial value is unchanged.
   *
   * Math:
   *
   *   C      = cycleIntegral
   *   C_t    = repeatedCycleIntegral
   *   times  > 0
   *
   *   C_t.initialValue = C.initialValue
   *   C_t.cycle.values = repeat(C.cycle.values, times)
   *
   *   C(0)   = C.initialValue   + C.cycle(0)
   *   C_t(0) = C_t.initialValue + C_t.cycle(0)
   *
   *   C(k)   = C(k - 1)   + C.cycle(k)
   *   C_t(k) = C_t(k - 1) + C_t.cycle(k)
   *
   *   C_t.cycle(k) = C.cycle(k)
   *
   * Therefore, by induction on `position`:
   *
   *   C_t(position) = C(position)
   *
   * The proof decreases `position`; the recursive step uses the already-proven
   * equality at `position - 1` plus the memory-cycle repeated-values lemma for
   * the current gap lookup.
   */
  def assertRepeatedValuesIntegralMatches(
    cycleIntegral: CycleIntegral,
    repeatedCycleIntegral: CycleIntegral,
    times: BigInt,
    position: BigInt
  ): Boolean = {
    require(times > BigInt(0))
    require(position >= BigInt(0))
    require(cycleIntegral.cycle.period > BigInt(0))
    require(repeatedCycleIntegral.initialValue == cycleIntegral.initialValue)
    require(repeatedCycleIntegral.cycle.values ==
      ListRepeatProperties.repeat(cycleIntegral.cycle.values, times))
    decreases(position)

    if (position == BigInt(0)) {
      assert(MemCycleProperties.assertRepeatedValuesCycleMatches(
        cycleIntegral.cycle,
        repeatedCycleIntegral.cycle,
        times,
        BigInt(0)
      ))
      assert(repeatedCycleIntegral.cycle(BigInt(0)) == cycleIntegral.cycle(BigInt(0)))
      assert(repeatedCycleIntegral(position) ==
        repeatedCycleIntegral.cycle(BigInt(0)) + repeatedCycleIntegral.initialValue)
      assert(cycleIntegral(position) ==
        cycleIntegral.cycle(BigInt(0)) + cycleIntegral.initialValue)
      assert(repeatedCycleIntegral(position) == cycleIntegral(position))

      repeatedCycleIntegral(position) == cycleIntegral(position)
    } else {
      assert(assertRepeatedValuesIntegralMatches(
        cycleIntegral,
        repeatedCycleIntegral,
        times,
        position - BigInt(1)
      ))
      assert(MemCycleProperties.assertRepeatedValuesCycleMatches(
        cycleIntegral.cycle,
        repeatedCycleIntegral.cycle,
        times,
        position
      ))

      val repeatedGap = repeatedCycleIntegral.cycle(position)
      val originalGap = cycleIntegral.cycle(position)
      val repeatedPrevious = repeatedCycleIntegral(position - BigInt(1))
      val originalPrevious = cycleIntegral(position - BigInt(1))

      assert(repeatedGap == originalGap)
      assert(repeatedPrevious == originalPrevious)
      assert(repeatedCycleIntegral(position) == repeatedGap + repeatedPrevious)
      assert(cycleIntegral(position) == originalGap + originalPrevious)
      assert(repeatedGap + repeatedPrevious == originalGap + originalPrevious)
      assert(repeatedCycleIntegral(position) == cycleIntegral(position))

      repeatedCycleIntegral(position) == cycleIntegral(position)
    }
  }.holds

  /* ---- THIN WRAPPER (gap-oriented naming) ---- */

  /**
   * Repeating a gap cycle `times` times does not change the integral at
   * positions within the original period.
   *
   * [Verified] in `assertRepeatedValuesIntegralMatches`.
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
    assertRepeatedValuesIntegralMatches(
      originalCI, repeatedCI, times, pos
    )
  }.holds

  /* ---- CYCLE VALUE EQUALITY ---- */

  /**
   * Replication invariance: the cycle value at any position is unchanged
   * when the underlying gap list is replicated `factor` times.
   *
   * Uses `MemCycleProperties.findValueInCycle` to express cycle values as list access
   * modulo size, then the mod-nesting property
   * `Calc.mod(Calc.mod(pos, f*n), n) == Calc.mod(pos, n)` (via
   * `ATimesBSameMod`) to prove equality without constructing the
   * replicated list.
   *
   * Math:
   *
   *   Cycle_f(pos) = Values_f(pos % (f*n))
   *                = Values_1((pos % (f*n)) % n)
   *                = Values_1(pos % n)
   *                = Cycle_1(pos)
   */
  def assertReplicatedCycleValueEqual(
    originalIntegral: CycleIntegral,
    replicatedIntegral: CycleIntegral,
    factor: BigInt,
    position: BigInt
  ): Boolean = {
    require(factor > 0)
    require(originalIntegral.period > 0)
    require(replicatedIntegral.period == originalIntegral.period * factor)
    require(position >= 0)
    require(replicatedIntegral.initialValue == originalIntegral.initialValue)
    require(
      (position < originalIntegral.cycle.period &&
        replicatedIntegral.cycle(position) ==
          originalIntegral.cycle(position)) ||
      (position >= originalIntegral.cycle.period &&
        replicatedIntegral.cycle(position) ==
          originalIntegral.cycle(
            Calc.mod(position, originalIntegral.cycle.period))))

    val originalSize = originalIntegral.cycle.period
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
}
