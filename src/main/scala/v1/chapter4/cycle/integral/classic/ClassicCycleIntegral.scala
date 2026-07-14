package v1.chapter4.cycle.integral.classic

import v1.chapter4.cycle.integral.recursive.CycleIntegral
import v1.chapter4.cycle.memory.MemCycle

/**
 * Compatibility surface for the original cycle-integral name.
 *
 * The canonical implementation is CycleIntegral. This wrapper remains so older
 * proof notes and tests can keep compiling while the codebase converges on the
 * canonical name.
 */
case class ClassicCycleIntegral(
  initialValue: BigInt,
  cycle: MemCycle
) {

  def toCycleIntegral: CycleIntegral =
    CycleIntegral(initialValue, cycle)

  /**
   * The integral of the cycle is defined as
   *    - the first element is the first element of the cycle plus the initial value
   *    - the rest of the elements are the sum of the previous element and the current element
   *
   * in other words:
   *
   * apply(0) = cycle(0) + initialValue
   * apply(n) = apply(n - 1) + cycle(n)
   *
   * @param position BigInt the position of the element in the cycle
   * @return BigInt the element at the given position
   */
  def apply(position: BigInt): BigInt = {
    require(position >= 0)
    toCycleIntegral(position)
  }

  def period: BigInt =
    toCycleIntegral.period

  def sum: BigInt =
    toCycleIntegral.sum
}
