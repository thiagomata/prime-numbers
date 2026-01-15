package v1.cycle.integral.recursive

import stainless.lang.decreases
import v1.cycle.memory.MemCycle

case class CycleIntegral(
  initialValue: BigInt,
  cycle: MemCycle
) {

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
    decreases(position)

    if (position == 0 ) {
      cycle(0) + initialValue
    } else {
      cycle(position) + apply(position - 1)
    }
  }

  def size: BigInt = cycle.size

  def sum: BigInt = cycle.sum()
}
