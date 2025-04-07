package v1.cycle.integral

import stainless.lang.decreases
import v1.cycle.Cycle

import scala.annotation.tailrec

case class CycleIntegral(
  initialValue: BigInt,
  cycle: Cycle
) {

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

  def sum(): BigInt = cycle.sum()
}
