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

    @tailrec
    def loop(accValue: BigInt, currentPos: BigInt): BigInt = {
      require(currentPos >= 0)
      decreases(currentPos)

      val currentValue = cycle(currentPos) + accValue
      if (currentPos == 0) then currentValue else loop(currentValue, currentPos - 1)
    }
    loop(initialValue, position)
  }

  def size: BigInt = cycle.size

  def sum(): BigInt = cycle.sum()
}
