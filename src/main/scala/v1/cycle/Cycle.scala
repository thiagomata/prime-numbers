package v1.cycle

import stainless.proof.check
import v1.Calc

case class Cycle(values: stainless.collection.List[BigInt]) {
  require(values.size > 0)

  def apply(value: BigInt): BigInt = {
    require(value >= 0)
    val index = Calc.mod(value, values.size)
    check(index >= 0)
    check(index < values.size)
    values(index)
  }
  
  def size: BigInt = values.size
}