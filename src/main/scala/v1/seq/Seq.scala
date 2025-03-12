package v1.seq

import stainless.lang.*
import v1.Calc

case class Seq (
  previous: stainless.collection.List[BigInt],
  loop: stainless.collection.List[BigInt]
) {
  require(loop.size > 0)
  
  def apply(index: BigInt): BigInt = {
    require(index >= 0)
    decreases(index)

    if (index < previous.size) {
      previous.apply(index)
    } else {
      val value = index - previous.size
      val mod = Calc.mod(value, loop.size)
      val loopValue = loop.apply(mod)
      if index > 0 then loopValue + this.apply(index - 1) else loopValue
//      loopValue + this.apply(index - 1)
    }
  }
}