package v1.seq

import stainless.lang.*
import v1.Calc
import v1.cycle.memory.MemCycle

case class Seq (
  previous: stainless.collection.List[BigInt],
  loop: MemCycle
) {
  require(loop.size > 0)
  
  def apply(index: BigInt): BigInt = {
    require(index >= 0)
    decreases(index)

    if (index < previous.size) {
      previous.apply(index)
    } else {
      val loopIndex = index - previous.size
      val loopValue = loop(loopIndex)
      if index > 0 then loopValue + this.apply(index - 1) else loopValue
    }
  }
}