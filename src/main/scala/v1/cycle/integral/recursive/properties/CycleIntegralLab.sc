import v1.cycle.integral.recursive.CycleIntegral
import v1.cycle.integral.recursive.properties.CycleIntegralProperties
import v1.cycle.memory.MemCycle
import v1.cycle.memory.properties.CycleCheckMod
import v1.list.ListBuilder.createList

val cycle = CycleIntegral(
  BigInt(1000),
  MemCycle(createList(Array(BigInt(1),BigInt(10),BigInt(100))))
)

cycle(BigInt(0))
cycle(BigInt(1))
cycle(BigInt(2))
cycle(BigInt(3))
cycle(BigInt(4))
cycle(BigInt(5))

cycle(3) - cycle(0) == cycle.sum

CycleIntegralProperties.assertCycleIntegralEqualsSumFirstPosition(cycle)
