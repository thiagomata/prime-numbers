import v1.cycle.Cycle
import v1.cycle.properties.CycleCheckMod
import v1.list.ListBuilder.createList

val cycle = Cycle(
  values = createList(Array(BigInt(7),BigInt(14),BigInt(21)))
)

cycle(BigInt(0))
cycle(BigInt(1))
cycle(BigInt(2))
cycle(BigInt(3))
cycle(BigInt(4))
cycle(BigInt(5))

val c7 = cycle.checkMod(7)
c7.evaluated(7)
c7.allModValuesAreZero(7)
c7.modIsZeroForAllValues

val c2 = c7.checkMod(2)
c2.evaluated(2)
c2.allModValuesAreZero(2)
c2.someModValuesAreZero(2)
c2.modIsZeroForSomeValues
c2.modIsZeroForAllValues
