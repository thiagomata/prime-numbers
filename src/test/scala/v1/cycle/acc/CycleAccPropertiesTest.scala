package v1.cycle.acc

import org.scalatest.funsuite.AnyFunSuiteLike
import v1.cycle.Cycle
import v1.tests.ArrayUtils.createListFromInt

class CycleAccPropertiesTest extends AnyFunSuiteLike {
  val primeCycles: List[Cycle] = List(
    Cycle(createListFromInt(Array(3))),
    Cycle(createListFromInt(Array(19))),
    Cycle(createListFromInt(Array(3, 5, 7))),
    Cycle(createListFromInt(Array(3, 5, 7, 11, 13, 17))),
  )

  val oddCycles: List[Cycle] = List(
    Cycle(createListFromInt(Array(3))),
    Cycle(createListFromInt(Array(3, 5, 7))),
    Cycle(createListFromInt(Array(3, 15, 17))),
  )

  val evenCycles: List[Cycle] = List(
    Cycle(createListFromInt(Array(2))),
    Cycle(createListFromInt(Array(2, 4, 8))),
    Cycle(createListFromInt(Array(10, 20, 30))),
  )

  val allCycles: List[Cycle] = primeCycles ++ oddCycles ++ evenCycles

  test("assertSimplifiedDiffValuesMatchCycle should hold for any cycle") {
    assert(allCycles.forall(
      cycle => {
        val cycleAcc = CycleAcc(1000, cycle)
        (BigInt(1) until cycleAcc.cycle.values.size).forall { position =>
          cycleAcc.assertSimplifiedDiffValuesMatchCycle(position)
        }
      }
    ))
  }
}
