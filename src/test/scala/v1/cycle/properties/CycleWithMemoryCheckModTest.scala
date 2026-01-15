package v1.cycle.properties

import org.scalatest.flatspec.*
import org.scalatest.matchers.should.*
import v1.cycle.memory.MemCycle
import v1.cycle.memory.properties.CycleCheckMod
import v1.tests.ArrayUtils.createListFromInt

import scala.BigInt

class CycleWithMemoryCheckModTest extends FlatSpec with Matchers {

  val primeCycles: List[MemCycle] = List(
    MemCycle(createListFromInt(Array(3))),
    MemCycle(createListFromInt(Array(19))),
    MemCycle(createListFromInt(Array(3,5,7))),
    MemCycle(createListFromInt(Array(3,5,7,11,13,17))),
  )

  val oddCycles: List[MemCycle] = List(
    MemCycle(createListFromInt(Array(3))),
    MemCycle(createListFromInt(Array(3,5,7))),
    MemCycle(createListFromInt(Array(3,15,17))),
  )

  val evenCycles: List[MemCycle] = List(
    MemCycle(createListFromInt(Array(2))),
    MemCycle(createListFromInt(Array(2,4,8))),
    MemCycle(createListFromInt(Array(10,20,30))),
  )

  val allCycles: List[MemCycle] = primeCycles ++ oddCycles ++ evenCycles

  "forAnyCheckModValuesRemains" should "hold for any cycle" in {
    val dividends = List(
      BigInt(2),
      BigInt(3),
      BigInt(5),
      BigInt(10),
    )

    assert(allCycles.forall(
      cycle => {
        dividends.forall(
          dividend => {
            CycleCheckMod.forAnyCheckModValuesRemains(
              cycle, dividend
            ) &&
              CycleCheckMod.forAnyCheckModValuesRemains(
                cycle.checkMod(dividend), dividend
              )
          }
        )
      }
    ))
  }

  "notEvaluatedNotInTheList" should "hold for any not evaluated cycle" in {
    val dividends = List(
      BigInt(2),
      BigInt(3),
      BigInt(5),
      BigInt(10),
    )

    assert(allCycles.forall(
      cycle => {
        dividends.forall(
          dividend => {
            CycleCheckMod.notEvaluatedNotInTheList(
              cycle, dividend
            )
          }
        )
      }
    ))
  }

  "evaluatedInSomeList" should "hold for any not evaluated cycle" in {
    val dividends = List(
      BigInt(2),
      BigInt(3),
      BigInt(5),
      BigInt(10),
    )

    assert(allCycles.forall(
      cycle => {
        dividends.forall(
          dividend => {
            CycleCheckMod.evaluatedInSomeList(
              cycle, dividend
            )
          }
        )
      }
    ))
  }

  "oneListNotInOther" should "hold for any not evaluated cycle" in {
    val dividends = List(
      BigInt(2),
      BigInt(3),
      BigInt(5),
      BigInt(10),
    )

    assert(allCycles.forall(
      cycle => {
        dividends.forall(
          dividend => {
            CycleCheckMod.oneListNotInOther(
              cycle, dividend
            )
          }
        )
      }
    ))
  }

  "ifInAllModAll" should "hold for any not evaluated cycle" in {
    val dividends = List(
      BigInt(2),
      BigInt(3),
      BigInt(5),
      BigInt(10),
    )

    assert(allCycles.forall(
      cycle => {
        dividends.forall(
          dividend => {
            CycleCheckMod.ifInAllModAll(
              cycle, dividend
            )
          }
        )
      }
    ))
  }

  "ifInSomeModSome" should "hold for any not evaluated cycle" in {
    val dividends = List(
      BigInt(2),
      BigInt(3),
      BigInt(5),
      BigInt(10),
    )

    assert(allCycles.forall(
      cycle => {
        dividends.forall(
          dividend => {
            CycleCheckMod.ifInSomeModSome(
              cycle, dividend
            )
          }
        )
      }
    ))
  }

  "ifInNoneModNone" should "hold for any not evaluated cycle" in {
    val dividends = List(
      BigInt(2),
      BigInt(3),
      BigInt(5),
      BigInt(10),
    )

    assert(allCycles.forall(
      cycle => {
        dividends.forall(
          dividend => {
            CycleCheckMod.ifInNoneModNone(
              cycle, dividend
            )
          }
        )
      }
    ))
  }

  "allModZeroPropagate" should "hold for any not evaluated cycle" in {
    val dividends = List(
      BigInt(2), BigInt(5),
    )

    val cycles: List[MemCycle] = List(
      MemCycle(createListFromInt(Array(20))),
      MemCycle(createListFromInt(Array(20, 40, 80))),
      MemCycle(createListFromInt(Array(10, 20, 30))),
    )

    assert(
      cycles.forall(
        cycle => {
          CycleCheckMod.allModZeroPropagate(
            cycle, BigInt(2), BigInt(5)
          )
        }
      )
    )
  }

  "someModZeroPropagate" should "hold for any not evaluated cycle" in {
    val dividends = List(
      BigInt(2), BigInt(5),
    )

    val cycles: List[MemCycle] = List(
      MemCycle(createListFromInt(Array(20, 21))),
      MemCycle(createListFromInt(Array(20, 40, 80, 21))),
      MemCycle(createListFromInt(Array(10, 20, 30, 21))),
    )

    assert(
      cycles.forall(
        cycle => {
          CycleCheckMod.someModZeroPropagate(
            cycle, BigInt(2), BigInt(5)
          )
        }
      )
    )
  }

  "noModZeroPropagate" should "hold for any not evaluated cycle" in {
    val dividends = List(
      BigInt(2), BigInt(3),
    )

    val cycles: List[MemCycle] = List(
      MemCycle(createListFromInt(Array(5, 7, 11))),
      MemCycle(createListFromInt(Array(11, 13, 17))),
      MemCycle(createListFromInt(Array(23, 49, 41))),
    )

    assert(
      cycles.forall(
        cycle => {
          CycleCheckMod.noModZeroPropagate(
            cycle, BigInt(2), BigInt(3)
          )
        }
      )
    )
  }


  "afterMethodListAndZeroModCountAreOnSync" should "hold for any cycle" in {
    val dividends = List(
      BigInt(2),
      BigInt(3),
      BigInt(5),
      BigInt(10),
    )

    assert(allCycles.forall(
      cycle => {
        dividends.forall(
          dividend => {
            CycleCheckMod.afterMethodListAndZeroModCountAreOnSync(
              cycle, dividend
            )
          }
        )
      }
    ))
  }
}

