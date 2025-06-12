package v1.cycle.acc

import v1.cycle.integral.CycleIntegral
import stainless.lang.*
import v1.Calc
import v1.Calc.{div, mod}
import v1.cycle.integral.properties.CycleIntegralProperties
import v1.div.properties.{ModOperations, ModSmallDividend}
import v1.list.integral.properties.IntegralProperties
import v1.list.properties.ListUtilsProperties
import verification.Helper.{assert, equality}

object CycleAccProperties {

  /**
   * Lemmas: apply(position) == integralValues(position) + initialValue
   *
   * @param cycleAcc CycleAcc any CycleAcc
   * @param position BigInt position in the cycle
   * @return Boolean if the properties hold
   */
  def assertFirstValuesMatchIntegral(cycleAcc: CycleAcc, position: BigInt): Boolean = {
    require(position >= 0)
    require(position < cycleAcc.integralValues.size)
    assert(ModSmallDividend.modSmallDividend(position, cycleAcc.integralValues.size))
    assert(Calc.mod(position, cycleAcc.integralValues.size) == position)
    assert(Calc.div(position, cycleAcc.integralValues.size) == 0)

    cycleAcc.apply(position) == cycleAcc.integralValues(position) + cycleAcc.initialValue
  }.holds

  /**
   * Lemmas: The difference between two consecutive values in the cycle
   * is equal to the cycle.values at the mod of higher position.
   *
   * apply(position + 1) - apply(position) == cycle.values(Calc.mod(position + 1, integralValues.size))
   *
   * in other words
   *
   * AccCycle(position + 1) - AccCycle(position) == cycle.values(Calc.mod(position + 1, integralValues.size))
   *
   * @param cycleAcc CycleAcc any CycleAcc
   * @param position BigInt position in the cycle
   * @return Boolean if the properties hold
   */
  def assertSimplifiedDiffValuesMatchCycle(cycleAcc: CycleAcc, position: BigInt): Boolean = {
    require( position >= 0)

    assert(cycleAcc.integralValues.size == cycleAcc.cycle.values.size)
    ModOperations.addOne(position, cycleAcc.integralValues.size)

    if (Calc.mod(position, cycleAcc.integralValues.size) == cycleAcc.integralValues.size - 1) {

      /* load some properties about the last integral value */

      assert(ListUtilsProperties.assertLastEqualsLastPosition(cycleAcc.integralValues.acc))
      assert(IntegralProperties.assertAccMatchesApply(cycleAcc.integralValues, cycleAcc.integralValues.size - 1))
      assert(IntegralProperties.assertLastEqualsSum(cycleAcc.integralValues))
      assert(IntegralProperties.assertSizeAccEqualsSizeList(cycleAcc.integralValues.list, cycleAcc.integralValues.init))
      assert(cycleAcc.integralValues.acc.last == cycleAcc.integralValues.last)
      assert(cycleAcc.integralValues.last     == cycleAcc.integralValues.acc(cycleAcc.integralValues.acc.size - 1))
      assert(cycleAcc.integralValues.last     == cycleAcc.integralValues(cycleAcc.integralValues.size - 1))

      /* check the addOne properties */

      assert(Calc.mod(position + 1, cycleAcc.integralValues.size) == 0)
      assert(Calc.div(position + 1, cycleAcc.integralValues.size) == Calc.div(position, cycleAcc.integralValues.size) + 1)

      /* calc apply(position)  */

      equality(
        cycleAcc.apply(position),
        Calc.div(position, cycleAcc.integralValues.size) * cycleAcc.integralValues.last +
          cycleAcc.integralValues(Calc.mod(position, cycleAcc.integralValues.size)) +
          cycleAcc.initialValue,
        Calc.div(position, cycleAcc.integralValues.size) * cycleAcc.integralValues.last +
          cycleAcc.integralValues(cycleAcc.integralValues.size - 1) +
          cycleAcc.initialValue
      )

      assert(IntegralProperties.assertAccMatchesApply(cycleAcc.integralValues, cycleAcc.integralValues.size - 1))
      assert(IntegralProperties.assertLastEqualsSum(cycleAcc.integralValues))
      assert(IntegralProperties.assertSizeAccEqualsSizeList(cycleAcc.integralValues.list, cycleAcc.integralValues.init))

      assert(cycleAcc.integralValues.apply(cycleAcc.integralValues.size - 1)   ==
        cycleAcc.integralValues.acc(cycleAcc.integralValues.size - 1))
      assert(cycleAcc.integralValues.acc(cycleAcc.integralValues.acc.size - 1) ==
          cycleAcc.integralValues.acc.last)

      /* calc apply(position + 1) */

      assert(cycleAcc.apply(position + 1) ==
        Calc.div(position + 1, cycleAcc.integralValues.size) * cycleAcc.integralValues.last +
          cycleAcc.integralValues(Calc.mod(position + 1, cycleAcc.integralValues.size)) +
          cycleAcc.initialValue
      )

      /* calc apply(position) */

      equality(
        cycleAcc.apply(position),
        // is equal to
        Calc.div(position, cycleAcc.integralValues.size) * cycleAcc.integralValues.last +
          cycleAcc.integralValues(cycleAcc.integralValues.size - 1) +
          cycleAcc.initialValue,
        // since integralValues(size - 1) == integralValues.last
        // is equal to
        Calc.div(position, cycleAcc.integralValues.size) * cycleAcc.integralValues.last +
          cycleAcc.integralValues.last +
          cycleAcc.initialValue
      )

      /* calc apply(position + 1) - apply(position) */

      equality(
        cycleAcc.apply(position + 1) - cycleAcc.apply(position),
        // is equal to
        0 + (                                                                                                           // replacing  apply by the definition
          Calc.div(position + 1, cycleAcc.integralValues.size) * cycleAcc.integralValues.last
            + cycleAcc.integralValues(Calc.mod(position + 1, cycleAcc.integralValues.size))
            + cycleAcc.initialValue
          )
          - (
          Calc.div(position, cycleAcc.integralValues.size) * cycleAcc.integralValues.last
            + cycleAcc.integralValues(cycleAcc.integralValues.size - 1)
            + cycleAcc.initialValue
          ),
        // is equal to
        0 + (Calc.div(position, cycleAcc.integralValues.size) + 1) * cycleAcc.integralValues.last                       // using the addOne properties
          + cycleAcc.integralValues(Calc.mod(position + 1, cycleAcc.integralValues.size))
          + cycleAcc.initialValue
          - Calc.div(position, cycleAcc.integralValues.size) * cycleAcc.integralValues.last
          - cycleAcc.integralValues(cycleAcc.integralValues.size - 1)
          - cycleAcc.initialValue,
        // is equal to
        0 + Calc.div(position, cycleAcc.integralValues.size) * cycleAcc.integralValues.last
          + cycleAcc.integralValues.last                                                                                // distributive property
          - Calc.div(position, cycleAcc.integralValues.size) * cycleAcc.integralValues.last                             // grouping similar terms
          + cycleAcc.integralValues(Calc.mod(position + 1, cycleAcc.integralValues.size))
          - cycleAcc.integralValues(cycleAcc.integralValues.size - 1)
          + cycleAcc.initialValue
          - cycleAcc.initialValue,
        // is equal to
        // simplifying
        0 + cycleAcc.integralValues.last
          + cycleAcc.integralValues(Calc.mod(position + 1, cycleAcc.integralValues.size))
          - cycleAcc.integralValues(cycleAcc.integralValues.size - 1),
        0 + cycleAcc.integralValues(0)                                                                                  // since mod(pos + 1, size) == 0
          + cycleAcc.integralValues.last
          - cycleAcc.integralValues.last,                                                                               // since integralValues(size - 1) == integralValues.last
        // is equal to
        cycleAcc.integralValues(0),
        // is equal to
        cycleAcc.cycle.values.head,
      )

      assert(
        cycleAcc.apply(position + 1) - cycleAcc.apply(position) == cycleAcc.cycle.values.head
      )

    } else {

      /* check addOne properties
       * mod(a + 1, b) == mod(a, b) + 1 and div(a + 1, b) == div(a, b)
       */
      assert(Calc.mod(position + 1, cycleAcc.integralValues.size) == Calc.mod(position, cycleAcc.integralValues.size) + 1)
      assert(Calc.div(position + 1, cycleAcc.integralValues.size) == Calc.div(position, cycleAcc.integralValues.size))

      /* calc apply(position) */

      assert(cycleAcc.apply(position) ==
        Calc.div(position, cycleAcc.integralValues.size) * cycleAcc.integralValues.last +
          cycleAcc.integralValues(Calc.mod(position, cycleAcc.integralValues.size)) +
          cycleAcc.initialValue
      )

      /* calc apply(position + 1) */

      assert(cycleAcc.apply(position + 1) ==
        Calc.div(position + 1, cycleAcc.integralValues.size) * cycleAcc.integralValues.last +
          cycleAcc.integralValues(Calc.mod(position + 1, cycleAcc.integralValues.size)) +
          cycleAcc.initialValue
      )
      assert(cycleAcc.apply(position + 1) ==
        Calc.div(position, cycleAcc.integralValues.size) * cycleAcc.integralValues.last +
          cycleAcc.integralValues(Calc.mod(position, cycleAcc.integralValues.size) + 1) +
          cycleAcc.initialValue
      )

      /* calc apply(position + 1) - apply(position) */

      equality(
        cycleAcc.apply(position + 1) - cycleAcc.apply(position),
        // is equal to
        0 + ( // replacing by the apply definition
          Calc.div(position, cycleAcc.integralValues.size) * cycleAcc.integralValues.last
            + cycleAcc.integralValues(Calc.mod(position, cycleAcc.integralValues.size) + 1)
            + cycleAcc.initialValue
          )
          - ( // replacing by the apply definition
          Calc.div(position, cycleAcc.integralValues.size) * cycleAcc.integralValues.last
            + cycleAcc.integralValues(Calc.mod(position, cycleAcc.integralValues.size))
            + cycleAcc.initialValue
          ),
        // is equal to
        0 + Calc.div(position, cycleAcc.integralValues.size) * cycleAcc.integralValues.last // using addOne properties
          + cycleAcc.integralValues(Calc.mod(position, cycleAcc.integralValues.size) + 1)   // using addOne properties
          + cycleAcc.initialValue
          - Calc.div(position, cycleAcc.integralValues.size) * cycleAcc.integralValues.last
          - cycleAcc.integralValues(Calc.mod(position, cycleAcc.integralValues.size))
          - cycleAcc.initialValue,
        // is equal to
        0 + cycleAcc.integralValues(Calc.mod(position, cycleAcc.integralValues.size) + 1)
          - cycleAcc.integralValues(Calc.mod(position, cycleAcc.integralValues.size))
      )

      /* integral values diff equals cycle.values(mod(pos + 1),size) */

      val a = Calc.mod(position, cycleAcc.integralValues.size)
      val b = Calc.mod(position, cycleAcc.integralValues.size) + 1
      assert(b - a == 1)

      assert(
        cycleAcc.apply(position + 1) - cycleAcc.apply(position) == 0
          + cycleAcc.integralValues(b)
          - cycleAcc.integralValues(a)
      )

      assert(IntegralProperties.assertAccDiffMatchesList(cycleAcc.integralValues, a))
      assert(
        cycleAcc.integralValues(b) - cycleAcc.integralValues(a) == cycleAcc.cycle.values(b)
      )
      assert(
        cycleAcc.apply(position + 1) - cycleAcc.apply(position) == cycleAcc.cycle.values(b)
      )
      assert(
        cycleAcc.apply(position + 1) - cycleAcc.apply(position) == cycleAcc.cycle.values(Calc.mod(position + 1, cycleAcc.integralValues.size))
      )
    }

    cycleAcc.apply(position + 1) - cycleAcc.apply(position) ==
      cycleAcc.cycle.values(Calc.mod(position + 1, cycleAcc.integralValues.size))
  }.holds

  /**
   * This function checks that the cycle accumulator and cycle integral are equal at a given position.
   *
   * in other words:
   *
   * For any position >= 0 => AccCycle(position) == CycleIntegral(position)
   *
   * Therefore, in the consumer point of view,
   * AccCycle and CycleIntegral are the same.
   *
   * @param cycleAcc CycleAcc any CycleAcc
   * @param cycleIntegral CycleIntegral any CycleIntegral with same cycle and initialValue
   * @param position BigInt any position bigger than or equal to 0
   * @return Boolean if the properties hold
   */
  def assertCycleAccEqualsCycleIntegral(
    cycleAcc: CycleAcc,
    cycleIntegral: CycleIntegral,
    position: BigInt,
  ): Boolean = {
    require(position >= 0)
    require(cycleAcc.cycle.values.nonEmpty)
    require(cycleIntegral.cycle.values.nonEmpty)
    require(cycleAcc.cycle.values == cycleIntegral.cycle.values)
    require(cycleAcc.cycle.size   == cycleIntegral.cycle.size)
    require(cycleAcc.initialValue == cycleIntegral.initialValue)
    decreases(position)

    assert(cycleAcc.cycle.size == cycleIntegral.cycle.size)
    val size = cycleAcc.cycle.size

    if (position == 0) {

      assert(div(position, size) == 0)
      assert(mod(position, size) == 0)
      assert(cycleAcc.integralValues(0) == cycleAcc.cycle.values.head)
      assert(cycleAcc(0) == (
        div(position, size) * cycleAcc.integralValues.last
        + cycleAcc.integralValues(mod(position,size)) + cycleAcc.initialValue)
      )
      assert(cycleAcc(0) == 0 + cycleAcc.integralValues(0) + cycleAcc.initialValue)
      assert(cycleAcc(0) == cycleAcc.cycle.values.head + cycleAcc.initialValue)

      assert(cycleIntegral(0) == cycleIntegral.cycle(0) + cycleIntegral.initialValue)
      assert(cycleIntegral(0) == cycleIntegral.cycle.values(mod(0, size)) + cycleIntegral.initialValue)
      assert(cycleIntegral(0) == cycleIntegral.cycle.values(0)            + cycleIntegral.initialValue)
      assert(cycleIntegral(0) == cycleIntegral.cycle.values.head          + cycleIntegral.initialValue)

      assert(cycleAcc(position) == cycleIntegral(position))
    } else {
      assertCycleAccEqualsCycleIntegral(
        cycleAcc,
        cycleIntegral,
        position - 1
      )

      assertSimplifiedDiffValuesMatchCycle(cycleAcc, position - 1)
      assert(
        cycleAcc(position) - cycleAcc(position - 1) ==
          cycleAcc.cycle.values(mod(position, cycleAcc.integralValues.size))
      )
      assert(cycleAcc.integralValues.size == size)

      assert(cycleAcc(position) == cycleAcc(position - 1) + cycleAcc.cycle(position))

      assert(cycleAcc(position - 1) == cycleIntegral(position - 1))

      CycleIntegralProperties.assertDiffEqualsCycleValue(cycleIntegral, position - 1)
      assert(cycleIntegral(position) == cycleIntegral(position - 1) + cycleIntegral.cycle(position))

      assert(cycleIntegral.cycle(position) == cycleIntegral.cycle.values(mod(position, size)))
      assert(cycleAcc.cycle(position) == cycleAcc.cycle.values(mod(position, size)))
      assert(cycleIntegral.cycle.values == cycleAcc.cycle.values)
      assert(cycleAcc.cycle.values(mod(position, size)) == cycleIntegral.cycle.values(mod(position, size)))
      assert(cycleAcc.cycle(position) == cycleAcc.cycle(position))

      assert(cycleIntegral(position) == cycleIntegral(position - 1) + cycleIntegral.cycle(position))
      assert(cycleIntegral(position) == cycleAcc(position - 1)      + cycleIntegral.cycle(position))
      assert(cycleIntegral(position) == cycleAcc(position - 1)      + cycleAcc.cycle(position))

      assert(cycleAcc(position) == cycleIntegral(position))
    }
    cycleAcc(position) == cycleIntegral(position)
  }.holds

  /**
   * Since the cycle accumulator and cycle integral are equal at any position,
   * we can use this lemma to prove that cycle integral is equal to the cycle accumulator
   * definition.
   *
   * In other words:
   *
   * cycleIntegral(position) ==
   *   div(position, size) * cycleAcc.integralValues.last +
   *   cycleAcc.integralValues(mod(position, size)) + cycleIntegral.initialValue
   *
   * @param cycleAcc CycleAcc any CycleAcc
   * @param cycleIntegral CycleIntegral any CycleIntegral with same cycle and initialValue
   * @param position BigInt any position bigger than or equal to 0
   * @return Boolean true if the properties hold
   */
  def assertCycleIntegralMatchCycleAccDef(
    cycleAcc: CycleAcc,
    cycleIntegral: CycleIntegral,
    position: BigInt,
  ): Boolean = {
    require(position >= 0)
    require(cycleAcc.cycle.values.nonEmpty)
    require(cycleIntegral.cycle.values.nonEmpty)
    require(cycleAcc.cycle.values == cycleIntegral.cycle.values)
    require(cycleAcc.cycle.size   == cycleIntegral.cycle.size)
    require(cycleAcc.initialValue == cycleIntegral.initialValue)
    decreases(position)

    assertCycleAccEqualsCycleIntegral(
      cycleAcc,
      cycleIntegral,
      position
    )
    val size = cycleAcc.cycle.size
    
    assert(cycleAcc(position) == cycleIntegral(position))
    assert(
      cycleAcc(position) == div(position, size) * cycleAcc.integralValues.last + 
      cycleAcc.integralValues(mod(position, size)) + cycleAcc.initialValue
    )
    
    cycleIntegral(position) == 
      div(position, size) * cycleAcc.integralValues.last +
        cycleAcc.integralValues(mod(position, size)) + cycleIntegral.initialValue
  }.holds
}
