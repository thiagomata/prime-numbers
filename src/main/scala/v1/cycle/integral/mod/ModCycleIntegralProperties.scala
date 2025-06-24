package v1.cycle.integral.mod

import stainless.lang.*
import v1.Calc
import v1.Calc.{div, mod}
import v1.cycle.integral.recursive.CycleIntegral
import v1.cycle.integral.recursive.properties.CycleIntegralProperties
import v1.div.properties.{ModOperations, ModSmallDividend}
import v1.list.integral.properties.IntegralProperties
import v1.list.properties.ListUtilsProperties
import verification.Helper.{assert, equality}

object ModCycleIntegralProperties {

  /**
   * Lemmas: apply(position) == integralValues(position) + initialValue
   *
   * @param modCycle ModCycle any ModCycle
   * @param position BigInt position in the cycle
   * @return Boolean if the properties hold
   */
  def assertFirstValuesMatchIntegral(modCycle: ModCycleIntegral, position: BigInt): Boolean = {
    require(position >= 0)
    require(position < modCycle.integralValues.size)
    assert(ModSmallDividend.modSmallDividend(position, modCycle.integralValues.size))
    assert(Calc.mod(position, modCycle.integralValues.size) == position)
    assert(Calc.div(position, modCycle.integralValues.size) == 0)

    modCycle.apply(position) == modCycle.integralValues(position) + modCycle.initialValue
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
   * @param modCycle ModCycle any ModCycle
   * @param position BigInt position in the cycle
   * @return Boolean if the properties hold
   */
  def assertSimplifiedDiffValuesMatchCycle(modCycle: ModCycleIntegral, position: BigInt): Boolean = {
    require( position >= 0)

    assert(modCycle.integralValues.size == modCycle.cycle.values.size)
    ModOperations.addOne(position, modCycle.integralValues.size)

    if (Calc.mod(position, modCycle.integralValues.size) == modCycle.integralValues.size - 1) {

      /* load some properties about the last integral value */

      assert(ListUtilsProperties.assertLastEqualsLastPosition(modCycle.integralValues.acc))
      assert(IntegralProperties.assertAccMatchesApply(modCycle.integralValues, modCycle.integralValues.size - 1))
      assert(IntegralProperties.assertLastEqualsSum(modCycle.integralValues))
      assert(IntegralProperties.assertSizeAccEqualsSizeList(modCycle.integralValues.list, modCycle.integralValues.init))
      assert(modCycle.integralValues.acc.last == modCycle.integralValues.last)
      assert(modCycle.integralValues.last     == modCycle.integralValues.acc(modCycle.integralValues.acc.size - 1))
      assert(modCycle.integralValues.last     == modCycle.integralValues(modCycle.integralValues.size - 1))

      /* check the addOne properties */

      assert(Calc.mod(position + 1, modCycle.integralValues.size) == 0)
      assert(Calc.div(position + 1, modCycle.integralValues.size) == Calc.div(position, modCycle.integralValues.size) + 1)

      /* calc apply(position)  */

      equality(
        modCycle.apply(position),
        Calc.div(position, modCycle.integralValues.size) * modCycle.integralValues.last +
          modCycle.integralValues(Calc.mod(position, modCycle.integralValues.size)) +
          modCycle.initialValue,
        Calc.div(position, modCycle.integralValues.size) * modCycle.integralValues.last +
          modCycle.integralValues(modCycle.integralValues.size - 1) +
          modCycle.initialValue
      )

      assert(IntegralProperties.assertAccMatchesApply(modCycle.integralValues, modCycle.integralValues.size - 1))
      assert(IntegralProperties.assertLastEqualsSum(modCycle.integralValues))
      assert(IntegralProperties.assertSizeAccEqualsSizeList(modCycle.integralValues.list, modCycle.integralValues.init))

      assert(modCycle.integralValues.apply(modCycle.integralValues.size - 1)   ==
        modCycle.integralValues.acc(modCycle.integralValues.size - 1))
      assert(modCycle.integralValues.acc(modCycle.integralValues.acc.size - 1) ==
          modCycle.integralValues.acc.last)

      /* calc apply(position + 1) */

      assert(modCycle.apply(position + 1) ==
        Calc.div(position + 1, modCycle.integralValues.size) * modCycle.integralValues.last +
          modCycle.integralValues(Calc.mod(position + 1, modCycle.integralValues.size)) +
          modCycle.initialValue
      )

      /* calc apply(position) */

      equality(
        modCycle.apply(position),
        // is equal to
        Calc.div(position, modCycle.integralValues.size) * modCycle.integralValues.last +
          modCycle.integralValues(modCycle.integralValues.size - 1) +
          modCycle.initialValue,
        // since integralValues(size - 1) == integralValues.last
        // is equal to
        Calc.div(position, modCycle.integralValues.size) * modCycle.integralValues.last +
          modCycle.integralValues.last +
          modCycle.initialValue
      )

      /* calc apply(position + 1) - apply(position) */

      equality(
        modCycle.apply(position + 1) - modCycle.apply(position),
        // is equal to
        0 + (                                                                                                           // replacing  apply by the definition
          Calc.div(position + 1, modCycle.integralValues.size) * modCycle.integralValues.last
            + modCycle.integralValues(Calc.mod(position + 1, modCycle.integralValues.size))
            + modCycle.initialValue
          )
          - (
          Calc.div(position, modCycle.integralValues.size) * modCycle.integralValues.last
            + modCycle.integralValues(modCycle.integralValues.size - 1)
            + modCycle.initialValue
          ),
        // is equal to
        0 + (Calc.div(position, modCycle.integralValues.size) + 1) * modCycle.integralValues.last                       // using the addOne properties
          + modCycle.integralValues(Calc.mod(position + 1, modCycle.integralValues.size))
          + modCycle.initialValue
          - Calc.div(position, modCycle.integralValues.size) * modCycle.integralValues.last
          - modCycle.integralValues(modCycle.integralValues.size - 1)
          - modCycle.initialValue,
        // is equal to
        0 + Calc.div(position, modCycle.integralValues.size) * modCycle.integralValues.last
          + modCycle.integralValues.last                                                                                // distributive property
          - Calc.div(position, modCycle.integralValues.size) * modCycle.integralValues.last                             // grouping similar terms
          + modCycle.integralValues(Calc.mod(position + 1, modCycle.integralValues.size))
          - modCycle.integralValues(modCycle.integralValues.size - 1)
          + modCycle.initialValue
          - modCycle.initialValue,
        // is equal to
        // simplifying
        0 + modCycle.integralValues.last
          + modCycle.integralValues(Calc.mod(position + 1, modCycle.integralValues.size))
          - modCycle.integralValues(modCycle.integralValues.size - 1),
        0 + modCycle.integralValues(0)                                                                                  // since mod(pos + 1, size) == 0
          + modCycle.integralValues.last
          - modCycle.integralValues.last,                                                                               // since integralValues(size - 1) == integralValues.last
        // is equal to
        modCycle.integralValues(0),
        // is equal to
        modCycle.cycle.values.head,
      )

      assert(
        modCycle.apply(position + 1) - modCycle.apply(position) == modCycle.cycle.values.head
      )

    } else {

      /* check addOne properties
       * mod(a + 1, b) == mod(a, b) + 1 and div(a + 1, b) == div(a, b)
       */
      assert(Calc.mod(position + 1, modCycle.integralValues.size) == Calc.mod(position, modCycle.integralValues.size) + 1)
      assert(Calc.div(position + 1, modCycle.integralValues.size) == Calc.div(position, modCycle.integralValues.size))

      /* calc apply(position) */

      assert(modCycle.apply(position) ==
        Calc.div(position, modCycle.integralValues.size) * modCycle.integralValues.last +
          modCycle.integralValues(Calc.mod(position, modCycle.integralValues.size)) +
          modCycle.initialValue
      )

      /* calc apply(position + 1) */

      assert(modCycle.apply(position + 1) ==
        Calc.div(position + 1, modCycle.integralValues.size) * modCycle.integralValues.last +
          modCycle.integralValues(Calc.mod(position + 1, modCycle.integralValues.size)) +
          modCycle.initialValue
      )
      assert(modCycle.apply(position + 1) ==
        Calc.div(position, modCycle.integralValues.size) * modCycle.integralValues.last +
          modCycle.integralValues(Calc.mod(position, modCycle.integralValues.size) + 1) +
          modCycle.initialValue
      )

      /* calc apply(position + 1) - apply(position) */

      equality(
        modCycle.apply(position + 1) - modCycle.apply(position),
        // is equal to
        0 + ( // replacing by the apply definition
          Calc.div(position, modCycle.integralValues.size) * modCycle.integralValues.last
            + modCycle.integralValues(Calc.mod(position, modCycle.integralValues.size) + 1)
            + modCycle.initialValue
          )
          - ( // replacing by the apply definition
          Calc.div(position, modCycle.integralValues.size) * modCycle.integralValues.last
            + modCycle.integralValues(Calc.mod(position, modCycle.integralValues.size))
            + modCycle.initialValue
          ),
        // is equal to
        0 + Calc.div(position, modCycle.integralValues.size) * modCycle.integralValues.last // using addOne properties
          + modCycle.integralValues(Calc.mod(position, modCycle.integralValues.size) + 1)   // using addOne properties
          + modCycle.initialValue
          - Calc.div(position, modCycle.integralValues.size) * modCycle.integralValues.last
          - modCycle.integralValues(Calc.mod(position, modCycle.integralValues.size))
          - modCycle.initialValue,
        // is equal to
        0 + modCycle.integralValues(Calc.mod(position, modCycle.integralValues.size) + 1)
          - modCycle.integralValues(Calc.mod(position, modCycle.integralValues.size))
      )

      /* integral values diff equals cycle.values(mod(pos + 1),size) */

      val a = Calc.mod(position, modCycle.integralValues.size)
      val b = Calc.mod(position, modCycle.integralValues.size) + 1
      assert(b - a == 1)

      assert(
        modCycle.apply(position + 1) - modCycle.apply(position) == 0
          + modCycle.integralValues(b)
          - modCycle.integralValues(a)
      )

      assert(IntegralProperties.assertAccDiffMatchesList(modCycle.integralValues, a))
      assert(
        modCycle.integralValues(b) - modCycle.integralValues(a) == modCycle.cycle.values(b)
      )
      assert(
        modCycle.apply(position + 1) - modCycle.apply(position) == modCycle.cycle.values(b)
      )
      assert(
        modCycle.apply(position + 1) - modCycle.apply(position) == modCycle.cycle.values(Calc.mod(position + 1, modCycle.integralValues.size))
      )
    }

    modCycle.apply(position + 1) - modCycle.apply(position) ==
      modCycle.cycle.values(Calc.mod(position + 1, modCycle.integralValues.size))
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
   * @param modCycle ModCycle any ModCycle
   * @param cycleIntegral CycleIntegral any CycleIntegral with same cycle and initialValue
   * @param position BigInt any position bigger than or equal to 0
   * @return Boolean if the properties hold
   */
  def assertModCycleEqualsCycleIntegral(
                                         modCycle: ModCycleIntegral,
                                         cycleIntegral: CycleIntegral,
                                         position: BigInt,
  ): Boolean = {
    require(position >= 0)
    require(modCycle.cycle.values.nonEmpty)
    require(cycleIntegral.cycle.values.nonEmpty)
    require(modCycle.cycle.values == cycleIntegral.cycle.values)
    require(modCycle.cycle.size   == cycleIntegral.cycle.size)
    require(modCycle.initialValue == cycleIntegral.initialValue)
    decreases(position)

    assert(modCycle.cycle.size == cycleIntegral.cycle.size)
    val size = modCycle.cycle.size

    if (position == 0) {

      assert(div(position, size) == 0)
      assert(mod(position, size) == 0)
      assert(modCycle.integralValues(0) == modCycle.cycle.values.head)
      assert(modCycle(0) == (
        div(position, size) * modCycle.integralValues.last
        + modCycle.integralValues(mod(position,size)) + modCycle.initialValue)
      )
      assert(modCycle(0) == 0 + modCycle.integralValues(0) + modCycle.initialValue)
      assert(modCycle(0) == modCycle.cycle.values.head + modCycle.initialValue)

      assert(cycleIntegral(0) == cycleIntegral.cycle(0) + cycleIntegral.initialValue)
      assert(cycleIntegral(0) == cycleIntegral.cycle.values(mod(0, size)) + cycleIntegral.initialValue)
      assert(cycleIntegral(0) == cycleIntegral.cycle.values(0)            + cycleIntegral.initialValue)
      assert(cycleIntegral(0) == cycleIntegral.cycle.values.head          + cycleIntegral.initialValue)

      assert(modCycle(position) == cycleIntegral(position))
    } else {
      assertModCycleEqualsCycleIntegral(
        modCycle,
        cycleIntegral,
        position - 1
      )

      assertSimplifiedDiffValuesMatchCycle(modCycle, position - 1)
      assert(
        modCycle(position) - modCycle(position - 1) ==
          modCycle.cycle.values(mod(position, modCycle.integralValues.size))
      )
      assert(modCycle.integralValues.size == size)

      assert(modCycle(position) == modCycle(position - 1) + modCycle.cycle(position))

      assert(modCycle(position - 1) == cycleIntegral(position - 1))

      CycleIntegralProperties.assertDiffEqualsCycleValue(cycleIntegral, position - 1)
      assert(cycleIntegral(position) == cycleIntegral(position - 1) + cycleIntegral.cycle(position))

      assert(cycleIntegral.cycle(position) == cycleIntegral.cycle.values(mod(position, size)))
      assert(modCycle.cycle(position) == modCycle.cycle.values(mod(position, size)))
      assert(cycleIntegral.cycle.values == modCycle.cycle.values)
      assert(modCycle.cycle.values(mod(position, size)) == cycleIntegral.cycle.values(mod(position, size)))
      assert(modCycle.cycle(position) == modCycle.cycle(position))

      assert(cycleIntegral(position) == cycleIntegral(position - 1) + cycleIntegral.cycle(position))
      assert(cycleIntegral(position) == modCycle(position - 1)      + cycleIntegral.cycle(position))
      assert(cycleIntegral(position) == modCycle(position - 1)      + modCycle.cycle(position))

      assert(modCycle(position) == cycleIntegral(position))
    }
    modCycle(position) == cycleIntegral(position)
  }.holds

  /**
   * Since the cycle accumulator and cycle integral are equal at any position,
   * we can use this lemma to prove that cycle integral is equal to the cycle accumulator
   * definition.
   *
   * In other words:
   *
   * cycleIntegral(position) ==
   *   div(position, size) * modCycle.integralValues.last +
   *   modCycle.integralValues(mod(position, size)) + cycleIntegral.initialValue
   *
   * @param modCycle ModCycle any ModCycle
   * @param cycleIntegral CycleIntegral any CycleIntegral with same cycle and initialValue
   * @param position BigInt any position bigger than or equal to 0
   * @return Boolean true if the properties hold
   */
  def assertCycleIntegralMatchModCycleDef(
                                           modCycle: ModCycleIntegral,
                                           cycleIntegral: CycleIntegral,
                                           position: BigInt,
  ): Boolean = {
    require(position >= 0)
    require(modCycle.cycle.values.nonEmpty)
    require(cycleIntegral.cycle.values.nonEmpty)
    require(modCycle.cycle.values == cycleIntegral.cycle.values)
    require(modCycle.cycle.size   == cycleIntegral.cycle.size)
    require(modCycle.initialValue == cycleIntegral.initialValue)
    decreases(position)

    assertModCycleEqualsCycleIntegral(
      modCycle,
      cycleIntegral,
      position
    )
    val size = modCycle.cycle.size
    
    assert(modCycle(position) == cycleIntegral(position))
    assert(
      modCycle(position) == div(position, size) * modCycle.integralValues.last + 
      modCycle.integralValues(mod(position, size)) + modCycle.initialValue
    )
    
    cycleIntegral(position) == 
      div(position, size) * modCycle.integralValues.last +
        modCycle.integralValues(mod(position, size)) + cycleIntegral.initialValue
  }.holds
}
