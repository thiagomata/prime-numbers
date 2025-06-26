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
  def assertFirstValuesMatchIntegral(modCycleIntegral: ModCycleIntegral, position: BigInt): Boolean = {
    require(position >= 0)
    require(position < modCycleIntegral.integralValues.size)
    assert(ModSmallDividend.modSmallDividend(position, modCycleIntegral.integralValues.size))
    assert(Calc.mod(position, modCycleIntegral.integralValues.size) == position)
    assert(Calc.div(position, modCycleIntegral.integralValues.size) == 0)

    modCycleIntegral.apply(position) == modCycleIntegral.integralValues(position) + modCycleIntegral.initialValue
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
  def assertSimplifiedDiffValuesMatchCycle(modCycleIntegral: ModCycleIntegral, position: BigInt): Boolean = {
    require( position >= 0)

    assert(modCycleIntegral.integralValues.size == modCycleIntegral.mCycle.size)
    ModOperations.addOne(position, modCycleIntegral.integralValues.size)

    if (Calc.mod(position, modCycleIntegral.integralValues.size) == modCycleIntegral.integralValues.size - 1) {

      /* load some properties about the last integral value */

      assert(ListUtilsProperties.assertLastEqualsLastPosition(modCycleIntegral.integralValues.acc))
      assert(IntegralProperties.assertAccMatchesApply(modCycleIntegral.integralValues, modCycleIntegral.integralValues.size - 1))
      assert(IntegralProperties.assertLastEqualsSum(modCycleIntegral.integralValues))
      assert(IntegralProperties.assertSizeAccEqualsSizeList(modCycleIntegral.integralValues.list, modCycleIntegral.integralValues.init))
      assert(modCycleIntegral.integralValues.acc.last == modCycleIntegral.integralValues.last)
      assert(modCycleIntegral.integralValues.last     == modCycleIntegral.integralValues.acc(modCycleIntegral.integralValues.acc.size - 1))
      assert(modCycleIntegral.integralValues.last     == modCycleIntegral.integralValues(modCycleIntegral.integralValues.size - 1))

      /* check the addOne properties */

      assert(Calc.mod(position + 1, modCycleIntegral.integralValues.size) == 0)
      assert(Calc.div(position + 1, modCycleIntegral.integralValues.size) == Calc.div(position, modCycleIntegral.integralValues.size) + 1)

      /* calc apply(position)  */

      equality(
        modCycleIntegral.apply(position),
        Calc.div(position, modCycleIntegral.integralValues.size) * modCycleIntegral.integralValues.last +
          modCycleIntegral.integralValues(Calc.mod(position, modCycleIntegral.integralValues.size)) +
          modCycleIntegral.initialValue,
        Calc.div(position, modCycleIntegral.integralValues.size) * modCycleIntegral.integralValues.last +
          modCycleIntegral.integralValues(modCycleIntegral.integralValues.size - 1) +
          modCycleIntegral.initialValue
      )

      assert(IntegralProperties.assertAccMatchesApply(modCycleIntegral.integralValues, modCycleIntegral.integralValues.size - 1))
      assert(IntegralProperties.assertLastEqualsSum(modCycleIntegral.integralValues))
      assert(IntegralProperties.assertSizeAccEqualsSizeList(modCycleIntegral.integralValues.list, modCycleIntegral.integralValues.init))

      assert(modCycleIntegral.integralValues.apply(modCycleIntegral.integralValues.size - 1)   ==
        modCycleIntegral.integralValues.acc(modCycleIntegral.integralValues.size - 1))
      assert(modCycleIntegral.integralValues.acc(modCycleIntegral.integralValues.acc.size - 1) ==
        modCycleIntegral.integralValues.acc.last)

      /* calc apply(position + 1) */

      assert(modCycleIntegral.apply(position + 1) ==
        Calc.div(position + 1, modCycleIntegral.integralValues.size) * modCycleIntegral.integralValues.last +
          modCycleIntegral.integralValues(Calc.mod(position + 1, modCycleIntegral.integralValues.size)) +
          modCycleIntegral.initialValue
      )

      /* calc apply(position) */

      equality(
        modCycleIntegral.apply(position),
        // is equal to
        Calc.div(position, modCycleIntegral.integralValues.size) * modCycleIntegral.integralValues.last +
          modCycleIntegral.integralValues(modCycleIntegral.integralValues.size - 1) +
          modCycleIntegral.initialValue,
        // since integralValues(size - 1) == integralValues.last
        // is equal to
        Calc.div(position, modCycleIntegral.integralValues.size) * modCycleIntegral.integralValues.last +
          modCycleIntegral.integralValues.last +
          modCycleIntegral.initialValue
      )

      /* calc apply(position + 1) - apply(position) */

      equality(
        modCycleIntegral.apply(position + 1) - modCycleIntegral.apply(position),
        // is equal to
        0 + (                                                                                                           // replacing  apply by the definition
          Calc.div(position + 1, modCycleIntegral.integralValues.size) * modCycleIntegral.integralValues.last
            + modCycleIntegral.integralValues(Calc.mod(position + 1, modCycleIntegral.integralValues.size))
            + modCycleIntegral.initialValue
          )
          - (
          Calc.div(position, modCycleIntegral.integralValues.size) * modCycleIntegral.integralValues.last
            + modCycleIntegral.integralValues(modCycleIntegral.integralValues.size - 1)
            + modCycleIntegral.initialValue
          ),
        // is equal to
        0 + (Calc.div(position, modCycleIntegral.integralValues.size) + 1) * modCycleIntegral.integralValues.last                       // using the addOne properties
          + modCycleIntegral.integralValues(Calc.mod(position + 1, modCycleIntegral.integralValues.size))
          + modCycleIntegral.initialValue
          - Calc.div(position, modCycleIntegral.integralValues.size) * modCycleIntegral.integralValues.last
          - modCycleIntegral.integralValues(modCycleIntegral.integralValues.size - 1)
          - modCycleIntegral.initialValue,
        // is equal to
        0 + Calc.div(position, modCycleIntegral.integralValues.size) * modCycleIntegral.integralValues.last
          + modCycleIntegral.integralValues.last                                                                                // distributive property
          - Calc.div(position, modCycleIntegral.integralValues.size) * modCycleIntegral.integralValues.last                             // grouping similar terms
          + modCycleIntegral.integralValues(Calc.mod(position + 1, modCycleIntegral.integralValues.size))
          - modCycleIntegral.integralValues(modCycleIntegral.integralValues.size - 1)
          + modCycleIntegral.initialValue
          - modCycleIntegral.initialValue,
        // is equal to
        // simplifying
        0 + modCycleIntegral.integralValues.last
          + modCycleIntegral.integralValues(Calc.mod(position + 1, modCycleIntegral.integralValues.size))
          - modCycleIntegral.integralValues(modCycleIntegral.integralValues.size - 1),
        0 + modCycleIntegral.integralValues(0)                                                                                  // since mod(pos + 1, size) == 0
          + modCycleIntegral.integralValues.last
          - modCycleIntegral.integralValues.last,                                                                               // since integralValues(size - 1) == integralValues.last
        // is equal to
        modCycleIntegral.integralValues(0),
        // is equal to
        modCycleIntegral.mCycle.values.head,
      )

      assert(
        modCycleIntegral.apply(position + 1) - modCycleIntegral.apply(position) == modCycleIntegral.mCycle.values.head
      )

    } else {

      /* check addOne properties
       * mod(a + 1, b) == mod(a, b) + 1 and div(a + 1, b) == div(a, b)
       */
      assert(Calc.mod(position + 1, modCycleIntegral.integralValues.size) == Calc.mod(position, modCycleIntegral.integralValues.size) + 1)
      assert(Calc.div(position + 1, modCycleIntegral.integralValues.size) == Calc.div(position, modCycleIntegral.integralValues.size))

      /* calc apply(position) */

      assert(modCycleIntegral.apply(position) ==
        Calc.div(position, modCycleIntegral.integralValues.size) * modCycleIntegral.integralValues.last +
          modCycleIntegral.integralValues(Calc.mod(position, modCycleIntegral.integralValues.size)) +
          modCycleIntegral.initialValue
      )

      /* calc apply(position + 1) */

      assert(modCycleIntegral.apply(position + 1) ==
        Calc.div(position + 1, modCycleIntegral.integralValues.size) * modCycleIntegral.integralValues.last +
          modCycleIntegral.integralValues(Calc.mod(position + 1, modCycleIntegral.integralValues.size)) +
          modCycleIntegral.initialValue
      )
      assert(modCycleIntegral.apply(position + 1) ==
        Calc.div(position, modCycleIntegral.integralValues.size) * modCycleIntegral.integralValues.last +
          modCycleIntegral.integralValues(Calc.mod(position, modCycleIntegral.integralValues.size) + 1) +
          modCycleIntegral.initialValue
      )

      /* calc apply(position + 1) - apply(position) */

      equality(
        modCycleIntegral.apply(position + 1) - modCycleIntegral.apply(position),
        // is equal to
        0 + ( // replacing by the apply definition
          Calc.div(position, modCycleIntegral.integralValues.size) * modCycleIntegral.integralValues.last
            + modCycleIntegral.integralValues(Calc.mod(position, modCycleIntegral.integralValues.size) + 1)
            + modCycleIntegral.initialValue
          )
          - ( // replacing by the apply definition
          Calc.div(position, modCycleIntegral.integralValues.size) * modCycleIntegral.integralValues.last
            + modCycleIntegral.integralValues(Calc.mod(position, modCycleIntegral.integralValues.size))
            + modCycleIntegral.initialValue
          ),
        // is equal to
        0 + Calc.div(position, modCycleIntegral.integralValues.size) * modCycleIntegral.integralValues.last // using addOne properties
          + modCycleIntegral.integralValues(Calc.mod(position, modCycleIntegral.integralValues.size) + 1)   // using addOne properties
          + modCycleIntegral.initialValue
          - Calc.div(position, modCycleIntegral.integralValues.size) * modCycleIntegral.integralValues.last
          - modCycleIntegral.integralValues(Calc.mod(position, modCycleIntegral.integralValues.size))
          - modCycleIntegral.initialValue,
        // is equal to
        0 + modCycleIntegral.integralValues(Calc.mod(position, modCycleIntegral.integralValues.size) + 1)
          - modCycleIntegral.integralValues(Calc.mod(position, modCycleIntegral.integralValues.size))
      )

      /* integral values diff equals cycle.values(mod(pos + 1),size) */

      val a = Calc.mod(position, modCycleIntegral.integralValues.size)
      val b = Calc.mod(position, modCycleIntegral.integralValues.size) + 1
      assert(b - a == 1)

      assert(
        modCycleIntegral.apply(position + 1) - modCycleIntegral.apply(position) == 0
          + modCycleIntegral.integralValues(b)
          - modCycleIntegral.integralValues(a)
      )

      assert(IntegralProperties.assertAccDiffMatchesList(modCycleIntegral.integralValues, a))
      assert(
        modCycleIntegral.integralValues(b) - modCycleIntegral.integralValues(a) == modCycleIntegral.mCycle.values(b)
      )
      assert(
        modCycleIntegral.apply(position + 1) - modCycleIntegral.apply(position) == modCycleIntegral.mCycle.values(b)
      )
      assert(
        modCycleIntegral.apply(position + 1) - modCycleIntegral.apply(position) == modCycleIntegral.mCycle.values(Calc.mod(position + 1, modCycleIntegral.integralValues.size))
      )
    }

    modCycleIntegral.apply(position + 1) - modCycleIntegral.apply(position) ==
      modCycleIntegral.mCycle.values(Calc.mod(position + 1, modCycleIntegral.integralValues.size))
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
                                         modCycleIntegral: ModCycleIntegral,
                                         cycleIntegral: CycleIntegral,
                                         position: BigInt,
  ): Boolean = {
    require(position >= 0)
    require(modCycleIntegral.mCycle.values.nonEmpty)
    require(cycleIntegral.cycle.values.nonEmpty)
    require(modCycleIntegral.mCycle.values == cycleIntegral.cycle.values)
    require(modCycleIntegral.mCycle.size   == cycleIntegral.cycle.size)
    require(modCycleIntegral.initialValue == cycleIntegral.initialValue)
    decreases(position)

    assert(modCycleIntegral.mCycle.size == cycleIntegral.cycle.size)
    val size = modCycleIntegral.mCycle.size

    if (position == 0) {

      assert(div(position, size) == 0)
      assert(mod(position, size) == 0)
      assert(modCycleIntegral.integralValues(0) == modCycleIntegral.mCycle.values.head)
      assert(modCycleIntegral(0) == (
        div(position, size) * modCycleIntegral.integralValues.last
        + modCycleIntegral.integralValues(mod(position,size)) + modCycleIntegral.initialValue)
      )
      assert(modCycleIntegral(0) == 0 + modCycleIntegral.integralValues(0) + modCycleIntegral.initialValue)
      assert(modCycleIntegral(0) == modCycleIntegral.mCycle.values.head + modCycleIntegral.initialValue)

      assert(cycleIntegral(0) == cycleIntegral.cycle(0) + cycleIntegral.initialValue)
      assert(cycleIntegral(0) == cycleIntegral.cycle.values(mod(0, size)) + cycleIntegral.initialValue)
      assert(cycleIntegral(0) == cycleIntegral.cycle.values(0)            + cycleIntegral.initialValue)
      assert(cycleIntegral(0) == cycleIntegral.cycle.values.head          + cycleIntegral.initialValue)

      assert(modCycleIntegral(position) == cycleIntegral(position))
    } else {
      assertModCycleEqualsCycleIntegral(
        modCycleIntegral,
        cycleIntegral,
        position - 1
      )

      assertSimplifiedDiffValuesMatchCycle(modCycleIntegral, position - 1)
      assert(
        modCycleIntegral(position) - modCycleIntegral(position - 1) ==
          modCycleIntegral.mCycle.values(mod(position, modCycleIntegral.integralValues.size))
      )
      assert(modCycleIntegral.integralValues.size == size)

      assert(modCycleIntegral(position) == modCycleIntegral(position - 1) + modCycleIntegral.mCycle(position))

      assert(modCycleIntegral(position - 1) == cycleIntegral(position - 1))

      CycleIntegralProperties.assertDiffEqualsCycleValue(cycleIntegral, position - 1)
      assert(cycleIntegral(position) == cycleIntegral(position - 1) + cycleIntegral.cycle(position))

      assert(cycleIntegral.cycle(position) == cycleIntegral.cycle.values(mod(position, size)))
      assert(modCycleIntegral.mCycle(position) == modCycleIntegral.mCycle.values(mod(position, size)))
      assert(cycleIntegral.cycle.values == modCycleIntegral.mCycle.values)
      assert(modCycleIntegral.mCycle.values(mod(position, size)) == cycleIntegral.cycle.values(mod(position, size)))
      assert(modCycleIntegral.mCycle(position) == modCycleIntegral.mCycle(position))

      assert(cycleIntegral(position) == cycleIntegral(position - 1) + cycleIntegral.cycle(position))
      assert(cycleIntegral(position) == modCycleIntegral(position - 1)      + cycleIntegral.cycle(position))
      assert(cycleIntegral(position) == modCycleIntegral(position - 1)      + modCycleIntegral.mCycle(position))

      assert(modCycleIntegral(position) == cycleIntegral(position))
    }
    modCycleIntegral(position) == cycleIntegral(position)
  }.holds

  /**
   * Since the cycle accumulator and cycle integral are equal at any position,
   * we can use this lemma to prove that cycle integral is equal to the cycle accumulator
   * definition.
   *
   * In other words:
   *
   * cycleIntegral(position) ==
   *   div(position, size) * modCycleIntegral.integralValues.last +
   *   modCycleIntegral.integralValues(mod(position, size)) + cycleIntegral.initialValue
   *
   * @param modCycle ModCycle any ModCycle
   * @param cycleIntegral CycleIntegral any CycleIntegral with same cycle and initialValue
   * @param position BigInt any position bigger than or equal to 0
   * @return Boolean true if the properties hold
   */
  def assertCycleIntegralMatchModCycleDef(
                                           modCycleIntegral: ModCycleIntegral,
                                           cycleIntegral: CycleIntegral,
                                           position: BigInt,
  ): Boolean = {
    require(position >= 0)
    require(modCycleIntegral.mCycle.values.nonEmpty)
    require(cycleIntegral.cycle.values.nonEmpty)
    require(modCycleIntegral.mCycle.values == cycleIntegral.cycle.values)
    require(modCycleIntegral.mCycle.size   == cycleIntegral.cycle.size)
    require(modCycleIntegral.initialValue == cycleIntegral.initialValue)
    decreases(position)

    assertModCycleEqualsCycleIntegral(
      modCycleIntegral,
      cycleIntegral,
      position
    )
    val size = modCycleIntegral.mCycle.size
    
    assert(modCycleIntegral(position) == cycleIntegral(position))
    assert(
      modCycleIntegral(position) == div(position, size) * modCycleIntegral.integralValues.last + 
      modCycleIntegral.integralValues(mod(position, size)) + modCycleIntegral.initialValue
    )
    
    cycleIntegral(position) == 
      div(position, size) * modCycleIntegral.integralValues.last +
        modCycleIntegral.integralValues(mod(position, size)) + cycleIntegral.initialValue
  }.holds
}
