package v1.cycle.acc

import v1.cycle.Cycle
import v1.div.DivMod
import v1.list.integral.Integral
import stainless.lang.*
import v1.Calc
import v1.div.properties.{ModOperations, ModSmallDividend, Summary}
import v1.list.properties.ListUtilsProperties
import verification.Helper.{assert, equality}

case class CycleAcc(
  initialValue:          BigInt,
  cycle:                 Cycle,
) {
  require(cycle.values.nonEmpty)

  val integralValues: Integral = Integral(
    list = cycle.values,
  )

  def apply(position: BigInt): BigInt = {
    require(position >= 0)
    val divMod = DivMod(position, integralValues.size, 0, position).solve
    assert(divMod.mod >= 0)
    assert(divMod.div >= 0)
    assert(position == divMod.div * integralValues.size + divMod.mod)
    divMod.div * integralValues.last + integralValues(divMod.mod) + initialValue
  }

  /**
   * Lemmas: apply(position) == integralValues(position) + initialValue
   *
   * @param position BigInt position in the cycle
   * @return Boolean if the properties hold
   */
  def assertFirstValuesMatchIntegral(position: BigInt): Boolean = {
    require(position >= 0)
    require(position < integralValues.size)
    assert(ModSmallDividend.modSmallDividend(position, integralValues.size))
    assert(Calc.mod(position, integralValues.size) == position)
    assert(Calc.div(position, integralValues.size) == 0)

    apply(position) == integralValues(position) + initialValue
  }.holds

  /**
   * Lemmas: The difference between two consecutive values in the cycle
   * is equal to the cycle.values at the mod of higher position.
   *
   * apply(position + 1) - apply(position) == cycle.values(Calc.mod(position + 1, integralValues.size))
   *
   * @param position BigInt position in the cycle
   * @return Boolean if the properties hold
   */
  def assertSimplifiedDiffValuesMatchCycle(position: BigInt): Boolean = {
    require( position >= 0)

    assert(integralValues.size == cycle.values.size)
    ModOperations.addOne(position, integralValues.size)

    if (Calc.mod(position, integralValues.size) == integralValues.size - 1) {

      /* load some properties about the last integral value */

      assert(ListUtilsProperties.assertLastEqualsLastPosition(integralValues.acc))
      assert(integralValues.assertAccMatchesApply(integralValues.size - 1))
      assert(integralValues.assertLastEqualsSum)
      assert(integralValues.assertSizeAccEqualsSizeList(integralValues.list, integralValues.init))
      assert(integralValues.acc.last == integralValues.last)
      assert(integralValues.last == integralValues.acc(integralValues.acc.size - 1))
      assert(integralValues.last == integralValues(integralValues.size - 1))

      /* check the addOne properties */

      assert(Calc.mod(position + 1, integralValues.size) == 0)
      assert(Calc.div(position + 1, integralValues.size) == Calc.div(position, integralValues.size) + 1)

      /* calc apply(position)  */

      equality(
        apply(position),
        Calc.div(position, integralValues.size) * integralValues.last +
          integralValues(Calc.mod(position, integralValues.size)) +
          initialValue,
        Calc.div(position, integralValues.size) * integralValues.last +
          integralValues(integralValues.size - 1) +
          initialValue
      )

      assert(integralValues.assertAccMatchesApply(integralValues.size - 1))
      assert(integralValues.assertLastEqualsSum)
      assert(integralValues.assertSizeAccEqualsSizeList(integralValues.list, integralValues.init))

      assert(integralValues.apply(integralValues.size - 1) == integralValues.acc(integralValues.size - 1))
      assert(integralValues.acc(integralValues.acc.size - 1) == integralValues.acc.last)

      /* calc apply(position + 1) */

      assert(apply(position + 1) ==
        Calc.div(position + 1, integralValues.size) * integralValues.last +
          integralValues(Calc.mod(position + 1, integralValues.size)) +
          initialValue
      )

      /* calc apply(position) */

      equality(
        apply(position),
        // is equal to
        Calc.div(position, integralValues.size) * integralValues.last +
          integralValues(integralValues.size - 1) +
          initialValue,
        // since integralValues(size - 1) == integralValues.last
        // is equal to
        Calc.div(position, integralValues.size) * integralValues.last +
          integralValues.last +
          initialValue
      )

      /* calc apply(position + 1) - apply(position) */

      equality(
        apply(position + 1) - apply(position),
        // is equal to
        0 + (                                                                   // replacing  apply by the definition
            Calc.div(position + 1, integralValues.size) * integralValues.last
              + integralValues(Calc.mod(position + 1, integralValues.size))
              + initialValue
            )
          - (
            Calc.div(position, integralValues.size) * integralValues.last
              + integralValues(integralValues.size - 1)
              + initialValue
          ),
        // is equal to
        0 + (Calc.div(position, integralValues.size) + 1) * integralValues.last // using the addOne properties
          + integralValues(Calc.mod(position + 1, integralValues.size))
          + initialValue
          - Calc.div(position, integralValues.size) * integralValues.last
          - integralValues(integralValues.size - 1)
          - initialValue,
        // is equal to
        0 + Calc.div(position, integralValues.size) * integralValues.last
          + integralValues.last                                                 // distributive property
          - Calc.div(position, integralValues.size) * integralValues.last       // grouping similar terms
          + integralValues(Calc.mod(position + 1, integralValues.size))
          - integralValues(integralValues.size - 1)
          + initialValue
          - initialValue,
        // is equal to
        // simplifying
        0 + integralValues.last
          + integralValues(Calc.mod(position + 1, integralValues.size))
          - integralValues(integralValues.size - 1),
        0 + integralValues(0)          // since mod(pos + 1, size) == 0
          + integralValues.last
          - integralValues.last,       // since integralValues(size - 1) == integralValues.last
        // is equal to
        integralValues(0),
        // is equal to
        cycle.values.head,
      )

      assert(
        apply(position + 1) - apply(position) == cycle.values.head
      )

    } else {

      /* check addOne properties
       * mod(a + 1, b) == mod(a, b) + 1 and div(a + 1, b) == div(a, b)
       */
      assert(Calc.mod(position + 1, integralValues.size) == Calc.mod(position, integralValues.size) + 1)
      assert(Calc.div(position + 1, integralValues.size) == Calc.div(position, integralValues.size))

      /* calc apply(position) */

      assert(apply(position) ==
        Calc.div(position, integralValues.size) * integralValues.last +
          integralValues(Calc.mod(position, integralValues.size)) +
          initialValue
      )

      /* calc apply(position + 1) */

      assert(apply(position + 1) ==
        Calc.div(position + 1, integralValues.size) * integralValues.last +
          integralValues(Calc.mod(position + 1, integralValues.size)) +
          initialValue
      )
      assert(apply(position + 1) ==
        Calc.div(position, integralValues.size) * integralValues.last +
          integralValues(Calc.mod(position, integralValues.size) + 1) +
          initialValue
      )

      /* calc apply(position + 1) - apply(position) */

      equality(
        apply(position + 1) - apply(position),
        // is equal to
        0 + ( // replacing by the apply definition
          Calc.div(position, integralValues.size) * integralValues.last
            + integralValues(Calc.mod(position, integralValues.size) + 1)
            + initialValue
          )
          - ( // replacing by the apply definition
          Calc.div(position, integralValues.size) * integralValues.last
            + integralValues(Calc.mod(position, integralValues.size))
            + initialValue
          ),
        // is equal to
        0 + Calc.div(position, integralValues.size) * integralValues.last // using addOne properties
          + integralValues(Calc.mod(position, integralValues.size) + 1)   // using addOne properties
          + initialValue
          - Calc.div(position, integralValues.size) * integralValues.last
          - integralValues(Calc.mod(position, integralValues.size))
          - initialValue,
        // is equal to
        0 + integralValues(Calc.mod(position, integralValues.size) + 1)
          - integralValues(Calc.mod(position, integralValues.size))
      )

      /* integral values diff equals cycle.values(mod(pos + 1),size) */

      val a = Calc.mod(position, integralValues.size)
      val b = Calc.mod(position, integralValues.size) + 1
      assert(b - a == 1)

      assert(
        apply(position + 1) - apply(position) == 0
          + integralValues(b)
          - integralValues(a)
      )

      integralValues.assertAccDiffMatchesList(a)
      assert(
        integralValues(b) - integralValues(a) == cycle.values(b)
      )
      assert(
        apply(position + 1) - apply(position) == cycle.values(b)
      )
      assert(
        apply(position + 1) - apply(position) == cycle.values(Calc.mod(position + 1, integralValues.size))
      )
    }

    apply(position + 1) - apply(position) ==
      cycle.values(Calc.mod(position + 1, integralValues.size))
  }
}
