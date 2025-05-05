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

  def assertFirstValuesMatchIntegral(position: BigInt): Boolean = {
    require(position >= 0)
    require(position < integralValues.size)
    assert(ModSmallDividend.modSmallDividend(position, integralValues.size))
    assert(Calc.mod(position, integralValues.size) == position)
    assert(Calc.div(position, integralValues.size) == 0)

    apply(position) == integralValues(position) + initialValue
  }.holds

  def assertSimplifiedDiffValuesMatchCycle(position: BigInt): Boolean = {
    require( position >= 0)

    assert(integralValues.size == cycle.values.size)
    ModOperations.addOne(position, integralValues.size)

    //   * if b == 1             then mod(a + 1, b) == mod(a,b) and div(a + 1, b) == div(a, b) + 1
    //   * if mod(a, b) == b - 1 then mod(a + 1, b) == 0        and div(a + 1, b) == div(a, b) + 1
    //   * otherwise             then mod(a + 1, b) == mod(a, b) + 1 and div(a + 1, b) == div(a, b)
    if (integralValues.size == 1) {

      // calc apply(position)

      assert(Calc.mod(position, integralValues.size) == 0)
      assert(Calc.div(position, integralValues.size) == position)

      equality(
        apply(position),
        Calc.div(position, integralValues.size) * integralValues.last +
          integralValues(Calc.mod(position, integralValues.size)) +
          initialValue,
        position * integralValues.last +
          integralValues(0) +
          initialValue
      )

//      assert(apply(position) ==
//        Calc.div(position, integralValues.size) * integralValues.last +
//          integralValues(Calc.mod(position, integralValues.size)) +
//          initialValue
//      )
//      assert(apply(position) ==
//        position * integralValues.last +
//          integralValues(0) +
//          initialValue
//      )

      // calc apply(position + 1)

      assert(Calc.mod(position + 1, integralValues.size) == 0)
      assert(Calc.div(position + 1, integralValues.size) == position + 1)

      equality(
        apply(position + 1),
        Calc.div(position + 1, integralValues.size) * integralValues.last +
          integralValues(Calc.mod(position + 1, integralValues.size)) +
          initialValue,
        (position + 1) * integralValues.last +
          integralValues(0) +
          initialValue
      )

//      assert(apply(position + 1) ==
//        Calc.div(position + 1, integralValues.size) * integralValues.last +
//          integralValues(Calc.mod(position + 1, integralValues.size)) +
//          initialValue
//      )
//      assert(apply(position + 1) ==
//        (position + 1) * integralValues.last +
//          integralValues(0) +
//          initialValue
//      )

      assert(integralValues.last == integralValues(0))
      assert(integralValues.last == integralValues(integralValues.size - 1))

      // calc apply(position + 1) - apply(position)

      equality(
        apply(position + 1) - apply(position),
        integralValues(integralValues.size - 1),
        integralValues(0),
        integralValues(Calc.mod(position + 1, integralValues.size)),
        cycle.values.head,
        cycle.values(0),
      )

//      assert(apply(position + 1) - apply(position) == integralValues(integralValues.size - 1))
//      assert(apply(position + 1) - apply(position) == integralValues(0))
//      assert(integralValues(Calc.mod(position + 1, integralValues.size)) == integralValues(0))
//      assert(integralValues(0) == cycle.values.head)
//      assert(integralValues(0) == cycle.values(0))

      return apply(position + 1) - apply(position) == cycle.values(0)
    }
    else  if (Calc.mod(position, integralValues.size) == integralValues.size - 1) {

      // load some properties about the last integral value

      assert(ListUtilsProperties.assertLastEqualsLastPosition(integralValues.acc))
      assert(integralValues.assertAccMatchesApply(integralValues.size - 1))
      assert(integralValues.assertLastEqualsSum)
      assert(integralValues.assertSizeAccEqualsSizeList(integralValues.list, integralValues.init))
      assert(integralValues.acc.last == integralValues.last)
      assert(integralValues.last == integralValues.acc(integralValues.acc.size - 1))
      assert(integralValues.last == integralValues(integralValues.size - 1))

      // check the addOne properties

      assert(Calc.mod(position + 1, integralValues.size) == 0)
      assert(Calc.div(position + 1, integralValues.size) == Calc.div(position, integralValues.size) + 1)

      // calc apply(position)

      assert(apply(position) ==
        Calc.div(position, integralValues.size) * integralValues.last +
          integralValues(Calc.mod(position, integralValues.size)) +
          initialValue
      )
      assert(apply(position) ==
        Calc.div(position, integralValues.size) * integralValues.last +
          integralValues(integralValues.size - 1) +
          initialValue
      )

      assert(integralValues.assertAccMatchesApply(integralValues.size - 1))
      assert(integralValues.assertLastEqualsSum)
      assert(integralValues.assertSizeAccEqualsSizeList(integralValues.list, integralValues.init))

      assert(integralValues.apply(integralValues.size - 1) == integralValues.acc(integralValues.size - 1))
      assert(integralValues.acc(integralValues.acc.size - 1) == integralValues.acc.last)

      // calc apply(position + 1)

      assert(apply(position + 1) ==
        Calc.div(position + 1, integralValues.size) * integralValues.last +
          integralValues(Calc.mod(position + 1, integralValues.size)) +
          initialValue
      )

      // calc apply(position)

      assert(apply(position) ==
        Calc.div(position, integralValues.size) * integralValues.last +
          integralValues(integralValues.size - 1) +
          initialValue
      )
      assert(apply(position) ==
        Calc.div(position, integralValues.size) * integralValues.last +
          integralValues.last +
          initialValue
      )

      // calc apply(position + 1) - apply(position)

      assert(
        apply(position + 1) - apply(position) == 0
          + (
            Calc.div(position + 1, integralValues.size) * integralValues.last
              + integralValues(Calc.mod(position + 1, integralValues.size))
              + initialValue
            )
          - (
            Calc.div(position, integralValues.size) * integralValues.last
              + integralValues(integralValues.size - 1)
              + initialValue
          )
      )
      assert(
        apply(position + 1) - apply(position) == 0
          + (Calc.div(position, integralValues.size) + 1) * integralValues.last
          + integralValues(Calc.mod(position + 1, integralValues.size))
          + initialValue
          - Calc.div(position, integralValues.size) * integralValues.last
          - integralValues(integralValues.size - 1)
          - initialValue
      )
      assert(
        apply(position + 1) - apply(position) == 0
          + Calc.div(position, integralValues.size) * integralValues.last
          + integralValues.last
          - Calc.div(position, integralValues.size) * integralValues.last
          + integralValues(Calc.mod(position + 1, integralValues.size))
          - integralValues(integralValues.size - 1)
          + initialValue
          - initialValue
      )
      assert(
        apply(position + 1) - apply(position) == 0
          + integralValues.last
          + integralValues(Calc.mod(position + 1, integralValues.size))
          - integralValues(integralValues.size - 1)
          + initialValue
          - initialValue
      )
      assert(Calc.mod(position + 1, integralValues.size) == 0)
      assert(
        apply(position + 1) - apply(position) == 0
          + integralValues(0)
          + integralValues.last
          - integralValues.last
          + initialValue
          - initialValue
      )

      // integralValues(0) == cycle.values.head == cycle.values(0)

      assert(integralValues(0) == cycle.values.head)
      assert(
        apply(position + 1) - apply(position) == cycle.values.head
      )

      // 0 == Calc.mod(position + 1, integralValues.size)

      return apply(position + 1) - apply(position) == integralValues(Calc.mod(position + 1, integralValues.size))
    }

    // check addOne properties
    // mod(a + 1, b) == mod(a, b) + 1 and div(a + 1, b) == div(a, b)
    assert(Calc.mod(position + 1, integralValues.size) == Calc.mod(position, integralValues.size) + 1)
    assert(Calc.div(position + 1, integralValues.size) == Calc.div(position, integralValues.size))

    // calc apply(position)

    assert(apply(position) ==
      Calc.div(position, integralValues.size) * integralValues.last +
        integralValues(Calc.mod(position, integralValues.size)) +
        initialValue
    )

    // calc apply(position + 1)

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

    // calc apply(position + 1) - apply(position)

    assert(
      apply(position + 1) - apply(position) == 0
        + (
        Calc.div(position, integralValues.size) * integralValues.last
          + integralValues(Calc.mod(position, integralValues.size) + 1)
          + initialValue
        )
        - (
        Calc.div(position, integralValues.size) * integralValues.last
          + integralValues(Calc.mod(position, integralValues.size))
          + initialValue
        )
    )
    assert(
      apply(position + 1) - apply(position) == 0
        + Calc.div(position, integralValues.size) * integralValues.last
        + integralValues(Calc.mod(position, integralValues.size) + 1)
        + initialValue
        - Calc.div(position, integralValues.size) * integralValues.last
        - integralValues(Calc.mod(position, integralValues.size))
        - initialValue
    )

    assert(
      apply(position + 1) - apply(position) == 0
        + integralValues(Calc.mod(position , integralValues.size) + 1)
        - integralValues(Calc.mod(position, integralValues.size))
    )

    // integral values diff equals cycle.values(mod(pos + 1),size)

    val a = Calc.mod(position, integralValues.size)
    val b = Calc.mod(position, integralValues.size) + 1
    assert( b - a == 1 )

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

    apply(position + 1) - apply(position) == cycle.values(Calc.mod(position + 1, integralValues.size))
  }

  def assertDiffValuesMatchCycle(position: BigInt): Boolean = {
    require(position >= 1)

    if (position < integralValues.size) {
      assertFirstValuesMatchIntegral(position)
      assertFirstValuesMatchIntegral(position - 1)
      assert(integralValues.assertAccDiffMatchesList(position - 1))
      assert(integralValues(position) - integralValues(position - 1) == cycle.values(position))
      assert(cycle.values(position) == cycle.values(Calc.mod(position, integralValues.size)))
      apply(position) - apply(position - 1) == cycle.values(Calc.mod(position, integralValues.size))
    }
    else if (position == integralValues.size) {
      equality(
        apply(position),
        Calc.div(position, integralValues.size) * integralValues.last
          + integralValues(Calc.mod(position, integralValues.size))
          + initialValue,
        Calc.div(integralValues.size, integralValues.size) * integralValues.last
          + integralValues(Calc.mod(integralValues.size, integralValues.size))
          + initialValue,
        1 * integralValues.last
          + integralValues(0)
          + initialValue,
        integralValues.last + integralValues(0) + initialValue,
      )
      assertFirstValuesMatchIntegral(position - 1)
      assert(
        apply(position - 1) ==
        Calc.div(position - 1, integralValues.size) * integralValues.last
          + integralValues(Calc.mod(position - 1, integralValues.size))
          + initialValue
      )
      assert(
        apply(position - 1) ==
        0 * integralValues.last
          + integralValues(integralValues.size - 1)
          + initialValue
      )
      assert(integralValues.assertLastEqualsSum)
      assert(integralValues.assertAccMatchesApply(position - 1))
      assert(
        integralValues.last ==
        integralValues.acc.last
      )
      assert(integralValues.assertLast)
      assert(
        integralValues.acc.last ==
          integralValues.acc(integralValues.size - 1)
      )
      assert(
        integralValues.acc(integralValues.size - 1) ==
          integralValues.apply(integralValues.size - 1)
      )
      assert(
        integralValues.apply(integralValues.size - 1) ==
          integralValues.last
      )
      assert(
        apply(position - 1) ==
        integralValues.last + initialValue
      )
      assert(
        apply(position) - apply(position - 1) ==
          ( integralValues.last + integralValues(0) + initialValue ) - ( integralValues.last + initialValue )
      )
      assert(
        apply(position) - apply(position - 1) ==
          integralValues.last + integralValues(0) + initialValue - integralValues.last - initialValue
      )
      assert(
        apply(position) - apply(position - 1) ==
          integralValues.last - integralValues.last + initialValue - initialValue + integralValues(0)
      )
      assert(
        apply(position) - apply(position - 1) ==
          integralValues(0)
      )
      apply(position) - apply(position - 1) == cycle.values(Calc.mod(position, integralValues.size))
    }
    else {
      assert(position > integralValues.size)
      assert(integralValues.nonEmpty)

      assert(apply(position) ==
        Calc.div(position, integralValues.size) * integralValues.last +
          integralValues(Calc.mod(position, integralValues.size)) + initialValue
      )
      assert(apply(position - 1) ==
        Calc.div(position - 1, integralValues.size) * integralValues.last +
          integralValues(Calc.mod(position - 1, integralValues.size)) + initialValue
      )
      equality(
        apply(position) - apply(position - 1),
        Calc.div(position, integralValues.size) * integralValues.last
          + integralValues(Calc.mod(position, integralValues.size))
          + initialValue
          - (
            Calc.div(position - 1, integralValues.size) * integralValues.last
              + integralValues(Calc.mod(position - 1, integralValues.size))
              + initialValue
          ),
        Calc.div(position, integralValues.size) * integralValues.last
          + integralValues(Calc.mod(position, integralValues.size))
          + initialValue
          - Calc.div(position - 1, integralValues.size) * integralValues.last
          - integralValues(Calc.mod(position - 1, integralValues.size))
          - initialValue,
        Calc.div(position, integralValues.size) * integralValues.last
          - Calc.div(position - 1, integralValues.size) * integralValues.last
          + integralValues(Calc.mod(position, integralValues.size))
          - integralValues(Calc.mod(position - 1, integralValues.size))
          + initialValue
          - initialValue,
        Calc.div(position, integralValues.size) * integralValues.last
          - Calc.div(position - 1, integralValues.size) * integralValues.last
          + integralValues(Calc.mod(position, integralValues.size))
          - integralValues(Calc.mod(position - 1, integralValues.size))
      )

      // div(pos,size) * last - div(pos-1,size) * last
      // acc(mod(pos,size)) - acc(mod(pos-1,size))
      // ...
      // cycle.values(mod(position,size))

      if (integralValues.size == 1) {
        // @todo: deal with this case
        return true
      }

      Summary.PropertySummary(
        position,
        integralValues.size,
        position - 1,
        0
      )

      if (Calc.mod(position, integralValues.size) == 0) {
        // mod(pos,size) == 0
        // div(pos,size) == div(pos-1,size) + 1

        assert(
          Calc.mod(position - 1, integralValues.size) == integralValues.size - 1
        )

        assert(
          Calc.div(position, integralValues.size) == Calc.div(position - 1, integralValues.size) + 1
        )



      } else {
        // mod(pos,size) == mod(pos-1,size) + 1
        // div(pos,size) == div(pos-1,size)

        assert(
          Calc.mod(position - 1, integralValues.size) == Calc.mod(position, integralValues.size) - 1
        )
        assert(
          Calc.div(position, integralValues.size) == Calc.div(position - 1, integralValues.size)
        )
      }

      true
      //       apply(position) - apply(position - 1) == cycle.values(Calc.mod(position, integralValues.size))
    }
  }.holds
}
