package v1.cycle.acc

import v1.cycle.Cycle
import v1.div.DivMod
import v1.list.integral.Integral
import stainless.lang.*
import v1.Calc
import v1.div.properties.{ModOperations, ModSmallDividend, Summary}
import verification.Helper.{assert, equality}

case class CycleAcc(
  initialValue:          BigInt,
  cycle:                 Cycle,
) {

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
