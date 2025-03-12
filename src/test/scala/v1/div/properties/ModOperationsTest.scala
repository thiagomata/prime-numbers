package v1.div.properties

import org.scalatest.flatspec.FlatSpec
import org.scalatest.matchers.should.Matchers

class ModOperationsTest extends FlatSpec with Matchers {

  val nonZeroValues: List[BigInt] = List.apply(
    BigInt(-1),
    BigInt(1),
    BigInt(2),
    BigInt(-2),
    BigInt(10),
    BigInt(-10),
  )

  "modAdd" should "hold for any non b zero pair" in {
    assert( nonZeroValues.forall(
      a => { nonZeroValues.forall(
        b => { nonZeroValues.forall(
          c => {
            ModOperations.modAdd(a,b,c)
            ModOperations.modAdd(0,b,c)
            ModOperations.modAdd(a,b,0)
          })
        })
      })
    )
  }

  "modLess" should "hold for any non b zero pair" in {
    assert( nonZeroValues.forall(
      a => { nonZeroValues.forall(
        b => { nonZeroValues.forall(
          c => {
            ModOperations.modLess(a,b,c)
            ModOperations.modLess(0,b,c)
            ModOperations.modLess(a,b,0)
          })
        })
      })
    )
  }

  "modZeroPlusC" should "hold for any non b zero pair" in {
    assert( nonZeroValues.forall(
      a => { nonZeroValues.forall(
        b => { nonZeroValues.forall(
          c => {
            ModOperations.modZeroPlusC(a * b,b,c)
          })
        })
      })
    )
  }
}

