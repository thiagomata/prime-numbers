package v1.div.properties

import org.scalatest.flatspec.FlatSpec
import org.scalatest.matchers.should.Matchers

class ModIdentityTest extends FlatSpec with Matchers {

  val nonZeroValues: List[BigInt] = List.apply(
    BigInt(-1),
    BigInt(1),
    BigInt(2),
    BigInt(-2),
    BigInt(10),
    BigInt(-10),
  )

  "ModIdentity" should "hold for any values" in {
    assert(
      nonZeroValues.forall(
        value => ModIdentity.modIdentity(value)
      )
    )
  }

  "longProof" should "hold for any values" in {
    assert(
      nonZeroValues.forall(
        value => ModIdentity.longProof(value)
      )
    )
  }
}
