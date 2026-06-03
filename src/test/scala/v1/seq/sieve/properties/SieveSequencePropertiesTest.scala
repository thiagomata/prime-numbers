package v1.seq.sieve.properties

import org.scalatest.flatspec.*
import org.scalatest.matchers.should.*

class SieveSequencePropertiesTest extends FlatSpec with Matchers {

  "atLeastOneMultiplePerBlock" should "hold for various p and start" in {
    assert(SieveSequenceProperties.atLeastOneMultiplePerBlock(BigInt(0), BigInt(2)))
    assert(SieveSequenceProperties.atLeastOneMultiplePerBlock(BigInt(0), BigInt(3)))
    assert(SieveSequenceProperties.atLeastOneMultiplePerBlock(BigInt(5), BigInt(3)))
    assert(SieveSequenceProperties.atLeastOneMultiplePerBlock(BigInt(10), BigInt(7)))
    assert(SieveSequenceProperties.atLeastOneMultiplePerBlock(BigInt(7), BigInt(5)))
  }
}
