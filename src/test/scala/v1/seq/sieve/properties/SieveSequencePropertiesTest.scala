package v1.seq.sieve.properties

import org.scalatest.flatspec.*
import org.scalatest.matchers.should.*

class SieveSequencePropertiesTest extends FlatSpec with Matchers {

  "assertS1HeadIsThree" should "hold" in {
    assert(SieveSequenceProperties.assertS1HeadIsThree())
  }

  "assertS1PrimesLength" should "hold" in {
    assert(SieveSequenceProperties.assertS1PrimesLength())
  }
}
