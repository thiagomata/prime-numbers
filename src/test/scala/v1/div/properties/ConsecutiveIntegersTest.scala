package v1.div.properties

import org.scalatest.flatspec.*
import org.scalatest.matchers.should.*
import v1.chapter2.div.properties.ConsecutiveIntegers

class ConsecutiveIntegersTest extends FlatSpec with Matchers {

  "existsZero" should "find a zero in p consecutive values" in {
    assert(ConsecutiveIntegers.existsZero(BigInt(0), BigInt(3)))
    assert(ConsecutiveIntegers.existsZero(BigInt(1), BigInt(3)))
    assert(ConsecutiveIntegers.existsZero(BigInt(2), BigInt(3)))
    assert(ConsecutiveIntegers.existsZero(BigInt(5), BigInt(7)))
    assert(ConsecutiveIntegers.existsZero(BigInt(7), BigInt(5)))
  }

  "nonzeroAfterZero" should "return non-zero for small steps" in {
    assert(ConsecutiveIntegers.nonzeroAfterZero(BigInt(0), BigInt(5), BigInt(1)))
    assert(ConsecutiveIntegers.nonzeroAfterZero(BigInt(0), BigInt(5), BigInt(4)))
    assert(ConsecutiveIntegers.nonzeroAfterZero(BigInt(6), BigInt(3), BigInt(1)))
    assert(ConsecutiveIntegers.nonzeroAfterZero(BigInt(6), BigInt(3), BigInt(2)))
  }
}
