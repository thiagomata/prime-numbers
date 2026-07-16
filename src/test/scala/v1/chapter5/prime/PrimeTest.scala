package v1.chapter5.prime

import org.scalatest.Inspectors.forAll
import org.scalatest.flatspec.*
import org.scalatest.matchers.should.*

class PrimeTest extends FlatSpec with Matchers {

  "isPrime" should "return false for 0 and 1" in {
    Prime.isPrime(BigInt(0)) should be(false)
    Prime.isPrime(BigInt(1)) should be(false)
  }

  it should "return true for 2" in {
    Prime.isPrime(BigInt(2)) should be(true)
  }

  it should "return true for small primes" in {
    forAll(List(2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47)) { p =>
      Prime.isPrime(BigInt(p)) should be(true)
    }
  }

  it should "return false for small composites" in {
    forAll(List(4, 6, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21, 22, 24, 25)) { c =>
      Prime.isPrime(BigInt(c)) should be(false)
    }
  }

  it should "return true for larger primes" in {
    forAll(List(53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113)) { p =>
      Prime.isPrime(BigInt(p)) should be(true)
    }
  }

  it should "return false for larger composites" in {
    forAll(List(49, 51, 55, 57, 63, 65, 69, 75, 77, 81, 85, 87, 91, 93, 95, 99)) { c =>
      Prime.isPrime(BigInt(c)) should be(false)
    }
  }

  "noDivisorInRange" should "return true when range is a single number that does not divide n" in {
    Prime.noDivisorInRange(BigInt(7), BigInt(4), BigInt(4)) should be(true)
  }

  it should "return false when n is divisible by from" in {
    Prime.noDivisorInRange(BigInt(10), BigInt(2), BigInt(5)) should be(false)
  }

  it should "return true when no divisor exists in range" in {
    Prime.noDivisorInRange(BigInt(7), BigInt(2), BigInt(7)) should be(true)
  }

  it should "return false when n is divisible somewhere in range" in {
    Prime.noDivisorInRange(BigInt(15), BigInt(2), BigInt(5)) should be(false)
  }

  it should "return true when from equals to" in {
    Prime.noDivisorInRange(BigInt(10), BigInt(7), BigInt(7)) should be(true)
  }
}
