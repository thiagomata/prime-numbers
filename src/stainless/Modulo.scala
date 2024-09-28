import stainless.annotation._
import stainless.lang._

object Modulo {
  def mod(a: BigInt, b: BigInt): BigInt = {
    require(a >= 0 && b > 0)
    // a - (a / b) * b
    if ( a >= b ) Modulo.mod((a - b), b) else a
  }
}

object ModuloIdentity {
  def identityProperty(n: BigInt): Boolean = {
    require(n > BigInt(0))
    Modulo.mod(n, n) == BigInt(0)
  }.holds
}

object ModuloAddition {
  def additiveProperty(a: BigInt, b: BigInt): Boolean = {
    require(a >= BigInt(0) && b > BigInt(0))
    Modulo.mod(a + b, b) == Modulo.mod(a, b)
  }.holds
}

object DivisionAlgorithm {
  def divisionAlgorithm(a: BigInt, b: BigInt): (BigInt, BigInt) = {
    require(a >= BigInt(0) && b > BigInt(0))
    val q = a / b
    val r = a - (q * b)
    (q, r)
  }


  def divisionProperty(a: BigInt, b: BigInt): Boolean = {
    require(a >= BigInt(0) && b > BigInt(0))
    val (q, r) = divisionAlgorithm(a, b)
    a == b * q + r && 0 <= r && r < b
  }.holds
}