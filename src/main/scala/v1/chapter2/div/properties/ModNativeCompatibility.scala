package v1.chapter2.div.properties

import stainless.lang.*
import v1.chapter2.div.{Calc, DivMod}

object ModNativeCompatibility {

  def percentEqualsCalcMod(a: BigInt, b: BigInt): Boolean = {
    require(a >= BigInt(0))
    require(b > BigInt(0))

    val nativeDiv = a / b
    val nativeMod = a % b

    val calcDiv = Calc.div(a, b)
    val calcMod = Calc.mod(a, b)
    val calcSolved = DivMod(a, b, BigInt(0), a).solve

    assert(nativeDiv * b + nativeMod == a)
    assert(nativeMod >= BigInt(0))
    assert(nativeMod < b)

    assert(calcDiv == calcSolved.div)
    assert(calcMod == calcSolved.mod)
    assert(calcDiv * b + calcMod == a)
    assert(calcMod >= BigInt(0))
    assert(calcMod < b)

    ModIdempotence.modUnique(a, b, nativeDiv, nativeMod, calcDiv, calcMod)

    val nativeWitness = DivMod(a, b, nativeDiv, nativeMod)
    val calcWitness = DivMod(a, b, calcDiv, calcMod)

    assert(nativeWitness.isFinal)
    assert(calcWitness.isFinal)
    assert(nativeWitness.solve == nativeWitness)
    assert(calcWitness.solve == calcWitness)
    assert(nativeWitness.solve == calcWitness.solve)
    assert(nativeWitness == calcWitness)
    assert(nativeMod == calcMod)

    a % b == Calc.mod(a, b)
  }.holds
}
