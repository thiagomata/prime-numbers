package v1.cycle.memory.properties

import stainless.lang.*
import v1.Calc
import v1.cycle.memory.MemCycle
import v1.div.properties.{AdditionAndMultiplication, ModIdempotence}
import verification.Helper.assert

object MemCycleProperties {

  /**
   * Getting a cycle key value is the same
   * of getting the cycle values  of the mod of the key by the cycle size.
   *
   * cycle(key) == cycle.values(mod(key, cycle.size)).
   *
   * @param cycle Cycle
   * @param key BigInt
   * @return true if the property holds
   */
  def findValueInCycle(cycle: MemCycle, key: BigInt): Boolean = {
    require(key >= 0)
    require(cycle.size > 0)
    cycle(key) == cycle.values(Calc.mod(key, cycle.size))
  }.holds

  /**
   * For small values, querying the key in the cycle
   *   is the same of querying the key in the values.
   *
   * cycle(key) == cycle.values(key)
   *
   * @param cycle cycle
   * @param key BigInt
   * @return true if the property holds
   */
  def smallValueInCycle(cycle: MemCycle, key: BigInt): Boolean = {
    require(key >= 0)
    require(key < cycle.size)
    require(cycle.size > 0)
    cycle(key) == cycle.values(key)
  }.holds

  /**
   * Adding zero, one or many times the size loop in the key do not change its value.
   *
   * cycle(key) == cycle(key + cycle.size * m )
   *
   * @param cycle Cycle
   * @param key BigInt element key
   * @param m BigInt multiplier
   * @return
   */
  def valueMatchAfterManyLoops(cycle: MemCycle, key: BigInt, m: BigInt): Boolean = {
    require(key >= 0)
    require(cycle.size > 0)
    require(m >= 0)
    AdditionAndMultiplication.ATimesBSameMod(key, cycle.size, m)
    cycle(key) == cycle(key + cycle.size * m)
  }.holds

  /**
   * If two values are loops around the cycle.size,
   * they should have the same value.
   *
   * cycle(key + cycle.size * m1) == cycle(key + cycle.size * m2)
   *
   * @param cycle Cycle
   * @param key BigInt
   * @param m1 BigInt multiplier
   * @param m2 BigInt multiplier
   * @return
   */
  def valueMatchAfterManyLoopsInBoth(cycle: MemCycle, key: BigInt, m1: BigInt, m2: BigInt): Boolean = {
    require(key >= 0)
    require(cycle.size > 0)
    require(m1 >= 0)
    require(m2 >= 0)
    AdditionAndMultiplication.ATimesBSameMod(key, cycle.size, m1)
    AdditionAndMultiplication.ATimesBSameMod(key, cycle.size, m2)
    assert(cycle(key) == cycle(key + cycle.size * m1))
    assert(cycle(key) == cycle(key + cycle.size * m2))
    AdditionAndMultiplication.APlusMultipleTimesBSameMod(key, cycle.size, m1)
    AdditionAndMultiplication.APlusMultipleTimesBSameMod(key, cycle.size, m2)
    assert(Calc.mod(key, cycle.size) == Calc.mod(key + cycle.size * m1, cycle.size))
    assert(Calc.mod(key, cycle.size) == Calc.mod(key + cycle.size * m2, cycle.size))
    assert(cycle(key + cycle.size * m1) == cycle(key))
    assert(cycle(key + cycle.size * m2) == cycle(key))
    assert(cycle(key + cycle.size * m2) == cycle(Calc.mod(key,cycle.size)))
    assert(cycle(key + cycle.size * m1) == cycle(key + cycle.size * m2))
  }.holds

  /**
   * For every cycle, dividend and key
   * Calc.mod(Cycle(key), dividend) == Calc.mod(Cycle.values(Calc.mod(key, cycle.size)), dividend)
   *
   * @param cycle Cycle
   * @param dividend BigInt
   * @param key BigInt
   * @return true if property holds
   */
  def propagateModFromValueToCycle(cycle: MemCycle, dividend: BigInt, key: BigInt): Boolean = {
    require(key >= 0)
    require(dividend > 0)
    require(cycle.size > 0)
    val modKeySize = Calc.mod(key, cycle.size)
    Calc.mod(cycle(key),dividend) == Calc.mod(cycle.values(modKeySize),dividend)
  }.holds

  def assertCycleOfPosEqualsCycleOfModPos(cycle: MemCycle, position: BigInt): Boolean = {
    require(position >= 0)
    require(cycle.size > 0)

    val size = cycle.size

    assert(cycle(position) == cycle.apply(position))
    assert(cycle(position) == cycle.values(Calc.mod(position, size)))

    assert(ModIdempotence.modIdempotence(position, size))
    assert(Calc.mod(Calc.mod(position, size),size) == Calc.mod(position, size))
    assert(cycle(position) == cycle(Calc.mod(position, size)))
  }.holds
}