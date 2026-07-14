package v1.chapter4.cycle.properties

import stainless.lang.*
import v1.chapter1.verification.Helper.assert
import v1.chapter2.div.Calc
import v1.chapter2.div.properties.{AdditionAndMultiplication, ModIdempotence, ModOperations}
import v1.chapter4.cycle.CycleUtils
import v1.chapter4.cycle.mod.ModCycle
import v1.chapter4.cycle.memory.MemCycle

object CycleProperties {

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
  def findValueInCycle(cycle: ModCycle, key: BigInt): Boolean = {
    require(key >= 0)
    require(cycle.period > 0)
    cycle(key) == cycle.values(Calc.mod(key, cycle.period))
  }.holds

  /**
   * Bridge lemma: If ModCycle and MemCycle have the same values,
   * they produce the same result at any position.
   */
  def assertModCycleEqualsMemCycle(
    modCycle: ModCycle,
    memCycle: MemCycle,
    position: BigInt
  ): Boolean = {
    require(modCycle.values == memCycle.values)
    require(modCycle.period == memCycle.period)
    require(position >= 0)
    require(position < modCycle.period)
    modCycle(position) == memCycle(position)
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
  def smallValueInCycle(cycle: ModCycle, key: BigInt): Boolean = {
    require(key >= 0)
    require(key < cycle.period)
    require(cycle.period > 0)
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
  def valueMatchAfterManyLoops(cycle: ModCycle, key: BigInt, m: BigInt): Boolean = {
    require(key >= 0)
    require(cycle.period > 0)
    require(m >= 0)
    AdditionAndMultiplication.ATimesBSameMod(key, cycle.period, m)
    cycle(key) == cycle(key + cycle.period * m)
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
  def valueMatchAfterManyLoopsInBoth(cycle: ModCycle, key: BigInt, m1: BigInt, m2: BigInt): Boolean = {
    require(key >= 0)
    require(cycle.period > 0)
    require(m1 >= 0)
    require(m2 >= 0)
    AdditionAndMultiplication.ATimesBSameMod(key, cycle.period, m1)
    AdditionAndMultiplication.ATimesBSameMod(key, cycle.period, m2)
    assert(cycle(key) == cycle(key + cycle.period * m1))
    assert(cycle(key) == cycle(key + cycle.period * m2))
    AdditionAndMultiplication.APlusMultipleTimesBSameMod(key, cycle.period, m1)
    AdditionAndMultiplication.APlusMultipleTimesBSameMod(key, cycle.period, m2)
    assert(Calc.mod(key, cycle.period) == Calc.mod(key + cycle.period * m1, cycle.period))
    assert(Calc.mod(key, cycle.period) == Calc.mod(key + cycle.period * m2, cycle.period))
    assert(cycle(key + cycle.period * m1) == cycle(key))
    assert(cycle(key + cycle.period * m2) == cycle(key))
    assert(cycle(key + cycle.period * m2) == cycle(Calc.mod(key,cycle.period)))
    assert(cycle(key + cycle.period * m1) == cycle(key + cycle.period * m2))
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
  def propagateModFromValueToCycle(cycle: ModCycle, dividend: BigInt, key: BigInt): Boolean = {
    require(key >= 0)
    require(dividend > 0)
    require(cycle.period > 0)
    val modKeySize = Calc.mod(key, cycle.period)
    Calc.mod(cycle(key),dividend) == Calc.mod(cycle.values(modKeySize),dividend)
  }.holds

  def assertCycleOfPosEqualsCycleOfModPos(cycle: ModCycle, position: BigInt): Boolean = {
    require(position >= 0)
    require(cycle.period > 0)

    val size = cycle.period

    assert(cycle(position) == cycle.apply(position))
    assert(cycle(position) == cycle.values(Calc.mod(position, size)))

    assert(ModIdempotence.modIdempotence(position, size))
    assert(Calc.mod(Calc.mod(position, size),size) == Calc.mod(position, size))
    assert(cycle(position) == cycle(Calc.mod(position, size)))
  }.holds

  def cycleValuePositiveOrZero(cycle: ModCycle, pos: BigInt): Boolean = {
    require(pos >= 0)
    require(cycle.period > 0)
    findValueInCycle(cycle, pos)
    val idx = Calc.mod(pos, cycle.period)
    assert(idx >= 0)
    assert(idx < cycle.period)
    CycleUtils.checkPositiveOrZeroAtIndex(cycle.values, idx)
    cycle(pos) >= 0
  }.holds

  def rotateAtValue(cycle: ModCycle, k: BigInt, i: BigInt): Boolean = {
    require(k >= 0)
    require(i >= 0)
    require(cycle.period > 0)

    val size = cycle.period
    val rotatedCycle = cycle.rotateAt(k)

    findValueInCycle(rotatedCycle, i)
    val modI = Calc.mod(i, size)
    assert(rotatedCycle(i) == rotatedCycle.values(modI))

    CycleUtils.collectRotatedValueAt(cycle.values, k, size, modI)
    assert(rotatedCycle.values(modI) == cycle.values(Calc.mod(k + modI, size)))

    ModIdempotence.modIdempotence(i, size)
    ModOperations.modAdd(k, size, Calc.mod(i, size))
    ModOperations.modAdd(k, size, i)
    assert(Calc.mod(k + modI, size) == Calc.mod(k + i, size))

    findValueInCycle(cycle, k + i)
    assert(cycle(k + i) == cycle.values(Calc.mod(k + i, size)))

    rotatedCycle(i) == cycle(k + i)
  }.holds
}