package v1.chapter4.cycle.memory.properties

import stainless.lang.*
import stainless.collection.List
import v1.chapter1.verification.Helper.assert
import v1.chapter2.div.Calc
import v1.chapter2.div.properties.{AdditionAndMultiplication, ModIdempotence, ModOperations}
import v1.chapter3.list.properties.ListRepeatProperties
import v1.chapter4.cycle.CycleUtils
import v1.chapter4.cycle.memory.MemCycle

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
   * A memory cycle backed by repeated physical storage has the same semantic
   * lookup as the original memory cycle.
   *
   * Math:
   *
   *   C      = cycle
   *   C_t    = repeatedCycle
   *   V      = C.values
   *   R      = repeat(V, times)
   *   n      = size(V)
   *   period = n * times
   *
   * Given:
   *
   *   C_t.values = R
   *
   * Then:
   *
   *   C_t(position)
   *     = R(mod(position, period))
   *     = V(mod(mod(position, period), n))
   *     = V(mod(position, n))
   *     = C(position)
   *
   * The proof deliberately separates construction from lookup equality. Callers
   * are responsible for building a valid `MemCycle` from the repeated storage;
   * this lemma only says that once such a cycle exists, the larger physical
   * period does not change the value read at any position.
   */
  def assertRepeatedValuesCycleMatches(
    cycle: MemCycle,
    repeatedCycle: MemCycle,
    times: BigInt,
    position: BigInt
  ): Boolean = {
    require(times > BigInt(0))
    require(position >= BigInt(0))
    require(cycle.size > BigInt(0))
    require(repeatedCycle.values == ListRepeatProperties.repeat(cycle.values, times))

    val values = cycle.values
    val repeatedValues = repeatedCycle.values
    val repeatedIndex = Calc.mod(position, values.size * times)
    val originalIndex = Calc.mod(position, values.size)

    assert(ListRepeatProperties.assertRepeatSize(values, times))
    assert(repeatedCycle.size == values.size * times)

    assert(findValueInCycle(repeatedCycle, position))
    assert(repeatedCycle(position) == repeatedValues(repeatedIndex))

    assert(ListRepeatProperties.assertRepeatedIndex(values, times, repeatedIndex))
    assert(repeatedValues(repeatedIndex) == values(Calc.mod(repeatedIndex, values.size)))

    assert(ModOperations.modByPositiveMultipleThenBase(position, values.size, times))
    assert(Calc.mod(repeatedIndex, values.size) == originalIndex)
    assert(repeatedValues(repeatedIndex) == values(originalIndex))

    assert(findValueInCycle(cycle, position))
    assert(cycle(position) == values(originalIndex))

    repeatedCycle(position) == cycle(position)
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
