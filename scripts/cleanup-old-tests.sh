#!/bin/bash
# Cleanup script: remove old misplaced test files after migration
# Review this script before running it.

set -e

# Chapter 1
rm src/test/scala/verification/HelperTest.scala
rm -rf src/test/scala/verification

# Chapter 2
rm src/test/scala/v1/DivTest.scala
rm src/test/scala/v1/div/MainTest.scala
rm -rf src/test/scala/v1/div
rm src/test/scala/v1/div/properties/AdditionAndMultiplicationTest.scala
rm src/test/scala/v1/div/properties/ModOperationsTest.scala
rm src/test/scala/v1/div/properties/SummaryTest.scala
rm src/test/scala/v1/div/properties/ModIdentityTest.scala
rm src/test/scala/v1/div/properties/ModIdempotenceTest.scala
rm src/test/scala/v1/div/properties/ModSmallDividendTest.scala
rm src/test/scala/v1/div/properties/ModSumTest.scala
rm src/test/scala/v1/div/properties/ConsecutiveIntegersTest.scala
rm -rf src/test/scala/v1/div/properties
# rm -rf src/test/scala/v1/div  # already removed above

# Chapter 3
rm src/test/scala/v1/list/ListUtilsTest.scala
rm src/test/scala/v1/list/properties/ListUtilsPropertiesTest.scala
rm src/test/scala/v1/list/properties/SliceEquivalenceLemmasTest.scala
rm -rf src/test/scala/v1/list/properties
rm src/test/scala/v1/list/integral/IntegralTest.scala
rm src/test/scala/v1/list/integral/properties/IntegralPropertiesTest.scala
rm -rf src/test/scala/v1/list/integral/properties
rm -rf src/test/scala/v1/list/integral
rm -rf src/test/scala/v1/list

# Chapter 4
rm src/test/scala/v1/cycle/gap/GapCycleTest.scala
rm -rf src/test/scala/v1/cycle/gap
rm src/test/scala/v1/cycle/mod/ModCycleTest.scala
rm -rf src/test/scala/v1/cycle/mod
rm src/test/scala/v1/cycle/memory/MemCycleTest.scala
rm -rf src/test/scala/v1/cycle/memory
rm src/test/scala/v1/cycle/properties/CycleWithMemoryCheckModTest.scala
rm src/test/scala/v1/cycle/properties/MemCyclePropertiesTest.scala
rm -rf src/test/scala/v1/cycle/properties
rm src/test/scala/v1/cycle/integral/CycleIntegralTest.scala
rm src/test/scala/v1/cycle/integral/CycleWithMemoryIntegralTest.scala
rm src/test/scala/v1/cycle/integral/properties/CycleWithMemoryIntegralPropertiesTest.scala
rm -rf src/test/scala/v1/cycle/integral/properties
rm src/test/scala/v1/cycle/integral/classic/ClassicCycleIntegralTest.scala
rm src/test/scala/v1/cycle/integral/classic/properties/ClassicCycleIntegralPropertiesTest.scala
rm -rf src/test/scala/v1/cycle/integral/classic/properties
rm -rf src/test/scala/v1/cycle/integral/classic
rm src/test/scala/v1/cycle/integral/mod/ModCycleIntegralTest.scala
rm src/test/scala/v1/cycle/integral/mod/ModCycleIntegralPropertiesTest.scala
rm -rf src/test/scala/v1/cycle/integral/mod
rm -rf src/test/scala/v1/cycle/integral
rm -rf src/test/scala/v1/cycle

# Chapter 5
rm src/test/scala/v1/prime/PrimeTest.scala
rm src/test/scala/v1/prime/AllPrimesSoFarListTest.scala
rm -rf src/test/scala/v1/prime

# Chapter 6
rm src/test/scala/v1/seq/sieve/CycleSieveSequenceTest.scala
rm src/test/scala/v1/seq/sieve/SpecSieveSequenceTest.scala
rm -rf src/test/scala/v1/seq/sieve
rm -rf src/test/scala/v1/seq

echo "All old test files removed successfully."
