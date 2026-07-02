# Objects and Properties Catalog

Complete inventory of all verified `.holds` lemmas across the codebase.
Last updated: 2026-07-02

**Total: 487 verified lemmas** across 6 chapters.

| Chapter                               | Lemmas |
|---------------------------------------|--------|
| ch1 (Verification Helpers)            | 0      |
| ch2 (Div/Mod)                         | 39     |
| ch3 (Lists, Integrals, Bounds)        | 87     |
| ch4 (Cycles, Cycle Integrals, Filter) | 106    |
| ch5 (Primes, Coprimality)             | 41     |
| ch6 (Sieve Sequence, Pipeline)        | 214    |

---

# Domain 1: Verification Helpers

## 1.1 Helper (`v1.chapter1.verification.Helper`)

`assert`, `equality`, `equals` — assertion helpers, no `.holds` lemmas.

---

# Domain 2: Division and Modulo

## 2.1 ModOne (`v1.chapter2.div.properties.ModOne`)

| Lemma               | Statement        |
|---------------------|------------------|
| **modOneIsZero(n)** | `mod(n, 1) == 0` |
| **divOneIsN(n)**    | `div(n, 1) == n` |

## 2.2 ModIdentity (`v1.chapter2.div.properties.ModIdentity`)

| Lemma              | Statement                                       |
|--------------------|-------------------------------------------------|
| **modIdentity(a)** | `mod(a, a) == 0 && div(a, a) == 1` for `a != 0` |
| **longProof(n)**   | `DivMod(n,n,0,n).solve == DivMod(n,n,1,0)`      |

## 2.3 ModSmallDividend (`v1.chapter2.div.properties.ModSmallDividend`)

| Lemma                     | Statement                                         |
|---------------------------|---------------------------------------------------|
| **modSmallDividend(a,b)** | `mod(a,b) == a && div(a,b) == 0` for `b > a >= 0` |

## 2.4 ModSum (`v1.chapter2.div.properties.ModSum`)

| Lemma                           | Statement                          |
|---------------------------------|------------------------------------|
| **sumSymmetricalMods(b,step)**  | `mod(step,b) + mod(b-step,b) == b` |
| **checkAllPreviousValues(a,b)** | `mod(a,b) == a` for `a < b`        |
| **checkValueShift(a,b)**        | `mod(a,b) == mod(a-b,b)`           |

## 2.5 ModIdempotence (`v1.chapter2.div.properties.ModIdempotence`)

| Lemma                                             | Statement                                                                  |
|---------------------------------------------------|----------------------------------------------------------------------------|
| **modIdempotencePositiveA(a,b)**                  | `mod(a,b) == mod(mod(a,b), b)`                                             |
| **modUniqueDiv(x,y)**                             | `x.solve == y.solve` when `x.a == y.a` and `x.b == y.b`                    |
| **modUnique(a,b,divx,modx,divy,mody)**            | `DivMod(a,b,divx,modx).solve == DivMod(a,b,divy,mody).solve`               |
| **modModPlus(a,b,c)**                             | `mod(mod(a,b)+mod(c,b),b) == mod(a,b)+mod(c,b)-b*div(mod(a,b)+mod(c,b),b)` |
| **modModMinus(a,b,c)**                            | `mod(mod(a,b)-mod(c,b),b) == mod(a,b)-mod(c,b)-b*div(mod(a,b)-mod(c,b),b)` |
| **assertDivModWithMoreDivAndLessModSameSolution** | `DivMod(a,b, div+1, mod-b).solve == DivMod(a,b, div, mod).solve`           |
| **assertDivModWithLessDivAndMoreModSameSolution** | `DivMod(a,b, div-1, mod+b).solve == DivMod(a,b, div, mod).solve`           |

## 2.6 ModOperations (`v1.chapter2.div.properties.ModOperations`)

| Lemma                                           | Statement                                     |
|-------------------------------------------------|-----------------------------------------------|
| **modByPositiveMultipleThenBase(a,base,times)** | `mod(mod(a,base*times), base) == mod(a,base)` |
| **modAdd(a,b,c)**                               | `mod(a+c,b) == mod(mod(a,b)+mod(c,b),b)`      |
| **modZeroPlusC(a,b,c)**                         | If `mod(a,b)==0`: `mod(a+c,b) == mod(c,b)`    |
| **modLess(a,b,c)**                              | `mod(a-c,b) == mod(mod(a,b)-mod(c,b),b)`      |
| **addOne(a,b)**                                 | Three cases for `div(a+1,b)` and `mod(a+1,b)` |

## 2.7 AdditionAndMultiplication (`v1.chapter2.div.properties.AdditionAndMultiplication`)

| Lemma                                 | Statement                                                     |
|---------------------------------------|---------------------------------------------------------------|
| **APlusBSameModPlusDiv(a,b)**         | `mod(a,b) == mod(a+b,b)` and `div(a,b)+1 == div(a+b,b)`       |
| **ALessBSameModDecreaseDiv(a,b)**     | `mod(a,b) == mod(a-b,b)` and `div(a,b)-1 == div(a-b,b)`       |
| **ATimesBSameMod(a,b,m)**             | `mod(a,b) == mod(a+b*m,b)`                                    |
| **APlusMultipleTimesBSameMod(a,b,m)** | Inductive version for `m >= 0`                                |
| **ALessMultipleTimesBSameMod(a,b,m)** | `mod(a,b) == mod(a-b*m,b)` for `m >= 0`                       |
| **MoreDivLessModManyTimes**           | Increasing div by m, decreasing mod by m*b preserves solution |
| **LessDivMoreModManyTimes**           | Decreasing div by m, increasing mod by m*b preserves solution |

## 2.8 ConsecutiveIntegers (`v1.chapter2.div.properties.ConsecutiveIntegers`)

| Lemma                                         | Statement                                                 |
|-----------------------------------------------|-----------------------------------------------------------|
| **nonzeroAfterZero(a,p,d)**                   | At most one zero in p consecutive values                  |
| **existsZero(n,p)**                           | Among p consecutive integers, at least one divisible by p |
| **exactlyOneZeroInConsecutive(n,p)**          | Exactly one zero in p consecutive                         |
| **atMostOneZero(n,p,i,j)**                    | Uniqueness of zero position                               |
| **zeroRepeatsEveryP(n,p,m)**                  | Zero repeats with period p                                |
| **zerosInMultipleBlocks(n,p,m)**              | Count of zeros in m+1 blocks is m+1                       |
| **countModZeroEqualsM(a,p,m)**                | m multiples of p in m*p consecutive                       |
| **twoPrimesDensity(a,p1,p2,m)**               | Density for two primes                                    |
| **densityForDivisor(a,modulus,divisor,m)**    | Density for divisor of modulus                            |
| **densityPreservedAfterFiltering(a,p1,p2,m)** | Density preserved after removing p1-multiples             |
| **densityForPrimeList(a,primes,M,m)**         | Density for a list of primes dividing M                   |

## 2.9 Summary (`v1.chapter2.div.properties.Summary`)

| Lemma                        | Statement                                   |
|------------------------------|---------------------------------------------|
| **PropertySummary(a,b,c,m)** | Conjunction of all major div/mod properties |

---

# Domain 3: Lists, Bounds, Integrals

## 3.1 ListUtils (`v1.chapter3.list.ListUtils`)

| Lemma                            | Statement                                        |
|----------------------------------|--------------------------------------------------|
| **listSumAddValue(list,value)**  | `sum(List(value) ++ list) == value + sum(list)`  |
| **listCombine(listA,listB)**     | `sum(listA ++ listB) == sum(listA) + sum(listB)` |
| **listSwap(listA,listB)**        | `sum(listA ++ listB) == sum(listB ++ listA)`     |
| **listAddValueTail(list,value)** | `sum(list ++ List(value)) == value + sum(list)`  |

## 3.2 ListBoundUtils (`v1.chapter3.list.ListBoundUtils`)

| Lemma                                                      | Statement                                                |
|------------------------------------------------------------|----------------------------------------------------------|
| **assertAppendGreaterThan(listA,listB,value)**             | `allGreaterThan(A++B, value)` from both halves           |
| **assertSplitAtPreservesAllGreaterThan(list,index,value)** | `splitAt` preserves `allGreaterThan` on both halves      |
| **assertAppendLessThan(listA,listB,bound)**                | `allLessThan(A++B, bound)` from both halves              |
| **assertSplitAtPreservesAllLessThan(list,index,bound)**    | `splitAt` preserves `allLessThan` on both halves         |
| **assertTransitiveLessThan(list,b,b2)**                    | `allLessThan(list,b) && b <= b2 => allLessThan(list,b2)` |
| **assertGreaterThanAtIndex(list,value,pos)**               | `allGreaterThan(list,v) => list(pos) > v`                |
| **assertLessThanAtIndex(list,bound,pos)**                  | `allLessThan(list,b) => list(pos) < b`                   |
| **assertGreaterThanHeadTail(list,value)**                  | `allGreaterThan(list,v) => head > v && tail satisfies`   |
| **assertTailShiftLeft(list,position)**                     | `list(position) == list.tail(position - 1)`              |

## 3.3 ListUtilsProperties (`v1.chapter3.list.properties.ListUtilsProperties`)

| Lemma                                              | Statement                                                         |
|----------------------------------------------------|-------------------------------------------------------------------|
| **assertAppendToSlice(list,from,to)**              | `slice(from,to) == slice(from,to-1) ++ List(list(to))`            |
| **accessTailShiftRight(list,position)**            | `list.tail(position) == list(position + 1)`                       |
| **assertLastEqualsLastPosition(list)**             | `list.last == list(list.size - 1)`                                |
| **assertSplitAtRecombines(list,index)**            | `front ++ back == list` (keystone)                                |
| **checkAllBiggerThanValueAtIndex(list,value,pos)** | `checkAllBiggerThanValue(list,v) => list(pos) > v`                |
| **checkAllBiggerThanValueHeadTail(list,value)**    | Decomposition of checkAllBiggerThanValue                          |
| **assertSplitAtOne(list)**                         | `splitAt(list,1)._2 == list.tail && ._1 == List(list.head)`       |
| **assertAppendApplyLeft(left,right,k)**            | `(left ++ right)(k) == left(k)` for `k < left.size`               |
| **assertSumPositive(list)**                        | `allGreaterThan(list,0) && nonEmpty => sum(list) > 0`             |
| **assertAppendApplyRight(left,right,k)**           | `(left ++ right)(k) == right(k - left.size)` for `k >= left.size` |

## 3.4 ShiftedList (`v1.chapter3.list.ShiftedList`)

| Lemma                                                    | Statement                                                                |
|----------------------------------------------------------|--------------------------------------------------------------------------|
| **assertAdjacentDifferenceEqualsGap(position)**          | `apply(i+1) - apply(i) == gaps(i)` (instance)                            |
| **assertSamePeriod(other)**                              | `size == other.size` (instance)                                          |
| **assertShiftedApplyIsOriginalPlusOne(origHead,gaps,i)** | `shifted.apply(i) == orig.apply(i+1)`                                    |
| **assertGapTranslation(origHead,gaps,i)**                | `shifted.apply(i+1)-shifted.apply(i) == orig.apply(i+2)-orig.apply(i+1)` |

## 3.5 RotationProperties (`v1.chapter3.list.properties.RotationProperties`)

| Lemma                                            | Statement                                           |
|--------------------------------------------------|-----------------------------------------------------|
| **assertAppendContainsLeft(left,right,x)**       | `left.contains(x) => (left++right).contains(x)`     |
| **assertAppendContainsRight(left,right,x)**      | `right.contains(x) => (left++right).contains(x)`    |
| **assertAppendContainsDecompose(left,right,x)**  | Disjunctive decomposition of ++ membership          |
| **assertAppendContainsSwap(left,right,x)**       | Membership is order-independent over ++             |
| **assertRotateContainsForward(list,index,x)**    | Rotation preserves elements (forward)               |
| **assertRotateContainsBackward(list,index,x)**   | Rotation preserves elements (backward)              |
| **assertRotateSameSize(list,index)**             | `rotateAt(list,index).size == list.size`            |
| **assertRotateSameSum(list,index)**              | `sum(rotateAt(list,index)) == sum(list)`            |
| **assertRotateSameLowerBound(list,index,value)** | Rotation preserves `allGreaterThan`                 |
| **assertRotateSameUpperBound(list,index,bound)** | Rotation preserves `allLessThan`                    |
| **assertRotatedAtIndexPlusOne(list,k)**          | `rotateAt(list,1)(k) == list(k+1)` for `k+1 < size` |

## 3.6 ListRepeatProperties (`v1.chapter3.list.properties.ListRepeatProperties`)

| Lemma                                                            | Statement                                                |
|------------------------------------------------------------------|----------------------------------------------------------|
| **assertModStableUnderSize(index,size)**                         | `mod(index-size, size) == mod(index, size)`              |
| **assertRepeatSumMultiplier(list,times)**                        | `sum(repeat(list,times)) == times * sum(list)`           |
| **assertConcatAccessLeft(listA,listB,index)**                    | `(A++B)(index) == A(index)` for `index < A.size`         |
| **assertConcatAccessRight(listA,listB,index)**                   | `(A++B)(index) == B(index-A.size)` for `index >= A.size` |
| **assertRepeatSize(list,times)**                                 | `repeat(list,times).size == list.size * times`           |
| **assertRepeatAllGreaterThan(list,times,value)**                 | Repeat preserves `allGreaterThan`                        |
| **assertRepeatConcat(list,times)**                               | `repeat(list,times) == list ++ repeat(list,times-1)`     |
| **assertRepeatSumDecomposition(list,times)**                     | Sum decomposes as head + rest                            |
| **assertRepeatSumTimes(list,times)**                             | `sum(repeat(list,times)) == sum(list) * times`           |
| **assertRepeatedIndex(list,times,index)**                        | `repeat(list,times)(index) == list(mod(index,size))`     |
| **assertMergePreservesListSum(values,mergeIndex)**               | Merge preserves list sum                                 |
| **assertMergeSumBase(oldValues,newValues)**                      | Base case for merge sum                                  |
| **assertMergeSumStep(oldValues,newValues)**                      | Step case for merge sum                                  |
| **assertSumNewValuesAfterMerge(oldValues,newValues,mergeIndex)** | New values sum after merge                               |
| **assertMergeSumPreserved(oldValues,newValues)**                 | `sum(newValues) == sum(oldValues)`                       |

## 3.7 RepeatedListProperties (`v1.chapter3.list.properties.RepeatedListProperties`)

| Lemma                        | Statement                                           |
|------------------------------|-----------------------------------------------------|
| **assertSumBase**            | `RepeatedList(list,1).sum == sum(list)`             |
| **assertSumStep**            | Step case for repeated sum                          |
| **assertSumMultiplier**      | `RepeatedList(list,times).sum == times * sum(list)` |
| **assertElementNotMultiple** | Repeated list element not multiple of filter        |

## 3.8 IntegralProperties (`v1.chapter3.list.integral.properties.IntegralProperties`)

| Lemma                                           | Statement                                             |
|-------------------------------------------------|-------------------------------------------------------|
| **assertHeadValueMatchDefinition(integral)**    | `integral.head == integral.list.head + integral.init` |
| **assertAccDifferenceEqualsTailHead(integral)** | `acc(1) - acc(0) == list(1)`                          |
| **assertAccDiffMatchesList(integral,position)** | `acc(pos+1) - acc(pos) == list(pos+1)`                |
| **assertAccMatchesApply(integral,position)**    | `acc(position) == apply(position)`                    |
| **assertSizeAccEqualsSizeList(integral)**       | `acc.size == list.size`                               |
| **assertLastEqualsSum(integral)**               | `integral.last == init + sum(list)`                   |
| **assertIntegralEqualsSum(integral,position)**  | `apply(pos) == init + sum(slice(list,0,pos))`         |
| **assertLast(integral)**                        | `apply(size-1) == integral.last`                      |
| **assertIntegralStrictlyIncreasing(integral,a,b)** | `allGreaterThan(list,0) && b > a => apply(b) > apply(a)` |
| **assertGapsPositive(integral,pos)**              | `apply(pos+1) > apply(pos) => list(pos+1) > 0` |

## 3.9 SortedList (`v1.chapter3.list.SortedList`)

| Lemma                                      | Statement                              |
|--------------------------------------------|----------------------------------------|
| **insertSorted(x,list)**                   | Postcondition: sorted input implies sorted output |
| **sortFiltered(list)**                     | Postcondition: output is ascending     |
| **assertSortFilteredAscending(list)**      | `sortFiltered` produces ascending list |
| **assertInsertSortedAscending(x,list)**    | `insertSorted` preserves ascending     |
| **assertTailAscending(list)**              | Tail of ascending is ascending         |
| **assertRemoveKeepsAscending(list,index)** | `removeAt` preserves ascending |
| **assertIsAscendingAtIndex(list,i)** | `isAscending(list) => list(i+1) > list(i)` for valid i |

## 3.10 MinBoundList (`v1.chapter3.list.MinBoundList`)

| Lemma                                                         | Statement                    |
|---------------------------------------------------------------|------------------------------|
| **assertTailGreaterThan(list,lowerBound)**                    | Tail preserves lower bound   |
| **assertFilterPreservesGreaterThan(list,lowerBound,divisor)** | Filter preserves lower bound |

## 3.11 MaxBoundList (`v1.chapter3.list.MaxBoundList`)

| Lemma                                                      | Statement                    |
|------------------------------------------------------------|------------------------------|
| **assertTailLessThan(list,upperBound)**                    | Tail preserves upper bound   |
| **assertFilterPreservesLessThan(list,upperBound,divisor)** | Filter preserves upper bound |

## 3.12 ListProduct (`v1.chapter3.list.properties.ListProduct`)

| Lemma                         | Statement                                           |
|-------------------------------|-----------------------------------------------------|
| **singletonProduct(x)**       | `product(List(x)) == x`                             |
| **productPullOutElement**     | `product(A ++ List(e) ++ B) == e * product(A ++ B)` |
| **productConcatLemma**        | `product(A ++ B) == product(A) * product(B)`        |
| **productConcatCommutative**  | `product(A ++ B) == product(B ++ A)`                |
| **positiveProduct(elements)** | Positive elements => positive product               |

## 3.13 ListProductDiv (`v1.chapter3.list.properties.ListProductDiv`)

| Lemma                             | Statement                                  |
|-----------------------------------|--------------------------------------------|
| **ListProductDiv**                | `product(elements) mod elements.head == 0` |
| **allElementsDivideProduct**      | Every element divides the product          |
| **insertedElementDividesProduct** | Inserted element divides resulting product |

## 3.14 SliceEquivalenceLemmas (`v1.chapter3.list.properties.SliceEquivalenceLemmas`)

| Lemma                                   | Statement                                |
|-----------------------------------------|------------------------------------------|
| **sliceEqualsSpec**                     | `headRecursiveSlice == indexRangeValues` |
| **appendOne**                           | `list ++ List(e) == list :+ e`           |
| **appendCons**                          | `Cons(h,t) :+ e == Cons(h, t :+ e)`      |
| **tailHeadAndIndexRangeSlicesAreEqual** | All three slicing strategies equivalent  |

---

# Domain 4: Cycles and Cycle Integrals

## 4.1 CycleUtils (`v1.chapter4.cycle.CycleUtils`)

| Lemma                          | Statement                                        |
|--------------------------------|--------------------------------------------------|
| **checkPositiveOrZeroAtIndex** | All non-negative => indexed element non-negative |
| **checkPositiveOrZeroCons**    | Cons preserves checkPositiveOrZero               |
| **collectRotatedValueAt**      | Rotated collection value at position             |

## 4.2 CycleProperties (`v1.chapter4.cycle.properties.CycleProperties`)

| Lemma                                   | Statement                                            |
|-----------------------------------------|------------------------------------------------------|
| **findValueInCycle**                    | `cycle(key) == cycle.values(mod(key,size))`          |
| **assertModCycleEqualsMemCycle**        | ModCycle and MemCycle agree for same values          |
| **smallValueInCycle**                   | `key < size => cycle(key) == cycle.values(key)`      |
| **valueMatchAfterManyLoops**            | `cycle(key) == cycle(key + size*m)`                  |
| **valueMatchAfterManyLoopsInBoth**      | Both m1 and m2 cases hold                            |
| **propagateModFromValueToCycle**        | Mod propagates from arbitrary position to base range |
| **assertCycleOfPosEqualsCycleOfModPos** | `cycle(pos) == cycle.values(mod(pos,size))`          |
| **cycleValuePositiveOrZero**            | All values >= 0 => cycle(pos) >= 0                   |
| **rotateAtValue**                       | `rotateAt(cycle,k)(i) == cycle(i+k)`                 |

## 4.3 MemCycleProperties (`v1.chapter4.cycle.memory.properties.MemCycleProperties`)

| Lemma                                   | Statement                                   |
|-----------------------------------------|---------------------------------------------|
| **findValueInCycle**                    | `cycle(key) == cycle.values(mod(key,size))` |
| **smallValueInCycle**                   | Direct lookup when key < size               |
| **assertRepeatedValuesCycleMatches**    | Repeating cycle values preserves value      |
| **valueMatchAfterManyLoops**            | `cycle(key) == cycle(key + size*m)`         |
| **valueMatchAfterManyLoopsInBoth**      | Both m1 and m2                              |
| **propagateModFromValueToCycle**        | Mod propagation to base range               |
| **assertCycleOfPosEqualsCycleOfModPos** | Equivalence chain                           |

## 4.4 CycleCheckMod (`v1.chapter4.cycle.memory.properties.CycleCheckMod`)

| Lemma                           | Statement                                      |
|---------------------------------|------------------------------------------------|
| **forAnyCheckModValuesRemains** | `checkMod` preserves `cycle.values`            |
| **notEvaluatedNotInTheList**    | Unevaluated dividend not in tracking lists     |
| **evaluatedInSomeList**         | After checkMod, dividend in some tracking list |
| **oneListNotInOther**           | Dividend in at most one tracking list          |
| **ifInAllModAll**               | All-values-zero classification correct         |
| **ifInSomeModSome**             | Some-values-zero classification correct        |
| **ifInNoneModNone**             | None-values-zero classification correct        |
| **allModZeroPropagate**         | All-zero class propagates correctly            |
| **noModZeroPropagate**          | No-zero class propagates correctly             |
| **someModZeroPropagate**        | Some-zero class propagates correctly           |

## 4.5 RecursiveCycle (`v1.chapter4.cycle.recursive.RecursiveCycle`)

| Lemma                        | Statement                                               |
|------------------------------|---------------------------------------------------------|
| **applyStructure**           | `pos < size => values(pos); else values(mod(pos,size))` |
| **cycleValuePositiveOrZero** | All >= 0 => apply(pos) >= 0                             |
| **cycleValueBiggerThan**     | All > x => apply(pos) > x                               |
| **rotateAtValue**            | Rotation matches expected                               |

## 4.6 RecursiveCycleMatchesModCycle (`v1.chapter4.cycle.recursive.properties.RecursiveCycleMatchesModCycle`)

| Lemma                                              | Statement                                             |
|----------------------------------------------------|-------------------------------------------------------|
| **assertCycleAndRecursiveCycleMathForSmallValues** | ModCycle and RecursiveCycle agree for small positions |

## 4.7 GapCycle (`v1.chapter4.cycle.gap.GapCycle`)

| Lemma                                                    | Statement                                             |
|----------------------------------------------------------|-------------------------------------------------------|
| **assertMemCycleValuesPositive(gc)**                     | All memCycle.values > 0                               |
| **assertCumulativeSumPositive(gc,pos)**                  | `cumulativeSum(pos) > 0`                              |
| **assertAllGreaterThanImpliesCheckPositiveOrZero(list)** | `allGreaterThan(list,0) => checkPositiveOrZero(list)` |

## 4.8 CycleIntegralProperties (`v1.chapter4.cycle.integral.recursive.properties.CycleIntegralProperties`)

| Lemma                                                      | Statement                                                     |
|------------------------------------------------------------|---------------------------------------------------------------|
| **assertRepeatedValuesIntegralMatches**                    | `repeatedCI(pos) == originalCI(pos)` for `pos < originalSize` |
| **assertCycleIntegralIncreasing(ci,a,b)**                  | Positive gaps => `ci(b) > ci(a)` for `b > a`                  |
| **assertCycleIntegralEqualsSumFirstPosition(ci)**          | `ci(0) == init + cycle(0)`                                    |
| **assertCycleIntegralEqualsSumSmallPositions(ci,pos)**     | `ci(pos) == sum(first-values-slice)` by induction             |
| **assertCycleIntegralEqualsSliceSum(ci,pos)**              | `ci(pos) == sum(slice of cycle values)`                       |
| **assertNextPosition(ci,pos)**                             | `ci(pos) == ci(pos-1) + cycle(pos)`                           |
| **assertDiffEqualsCycleValue(ci,pos)**                     | `ci(pos+1) - ci(pos) == cycle(pos+1)`                         |
| **assertSameDiffAfterCycle(ci,pos)**                       | `ci(b+size)-ci(a+size) == ci(b)-ci(a)`                        |
| **assertLastElementBeforeLoop(ci)**                        | `ci(size-1) == sum(first-values-slice)`                       |
| **assertSumModValueAsListEqualsCycleIntegralLoop(ci,pos)** | `ci(pos) == sum(mod-values-list)`                             |
| **assertCycleIntegralEqualsSumOfModValuesAsList(ci,pos)**  | Wrapper for above                                             |
| **assertFirstValuesAsSliceEqualsModValuesAsList(ci,pos)**  | Slice == mod-values for small positions                       |
| **assertCycleValuePositive(ci,pos)**                       | `cycle(pos) > 0` when all values > 0                          |
| **assertCycleIntegralPositive(ci,pos)**                    | `ci(pos) > 0` when init >= 0 and all values > 0               |
| **assertConsecutiveGapSumEqualsDiff(ci,k)**                | `ci(k+1)-ci(k-1) == cycle(k)+cycle(k+1)`                      |

## 4.9 ClassicCycleIntegralProperties (`v1.chapter4.cycle.integral.classic.properties.ClassicCycleIntegralProperties`)

Same 10 properties as CycleIntegralProperties (§4.8), for `ClassicCycleIntegral`. See source for full listing.

## 4.10 CycleIntegralOnesProperties (`v1.chapter4.cycle.integral.recursive.properties.CycleIntegralOnesProperties`)

| Lemma                                                     | Statement                                   |
|-----------------------------------------------------------|---------------------------------------------|
| **assertCycleIntegralOfOnes(init,pos)**                   | For unit cycle: `ci(pos) == init + pos + 1` |
| **assertCycleIntegralOfOnesStrictlyIncreasing(init,a,b)** | `ci(b) > ci(a)` for `b > a` with unit cycle |

## 4.11 CycleIntegralFilterProperties (`v1.chapter4.cycle.integral.recursive.properties.CycleIntegralFilterProperties`)

| Lemma                                       | Statement                                                                          |
|---------------------------------------------|------------------------------------------------------------------------------------|
| **assertCITelescopeRecurrence(ci,from,to)** | `ci(to)-ci(from) == cycle(to)+(ci(to-1)-ci(from))`                                 |
| **assertSurvivorAtNotMultiple**             | `mod(survivors(index), fv) != 0` for all survivors                                 |
| **assertCIShiftEqualsSum**                  | `ci(pos + size) - ci(pos) == ci.sum`                                               |
| **assertMergedGapIsCITelescope**            | `ci(to) - ci(from) > 0` for consecutive survivors                                  |
| **assertGapsFromValuesAtIndex**             | `gapsFromValues(list)(index) == list(index+1) - list(index)`                       |
| **assertGapsFromValuesSize**                | `gapsFromValues(list).size + 1 == list.size`                                       |
| **assertFirstSurvivorHead**                 | `survivorValues(ci,fv,start,count).head == ci(start)`                              |
| **assertNewCIGeneratesFiltered**            | `newCI(pos) == survivors(pos)` with correct gap cycle                              |
| **assertNewCIMatchesSurvivors**             | `newCI(pos) == survivors(pos + 1)`                                                 |
| **assertSameBeforeMerge**                   | `newCI.cycle(until) == oldCI.cycle(until)` for `until < mergeIndex`                |
| **assertShiftAtMerge**                      | `newCI.cycle(mergeIndex) == oldCI.cycle(mergeIndex) + oldCI.cycle(mergeIndex+1)`   |
| **assertShiftAfterMerge**                   | `newCI.cycle(until) == oldCI.cycle(until+1)` for `until > mergeIndex`              |
| **assertRemoveOneMultiple**                 | Removing one multiple at position correctly updates the integral                   |
| **assertFindFirstMultipleCorrect**          | `findFirstMultiple(ci,fv,start,until)` returns first pos with `mod(ci(pos),fv)==0` |
| **assertSameCIWithSameCycle**               | Same cycle values + same init => identical `apply` at all positions                |
| **assertReplicatedCycleValueEqual**         | `replicatedCI(pos) == originalCI(pos)` when pos in original range                  |
| **assertRemoveMultipleModNotZero**          | After removing a multiple position, merged gap `mod fv != 0`                       |
| **assertCycleAtSizeMatch**                  | `oldCI.cycle(pos) == newCI.cycle(pos)` at matching positions                       |
| **assertNewCIAtSizeEqualsOld**              | `newCI(0) == oldCI(0) && newCI.cycle.size + 1 == oldCI.cycle.size`                 |
| **assertGapsFromSurvivorsMatchCI**          | `newCI.cycle(pos) == survivors(pos+1) - survivors(pos)`                            |
| **assertFilterMergeComposition**            | Filter-then-merge produces correct CI matching survivors                           |
| **assertNextGapsValid**                     | `newCI` gaps are positive and `mod != 0` for filter value                          |

## 4.12 GapProperties (`v1.chapter4.cycle.integral.recursive.properties.GapProperties`)

| Lemma                                                            | Statement                                                       |
|------------------------------------------------------------------|-----------------------------------------------------------------|
| **assertRotateOneShiftsIntegralByOne(head,gaps,i)**              | Rotation-by-1 + head shift = integral shift by 1                |
| **assertRepeatedGapsPreservesIntegral(ci,repeatedCI,times,pos)** | Repeated gaps preserve integral at bounded pos                  |
| **assertTwoGapSumEqualsDiff(ci,k)**                              | 2-gap telescoping sum                                           |
| **assertMergedGapPositive(ci,fv,from,to)**                       | Merged survivor gap > 0                                         |
| **assertFirstSurvivorIsHead(ci,fv,start,count)**                 | First survivor = CI head                                        |
| **assertSurvivorsNonEmpty(ci,fv,start,count)**                   | Survivors list non-empty                                        |
| **allMultiplesInRange(ci,fv,from,until)**                        | Predicate: every CI value in `[from, until)` is a multiple of fv |
| **assertAllMultiplesInRangeTail(ci,fv,from,until)**              | Tail of a non-empty all-multiple prefix is all-multiple         |
| **assertFirstSurvivorAtPosition(ci,fv,start,count,pos)**         | If `[start,pos)` are multiples and `pos` survives, head survivor is `ci(pos)` |
| **assertSurvivorValuesSplitAtFirstPosition(ci,fv,start,count,pos)** | If `[start,pos)` are multiples and `pos` survives, split survivors at `ci(pos)` |
| **assertSurvivorValuesContainsNonMultipleAtPosition(ci,fv,start,count,pos)** | Scanned non-multiple CI value is kept in survivors              |
| **assertSurvivorValuesContainsOnlyNonMultiples(ci,fv,start,count,value)** | Every value kept in survivors is a non-multiple                 |
| **assertSurvivorValuesExcludesMultipleAtPosition(ci,fv,start,count,pos)** | Scanned multiple CI value is excluded from survivors            |
| **assertLastSurvivorIsLastScanned(ci,fv,start,count)**           | Last survivor = last scanned                                    |
| **assertCIModDivFormula(ci,pos)**                                | `ci(pos) == ci(pos%size) + (pos/size)*ci.sum`                   |
| **assertFilteredSumEqualsOriginalSum(ci,fv)**                    | Filtered sum = ci.sum (1 period, size+1 positions)              |
| **assertModIsPeriodic(ci,m,pos)**                                | `mod(ci(pos),m) == mod(ci(pos%size),m)` when `mod(ci.sum,m)==0` |
| **assertPeriodicShift(ci,k)**                                    | `ci(k+size) - ci(k) == ci.sum`                                  |
| **assertFullCycleShift(ci,pos)**                                 | One period shift                                                |
| **assertMultiCycleShift(ci,pos,m)**                              | `ci(pos+size*m) == ci(pos) + m*ci.sum`                          |

## 4.13 ModCycleIntegralProperties (`v1.chapter4.cycle.integral.mod.ModCycleIntegralProperties`)

| Lemma                                    | Statement                                                |
|------------------------------------------|----------------------------------------------------------|
| **assertFirstValuesMatchIntegral**       | `apply(pos) == integralValues(pos) + init` for small pos |
| **assertSimplifiedDiffValuesMatchCycle** | Simplified diff values match cycle                       |
| **assertModCycleEqualsCycleIntegral**    | ModCycleIntegral == CycleIntegral                        |
| **assertCycleIntegralMatchModCycleDef**  | CI matches ModCycle definition                           |

---

# Domain 5: Primes and Coprimality

## 5.1 CoprimeUtils (`v1.chapter5.prime.CoprimeUtils`)

| Lemma                                                 | Statement                                             |
|-------------------------------------------------------|-------------------------------------------------------|
| **assertModZero(n)**                                  | `mod(0,n) == 0`                                       |
| **assertModZeroImpliesDivTimesBEqualsA(a,b)**         | `mod(a,b)==0 => div(a,b)*b == a`                      |
| **assertMultipleModZero(k,n)**                        | `mod(k*n, n) == 0`                                    |
| **assertIsCoprimeForAll(n,primes)**                   | `isCoprime(n,primes) => mod(n,p) != 0` for each prime |
| **assertHasPrimeFactorImpliesNotCoprime(n,d,primes)** | Prime factor => not coprime                           |
| **assertNoDivisorByFactorList(n,d,primes)**           | Coprime to primes + d has factor => mod(n,d) != 0     |

## 5.2 Prime (`v1.chapter5.prime.Prime`)

| Lemma                                              | Statement                                          |
|----------------------------------------------------|----------------------------------------------------|
| **noDivisorInRangeExcludesValue(n,from,to,value)** | `noDivisorInRange(n,from,to) => mod(n,value) != 0` |

## 5.3 PrimeUtils (`v1.chapter5.prime.PrimeUtils`)

| Lemma                                       | Statement                                      |
|---------------------------------------------|------------------------------------------------|
| **primorialConcatLemma(prefix,suffix)**     | `primorial(A++B) == primorial(A)*primorial(B)` |
| **primorialUnfold(primes)**                 | `primorial(p::ps) == p.value * primorial(ps)`  |
| **primorialPositive(primes)**               | `primorial(primes) > 0`                        |
| **primeIsCoprimeWithSmallerList(v,primes)** | Prime larger than head is coprime to list      |

## 5.4 SortedPrimeList (`v1.chapter5.prime.SortedPrimeList`)

| Lemma                                       | Statement                           |
|---------------------------------------------|-------------------------------------|
| **assertSortFilteredDescending(list)**      | `sortFiltered` preserves descending |
| **assertInsertSortedDescending(x,list)**    | `insertSorted` preserves descending |
| **assertTailDescending(list)**              | Tail of descending is descending    |
| **assertRemoveKeepsDescending(list,index)** | `removeAt` preserves descending     |

## 5.5 FilterPreservesPrimesProperties (`v1.chapter5.prime.properties.FilterPreservesPrimesProperties`)

| Lemma                                                             | Statement                                      |
|-------------------------------------------------------------------|------------------------------------------------|
| **noDivisorInRangeImpliesModNonZero(n,from,to,d)**                | Bridge: noDivisorInRange => mod != 0           |
| **assertPrimeNotDivisibleByDistinctPrime(q,p)**                   | Distinct primes: `mod(q,p) != 0`               |
| **assertFilterPreservesAllPrimes(q,filterPrime)**                 | Prime not removed by filtering different prime |
| **assertFilteredContainsAllPrimes(originalPrimes,filterPrime,q)** | All primes != filterPrime survive              |

## 5.6 PrimeProperties (`v1.chapter5.prime.properties.PrimeProperties`)

| Lemma                                                      | Statement                                        |
|------------------------------------------------------------|--------------------------------------------------|
| **findSmallestDivisorEquiv(n,from)**                       | Smallest divisor semantics                       |
| **findSmallestDivisorIsNImpliesNoDivisorInRange(n,from)**  | `result==n => no divisor`                        |
| **findSmallestDivisorReturnsFromIfZero(n,from)**           | `mod(n,from)==0 => result==from`                 |
| **findSmallestDivisorResultModZeroFrom(n,from,d)**         | Divisibility of result                           |
| **findSmallestDivisorResultModZero(n,d)**                  | Wrapper for above                                |
| **assertSmallestDivisorIsPrimeDirect(n,d,from)**           | Smallest divisor has no smaller divisor          |
| **assertSmallestDivisorIsPrime(n,d)**                      | Smallest divisor is prime                        |
| **primorialPlusOneModAny(primes)**                         | `primorial+1` not divisible by any prime in list |
| **primorialPlusOneTailLoop(previous,current)**             | Inductive engine for above                       |
| **newPrimeNotInList(primes)**                              | Euclid-constructed prime not in list             |
| **notContainsFromValueNotMatchesAny(primes,sortedList,d)** | Bridge: not matches => not contains              |
| **euclidPrimeGreaterThanHead(sortedList)**                 | Euclid prime > head                              |
| **euclidTheorem(primes)**                                  | Euclid's theorem                                 |
| **assertNoDivisorInRangeFromHelper(n,primes,from,to)**     | Coprime => no divisor in range                   |
| **assertHeadIsPrime(head,primesTail)**                     | Coprime to tail + covered range => prime         |
| **assertFindSmallestDivisorAtMost(n,from,q)**              | Divisor q => smallest divisor <= q               |
| **assertCompositeHasDivisorStrictlyBelowN(n)**             | Composite has divisor < n                        |
| **assertSmallestDivisorAtMostSqrt(n)**                     | `d*d <= n` for smallest divisor d                |
| **assertDivisibleByFactorListNotCoprime(n,d,primes)**      | Divisible by non-coprime => not coprime          |
| **assertDivisorBelowHead(d,head)**                         | `d*d < head*head => d < head`                    |

---

# Domain 6: Sieve Sequence

## 6.1 SieveSequenceProperties (`v1.chapter6.seq.sieve.SieveSequenceProperties`)

| Lemma                               | Statement            |
|-------------------------------------|----------------------|
| **assertStrictlyIncreasing(seq,k)** | `seq(k+1) > seq(k)`  |
| **assertHeadIsMinimum(seq,k)**      | `seq(k) >= seq.head` |
| **assertAllValuesPositive(seq,k)**  | `seq(k) > 0`         |
| **assertHeadIsPrime(seq)**          | `seq.head` is prime  |

## 6.2 CycleSieveSequence (`v1.chapter6.seq.sieve.CycleSieveSequence`)

| Lemma                             | Statement         |
|-----------------------------------|-------------------|
| **assertNextHeadGreaterThanHead** | `apply(1) > head` |

## 6.3 SieveSequenceNextLevel (`v1.chapter6.seq.sieve.SieveSequenceNextLevel`)

| Lemma                                                   | Statement                                                    |
|---------------------------------------------------------|--------------------------------------------------------------|
| **assertAllGreaterThanReverse(list,value)**             | `allGreaterThan(list, v) == allGreaterThan(list.reverse, v)` |
| **assertCollectGapsAllPositive(seq,...)**               | `allGreaterThan(collectGaps(seq), 0)`                        |
| **assertNextPrimesNonEmpty(seq)**                       | `seq.next.primes.nonEmpty`                                   |
| **assertNextHeadPositive(seq)**                         | `seq.next.head.value > 0`                                    |
| **assertNextPrimesPositive(seq)**                       | `allGreaterThan(primeValues(seq.next.primes), 0)`            |
| **assertNextHeadBiggerThanOne(seq)**                    | `seq.next.head.value > 1`                                    |
| **assertNextPrimesBiggerThanOne(seq)**                  | `allGreaterThan(primeValues(seq.next.primes), 1)`            |
| **assertNextTailProductEqualOrBiggerThanElements(seq)** | `product(tailPrimes) >= each tail prime value`               |
| **assertNextHeadCoprimeToPrimes(seq)**                  | `isCoprime(nextHead, allPrimeValues)`                        |
| **assertNextExpandedCoprime(seq)**                      | Expanded residues remain coprime to tail primes              |
| **assertNextFilteredCoprime(seq)**                      | Filtered residues remain coprime to tail primes              |
| **assertResiduesCoprime(seq)**                          | `all r in residues(seq): isCoprime(r, tailPrimes)`           |
| **assertNextGapsNonEmpty(seq)**                         | `nextGaps(seq).nonEmpty`                                     |
| **assertNextGapsSize(seq)**                             | `nextGaps(seq).size == nextSorted(seq).list.size`            |
| **assertNextSortedStrictlyAscending(seq,i)**           | `nextSorted(seq).list(i+1) > nextSorted(seq).list(i)`       |
| **assertNextGapsAllPositiveGivenSortedBounds(seq)**     | `sortFiltered` sortedness plus range/head bounds imply `allGreaterThan(nextGaps,0)` |
| **assertNextRotatedGapsAllPositiveGivenSortedBounds(seq)** | Positive next gaps imply rotated next gaps are positive |

## 6.4 SieveUtils (`v1.chapter6.seq.sieve.SieveUtils`)

| Lemma                                                             | Statement                                                              |
|-------------------------------------------------------------------|------------------------------------------------------------------------|
| **assertIsCoprimeSound(value,primes)**                            | `isCoprime(value, primes) => mod(value, p) != 0` for all `p` in primes |
| **assertModZeroImpliesDivTimesBEqualsA(a,b)**                     | `mod(a,b)==0 => div(a,b)*b == a`                                       |
| **assertModZero(n)**                                              | `mod(0, n) == 0`                                                       |
| **assertMultipleModZero(k,n)**                                    | `mod(k*n, n) == 0`                                                     |
| **assertAddPreservesNotZeroMod(v,p,add)**                         | Adding multiple of `p` preserves `mod != 0`                            |
| **assertProductNonNegative(list)**                                | Product of positive list `>= 0`                                        |
| **assertHeadDividesProduct(list)**                                | `mod(product(list), list.head) == 0`                                   |
| **assertAllElementsDivideProduct(list)**                          | Every element divides the product                                      |
| **assertAllFromPrefix(prefixProd,list)**                          | Prefix product recursion helper                                        |
| **assertMultiplePreservesDivisible(a,b,p)**                       | `mod(b,p)==0 => mod(a*b,p)==0`                                         |
| **assertExpandedCoprime(r,i,modulus,primes)**                     | `r + i*modulus` coprime to primes                                      |
| **assertExpandedCoprimeViaPrefix(r,i,modulus,primes,prefixProd)** | Recursive version                                                      |
| **assertExpandedForAllJHelper(r,modulus,p,j,primes)**             | For all `j` in `[0,p)`, expanded values coprime                        |
| **assertExpandedForAllJ(r,modulus,p,primes)**                     | Wrapper for above                                                      |
| **assertAllRExpandedCoprime(modulus,p,primes)**                   | Every coprime residue expanded keeps coprimality                       |
| **assertAllRExpandedCoprimeRec(r,modulus,p,primes)**              | Recursive helper                                                       |
| **assertDivTransitive(c,b,a)**                                    | `mod(c,b)==0 && mod(b,a)==0 => mod(c,a)==0`                            |
| **assertFilterNonEmpty(list,divisor)**                            | Filter preserves non-emptiness                                         |
| **assertIsCoprimeForAll(n,primes)**                               | `isCoprime(n,primes) => mod(n, p) != 0` for all `p`                    |
| **assertPrimeFactorDivides(n,primes)**                            | Found prime factor divides `n`                                         |
| **assertNoDivisorByFactorList(n,d,primes)**                       | Coprime + d has factor => `mod(n,d) != 0`                              |
| **assertCalculateGapsSize(sorted,modulus)**                       | `calculateGaps(sorted,modulus).size == sorted.size`                    |
| **assertPairwiseGapsSize(list)**                                  | `pairwiseGaps(list).size == list.size - 1`                             |
| **assertPairwiseGapsAllPositive(list)**                           | Strict ascending input gives positive adjacent gaps                    |
| **assertWrapGapPositive(sorted,modulus)**                         | Upper-bound + nonnegative head gives positive wrap gap                 |
| **assertCalculateGapsAllPositive(sorted,modulus)**                 | Sorted bounded residues give positive calculated gaps                  |
| **assertSplitAtPreservesAllGreaterThan(list,index,value)**        | Delegation to ch3                                                      |
| **assertRotateAtPreservesAllGreaterThan(list,index,value)**       | Delegation to ch3                                                      |
| **assertRotateAtPreservesNonEmpty(list,index)**                   | Rotation preserves non-emptiness                                       |
| **assertInsertSortedAscending(x,list)**                           | Insert preserves ascending order                                       |
| **assertSortFilteredAscending(list)**                             | Sort preserves ascending order                                         |
| **assertAddOffsetNonNegative(list,offset)**                       | `addOffset` preserves non-negativity                                   |
| **assertAddOffsetAllLessThan(list,bound,offset)**                 | `addOffset` preserves `< bound + offset`                               |
| **assertExpandSingleRange(residues,mod,p,i)**                     | Expand range: non-negative, `< p*mod`                                  |
| **assertExpandResiduesRange(residues,mod,p)**                     | Wrapper for expand range                                               |
| **assertFilterListNonNegative(list,divisor)**                     | `filterList` preserves `>= 0`                                          |
| **assertFilterListAllLessThan(list,bound,divisor)**               | `filterList` preserves `< bound`                                       |
| **assertInsertSortedNonNegative(x,list)**                         | `insertSorted` preserves `>= 0`                                        |
| **assertSortFilteredNonNegative(list)**                           | `sortFiltered` preserves `>= 0`                                        |
| **assertInsertSortedAllLessThan(x,list,bound)**                   | `insertSorted` preserves `< bound`                                     |
| **assertSortFilteredAllLessThan(list,bound)**                     | `sortFiltered` preserves `< bound`                                     |
| **assertValueNeverDecreases(a,b)**                                | `a*b >= a && a*b >= b` for positive `a,b`                              |
| **assertSumPairwiseGaps(list)**                                   | `sum(pairwiseGaps(list)) == list.last - list.head`                     |
| **assertCalculateGapsSum(sorted,modulus)**                        | `sum(calculateGaps(sorted,modulus)) == modulus`                        |
| **assertProductEqualOrBiggerThanElements(list)**                  | `product(list) >= each element` for elements > 1                       |
| **assertHasPrimeFactorImpliesNotCoprime(d,primes)**               | Prime factor => not coprime                                            |
| **assertGenerateResiduesAllCoprime(i,modulus,primes)**            | Every value in `generateResidues` coprime                              |
| **assertResiduesAllCoprime(modulus,primes)**                      | Wrapper for above                                                      |
| **assertGenerateResiduesContainsCoprime(v,i,modulus,primes)**     | Completeness: every coprime `v` in range appears                       |
| **assertResiduesComplete(modulus,primes)**                        | `residues` contains every coprime in `[0,modulus)`                     |
| **assertResiduesCompleteRec(i,modulus,primes)**                   | Recursive helper                                                       |
| **assertNoDivisorInRangeHelper(n,primes,from,to)**                | Coprime => no divisor in range                                         |

## 6.5 SpecSieveSequence (`v1.chapter6.seq.sieve.SpecSieveSequence`)

65 lemmas (20 public, 45 private). Key public lemmas:

| Lemma                                                                   | Statement                                                      |
|-------------------------------------------------------------------------|----------------------------------------------------------------|
| **applyStrictlyIncreases(k)**                                           | `apply(k+1) > apply(k)`                                        |
| **assertApplyInjective(i,j)**                                           | `apply(i) == apply(j) => i == j`                               |
| **assertApplyModIsCoprime(k)**                                          | `isCoprime(mod(apply(k), filterModulus), filterValues)`        |
| **assertGapPositive(k)**                                                | `apply(k+1) - apply(k) > 0`                                    |
| **assertGapSum(p)**                                                     | `sumGap(0, p) == filterModulus`                                |
| **assertApplyEqualsHeadPlusGapSum(pos)**                                | `apply(pos) == head + sumGap(0, pos)`                          |
| **assertGapListPositive(from,count)**                                   | `allGreaterThan(gapList(from, count), 0)`                      |
| **assertGapListSize(from,count)**                                       | `gapList(from, count).size == count`                           |
| **assertGapListApplyEqualsGapAtPosition(from,count,r)**                 | `gapList(from,count)(r) == apply(from+r+1) - apply(from+r)`    |
| **assertSpecGapPeriodPositive(period)**                                 | `allGreaterThan(specGapPeriod(period).memCycle.values, 0)`     |
| **assertSpecGapCycleIntegralBase(period)**                              | `CycleIntegral(head, gaps)(0) == apply(1)`                     |
| **assertMemCycleGapMatch(i,period)**                                    | `memCycle(i) == apply(i+1) - apply(i)`                         |
| **assertSpecGapCycleIntegralMatchesApply(period,k)**                    | `CycleIntegral(head, gaps)(k-1) == apply(k)` for `k > 0`       |
| **assertNextValueAcceptedByThis(k)**                                    | `mod(next(k), head) != 0`                                      |
| **assertAcceptedByNextWhenOldAcceptedAndNewHeadNonMultiple(nextSeq,value)** | Private: old accepted + new-head non-multiple => accepted by next |
| **assertNextAcceptedImpliesOldAcceptedAndNewHeadNonMultiple(nextSeq,value)** | Private: accepted by next => old accepted and new-head non-multiple |
| **assertRejectedByNextWhenNewHeadMultiple(nextSeq,value,p)**            | Private: new-head multiple is rejected by next                 |
| **assertApplyMonotonic(from,until)**                                    | `from <= until => apply(from) <= apply(until)`                 |
| **assertFilterPreservesNextGap(nextSeq,k)**                             | Gap copy when old value accepted by next                       |
| **assertConsecutiveAcceptedByNextPreservesGap(nextSeq,k)**              | Consecutive old values accepted => gap copied                  |
| **assertMergeGapEqualsOldGapSum(nextSeq,k,period)**                     | Private: skipped successor merge equals old gap telescope      |
| **assertMergedGapPrefixMatchesNext(nextSeq,k,seqIdx,remaining,period)** | `mergedGapPrefix(...)(seqIdx) == nextSeq.gapList(...)(seqIdx)` |
| **assertApplyOneEqualsNextPrime()**                                     | `apply(1) == nextPrime.value` when `nextPrime < head*head`     |
| **assertMergeLandsOnFirstSurvivor(nextSeq,k,period)**                   | Merged gap lands on first survivor position                    |

## 6.6 SpecDerivedSieveSequence (`v1.chapter6.seq.sieve.SpecDerivedSieveSequence`)

38 lemmas (36 public, 2 private). Key public lemmas:

| Lemma                                                  | Statement                                                   |
|--------------------------------------------------------|-------------------------------------------------------------|
| **assertApplyMatches(k)**                              | `cycle(k) == spec(k)` for small `k`                         |
| **assertNextHeadMatches()**                            | `cycle(1) == spec.next.head.value`                          |
| **assertPrimesMatch()**                                | `primesMatch` for all cached prime + head equivalences      |
| **assertCycleHeadMatchesSpecHead()**                   | `cycle.head == spec.head.value`                             |
| **assertCyclePrimesTailEqualsSpecFilterValues()**      | `cycle.primesTailValues == spec.filterValues`               |
| **assertCycleModulusEqualsSpecFilterModulus()**        | `cycle.modulus == spec.filterModulus`                       |
| **assertNextPipelineGapsIsNextRotatedGaps()**          | `nextPipelineGaps(cycle) == nextRotatedGaps(cycle)`         |
| **assertCycleGapCycleEqualsSpecGapCycle()**            | `cycle.gapCycle == spec.specGapCycle(period)`               |
| **assertCycleSpecNextFilterDecisionMatches(k)**        | `cycle(k)` and `spec(k)` have the same next-filter decision |
| **assertCycleApplyLowersToIntegral(k)**                | `cycle(k) == cycle.integral(k - 1)` for `k > 0`             |
| **assertNewHeadCoprimeToAllPrimes()**                  | `isCoprime(cycle(1), allPrimeValues)`                       |
| **assertCycleValueCoprimeToTail(k)**                   | `isCoprime(cycle(k), tailPrimes)`                           |
| **assertCycleSurvivorValuesStartAtSpecNextHead(count)** | cycle survivor scan splits at `spec.next.head.value`       |
| **assertFullEquivalence(nextPeriod,k)**                | `cycle(k) == spec(k) && cycle(1) == spec.next.head.value`   |
| **assertNextGapListMatchesSpecNext(from,count)**       | `nextGapList(from,count) == spec.next.gapList(from,count)`  |
| **assertNextCycleMatchesSpecNext(nextPeriod)**         | Next canonical cycle fully matches spec.next                |
| **assertModulusPositive()**                            | `cycle.modulus > 0`                                         |
| **assertPrimesTailValuesPositive()**                   | `allGreaterThan(primesTailValues, 0)`                       |
| **assertNextPipelineGapsPositiveFromSpec(nextPeriod)** | `allGreaterThan(nextPipelineGaps, 0)` from spec equivalence |
| **assertRepeatedGapListIndexMatches(times,index)**     | `repeatedGapList(times)(index) == gapList(mod(index,size))` |
| **assertRepeatedCycleApplyMatches(times,k)**           | `repeatedCycle(times)(k) == cycle(k)`                       |
| **assertRepeatedCycleIntegralMatches(times,pos)**      | `repeatedCI(pos) == originalCI(pos)` for small pos          |
| **assertSpecNextIsKthSurvivor(nextPeriod,k)**          | `spec.next(k) == cycle(indexOfAccepted(spec.next(k)))`      |

## 6.7 SpecCycleSieveEquivalence (`v1.chapter6.seq.sieve.SpecCycleSieveEquivalence`)

39 lemmas (21 public, 18 private). Key public lemmas:

| Lemma                                                                      | Statement                                                              |
|----------------------------------------------------------------------------|------------------------------------------------------------------------|
| **assertHeadsMatchFromPrimeValues(spec,cycle)**                            | `cycle.head == spec.head.value`                                        |
| **assertApplyZeroMatchesFromPrimeValues(spec,cycle)**                      | `cycle(0) == spec(0)`                                                  |
| **assertSpecCycleApplyMatchesFromSameHeadAndGaps(spec,cycle,period,pos)**  | `cycle(pos) == spec(pos)` for all `pos` given same head/gaps           |
| **assertCycleApplyMatchesFromSameHeadAndGaps(cycle1,cycle2,pos)**          | Two cycles with same head+gaps produce identical sequences             |
| **assertCurrentApplyOneEqualsSpecNextHead(spec,cycle,period)**             | `cycle(1) == spec.next.head.value`                                     |
| **assertNextAcceptsMatchesCyclePrimesCoprime(spec,cycle,value)**           | `spec.next.accepts(value) == isCoprime(value, cycle.primes)`           |
| **assertWalkGapsAllPositive(cycle)**                                       | `allGreaterThan(walkGaps(cycle), 0)`                                   |
| **assertFilterValuesMatchTailPrimes(spec,cycle)**                          | `cycle.tailPrimesValues == spec.filterValues`                          |
| **assertSpecAcceptsMatchesCycleTailCoprime(spec,cycle,value)**             | `spec.accepts(value) == isCoprime(value, tailPrimesValues)`            |
| **assertResiduesContainCoprimeBelowModulus(modulus,filters,residue)**      | Completeness: all coprime residues in `[0, modulus)` in list           |
| **assertGenerateResiduesContainOnlyCoprime(modulus,filters,residue,from)** | Soundness: all generated residues are coprime                          |
| **assertResiduesAreCoprimeBelowModulus(modulus,filters,residue)**          | Wrapper: all residues are coprime                                      |
| **assertFilterListContainsIf(list,value,divisor)**                         | Private: input value with nonzero mod survives `filterList`            |
| **assertFilterListContainsOnlyIf(list,value,divisor)**                     | Private: `filterList` output came from input and has nonzero mod       |
| **assertExpandedResiduesRepresentPeriod(seq,value)**                       | Every coprime value in `[0, head*modulus)` in expanded residues        |
| **assertNextFilteredContainsCoprime(seq,value)**                           | `nextFiltered(seq).contains(value)` for any coprime `value`            |
| **assertNextSortedContainsCoprime(seq,value)**                             | `nextSorted(seq).contains(value)` for any coprime `value`              |
| **assertNextSortedOnlyContainsFiltered(seq,value)**                        | `nextSorted(seq).contains(value) => nextFiltered(seq).contains(value)` |

## 6.8 CycleUtils (`v1.chapter6.seq.sieve.CycleUtils`)

| Lemma                            | Statement                            |
|----------------------------------|--------------------------------------|
| **assertAllLessThanTransitive**  | `allLessThan` is transitive          |
| **assertAllLessThanAppend**      | `allLessThan(A++B, bound)` from both |
| **assertCheckNonNegativeAppend** | Non-negative preserved by ++         |
