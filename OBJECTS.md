# Key Objects & Proved Properties

## Quick Reference Table

| Property                                         | File                                 | Domain     |
|--------------------------------------------------|--------------------------------------|------------|
| **Division & Modulo**                            |                                      |
| `modSmallDividend`                               | ModSmallDividend.scala               | Div/Mod|
| `modIdentity`                                    | ModIdentity.scala                    | Div/Mod|
| `longProof`                                      | ModIdentity.scala                    | Div/Mod|
| `modIdempotence`                                 | ModIdempotence.scala                 | Div/Mod|
| `modIdempotencePositiveA`                        | ModIdempotence.scala                 | Div/Mod|
| `modUniqueDiv`                                   | ModIdempotence.scala                 | Div/Mod|
| `modUnique`                                      | ModIdempotence.scala                 | Div/Mod|
| `modModPlus`                                     | ModIdempotence.scala                 | Div/Mod|
| `modModMinus`                                    | ModIdempotence.scala                 | Div/Mod|
| `APlusBSameModPlusDiv`                           | AdditionAndMultiplication.scala      | Div/Mod|
| `ALessBSameModDecreaseDiv`                       | AdditionAndMultiplication.scala      | Div/Mod|
| `ATimesBSameMod`                                 | AdditionAndMultiplication.scala      | Div/Mod|
| `APlusMultipleTimesBSameMod`                     | AdditionAndMultiplication.scala      | Div/Mod|
| `ALessMultipleTimesBSameMod`                     | AdditionAndMultiplication.scala      | Div/Mod|
| `assertDivModWithMoreDivAndLessModSameSolution`  | AdditionAndMultiplication.scala      | Div/Mod|
| `assertDivModWithLessDivAndMoreModSameSolution`  | AdditionAndMultiplication.scala      | Div/Mod|
| `MoreDivLessModManyTimes`                        | AdditionAndMultiplication.scala      | Div/Mod|
| `LessDivMoreModManyTimes`                        | AdditionAndMultiplication.scala      | Div/Mod|
| `modAdd`                                         | ModOperations.scala                  | Div/Mod|
| `modZeroPlusC`                                   | ModOperations.scala                  | Div/Mod|
| `modLess`                                        | ModOperations.scala                  | Div/Mod|
| `addOne`                                         | ModOperations.scala                  | Div/Mod|
| `sumSymmetricalMods`                             | ModSum.scala                         | Div/Mod|
| `checkAllPreviousValues`                         | ModSum.scala                         | Div/Mod|
| `sumAllValues`                                   | ModSum.scala                         | Div/Mod|
| `sumAllMods`                                     | ModSum.scala                         | Div/Mod|
| `sumAllModsEqualSumOfAllSmallValues`             | ModSum.scala                         | Div/Mod|
| `checkValueShift`                                | ModSum.scala                         | Div/Mod|
| **Lists**                                        |                                      |
| `listSumAddValue`                                | ListUtilsProperties.scala            | Lists|
| `listCombine`                                    | ListUtilsProperties.scala            | Lists|
| `listSwap`                                       | ListUtilsProperties.scala            | Lists|
| `listAddValueTail`                               | ListUtilsProperties.scala            | Lists|
| `assertAppendToSlice`                            | ListUtilsProperties.scala            | Lists|
| `assertTailShiftLeft`                            | ListUtilsProperties.scala            | Lists|
| `accessTailShiftRight`                           | ListUtilsProperties.scala            | Lists|
| `assertLastEqualsLastPosition`                   | ListUtilsProperties.scala            | Lists|
| `checkAllBiggerThanValueAtIndex`                 | ListUtilsProperties.scala            | Lists|
| `checkAllBiggerThanValueHeadTail`                | ListUtilsProperties.scala            | Lists|
| `headRecursiveSlice`                             | SliceEquivalenceLemmas.scala         | Lists|
| `indexRangeValues`                               | SliceEquivalenceLemmas.scala         | Lists|
| `sliceEqualsSpec`                                | SliceEquivalenceLemmas.scala         | Lists|
| `appendOne`                                      | SliceEquivalenceLemmas.scala         | Lists|
| `appendCons`                                     | SliceEquivalenceLemmas.scala         | Lists|
| `tailHeadAndIndexRangeSlicesAreEqual`            | SliceEquivalenceLemmas.scala         | Lists|
| `assertHeadValueMatchDefinition`                 | IntegralProperties.scala             | Lists|
| `assertAccDifferenceEqualsTailHead`              | IntegralProperties.scala             | Lists|
| `assertAccDiffMatchesList`                       | IntegralProperties.scala             | Lists|
| `assertAccMatchesApply`                          | IntegralProperties.scala             | Lists|
| `assertSizeAccEqualsSizeList`                    | IntegralProperties.scala             | Lists|
| `assertLastEqualsSum`                            | IntegralProperties.scala             | Lists|
| `assertIntegralEqualsSum`                        | IntegralProperties.scala             | Lists|
| `assertLast`                                     | IntegralProperties.scala             | Lists|
| `singletonProduct`                             | ListProduct.scala                    | Lists|
| `productPullOutElement`                        | ListProduct.scala                    | Lists|
| `productConcatLemma`                           | ListProduct.scala                    | Lists|
| `productConcatCommutative`                     | ListProduct.scala                    | Lists|
| `positiveProduct`                              | ListProduct.scala                    | Lists|
| `ListProductDiv`                               | ListProductDiv.scala                 | Lists|
| `allElementsDivideProduct`                     | ListProductDiv.scala                 | Lists|
| `insertedElementDividesProduct`                | ListProductDiv.scala                 | Lists|
| **Cycles**                                       |                                      |
| `findValueInCycle`                               | CycleProperties.scala                | Cycles|
| `smallValueInCycle`                              | CycleProperties.scala                | Cycles|
| `valueMatchAfterManyLoops`                       | CycleProperties.scala                | Cycles|
| `valueMatchAfterManyLoopsInBoth`                 | CycleProperties.scala                | Cycles|
| `propagateModFromValueToCycle`                   | CycleProperties.scala                | Cycles|
| `assertCycleOfPosEqualsCycleOfModPos`            | CycleProperties.scala                | Cycles|
| `cycleValuePositiveOrZero`                       | CycleProperties.scala                | Cycles|
| `rotateAtValue`                                  | CycleProperties.scala                | Cycles|
| `findValueInCycle`                               | MemCycleProperties.scala             | Cycles|
| `smallValueInCycle`                              | MemCycleProperties.scala             | Cycles|
| `valueMatchAfterManyLoops`                       | MemCycleProperties.scala             | Cycles|
| `valueMatchAfterManyLoopsInBoth`                 | MemCycleProperties.scala             | Cycles|
| `propagateModFromValueToCycle`                   | MemCycleProperties.scala             | Cycles|
| `assertCycleOfPosEqualsCycleOfModPos`            | MemCycleProperties.scala             | Cycles|
| **Cycle Integrals**                              |                                      |
| `assertCycleIntegralEqualsSumFirstPosition`      | CycleIntegralProperties.scala        | CycleInteg|
| `assertCycleIntegralEqualsSumSmallPositions`     | CycleIntegralProperties.scala        | CycleInteg|
| `assertCycleIntegralEqualsSliceSum`              | CycleIntegralProperties.scala        | CycleInteg|
| `assertNextPosition`                             | CycleIntegralProperties.scala        | CycleInteg|
| `assertDiffEqualsCycleValue`                     | CycleIntegralProperties.scala        | CycleInteg|
| `assertSameDiffAfterCycle`                       | CycleIntegralProperties.scala        | CycleInteg|
| `assertLastElementBeforeLoop`                    | CycleIntegralProperties.scala        | CycleInteg|
| `assertSumModValueAsListEqualsCycleIntegralLoop` | CycleIntegralProperties.scala        | CycleInteg|
| `assertCycleIntegralEqualsSumOfModValuesAsList`  | CycleIntegralProperties.scala        | CycleInteg|
| `getFirstValuesAsSlice`                          | CycleIntegralProperties.scala        | CycleInteg|
| `getModValuesAsList`                             | CycleIntegralProperties.scala        | CycleInteg|
| `assertFirstValuesAsSliceEqualsModValuesAsList`  | CycleIntegralProperties.scala        | CycleInteg|
| `assertCycleValuePositive`                       | CycleIntegralProperties.scala        | CycleInteg|
| `assertCycleIntegralPositive`                    | CycleIntegralProperties.scala        | CycleInteg|
| `assertCycleIntegralEqualsSumFirstPosition`      | ClassicCycleIntegralProperties.scala | CycleInteg|
| `assertCycleIntegralEqualsSumSmallPositions`     | ClassicCycleIntegralProperties.scala | CycleInteg|
| `assertCycleIntegralEqualsSliceSum`              | ClassicCycleIntegralProperties.scala | CycleInteg|
| `assertNextPosition`                             | ClassicCycleIntegralProperties.scala | CycleInteg|
| `assertDiffEqualsCycleValue`                     | ClassicCycleIntegralProperties.scala | CycleInteg|
| `assertSameDiffAfterCycle`                       | ClassicCycleIntegralProperties.scala | CycleInteg|
| `assertLastElementBeforeLoop`                    | ClassicCycleIntegralProperties.scala | CycleInteg|
| `assertSumModValueAsListEqualsCycleIntegralLoop` | ClassicCycleIntegralProperties.scala | CycleInteg|
| `assertCycleIntegralEqualsSumOfModlValuesAsList` | ClassicCycleIntegralProperties.scala | CycleInteg|
| `getFirstValuesAsSlice`                          | ClassicCycleIntegralProperties.scala | CycleInteg|
| `getModValuesAsList`                             | ClassicCycleIntegralProperties.scala | CycleInteg|
| `assertFirstValuesAsSliceEqualsModValuesAsList`  | ClassicCycleIntegralProperties.scala | CycleInteg|
| `assertFirstValuesMatchIntegral`                 | ModCycleIntegralProperties.scala     | CycleInteg|
| `assertSimplifiedDiffValuesMatchCycle`           | ModCycleIntegralProperties.scala     | CycleInteg|
| `assertModCycleEqualsCycleIntegral`              | ModCycleIntegralProperties.scala     | CycleInteg|
| `assertCycleIntegralMatchModCycleDef`            | ModCycleIntegralProperties.scala     | CycleInteg|
| **Sieve**                                        |                                      |
| `product`                                        | SieveUtils.scala                     | Sieve      |
| `isCoprime`                                      | SieveUtils.scala                     | Sieve      |
| `residues`                                       | SieveUtils.scala                     | Sieve      |
| `filterList`                                     | SieveUtils.scala                     | Sieve      |
| `calculateGaps`                                  | SieveUtils.scala                     | Sieve      |
| `rotateAt`                                       | SieveUtils.scala                     | Sieve      |
| `assertRotateAtPreservesNonEmpty`                | SieveUtils.scala                     | Sieve      |
| `allGreaterThan`                                 | ListBoundUtils.scala                 | Sieve      |
| `allPositive`                                    | ListBoundUtils.scala                 | Sieve      |
| `assertGreaterThanAtIndex`                       | ListBoundUtils.scala                 | Sieve      |
| `assertAppendGreaterThan`                        | ListBoundUtils.scala                 | Sieve      |
| `hasPrimeFactorInList`                           | SieveUtils.scala                     | Sieve      |
| `assertHasPrimeFactorImpliesNotCoprime`          | SieveUtils.scala                     | Sieve      |
| `assertNoDivisorInRangeHelper`                   | SieveUtils.scala                     | Sieve      |
| **Prime**                                       |                                      |
| `isPrime`                                       | Prime.scala                          | Prime|
| `noDivisorInRange`                              | Prime.scala                          | Prime|
| `primorial`                                     | PrimeUtils.scala                     | Prime|
| `primorialUnfold`                               | PrimeUtils.scala                     | Prime|
| `primorialPositive`                             | PrimeUtils.scala                     | Prime|
| `biggerPrime`                                   | PrimeUtils.scala                     | Prime|
| `isMultiple`                                    | PrimeUtils.scala                     | Prime|
| `primorialPlusOneModAny`                       | PrimeProperties.scala                | Prime|
| `newPrimeFromEuclid`                           | PrimeProperties.scala                | Prime|
| `euclidTheorem`                                | PrimeProperties.scala                | Prime|
| `assertPrimeNotDivisibleByDistinctPrime`       | FilterPreservesPrimesProperties.scala| Prime|
| `assertFilterPreservesAllPrimes`               | FilterPreservesPrimesProperties.scala| Prime|
| `assertFilteredContainsAllPrimes`              | FilterPreservesPrimesProperties.scala| Prime|
| `assertNoDivisorInRangeFromHelper`             | PrimeProperties.scala                | Prime|
| `assertHeadIsPrime`                            | PrimeProperties.scala                | Prime|
| **CycleIntegralOnes**                          |                                      |
| `assertCycleIntegralOfOnes`                    | CycleIntegralOnesProperties.scala    | CycleIntegral |
| `assertCycleIntegralOfOnesStrictlyIncreasing`  | CycleIntegralOnesProperties.scala    | CycleIntegral |

---

# Domain 1: Division & Modulo

## 1.1 DivMod (`v1.div.DivMod`)

Recursive division solver. Core primitive for all mod/div operations.

| Field/Method | Definition                                 | Notes                 |
|--------------|--------------------------------------------|-----------------------|
| **a**        | Dividend                                   | `BigInt`              |
| **b**        | Divisor                                    | `BigInt`, non-zero    |
| **div**      | Quotient                                   | `BigInt`              |
| **mod**      | Remainder                                  | `BigInt`              |
| **solve**    | Recursively adjusts div/mod to final state | Returns solved DivMod |
| **isFinal**  | `0 <= mod < absB`                          | Final state condition |
| **isValid**  | `a == div * b + mod`                       | Valid state condition |

**Mathematical Definition** (from [articles/modulo.md](./articles/modulo.md)):

```math
\begin{aligned}
\forall \text{ } a, b, div, mod & \in \mathbb{Z} : b \neq 0, a = \text{div} \cdot b + \text{mod} \\
\text{DivMod.solve}(a, b, \text{div}, \text{mod}) &=
\begin{cases}
\text{DivMod}(a, b, \text{div}, \text{mod}) & \text{if } 0 \leq \text{mod} < |b| \\
\text{DivMod.solve}(a, b, \text{div} + \text{sign}(b), \text{mod} - |b|) & \text{if } \text{mod} \geq |b| \\
\text{DivMod.solve}(a, b, \text{div} - \text{sign}(b), \text{mod} + |b|) & \text{if } \text{mod} < 0 \\
\end{cases}
\end{aligned}
```

---

## 1.2 Calc (`v1.Calc`)

Provides the `mod` and `div` operations extracted from DivMod.

| Function      | Definition                     | Notes     |
|---------------|--------------------------------|-----------|
| **mod(a, b)** | `DivMod(a, b, 0, a).solve.mod` | Remainder |
| **div(a, b)** | `DivMod(a, b, 0, a).solve.div` | Quotient  |

---

## 1.3 ModSmallDividend (`v1.div.properties.ModSmallDividend`)

**Property**: `modSmallDividend`

**Mathematical Formula** (from [articles/modulo.md](./articles/modulo.md)):

```math
\begin{aligned}
\forall \text{ } a, b \in \mathbb{N} : b \neq 0 \\
b > a \geq 0 \implies a \text{ mod } b & = a \\
b > a \geq 0 \implies a \text{ div } b & = 0
\end{aligned}
```

**Statement**: If dividend is smaller than divisor, result is the dividend itself.

**Preconditions**: `b > 0`, `b > a`, `a >= 0`

**Source**: `src/main/scala/v1/chapter2/div/properties/ModSmallDividend.scala:11`

---

## 1.4 ModIdentity (`v1.div.properties.ModIdentity`)

**Property**: `modIdentity`

**Mathematical Formula** (from [articles/modulo.md](./articles/modulo.md)):

```math
\begin{aligned}
\forall \text{ } n \in \mathbb{N} : n & \neq 0 \\
n \text{ mod } n & = 0 \\
n \text{ div } n & = 1
\end{aligned}
```

**Statement**: The modulo of every number by itself is zero, division is one.

**Preconditions**: `a != 0`

**Source**: `src/main/scala/v1/chapter2/div/properties/ModIdentity.scala:9`

**Also**: `longProof` (line #14) - Detailed step-by-step proof

---

## 1.5 ModIdempotence (`v1.div.properties.ModIdempotence`)

| Property                    | Statement                                                           | Preconditions                                        |
|-----------------------------|---------------------------------------------------------------------|------------------------------------------------------|
| **modIdempotence**          | `mod(a, b) == mod(mod(a, b), b)`                                    | `b != 0`                                             |
| **modIdempotencePositiveA** | Same for `a >= 0`                                                   | `b != 0`, `a >= 0`                                   |
| **modUniqueDiv**            | Same a,b produces same DivMod solution                              | `x.isValid`, `y.isValid`, same a,b                   |
| **modUnique**               | Unique remainder for any a,b                                        | `b != 0`, `divx*b + modx == a`, `divy*b + mody == a` |
| **modModPlus**              | `mod(mod(a,b) + mod(c,b), b) == mod(a,b) + mod(c,b) - b * div(...)` | `b != 0`                                             |
| **modModMinus**             | `mod(mod(a,b) - mod(c,b), b) == mod(a,b) - mod(c,b) - b * div(...)` | `b != 0`                                             |

**Mathematical Formula** (from [articles/modulo.md](./articles/modulo.md)):

```math
\begin{aligned}
\forall \text{ } a, b & \in \mathbb{Z} : b \neq 0 \\
a \text{ mod } b & = ( a \text{ mod } b ) \text{ mod } b
\end{aligned}
```

**Source**: `src/main/scala/v1/chapter2/div/properties/ModIdempotence.scala`

---

## 1.6 AdditionAndMultiplication (`v1.div.properties.AdditionAndMultiplication`)

Quotient invariance under linear shifts.

| Property                                          | Statement                                                  | Preconditions                         |
|---------------------------------------------------|------------------------------------------------------------|---------------------------------------|
| **APlusBSameModPlusDiv**                          | `mod(a+b,b) == mod(a,b)`, `div(a+b,b) == div(a,b)+1`       | `b != 0`                              |
| **ALessBSameModDecreaseDiv**                      | `mod(a-b,b) == mod(a,b)`, `div(a-b,b) == div(a,b)-1`       | `b != 0`                              |
| **ATimesBSameMod**                                | `mod(a+b*m,b) == mod(a,b)`, `div(a+b*m,b) == div(a,b)+m`   | `b != 0`                              |
| **APlusMultipleTimesBSameMod**                    | Same for positive m                                        | `b != 0`, `m >= 0`                    |
| **ALessMultipleTimesBSameMod**                    | Same for negative shift                                    | `b != 0`, `m >= 0`                    |
| **assertDivModWithMoreDivAndLessModSameSolution** | DivMod(a,b,div+1,mod-b).solve == DivMod(a,b,div,mod).solve | `b != 0`, `div*b + mod == a`          |
| **assertDivModWithLessDivAndMoreModSameSolution** | DivMod(a,b,div-1,mod+b).solve == ...                       | `b != 0`, `div*b + mod == a`          |
| **MoreDivLessModManyTimes**                       | Same invariance for m iterations                           | `b > 0`, `div*b + mod == a`, `m >= 1` |
| **LessDivMoreModManyTimes**                       | Same for negative direction                                | `b != 0`, `div*b + mod == a`, `m > 0` |

**Mathematical Formula** (from [articles/modulo.md](./articles/modulo.md)):

```math
\begin{aligned}
\forall \text{ } a, b, m \in \mathbb{Z} : b \neq 0 \\
(a + b \cdot m) \text{ mod } b & = a \text{ mod } b \\
(a - b \cdot m) \text{ mod } b & = a \text{ mod } b \\
(a + b \cdot m ) \text{ div } b & = (a \text{ div } b) + m \\
(a - b \cdot m ) \text{ div } b & = (a \text{ div } b) - m
\end{aligned}
```

**Source**: `src/main/scala/v1/chapter2/div/properties/AdditionAndMultiplication.scala`

---

## 1.7 ModOperations (`v1.div.properties.ModOperations`)

Modulo distributivity over addition/subtraction.

| Property         | Statement                                    | Preconditions                     |
|------------------|----------------------------------------------|-----------------------------------|
| **modAdd**       | `mod(a+c,b) == mod(mod(a,b) + mod(c,b), b)`  | `b != 0`                          |
| **modZeroPlusC** | If `mod(a,b) == 0`: `mod(a+c,b) == mod(c,b)` | `b != 0`, `c >= 0`, `mod(a,b)==0` |
| **modLess**      | `mod(a-c,b) == mod(mod(a,b) - mod(c,b), b)`  | `b != 0`                          |
| **addOne**       | Unit-step increment law                      | `b > 0`, `a >= 0`                 |

**Mathematical Formula** (from [articles/modulo.md](./articles/modulo.md)):

```math
\begin{aligned}
\forall \text{ } a, b, c & \in \mathbb{Z} : b \neq 0 \\
( a + c ) \text{ mod } b & = ( a \text{ mod } b + c \text{ mod } b ) \text{ mod } b \\
( a - c ) \text{ mod } b & = ( a \text{ mod } b - c \text{ mod } b ) \text{ mod } b
\end{aligned}
```

```math
\begin{aligned}
\forall \text{ } a, b & \in \mathbb{N} : b \neq 0 \\
a \text{ mod } b = b - 1    & \implies (a + 1) \text{ mod } b = 0 \\
a \text{ mod } b \neq b - 1 & \implies (a + 1) \text{ mod } b = (a \text{ mod } b) + 1
\end{aligned}
```

**Source**: `src/main/scala/v1/chapter2/div/properties/ModOperations.scala`

---

## 1.8 ModSum (`v1.div.properties.ModSum`)

Summation properties related to modulo.

| Property                               | Statement                                    | Preconditions                        |
|----------------------------------------|----------------------------------------------|--------------------------------------|
| **sumSymmetricalMods**                 | `mod(step,b) + mod(b-step,b) == b`           | `b > 0`, `step > 0`, `step < b`      |
| **checkAllPreviousValues**             | If `a < b`: `mod(a,b) == a`                  | `b > 0`, `a < b`, `a >= 0`           |
| **sumAllValues**                       | Sum from `from` to `to`                      | `from >= 0`, `to >= 0`, `to >= from` |
| **sumAllMods**                         | Sum of mods from `from` to `to`              | `b > 0`, `from >= 0`, `to >= 0`      |
| **sumAllModsEqualSumOfAllSmallValues** | `sumAllMods(0,b-1,b) == sumAllValues(0,b-1)` | `b > 0`                              |
| **checkValueShift**                    | `mod(a,b) == mod(a-b,b)` recursively         | `b > 0`, `a >= 0`                    |

**Source**: `src/main/scala/v1/chapter2/div/properties/ModSum.scala`

---

# Domain 2: Lists

## 2.1 ListUtils (`v1.list.ListUtils`)

Core list operations.

| Function                             | Definition                                                  | Notes              |
|--------------------------------------|-------------------------------------------------------------|--------------------|
| **sum(list)**                        | `if empty then 0 else head + sum(tail)`                     | Recursive sum      |
| **slice(list, from, to)**            | `if from==to then [list(to)] else slice(...) ++ [list(to)]` | Tail-recursive     |
| **head(list)**                       | First element                                               | Requires non-empty |
| **tail(list)**                       | All but first                                               | Requires non-empty |
| **last(list)**                       | Final element                                               | Requires non-empty |
| **checkAllBiggerThanValue(list, v)** | All elements > v                                            | Boolean check      |

**Mathematical Definition** (from [articles/list.md](./articles/list.md)):

```math
\begin{aligned}
sum(L) &= 
\begin{cases}
0 & \text{if } L = L_e \\
head(L) + sum(tail(L)) & \text{otherwise} \\
\end{cases} \\
L[f \dots t] &= 
\begin{cases}
[ L_t ] & \text{if } f = t \\
\text{slice}(L, f, t - 1) ⧺ [L_t] & \text{if } f < t \\
\end{cases}
\end{aligned}
```

**Source**: `src/main/scala/v1/chapter3/list/ListUtils.scala`

---

## 2.2 ListBoundUtils (`v1.list.ListBoundUtils`)

Bounds checking for lists.

| Function                                   | Statement                   | Notes                            |
|--------------------------------------------|-----------------------------|----------------------------------|
| **allGreaterThan(list, v)**                | All elements > v
| **allPositive(list)**                      | All elements > 0            | Alias for `allGreaterThan(_, 0)` |
| **assertGreaterThanAtIndex(list, v, pos)** | `list(pos) > v`             | Requires allGreaterThan          |
| **assertAppendGreaterThan(a, b, v)**       | `allGreaterThan(a ++ b, v)` | If both > v                      |

**Source**: `src/main/scala/v1/chapter3/list/ListBoundUtils.scala`

---

## 2.3 Integral (`v1.list.integral.Integral`)

Bounded list prefix sum (discrete integral).

```
apply(0) = list(0) + init
apply(k) = list(k) + apply(k-1)
```

| Field/Method | Definition             | Notes                   |
|--------------|------------------------|-------------------------|
| **list**     | Original list          | `List[BigInt]`          |
| **init**     | Initial value          | `BigInt`                |
| **acc**      | Accumulated list       | Same size as list       |
| **head**     | `list.head + init`     | First accumulated value |
| **apply(k)** | Cumulative sum up to k
| **last**     | `init + sum(list)`     | Final accumulated value |
| **size**     | `list.size`

**Mathematical Definition** (from [articles/integral.md](./articles/integral.md)):

```math
\begin{aligned}
I_k &:= 
\begin{cases}
L_0 + init & \text{if } k = 0 \\
\text{Integral}(\text{tail}(L),\ \text{head}(L) + init)_{(k - 1)} & \text{if } k > 0 \\
\end{cases}
\end{aligned}
```

**Source**: `src/main/scala/v1/chapter3/list/integral/Integral.scala`

---

## 2.4 IntegralProperties (`v1.list.integral.properties.IntegralProperties`)

| Property                              | Statement                                | Preconditions              |
|---------------------------------------|------------------------------------------|----------------------------|
| **assertHeadValueMatchDefinition**    | `acc(0) == list(0) + init`               | `list.nonEmpty`            |
| **assertAccDifferenceEqualsTailHead** | `acc(1) - acc(0) == list(1)`             | `list.size > 1`            |
| **assertAccDiffMatchesList**          | `acc(pos+1) - acc(pos) == list(pos+1)`   | `list.size > 1`, valid pos |
| **assertAccMatchesApply**             | `apply(pos) == acc(pos)`                 | `list.nonEmpty`, valid pos |
| **assertSizeAccEqualsSizeList**       | `acc.size == list.size`                  | —                          |
| **assertLastEqualsSum**               | `acc.last == init + sum(list)`           | `list.nonEmpty`            |
| **assertIntegralEqualsSum**           | `apply(pos) == init + sum(list[0..pos])` | `list.nonEmpty`, valid pos |
| **assertLast**                        | `apply(size-1) == last`                  | `list.nonEmpty`            |

**Mathematical Properties** (from [articles/integral.md](./articles/integral.md)):

```math
\begin{aligned}
I_0 &= x_0 + init \\
I_k &= init + \sum_{i=0}^k x_i \\
I_{n-1} &= init + \sum_{i=0}^{n-1} x_i \\
I_{p+1} - I_p &= x_{p+1}
\end{aligned}
```

**Source**: `src/main/scala/v1/chapter3/list/integral/properties/IntegralProperties.scala`

---

## 2.5 SliceEquivalenceLemmas (`v1.list.properties.SliceEquivalenceLemmas`)

Three different slice implementations proved equivalent.

| Property                                | Statement                                | Preconditions                   |
|-----------------------------------------|------------------------------------------|---------------------------------|
| **headRecursiveSlice(list, from, to)**  | Forward slice using Cons                 | `0 <= from <= to < list.length` |
| **indexRangeValues(list, from, to)**    | Index-based slice                        | Same                            |
| **sliceEqualsSpec**                     | `headRecursiveSlice == indexRangeValues` | Same                            |
| **appendOne**                           | `list ++ List(e) == list :+ e`           | —                               |
| **appendCons**                          | `Cons(h,t) :+ e == Cons(h, t :+ e)`      | —                               |
| **tailHeadAndIndexRangeSlicesAreEqual** | All three implementations equal          | `0 <= from <= to < list.length` |

**Mathematical Proof** (from [articles/list.md](./articles/list.md)):

```math
\begin{aligned}
\forall \text{ } L \in 𝕃, \forall \text{ } i, j \in \mathbb{N},\ i \leq j < |L| \\
\text{slice}(L, i, j) &= L[i \dots j]
\end{aligned}
```

**Source**: `src/main/scala/v1/chapter3/list/properties/SliceEquivalenceLemmas.scala`

---

## 2.6 ListUtilsProperties (`v1.list.properties.ListUtilsProperties`)

| Property                            | Statement                                                | Preconditions                                      |
|-------------------------------------|----------------------------------------------------------|----------------------------------------------------|
| **listSumAddValue**                 | `sum(List(v) ++ L) == v + sum(L)`                        | —                                                  |
| **listCombine**                     | `sum(A ++ B) == sum(A) + sum(B)`                         | —                                                  |
| **listSwap**                        | `sum(A ++ B) == sum(B ++ A)`                             | —                                                  |
| **listAddValueTail**                | `sum(L ++ List(v)) == v + sum(L)`                        | —                                                  |
| **assertAppendToSlice**             | `slice(L,f,t) == slice(L,f,t-1) ++ [L_t]`                | `f >= 0`, `f < t`, `t < list.size`                 |
| **assertTailShiftLeft**             | `list(pos) == list.tail(pos-1)`                          | `list.nonEmpty`, valid pos                         |
| **accessTailShiftRight**            | `list.tail(pos) == list(pos+1)`                          | `list.nonEmpty`, valid pos                         |
| **assertLastEqualsLastPosition**    | `list.last == list(size-1)`                              | `list.nonEmpty`                                    |
| **checkAllBiggerThanValueAtIndex**  | If all > v, then `list(pos) > v`                         | `checkAllBiggerThanValue(list,v)`, valid pos       |
| **checkAllBiggerThanValueHeadTail** | `list.head > v && checkAllBiggerThanValue(list.tail, v)` | `checkAllBiggerThanValue(list,v)`, `list.nonEmpty` |

**Mathematical Properties** (from [articles/list.md](./articles/list.md)):

```math
\begin{aligned}
\sum ([v] ⧺ L) &= v + \sum L \\
\sum (A ⧺ B) &= \sum A + \sum B \\
L[f \dots t] &= L[f \dots {(t - 1)}] ⧺ [L_t] \\
|L| > 0 &\implies L_{|L|-1} = \text{last}(L) \\
i > 0 &\implies L_i = \text{tail}(L)_{i-1}
\end{aligned}
```

**Source**: `src/main/scala/v1/chapter3/list/properties/ListUtilsProperties.scala`

---

## 2.7 ListProduct (`v1.list.properties.ListProduct`)

Product of all elements in a list. Provides lemmas about product factorization.

### `product(list: List[BigInt]): BigInt`

Recursive product: empty list → `1`, otherwise `head * product(tail)`.

| Lemma                              | Statement                                                       | Preconditions |
|------------------------------------|-----------------------------------------------------------------|---------------|
| **singletonProduct**               | `product(List(x)) == x`                                         | —             |
| **productPullOutElement**          | `product(listA ++ List(e) ++ listB) == e * product(listA ++ listB)` | —          |
| **productConcatLemma**             | `product(listA ++ listB) == product(listA) * product(listB)`    | —             |
| **productConcatCommutative**       | `product(listA ++ listB) == product(listB ++ listA)`            | —             |
| **positiveProduct**                | `product(elements) > 0`                                         | `allGreaterThan(elements, 0)` |

**Source**: `src/main/scala/v1/chapter3/list/properties/ListProduct.scala`

---

## 2.8 ListProductDiv (`v1.list.properties.ListProductDiv`)

Divisibility lemmas: every element of a list divides the product of the list.

| Lemma                              | Statement                                                       | Preconditions |
|------------------------------------|-----------------------------------------------------------------|---------------|
| **ListProductDiv**                 | `mod(product(elements), elements.head) == 0`                    | `elements.nonEmpty`, `allGreaterThan(elements, 0)` |
| **allElementsDivideProduct**       | `mod(product(elements), x) == 0` for every `x in elements`      | `allGreaterThan(elements, 0)` |
| **insertedElementDividesProduct**  | `mod(product(prefix ++ List(e) ++ suffix), e) == 0`             | `e > 0`, `allGreaterThan(prefix ++ suffix, 0)` |

**Source**: `src/main/scala/v1/chapter3/list/properties/ListProductDiv.scala`

---

# Domain 3: Cycles

## 3.1 ModCycle (`v1.cycle.mod.ModCycle`)

Lowest-level cycle using modulo indexing.

```
apply(k) = values(k % size)
```

| Field/Method | Definition         | Notes                 |
|--------------|--------------------|-----------------------|
| **values**   | `List[BigInt]`     | Non-empty, stored raw |
| **size**     | `values.size`
| **apply(k)** | `values(k % size)` | Unbounded access      |
| **sum**      | Sum of all values

**Invariant**: `values.nonEmpty && checkPositiveOrZero(values)` (constructor require)

**Mathematical Definition** (from [articles/cycle.md](./articles/cycle.md)):

```math
\begin{aligned}
L &= [v_0, v_1, \dots, v_{n-1}] \in \mathbb{N}_0^n,\quad n = |L|,\quad n > 0 \\
\text{ModCycle}_i &= L_{i \text{ mod } n}
\end{aligned}
```

**Source**: `src/main/scala/v1/chapter4/cycle/mod/ModCycle.scala`

---

## 3.2 MemCycle (`v1.cycle.memory.MemCycle`)

Memory cycle wrapping ModCycle with caching.

| Field/Method | Definition     | Notes         |
|--------------|----------------|---------------|
| **cycle**    | `ModCycle`     | Delegation    |
| **values**   | `cycle.values` | Direct access |
| **size**     | `cycle.size`
| **apply(k)** | `cycle(k)`     | Delegates     |

**Invariant**: `isValid(values, modIsZeroForAllValues, ...)`

**Source**: `src/main/scala/v1/chapter4/cycle/memory/MemCycle.scala`

---

## 3.3 RecursiveCycle (`v1.cycle.recursive.RecursiveCycle`)

Recursively defined cycle (equivalent to ModCycle).

```
apply(0) = values(0)
apply(k) = values(k) if k < size else apply(k - size)
```

**Proved Equivalent to ModCycle** in [articles/cycle.md](./articles/cycle.md):

```math
\text{RecCycle}_i = \text{ModCycle}_i = L_{i \text{ mod } n}
```

**Source**: `src/main/scala/v1/chapter4/cycle/recursive/RecursiveCycle.scala`

---

## 3.4 CycleProperties (`v1.cycle.properties.CycleProperties`)

ModCycle lemmas.

| Property                                | Statement                                           | Preconditions                    |
|-----------------------------------------|-----------------------------------------------------|----------------------------------|
| **findValueInCycle**                    | `cycle(key) == cycle.values(mod(key, size))`        | `key >= 0`, `size > 0`           |
| **smallValueInCycle**                   | If `key < size`: `cycle(key) == cycle.values(key)`  | `key >= 0`, `key < size`         |
| **valueMatchAfterManyLoops**            | `cycle(key) == cycle(key + size*m)`                 | `key >= 0`, `size > 0`, `m >= 0` |
| **valueMatchAfterManyLoopsInBoth**      | `cycle(key + size*m1) == cycle(key + size*m2)`      | `key >= 0`, `m1,m2 >= 0`         |
| **propagateModFromValueToCycle**        | `cycle(key) % d == cycle.values(mod(key,size)) % d` | `key >= 0`, `d > 0`              |
| **assertCycleOfPosEqualsCycleOfModPos** | `cycle(pos) == cycle(mod(pos, size))`               | `pos >= 0`, `size > 0`           |
| **cycleValuePositiveOrZero**            | `cycle(pos) >= 0`                                   | `pos >= 0`, `size > 0`           |
| **rotateAtValue**                       | `rotateAt(k)(i) == cycle(k + i)`                    | `k >= 0`, `i >= 0`               |

**Mathematical Properties** (from [articles/cycle.md](./articles/cycle.md)):

```math
\begin{aligned}
\text{Cycle}_{i + n \cdot m} &= \text{Cycle}_i \\
\text{Cycle}_{i + n \cdot m_1} &= \text{Cycle}_{i + n \cdot m_2} \\
\text{Cycle}_i &= L_{i \text{ mod } n}
\end{aligned}
```

**Source**: `src/main/scala/v1/chapter4/cycle/properties/CycleProperties.scala`

---

## 3.5 MemCycleProperties (`v1.cycle.memory.properties.MemCycleProperties`)

Same as CycleProperties but for MemCycle wrapper.

| Property                                | Statement                                           | Preconditions                    |
|-----------------------------------------|-----------------------------------------------------|----------------------------------|
| **findValueInCycle**                    | `cycle(key) == cycle.values(mod(key, size))`        | `key >= 0`, `size > 0`           |
| **smallValueInCycle**                   | If `key < size`: `cycle(key) == cycle.values(key)`  | `key >= 0`, `key < size`         |
| **valueMatchAfterManyLoops**            | `cycle(key) == cycle(key + size*m)`                 | `key >= 0`, `size > 0`, `m >= 0` |
| **valueMatchAfterManyLoopsInBoth**      | `cycle(key + size*m1) == cycle(key + size*m2)`      | `key >= 0`, `m1,m2 >= 0`         |
| **propagateModFromValueToCycle**        | `cycle(key) % d == cycle.values(mod(key,size)) % d` | `key >= 0`, `d > 0`              |
| **assertCycleOfPosEqualsCycleOfModPos** | `cycle(pos) == cycle(mod(pos, size))`               | `pos >= 0`, `size > 0`           |

**Source**: `src/main/scala/v1/chapter4/cycle/memory/properties/MemCycleProperties.scala`

---

# Domain 4: Cycle Integrals

## 4.1 CycleIntegral (`v1.cycle.integral.recursive.CycleIntegral`)

Recursive cumulative sum over unbounded cycle.

```
apply(0) = cycle(0) + initialValue
apply(k) = cycle(k) + apply(k-1)
```

| Field/Method     | Definition     | Notes          |
|------------------|----------------|----------------|
| **initialValue** | Starting value | `BigInt`       |
| **cycle**        | `MemCycle`     | Backing cycle  |
| **apply(k)**     | Cumulative sum | Unbounded      |
| **size**         | `cycle.size`
| **sum**          | `cycle.sum()`  | Full cycle sum |

**Mathematical Definition** (from [articles/integral-cycle.md](./articles/integral-cycle.md)):

```math
\begin{aligned}
\text{CycleIntegral}(L, init)_i &= \sum_{j=0}^i \text{Cycle}(L)_j + init
\end{aligned}
```

**Source**: `src/main/scala/v1/chapter4/cycle/integral/recursive/CycleIntegral.scala`

---

## 4.2 ClassicCycleIntegral (`v1.cycle.integral.classic.ClassicCycleIntegral`)

Classic recursive definition of cycle integral.

**Source**: `src/main/scala/v1/chapter4/cycle/integral/classic/ClassicCycleIntegral.scala`

---

## 4.3 ModCycleIntegral (`v1.cycle.integral.mod.ModCycleIntegral`)

Modulo-based cycle integral formula.

```
apply(k) = (k div size) * sum + integralValues(k mod size) + initialValue
```

**Source**: `src/main/scala/v1/chapter4/cycle/integral/mod/ModCycleIntegral.scala`

---

## 4.4 CycleIntegralProperties (`v1.cycle.integral.recursive.properties.CycleIntegralProperties`)

| Property                                           | Statement                                                 | Preconditions                                  |
|----------------------------------------------------|-----------------------------------------------------------|------------------------------------------------|
| **assertCycleIntegralEqualsSumFirstPosition**      | `ci(0) == sum([init, cycle(0)])`                          | —                                              |
| **assertCycleIntegralEqualsSumSmallPositions**     | `ci(pos) == sum(firstValuesSlice(pos))`                   | `pos < size`, `pos > 0`                        |
| **assertCycleIntegralEqualsSliceSum**              | `ci(pos) == sum(getFirstValuesAsSlice(pos))`              | `pos < size`, `pos >= 0`                       |
| **assertNextPosition**                             | `ci(pos) == ci(pos-1) + ci.cycle(pos)`                    | `pos > 0`                                      |
| **assertDiffEqualsCycleValue**                     | `ci(pos+1) - ci(pos) == ci.cycle(pos+1)`                  | `pos >= 0`                                     |
| **assertSameDiffAfterCycle**                       | `ci(b) - ci(a) == ci(d) - ci(c)` where c=a+size, d=b+size | `pos >= 0`                                     |
| **assertLastElementBeforeLoop**                    | `ci(size-1) == sum(firstValuesSlice(size-1))`             | —                                              |
| **assertSumModValueAsListEqualsCycleIntegralLoop** | `ci(pos) == sum(getModValuesAsList(pos))`                 | `pos >= 0`                                     |
| **assertCycleIntegralEqualsSumOfModValuesAsList**  | `ci(pos) == sum(listModValues)`                           | `pos >= 0`                                     |
| **getFirstValuesAsSlice**                          | Helper: `[init] ++ slice(cycle, 0, pos)`                  | `pos >= 0`, `pos < size`                       |
| **getModValuesAsList**                             | Helper: builds list of cycle values                       | `pos >= 0`                                     |
| **assertFirstValuesAsSliceEqualsModValuesAsList**  | Two helper lists equal                                    | `pos >= 0`, `pos < size`                       |
| **assertCycleValuePositive**                       | `ci.cycle(pos) > 0`                                       | `pos >= 0`, `allGreaterThan(cycle.values, 0)`  |
| **assertCycleIntegralPositive**                    | `ci(pos) > 0`                                             | `init >= 0`, `allGreaterThan(cycle.values, 0)` |

**Key Lemma**: `assertCycleIntegralPositive` — proves integral values > 0 when cycle values > 0

**Mathematical Properties** (from [articles/integral-cycle.md](./articles/integral-cycle.md)):

```math
\begin{aligned}
\text{CycleIntegral}(L, init)_i &= \sum_{j=0}^i L_{(j \text{ mod } n)} + init \\
\text{CycleIntegral}_{i+1} - \text{CycleIntegral}_i &= L_{(i+1) \text{ mod } n}
\end{aligned}
```

**Source**: `src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralProperties.scala`

---

## 4.5 ClassicCycleIntegralProperties (`v1.cycle.integral.classic.properties.ClassicCycleIntegralProperties`)

Same properties as CycleIntegralProperties but for ClassicCycleIntegral.

| Property                                           | Statement                              | Preconditions |
|----------------------------------------------------|----------------------------------------|---------------|
| **assertCycleIntegralEqualsSumFirstPosition**      |
| **assertCycleIntegralEqualsSumSmallPositions**     |
| **assertCycleIntegralEqualsSliceSum**              |
| **assertNextPosition**                             | `ci(pos) == ci(pos-1) + ci.cycle(pos)` | `pos > 0`     |
| **assertDiffEqualsCycleValue**                     |
| **assertSameDiffAfterCycle**                       |
| **assertLastElementBeforeLoop**                    |
| **assertSumModValueAsListEqualsCycleIntegralLoop** |
| **assertCycleIntegralEqualsSumOfModlValuesAsList** |
| **getFirstValuesAsSlice**                          | Helper function
| **getModValuesAsList**                             | Helper function
| **assertFirstValuesAsSliceEqualsModValuesAsList**  |

**Source**: `src/main/scala/v1/chapter4/cycle/integral/classic/properties/ClassicCycleIntegralProperties.scala`

---

## 4.6 ModCycleIntegralProperties (`v1.cycle.integral.mod.ModCycleIntegralProperties`)

| Property                                 | Statement                                                             | Preconditions                           |
|------------------------------------------|-----------------------------------------------------------------------|-----------------------------------------|
| **assertFirstValuesMatchIntegral**       | `apply(pos) == integralValues(pos) + init`                            | `pos >= 0`, `pos < integralValues.size` |
| **assertSimplifiedDiffValuesMatchCycle** | `apply(pos+1) - apply(pos) == cycle.values(mod(pos+1, size))`         | `pos >= 0`                              |
| **assertModCycleEqualsCycleIntegral**    | `modCycleIntegral(pos) == cycleIntegral(pos)`                         | Matching cycles/initialValues           |
| **assertCycleIntegralMatchModCycleDef**  | `ci(pos) == div(pos,size)*sum + integralValues(mod(pos,size)) + init` | Matching cycles/initialValues           |

**Mathematical Formula** (from [articles/integral-cycle.md](./articles/integral-cycle.md)):

```math
\begin{aligned}
\text{ModCycleIntegral}(L, init)_i &= (i \text{ div } n) \cdot T + I_{i \text{ mod } n} + init
\end{aligned}
```

**Source**: `src/main/scala/v1/chapter4/cycle/integral/mod/ModCycleIntegralProperties.scala`

---

# Domain 5: Sieve Sequence

## 5.1 SieveUtils (`v1.seq.sieve.SieveUtils`)

Utility functions for sieve sequence construction.

| Function                                      | Purpose                                      | Notes |
|-----------------------------------------------|----------------------------------------------|-------|
| **product(list)**                             | Multiply all elements                        | |
| **isCoprime(value, primes)**                  | Check not divisible by any prime              | |
| **residues(modulus, primes)**                 | Generate coprime residues                     | |
| **filterList(list, divisor)**                 | Remove multiples of divisor                   | |
| **calculateGaps(sorted, modulus)**            | Compute gaps + wrap gap                       | |
| **rotateAt(list, index)**                     | Rotate list at index                          | |
| **hasPrimeFactorInList(d, primes)**           | `∃ p ∈ primes: mod(d, p) == 0`               | |
| **assertAllNotCoprimeInRange(limit, d, primes)** | `∀ d ∈ [d, limit): hasPrimeFactorInList(d, primes)` | |
| **assertRotateAtPreservesNonEmpty**           | rotateAt preserves non-emptiness              | `.holds` lemma |
| **assertHasPrimeFactorImpliesNotCoprime**     | `hasPrimeFactorInList(d) ⇒ !isCoprime(d)`     | `.holds` lemma |
| **assertNoDivisorInRangeHelper**              | `Calc.mod(n, d) != 0` for all d in `[from, to)` | `.holds` lemma |

**Source**: `src/main/scala/v1/chapter6/seq/sieve/SieveUtils.scala`

---

## 5.2 GapCycle (`v1.cycle.gap.GapCycle`)

Wrapper around MinBoundList with **strict positivity** invariant.

| Field/Method                           | Definition                   | Notes             |
|----------------------------------------|------------------------------|-------------------|
| **values**                             | `MinBoundList`               | `lowerBound == 0` |
| **memCycle**                           | `MemCycle(values.list)`      | All gaps > 0      |
| **integral**                           | `CycleIntegral(0, memCycle)`
| **gap(index)**                         | `memCycle(index)`
| **cumulativeSum(index)**               | `integral(index)`
| **size**                               | `values.size`
| **sum**                                | `memCycle.sum()`
| **assertCumulativeSumPositive**        | `cumulativeSum(pos) > 0`     | `.holds` lemma    |
| **allGreaterThan→checkPositiveOrZero** | Implication lemma            | `.holds` lemma    |

**Invariant**: `allGreaterThan(values.list, 0)` — ALL gaps > 0 (strict positivity)

**Source**: `src/main/scala/v1/chapter4/cycle/gap/GapCycle.scala`

---

## 5.3 CycleSieveSequence (`v1.seq.sieve.CycleSieveSequence`)

Main sequence object.

```
integral = CycleIntegral(primes.head, gapCycle.memCycle)

apply(0) = head
apply(k) = integral(k-1) for k >= 1
```

| Field/Method | Definition                                      | Notes                       |
|--------------|-------------------------------------------------|-----------------------------|
| **primes**   | `List[BigInt]`                                  | All > 0                     |
| **gapCycle** | `GapCycle`                                      | Carries allGreaterThan      |
| **integral** | `CycleIntegral(primes.head, gapCycle.memCycle)` | Key: uses gapCycle.memCycle |
| **apply(k)**     | `head` if k=0, else `integral(k-1)`
| **head**     | `primes.head`                                   | Prime > 0                   |
| **modulus**  | `product(primes.tail)`
| **first-step progress invariant** | `primes.head + gapCycle.memCycle(0) > primes.head` | Constructor requirement expressing that `apply(1)` is strictly above the current head. Preserved by every verified construction path. |
| **assertNextHeadGreaterThanHead()** | `apply(1) > head` | Public alias exposing first-step progress without unfolding `CycleIntegral`; also makes positivity and nonzero facts for the next head cheap to derive. Verified with 8825 valid. |
| **nextWithGapCycle(newGapCycle)** | Builds `CycleSieveSequence(apply(1) :: primes, newGapCycle)` | Conditional verified builder. Requires the supplied gap cycle's first generated value to preserve the old filters and exclude the new head. Verified with 7997 valid. |
| **next**     | Builds next Cycle stage with `apply(1) :: primes` and a `GapCycle` from `SieveSequenceNextLevel.nextGapsWalk(this)` | No longer `@extern`. Conditional verified walk-backed builder. Requires `nextGapsWalk(this)` to be non-empty and all positive, then requires the first post-head value generated by the new gap cycle to preserve the old filters, exclude the new head, and preserve `Calc.mod(SieveUtils.product(primes), apply(1)) != 0`. Verified with 8070 valid. |

**Critical Chain**:

- `seq.integral.initialValue = seq.head > 0` ✓
- `seq.integral.cycle.values = seq.gapCycle.memCycle.values`
- `seq.gapCycle` requires `allGreaterThan(values.list, 0)` ✓
- So `assertCycleIntegralPositive(seq.integral, pos)` is **provable**!

**Source**: `src/main/scala/v1/chapter6/seq/sieve/CycleSieveSequence.scala`

---

## 5.4 SpecSieveSequence (`v1.seq.sieve.SpecSieveSequence`)

Linear-scan baseline model of sieve sequences. Generates values by scanning consecutive integers forward, accepting those coprime to the tail primes.

### Public API

| Field/Method | Definition | Notes |
|---|---|---|
| **primes** | `AllPrimesSoFarList` | Descending, head is the newest/starting prime |
| **head** | `primes.head` | Starting value, coprime to all tail primes |
| **filterPrimes** | `primes.list.tail.list` | Active divisibility filters (tail only, not head) |
| **filterValues** | `PrimeUtils.primeValues(filterPrimes)` | Numeric divisor values |
| **filterModulus** | Product of filterPrimes | Period of the tail-filter pattern |
| **apply(k)** | `k`-th generated value | Linear scan, bounded by `searchBound(k)` |
| **passesFilter(v)** | `isCoprime(v, filterValues)` | Survives all tail primes |
| **accepts(v)** | `passesFilter(v)` | Requires `v >= head.value` |
| **indexOfAccepted(v)** | Index where `apply(k) == v` | Completeness witness |
| **assertApplyOneAtOrBeforeAccepted(v)** | `accepts(v)` ∧ `v > head.value` ⇒ `apply(1) <= v` | Public first-step completeness wrapper over the private skipped-interval proof. |
| **next** | Builds next stage with `primes.next` | Requires `primes.nextPrime.value < head.value * head.value`, in the same style as `List.head` requiring a non-empty list. Returns `SpecSieveSequence`. |

### Search Bound Lemmas

| Lemma | Statement | Notes |
|---|---|---|
| **searchBoundPassesFilter(k)** | `passesFilter(searchBound(k))` | Proves the inclusive search bound survives all active tail filters. Foundation for `apply(k)`'s completeness. Private `.holds`. |

### Gap Lemmas (proved)

| Lemma | Statement | Notes |
|---|---|---|
| **assertGapPositive(k)** | `apply(k+1) - apply(k) > 0` | Uses `applyStrictlyIncreases(k)`. Public `.holds`. |
| **assertGapPeriodic(k, p)** | `apply(k+1+p) - apply(k+p) == apply(k+1) - apply(k)` where `p = indexOfAccepted(head+M)` | Uses `assertBlockShift` at `k` and `k+1`. Public `.ensuring`. |
| **assertGapSum(p)** | `sum_{i=0}^{p-1} (apply(i+1)-apply(i)) == M` | Via `sumGap` (private) + `assertSumGapTelescopes` (private). Public `.holds`. |
| **assertSumGapPositive(from, until)** | `until > from ⇒ sumGap(from, until) > 0` | Private `.holds`. Positivity companion to `assertSumGapTelescopes`. Inducts on `until - from`, using `applyStrictlyIncreases(from)` for each summand. Foundation for proving every gap emitted by `mergedGapPrefix` is positive. |
| **assertFilterPreservesNextPosition(nextSeq, k)** | `nextSeq.filterValues.tail == filterValues` ∧ `nextSeq.accepts(apply(k))` ∧ `Calc.mod(apply(k+1), p) ≠ 0` ⇒ `nextSeq(indexOfAccepted(V)+1) == apply(k+1)` | Proves that adding a filter prime preserves the next-position relationship between two V0 sequences. Uses `nextDoesNotPassAcceptedValue` bidirectionally. Private .holds. 6379 valid. |
| **assertFilterPreservesNextGap(nextSeq, k)** | Same copy-case preconditions as `assertFilterPreservesNextPosition`: `nextSeq.filterValues.tail == filterValues` ∧ `nextSeq.accepts(apply(k))` ∧ `Calc.mod(apply(k+1), p) ≠ 0` ⇒ `nextSeq(vIdx+1) - nextSeq(vIdx) == apply(k+1) - apply(k)` | Private `.holds` corollary. Names the copied-gap fact so later gap-list proofs can consume it directly. Verified with 7259 valid. |
| **assertConsecutiveAcceptedByNextPreservesGap(nextSeq, k)** | If `nextSeq.filterValues.tail == filterValues`, its head is no smaller, and both `apply(k)` and `apply(k+1)` are in its domain and accepted, then `nextSeq(indexOfAccepted(apply(k))+1) - nextSeq(indexOfAccepted(apply(k))) == apply(k+1) - apply(k)` | Public `.holds`. General copy rule that does not require equal sequence heads. Uses a two-sided no-skipping argument to prove the next-sequence successor of `apply(k)` is exactly `apply(k+1)`. The explicit lower-bound preconditions keep cross-instance domain facts visible to Stainless. Full verification: 9149 valid. |

### Residue Cycle Lemmas

| Lemma | Statement | Notes |
|---|---|---|
| **assertApplyModIsCoprime(k)** | `isCoprime(Calc.mod(apply(k), filterModulus), filterValues)` | Proves every generated value's residue modulo `filterModulus` is coprime to all filter primes. Uses prefix-product decomposition via `expandedCoprimePreservesFilter`. Public `.holds`. |
| **assertApplyResidueCycles(k, p)** | `Calc.mod(apply(k + p), filterModulus) == Calc.mod(apply(k), filterModulus)` where `p = indexOfAccepted(head + filterModulus)` | Proves residue cycling with period p via `assertBlockShift`. Public `.ensuring`. |

### Filter Bridge Lemmas

Bridges between old-filter acceptance and next-filter acceptance for `SpecSieveSequence.next()`.

| Lemma | Statement | Notes |
|---|---|---|
| **assertAcceptedByNextWhenOldAcceptedAndNewHeadNonMultiple(nextSeq, value)** | `accepts(value)` ∧ `Calc.mod(value, nextSeq.filterValues.head) ≠ 0` ∧ `nextSeq.filterValues.tail == filterValues` ⇒ `nextSeq.accepts(value)` | Bridges old-filter acceptance plus non-multiple-of-new-head to next-filter acceptance. Private `.holds`. |
| **assertNextAcceptedImpliesOldAcceptedAndNewHeadNonMultiple(nextSeq, value)** | `nextSeq.accepts(value)` ∧ `nextSeq.filterValues.tail == filterValues` ⇒ `accepts(value)` ∧ `Calc.mod(value, nextSeq.filterValues.head) ≠ 0` | Reverse bridge: projects next-filter acceptance back to old-filter acceptance and non-multiple fact. Private `.holds`. |
| **assertRejectedByNextWhenNewHeadMultiple(nextSeq, value, p)** | `Calc.mod(value, p) == 0` ∧ `nextSeq.filterValues.head == p` ⇒ `¬nextSeq.accepts(value)` | Negative bridge: a multiple of the new head filter is rejected by nextSeq. Private `.holds`. |

### Index-Order Lemmas

| Lemma | Statement | Notes |
|---|---|---|
| **applyIndexOrderPreservesValues(from, until)** | `from ≤ until ⇒ apply(from) ≤ apply(until)` | Cumulative ordering: earlier indices produce no-larger values. Private `.holds`. |
| **applyIndexStrictlyPreservesValues(from, until)** | `from < until ⇒ apply(from) < apply(until)` | Strict companion: earlier indices produce strictly smaller values. Private `.holds`. |
| **valueBoundImpliesIndexBound(index, bound)** | `apply(index) ≤ apply(bound) ⇒ index ≤ bound` | Contrapositive: a value bound constrains the index. Private `.holds`. |
| **assertApplyMonotonic(from, until)** | `from ≤ until ⇒ apply(from) ≤ apply(until)` | Public wrapper for `applyIndexOrderPreservesValues`. Exposed for Canonical cross-instance lower-bound proofs. |

### Skip/Merge Lemmas (proof of gap merging)

The core lemmas for proving that when a new filter prime removes the immediate next value, the next-sequence skips ahead to the first surviving old-stream value and merges the intervening gaps.

| Lemma | Statement | Notes |
|---|---|---|
| **findFirstNonMultipleAfter(k, p, bound)** | Returns the first index `≥ k+1` where `Calc.mod(apply(res), p) ≠ 0`, with `res ≤ bound` | Recursive helper with `decreases(bound - k)`. Private `.ensuring`. |
| **assertFirstNonMultipleIsAtOrBefore(k, zIdx, p, bound)** | `Calc.mod(apply(zIdx), p) ≠ 0` ∧ `zIdx > k` ⇒ `findFirstNonMultipleAfter(k, p, bound) ≤ zIdx` | Proves the helper returns the *first* non-multiple, not just any. Private `.holds`. |
| **assertBlockShiftMultiple(k, n, period)** | `apply(period) == head + M` ⇒ `apply(k + n*period) == apply(k) + n*M` | Repeated block shift: shifting by n periods multiplies the shift. Private `.holds`. |
| **assertSkippedIndexBeforeFirstIsMultiple(k, idx, p, bound)** | `k < idx < findFirstNonMultipleAfter(k, p, bound)` ⇒ `Calc.mod(apply(idx), p) == 0` | Every old index between k and the first survivor is a multiple of p. Private `.holds`. |
| **assertNextAnchorBeforeFirstSurvivor(nextSeq, k, p, bound)** | `nextSeq.accepts(apply(k))` ⇒ `nextSeq(indexOfAccepted(apply(k))) < apply(m)` where `m = findFirstNonMultipleAfter(k, p, bound)` | Anchors the next-sequence index before the first old survivor. Private `.holds`. |
| **assertSkippedOldValueRejectedByNext(nextSeq, k, idx, p, bound)** | `k < idx < m` ⇒ `¬nextSeq.accepts(apply(idx))` where `m = findFirstNonMultipleAfter(k, p, bound)` | Composes the skip invariant with the negative filter bridge. Private `.holds`. |
| **assertNextValueAtOrBeforeFirstSurvivor(nextSeq, k, p, bound)** | `nextSeq(indexOfAccepted(apply(k)) + 1) ≤ apply(m)` where `m = findFirstNonMultipleAfter(k, p, bound)` | Upper inequality for the skip-to-first-survivor equality. Uses next-sequence completeness through `nextDoesNotPassAcceptedValue`. Private `.holds`. |
| **assertNextSuccessorOldIndexAfterAnchor(nextSeq, k)** | For `z = nextSeq(indexOfAccepted(apply(k)) + 1)`, `indexOfAccepted(z) > k` in the old sequence | Reverse-index helper for gap merging. Uses next-sequence strict growth, the reverse filter bridge, and old-stream monotonicity. Private `.holds`. |
| **assertNextSuccessorOldIndexWithinBound(nextSeq, k, p, bound)** | For `z = nextSeq(indexOfAccepted(apply(k)) + 1)`, `indexOfAccepted(z) ≤ bound` in the old sequence | Bounded reverse-index helper. Uses the upper inequality, old-stream monotonicity, and `valueBoundImpliesIndexBound`. Private `.holds`. |
| **assertFirstSurvivorAtOrBeforeNextValue(nextSeq, k, p, bound)** | `apply(m) ≤ nextSeq(indexOfAccepted(apply(k)) + 1)` where `m = findFirstNonMultipleAfter(k, p, bound)` | Lower inequality for the skip-to-first-survivor equality. Uses the reverse-index bounds, the reverse filter bridge, first-non-multiple minimality, and old-stream monotonicity. Private `.holds`. |
| **assertNextSuccessorIsFirstSurvivor(nextSeq, k, p, bound)** | `nextSeq(indexOfAccepted(apply(k)) + 1) == apply(findFirstNonMultipleAfter(k, p, bound))` | Bounded skip-to-first-survivor equality. Connects the upper and lower inequality helpers. Private `.holds`. |
| **assertPeriodBoundIsNonMultiple(nextSeq, k, period)** | For `p = nextSeq.filterValues.head` and `bound = k + p*period`, proves `p > 0`, `bound > k`, and `Calc.mod(apply(bound), p) != 0` | Private endpoint lemma for period-based bounded search. Exposes the facts callers need before constructing `findFirstNonMultipleAfter`. Private `.ensuring`. Verified with 7321 valid. |
| **assertSkipUntilNonMultiple(nextSeq, k, period)** | `nextSeq(vIdx+1) == apply(m)` where `m = findFirstNonMultipleAfter(k, p, bound)` and `bound = k + p*period` | Period-based private gap-merge wrapper. Uses block shifting to build a finite non-multiple endpoint, then delegates to the bounded skip-to-first-survivor equality. Private `.holds`. |
| **assertMergeLandsOnFirstSurvivor(nextSeq, k, period)** | Same landing equality as `assertSkipUntilNonMultiple`: `nextSeq(vIdx+1) == apply(m)` for the first old-stream non-multiple after `k` | Private property-name alias for the merge landing proof. Consumes `assertPeriodBoundIsNonMultiple`, constructs the first-survivor witness, and proves the equality directly. Private .holds. Verified with 7340 valid. |
| **assertMergeGapEqualsOldGapSum(nextSeq, k, period)** | `nextSeq(vIdx+1) - nextSeq(vIdx) == sumGap(k, m)` where `m = findFirstNonMultipleAfter(k, p, bound)` | Private merged-gap corollary. Uses the landing alias plus `assertSumGapTelescopes(k, m)` to prove that a skipped run merges exactly into the sum of old adjacent gaps. Verified with 7391 valid. |
| **nextMergedGapOldIndex(nextSeq, k, period)** | Returns an old index `res > k` such that `nextSeq.accepts(apply(res))`, choosing `k+1` for the copy case or the first bounded survivor for the merge case. Also exports both value equality (`nextSeq(nextSeqIndex+1) == apply(res)`) and difference equality (`nextSeq(nextSeqIndex+1) - nextSeq(nextSeqIndex) == sumGap(k, res)`) in the postcondition. | Private one-step index transformer for prefix construction. Preserves the recursive invariant that the returned old-stream value appears in the next sequence. Postcondition strengthened to include both gap equalities: each branch asserts the corresponding gap lemma (`assertFilterPreservesNextGap` for copy, `assertMergeGapEqualsOldGapSum` for merge) plus the direct value equality, and the `.ensuring` block re-exports both. Verified with 7755 valid. |
| **mergedGapPrefix(nextSeq, k, remaining, period)** | Builds `remaining` copied-or-merged gaps by repeatedly advancing through old indices and emitting `sumGap(k, nextK)` | Private bounded prefix transformer. Termination decreases on `remaining`, while skipped old indices are handled by `nextMergedGapOldIndex`. Verified with 7478 valid. |
| **assertMergedGapPrefixAllPositive(nextSeq, k, remaining, period)** | `allGreaterThan(mergedGapPrefix(nextSeq, k, remaining, period), 0)` | Private `.holds`. List-level positivity lift. Cons step combines single-step `assertSumGapPositive` (head) with inductive hypothesis (tail), making the head/tail split explicit via `ListBoundUtils.assertGreaterThanHeadTail`. Verified with 7555 valid. |
| **assertApplyEqualsHeadPlusGapSum(position)** | `apply(k) == head.value + sumGap(0, k)` for k >= 0 | Public `.holds`. Entry point for expressing V0.apply as a CycleIntegral. Wraps private `assertSumGapTelescopes(0, k)`. Verified with 7562 valid. |
| **gapList(from, count)** | Returns `List[BigInt] = [gap(from), ..., gap(from+count-1)]` | Public function. Structural recursion on `count`. Verified with 7568 valid. |
| **assertGapListPositive(from, count)** | `allGreaterThan(gapList(from, count), 0)` | Public `.holds`. Induction on `count`, uses `assertGapPositive` for each element. Verified with 7579 valid. |
| **assertGapListSize(from, count)** | `gapList(from, count).size == count` | Public `.holds`. Induction on `count`. Verified with 7590 valid. |
| **assertGapListFirstEqualsGap(from, count)** | `count > 0 ⇒ gapList(from, count).head == apply(from+1) - apply(from)` | Private `.holds`. The head of any non-empty gapList is the gap at `from`. Verified with 7836 valid. |
| **assertGapListApplyEqualsGapAtPosition(from, count, r)** | `r < count ∧ count > 0 ⇒ gapList(from, count)(r) == apply(from+r+1) - apply(from+r)` | Private `.holds`. Every position in gapList stores the corresponding adjacent gap. Induction on `r` shifting the `from` parameter. Verified with 7855 valid. |
| **specGapCycle(period)** | Builds `GapCycle(gapList(0, period))` when `period > 0` and `apply(period) == head.value + filterModulus`; exports `result.memCycle.values == gapList(0, period)` | Public constructor bridge for the Spec-vs-Cycle equivalence ticket. Packages the existing gap-list positivity and non-empty facts into the `GapCycle` constructor preconditions. Verified with 7771 valid. |
| **assertGapPeriodicMultiple(k, n, period)** | `gap(k + n*period) == gap(k)` for all `n >= 0`, given `apply(period) == head + M` | Private `.holds`. Extends `assertGapPeriodic` to multiple periods. Induction on `n`. Verified with 7877 valid. |
| **assertMemCycleGapMatch(i, period)** | `memCycle(i) == apply(i+1) - apply(i)` for all `i >= 0`, where `memCycle = specGapCycle(period).memCycle` | Public `.holds`. Two-case induction: `i < period` uses `smallValueInCycle` + `assertGapListApplyEqualsGapAtPosition`; `i >= period` uses `valueMatchAfterManyLoops` + `assertGapPeriodic`. Exposed so representation bridges can consume the pure Spec fact without putting Cycle construction on Spec. |
| **assertSpecGapCycleIntegralBase(period)** | `CycleIntegral(head.value, specGapCycle(period).memCycle)(0) == apply(1)` when `period > 0` and `apply(period) == head.value + filterModulus` | Public base case for the Spec gap-cycle integral reconstruction theorem. Proves that the first integral step over the packaged Spec gaps reaches the second Spec-generated value. Verified with 7788 valid. |
| **assertSpecGapCycleIntegralMatchesApply(period, k)** | `CycleIntegral(head.value, specGapCycle(period).memCycle)(k-1) == apply(k)` for all `k > 0`, given `period > 0` and `apply(period) == head.value + filterModulus` | Public general integral reconstruction theorem. Induction on `k`: base `assertSpecGapCycleIntegralBase`, step uses `assertNextPosition` + `assertMemCycleGapMatch`. Verified with 7943 valid. |
| **assertMergedGapPrefixHeadMatchesNext(nextSeq, k, period)** | `mergedGapPrefix(nextSeq, k, 1, period).head == nextSeq(vIdx+1) - nextSeq(vIdx)` where `vIdx = nextSeq.indexOfAccepted(apply(k))` | Private `.holds`. Proves the first emitted gap matches the corresponding next-sequence gap. Relies on `nextMergedGapOldIndex`'s strengthened postcondition. Verified with 7643 valid. |
| **assertApplyIncreases(fromIndex, toIndex)** | `apply(fromIndex) < apply(toIndex)` when `fromIndex < toIndex` | Private `.holds`. Proves strict increase over arbitrary distances by induction on `toIndex - fromIndex` using `applyStrictlyIncreases`. Verified with 7755 valid. |
| **assertApplyInjective(firstIndex, secondIndex)** | `firstIndex == secondIndex` given `apply(firstIndex) == apply(secondIndex)` | Public `.holds`. Proves injectivity of `apply` by contradiction using `assertApplyIncreases`. Verified with 7755 valid. |
| **assertMergedGapPrefixMatchesNext(nextSeq, k, seqIndex, remaining, period)** | `mergedGapPrefix(...) == nextSeq.gapList(seqIndex, remaining)` where `nextSeq(seqIndex) == apply(k)` | Private `.holds`. Full prefix equality. Induction on `remaining`: head from `assertMergedGapPrefixHeadMatchesNext`, tail from IH with `nextSeq.assertApplyInjective` to connect `seqIndex` to `nextSeq.indexOfAccepted(apply(k))`. Verified with 7755 valid. |

### Filter Membership Lemmas

Proving that a prime divisor below `head` appears in `filterValues`, using parallel scans of the sorted prime list and its value list.

| Lemma | Statement | Notes |
|---|---|---|
| **assertFilterValuesContainsInTail(d, tail, tailFilterValues, n)** | `contains(d, tail)` ∧ `tailFilterValues == primeValues(tail.list)` ∧ `mod(n, d) == 0` ⇒ `tailFilterValues.head == d` when found | Scans a prime tail and its value list in parallel, proving matching element positions. Private `.holds`. |
| **assertFilterValuesContains(d)** | `contains(d, primes.list.tail)` ∧ `mod(apply(1), d) == 0` ⇒ d is in `filterValues` | Uses `assertFilterValuesContainsInTail` for the recursive step. Proves d's value appears in the filter list by scanning the tail primes. Private `.holds`. |
| **divisorInFilterValues(n, d, values)** | `mod(n, d) == 0` ∧ `listContains(d, values)` ⇒ `!isCoprime(n, values)` | Scans filter values for d, proving non-coprimality when d divides n. Private `.holds`. |
| **listContains(d, values)** | Scans values for d (utility function) | No `.holds`. |

### Prime Bridge Lemmas

Cross-object lemmas bridging `AllPrimesSoFarList` prime search with `SpecSieveSequence` generation.

| Lemma | Statement | Notes |
|---|---|---|
| **assertApplyOneAtOrBeforeAccepted(value)** | `accepts(value)` ∧ `value > head.value` ⇒ `apply(1) ≤ value` | First-step completeness: the first generated value cannot jump past any accepted value beyond the head. Private `.holds`. |
| **assertNextPrimePassesV0Filter(primes)** | `AllPrimesSoFarList.nextPrime(primes.list).value` is coprime to `PrimeUtils.primeValues(primes.list.tail.list)` | The next prime after the list head passes the V0 tail filter. Uses `PrimeUtils.primeIsCoprimeWithSmallerList`. Private `.holds`. |
| **assertApplyOneLeqValue(value)** | `accepts(value)` ∧ `value > head.value` ⇒ `apply(1) ≤ value` | Proves `apply(1)` ≤ any accepted value. Uses `indexOfAccepted` and `assertApplyMonotonic`. Private `.holds`. |
| **assertApplyOneGtHead()** | `head.value + 1 ≤ apply(1)` | Proves the first generated value is strictly larger than head + 1. Uses `applyStrictlyIncreases`. Private `.holds`. |
| **assertApplyOneIsPrimeIfBelowHeadSq()** | `apply(1) < head²` ⇒ `Prime.isPrime(apply(1))` | Uses the sqrt-bound lemma + divisor filtering to prove apply(1) cannot be composite below head². Private `.holds`. |
| **assertApplyOneBelowHeadSqFromUpper(value)** | `apply(1) ≤ value` ∧ `value < head²` ⇒ `apply(1) < head²` | Tiny conditional-branch arithmetic wrapper for feeding `assertApplyOneIsPrimeIfBelowHeadSq()`. Private `.holds`. |
| **assertApplyOnePrimeFromUpperBelowHeadSq(value)** | `apply(1) ≤ value` ∧ `value < head²` ⇒ `Prime.isPrime(apply(1))` | One-call wrapper around square-bound primality so the final bridge can avoid carrying divisor/filter proof VCs. Private `.holds`. |
| **assertOwnNextPrimeAccepted()** | `accepts(AllPrimesSoFarList.nextPrime(primes.list).value)` | Packages the current instance's direct next-prime result as a V0 tail-filter accepted value. Private `.holds`. |
| **assertApplyOneAtOrBeforeOwnNextPrime()** | `apply(1) ≤ AllPrimesSoFarList.nextPrime(primes.list).value` | Lemma 2 wrapper: the first V0 survivor cannot skip past the accepted direct next-prime result. Private `.holds`. |
| **assertApplyOnePrimeIfOwnNextPrimeBelowHeadSq()** | `nextPrime.value < head²` ⇒ `Prime.isPrime(apply(1))` | Conditional-branch wrapper proving apply(1) prime from the direct next-prime square bound, without requiring a global prime-before-square theorem. Private `.holds`. |

### P4 (Period equals residue count) — SKIPPED

The property `indexOfAccepted(head+M) == residues(M, filterValues).size` is mathematically true (by interval periodicity) but the Stainless proof requires a counting lemma that timed out. Left as open problem.

### Source

`src/main/scala/v1/chapter6/seq/sieve/SpecSieveSequence.scala`

---

## 5.5 CanonicalCycleSieve (`v1.seq.sieve.CanonicalCycleSieve`)

Intermediate representation that receives a `SpecSieveSequence` and extracts
its unique canonical `CycleSieveSequence`. This object owns all direct
Spec-to-Cycle construction and correspondence, keeping both underlying
sequence classes focused on their own semantics.

| Field/Method | Statement | Notes |
|---|---|---|
| **cycle** | `CycleSieveSequence(primeValues(spec.primes), spec.specGapCycle(period))` | Canonical extraction. Requires the positive period anchor, Spec next-prime square bound, and tail-product non-divisibility condition. |
| **assertApplyMatches(k)** | `cycle(k) == spec(k)` for `k >= 0` | Canonical behavior equality. Uses the shared head at zero and the Spec gap-cycle integral reconstruction for positive indices. |
| **assertHeadMatches()** | `cycle.head == spec.head.value` | Public representation alias. |
| **assertPrimesMatch()** | `cycle.primes == PrimeUtils.primeValues(spec.primes.list.list)` | Public representation alias. |
| **assertGapCycleMatches()** | `cycle.gapCycle.memCycle == spec.specGapCycle(period).memCycle` | Public representation alias. |
| **assertNextHeadMatches()** | `cycle(1) == spec.next.head.value` | Canonical next-head bridge. |
| **assertCurrentValueAtOrAboveNextHead(k)** | `k >= 1 ⇒ spec(k) >= spec.next.head.value` | Public ordering bridge. Combines current Spec monotonicity from index one with `assertNextHeadMatches` and canonical apply equality at index one. Isolates the domain fact needed by next-stage acceptance proofs. Full verification: 9170 valid. |
| **assertNextAcceptsMatches(value)** | `spec.next.accepts(value) == SieveUtils.isCoprime(value, cycle.primes)` | Canonical next-stage filter bridge. |
| **assertNextPrimesMatch()** | `cycle(1) :: cycle.primes == PrimeUtils.primeValues(spec.next.primes.list.list)` | Canonical next-stage raw-prime-list bridge. |
| **assertWalkDecisionMatchesNextAccept(k)** | `Calc.mod(cycle(k), cycle.head) != 0 == spec.next.accepts(cycle(k))` for `k >= 1` | Walk branch condition bridge. Connects `collectGaps` skip/keep decision to next-stage acceptance. |
| **assertCurrentNonMultipleAcceptedByNext(k)** | `k >= 1 ∧ Calc.mod(cycle(k), cycle.head) != 0 ⇒ spec.next.accepts(spec(k))` | Public constructive acceptance bridge. Combines current tail-filter acceptance with non-divisibility by the newly added head filter. Consumes `assertCurrentValueAtOrAboveNextHead` for the next-sequence domain bound, avoiding the previous combined-VC timeout. Full verification: 9213 valid. |
| **assertNextGapCycleValuesEqualSpecNextGapList(nextPeriod)** | `spec.next.specGapCycle(nextPeriod).memCycle.values == spec.next.gapList(0, nextPeriod)` | Canonical next-stage gap cycle values match spec.next gap list by construction. |
| **assertNextApplyMatches(nextPeriod, k)** | `CycleIntegral(spec.next.head, spec.next.specGapCycle(nextPeriod).memCycle)(k-1) == spec.next(k)` | Canonical next-stage apply match. Uses Spec's own verified gap-cycle integral reconstruction lemma. |
| **assertNextGapEqualsCurrentGapSum(nextPeriod, i)** | `spec.next(i+1) - spec.next(i) == spec(k_{i+1}) - spec(k_i)` where `k_i = spec.indexOfAccepted(spec.next(i))` | Single-gap merge property. Each next gap equals the sum of current gaps from `k_i` to `k_{i+1}-1`. Proves merge using `indexOfAccepted` instead of scanning positions. |
| **assertNextValueMatchesCyclePosition(k)** | `spec.next(k) == cycle(pos)` where `pos = spec.indexOfAccepted(spec.next(k))` for `k >= 0` | Value-level correspondence between next Spec stage and current canonical cycle. Uses `indexOfAccepted.ensuring` and `assertApplyMatches` to bridge. |
| **assertNextFirstGapMatchesSpecNext(nextPeriod)** | `spec.next(1) - spec.next(0) == spec.next.gapList(0, nextPeriod).head` | First single-gap equality for the Leg-3 gap-list proof (see `canonical-next-strategy.md`). Proves the head of the next gap list without scanning positions — pure arithmetic substitution plus `assertApplyMonotonic`. Foundation for the list-level lift. |
| **assertNextGapAtMatchesSpecNext(nextPeriod, index)** | `spec.next(index+1) - spec.next(index) == spec.next.gapList(0, nextPeriod).apply(index)` for `0 <= index < nextPeriod` | Positional single-gap equality. Generalizes `assertNextFirstGapMatchesSpecNext` to arbitrary index. Consumes `SpecSieveSequence.assertGapListApplyEqualsGapAtPosition` (made public) and `assertGapListSize` (to discharge the `.apply` precondition). Per-position input to the list-level equality. |
| **nextGapList(from, count)** | `[spec.next(from+1)-spec.next(from), ..., spec.next(from+count)-spec.next(from+count-1)]` | Canonical-computed next gap list, forward-ordered, built directly from `spec.next` adjacent differences. Sliding `from` parameter mirrors `spec.next.gapList`'s recursion shape. |
| **assertNextGapListMatchesSpecNext(from, count)** | `nextGapList(from, count) == spec.next.gapList(from, count)` | List-level equality. Induction on `count` with sliding `from`, mirroring `assertGapListPositive`. Consumes `assertGapListFirstEqualsGap` (made public) for the head case. Verified with 9062 valid. |
| **assertGapPeriodicMatchesSpec(k, period)** | `cycle(period+k+1) - cycle(period+k) == cycle(k+1) - cycle(k)` under `spec(period) == spec.head.value + spec.filterModulus` | Periodicity transfer. Pure transfer lemma: calls `spec.assertGapPeriodic`, rewrites `spec.apply` → `cycle` via `assertApplyMatches` at four positions. Verified with 9087 valid. |
| **assertGapPositiveMatchesSpec(k)** | `cycle(k+1) - cycle(k) > 0` | Positivity transfer. Pure transfer: calls `spec.assertGapPositive`, rewrites via `assertApplyMatches`. Verified with 9100 valid. |
| **assertCopyGapMatchesSpec(k)** | For `k >= 1`, if `cycle(k) mod cycle.head != 0` and `cycle(k+1) mod cycle.head != 0`: `spec.next(nextIndex+1) - spec.next(nextIndex) == cycle(k+1) - cycle(k)` where `nextIndex = spec.next.indexOfAccepted(spec(k))` | Canonical copy rule. When two consecutive current values survive the new head filter, their gap is copied unchanged. Uses `assertCurrentNonMultipleAcceptedByNext` and `assertConsecutiveAcceptedByNextPreservesGap`. Verified with 9266 valid. |
| **assertAcceptsEqualWhenTrue(seq1, seq2, v)** | `seq1 == seq2 ∧ seq1.accepts(v) ⇒ seq2.accepts(v)` | Directed instance-equality bridge. Requires `v >= seq1.head.value` and `seq1.passesFilter(v)`, unfolds structural equalities (`head`, `primes`) to transfer the bound to `seq2`. Verified with 9299 valid. |
| **assertAcceptsEqualWhenFalse(seq1, seq2, v)** | `seq1 == seq2 ∧ ¬seq1.accepts(v) ⇒ ¬seq2.accepts(v)` | Dual of `assertAcceptsEqualWhenTrue`. Requires `v >= seq1.head.value` and `¬seq1.passesFilter(v)`, unfolds structural equalities to transfer non-acceptance. |
| **assertCycleGapEqualsSpecGap(k)** | `spec(k+1) - spec(k) == cycle(k+1) - cycle(k)` for `k >= 0` | Pure consequence of `assertApplyMatches` at `k` and `k+1`. Isolates the cycle-side gap equality from the copy-gap lemma. |
| **assertNextAcceptsViaAlias(k)** | For `k >= 1` and `Calc.mod(cycle(k), cycle.head) != 0`: `nextSeq.accepts(spec(k))` where `nextSeq = spec.next` | Bridges a cached `.holds` acceptance result through a local `val` alias using `assertAcceptsEqualWhenTrue`. Requires explicit `assertCurrentValueAtOrAboveNextHead(k)` before the bridge call. |
| **assertCurrentMultipleRejectedByNext(k)** | For `k >= 1` and `Calc.mod(cycle(k), cycle.head) == 0`: `¬spec.next.accepts(spec(k))` | Rejection side of the merge rule. Mirror of `assertCurrentNonMultipleAcceptedByNext`. When a current value is a multiple of head, it is not coprime with `cycle.primes` and is rejected by the next stage. |
| **assertNextFilterModulusRelation()** | `spec.next.filterModulus == cycle.head * spec.filterModulus` | Period sum transfer. When the old head becomes a filter prime in `spec.next`, the filter modulus grows by that factor. |

**Source**: `src/main/scala/v1/chapter6/seq/sieve/CanonicalCycleSieve.scala`

---

## 5.6 SpecCycleSieveEquivalence (`v1.seq.sieve.SpecCycleSieveEquivalence`)

Local bridge lemmas for the Spec-vs-Cycle apply equivalence proof. These lemmas
do not introduce new mathematics; they expose already-obvious representation
facts under local names so the eventual top-level proof can depend on small,
verified aliases instead of rebuilding representation reasoning inline.

| Lemma | Statement | Notes |
|---|---|---|
| **assertHeadsMatchFromPrimeValues(spec, cycle)** | `cycle.primes == PrimeUtils.primeValues(spec.primes.list.list)` ⇒ `spec.head.value == cycle.head` | Public representation bridge. Converts full prime-list correspondence into head equality. Verified with 7794 valid. |
| **assertApplyZeroMatchesFromPrimeValues(spec, cycle)** | `cycle.primes == PrimeUtils.primeValues(spec.primes.list.list)` ⇒ `spec(0) == cycle(0)` | Public base-case apply bridge. Uses head equality plus both `apply(0)` definitions. Verified with 7826 valid. |
| **assertCycleApplyPositiveIsIntegral(cycle, position)** | `position > 0` ⇒ `cycle(position) == cycle.integral(position - 1)` | Public cycle-side apply bridge. Exposes the positive branch of `CycleSieveSequence.apply` under a local alias for the final equivalence proof. Verified with 7829 valid. |
| **assertCycleIntegralUsesGapCycle(cycle)** | `cycle.integral == CycleIntegral(cycle.head, cycle.gapCycle.memCycle)` | Public cycle-side integral alias. Names the integral construction for the final equivalence proof without unfolding class internals. Verified with 7829 valid. |
| **assertSpecCycleApplyPositiveMatchesFromSameHeadAndGaps(spec, cycle, period, position)** | `position > 0` ∧ `spec.head.value == cycle.head` ∧ `spec.specGapCycle(period).memCycle == cycle.gapCycle.memCycle` ⇒ `spec(position) == cycle(position)` | Public conditional positive-index equivalence theorem. Proves that same head plus same stored gaps reconstruct the same positive apply values. Verified with 7959 valid. |
| **assertSpecCycleApplyMatchesFromSameHeadAndGaps(spec, cycle, period, position)** | `position >= 0` ∧ `spec.head.value == cycle.head` ∧ `spec.specGapCycle(period).memCycle == cycle.gapCycle.memCycle` ⇒ `spec(position) == cycle(position)` | Public conditional all-index equivalence theorem. Splits `position == 0` by head equality and delegates positive positions to `assertSpecCycleApplyPositiveMatchesFromSameHeadAndGaps`. Verified with 7978 valid. |
| **assertSpecNextPrimeValuesExtendCurrent(spec)** | `spec.primes.nextPrime.value < spec.head.value * spec.head.value` ⇒ `PrimeUtils.primeValues(spec.next.primes.list.list) == spec.next.head.value :: PrimeUtils.primeValues(spec.primes.list.list)` | Public next-stage representation bridge. Exposes that Spec `next` prepends its new head to the current raw prime values. Verified with 7985 valid. |
| **assertConditionalNextPrimeValuesMatch(spec, cycle, newGapCycle)** | Current prime-list correspondence ∧ Spec next precondition ∧ `cycle(1) == spec.next.head.value` ∧ `newGapCycle` satisfies `nextWithGapCycle` preconditions ⇒ `cycle.nextWithGapCycle(newGapCycle).primes == PrimeUtils.primeValues(spec.next.primes.list.list)` | Public conditional next-stage raw-prime bridge. Converts the assumed next-head equality into the raw list correspondence needed for the next stage. Verified with 8020 valid. |
| **assertConditionalNextApplyMatchesFromSameHeadAndGaps(spec, cycle, newGapCycle, nextPeriod, position)** | Current prime-list correspondence ∧ Spec next precondition ∧ `cycle(1) == spec.next.head.value` ∧ `newGapCycle` satisfies `nextWithGapCycle` preconditions ∧ `nextSpec(nextPeriod) == nextSpec.head.value + nextSpec.filterModulus` ∧ `nextSpec.specGapCycle(nextPeriod).memCycle == nextCycle.gapCycle.memCycle` ⇒ `spec.next(position) == cycle.nextWithGapCycle(newGapCycle)(position)` | Public conditional next-stage apply bridge. Avoids the `@extern` `next()` method and reuses the all-index same-head/same-gaps theorem on `spec.next` and `cycle.nextWithGapCycle(newGapCycle)`. Verified with 8059 valid. |
| **assertFilterValuesMatchTailPrimes(spec, cycle)** | `cycle.primes == PrimeUtils.primeValues(spec.primes.list.list)` ⇒ `cycle.primes.tail == spec.filterValues` | Public representation bridge. Converts the same full prime-list correspondence into active-filter equality. This is the dependency needed by the next acceptance-predicate bridge. Verified with 7806 valid. |
| **assertSpecAcceptsMatchesCycleTailCoprime(spec, cycle, value)** | `cycle.primes == PrimeUtils.primeValues(spec.primes.list.list)` ∧ `value >= spec.head.value` ⇒ `spec.accepts(value) == SieveUtils.isCoprime(value, cycle.primes.tail)` | Public semantic bridge. Rewrites Spec acceptance into the cycle-side tail-coprime predicate by consuming `assertFilterValuesMatchTailPrimes`. Verified with 7817 valid. |
| **assertResiduesContainCoprimeBelowModulus(modulus, filters, residue)** | `0 <= residue < modulus` ∧ positive filters ∧ `SieveUtils.isCoprime(residue, filters)` ⇒ `SieveUtils.residues(modulus, filters).contains(residue)` | Public residue completeness alias (E1a). Exposes the existing `SieveUtils.assertGenerateResiduesContainsCoprime` proof in the exact one-value shape needed by the Spec/Cycle residue pipeline bridge. Verified with 8082 valid. |
| **assertResiduesAreCoprimeBelowModulus(modulus, filters, residue)** | `SieveUtils.residues(modulus, filters).contains(residue)` ⇒ `SieveUtils.isCoprime(residue, filters)` | Public residue soundness alias (E1b). Inverse of E1a: any element found in the residue list passes the coprime test. Verified with 8137 valid. |
| **assertExpandedResiduesRepresentPeriod(seq, value)** | `0 ≤ value < seq.head * seq.modulus ∧ isCoprime(value, seq.primes.tail)` ⇒ `expandResidues(residues(seq.modulus, seq.primes.tail), seq.modulus, seq.head).contains(value)` | Public E2 lemma. Proves the expanded residue pipeline covers exactly one period of coprime values. Proof decomposes `value = r + q*modulus` via DivMod, uses `assertModPreservesCoprime` for coprimality preservation, and `assertAddOffsetContains` + `assertExpandResiduesExtendsTo` for expansion membership. Verified with 8319 valid. |
| **assertNextFilteredContainsCoprime(seq, value)** | `0 <= value < seq.head * seq.modulus` ∧ `SieveUtils.isCoprime(value, seq.head :: seq.primes.tail)` ⇒ `SieveSequenceNextLevel.nextFiltered(seq).contains(value)` | Public reverse-direction filtered-pipeline lemma. Uses expanded-period membership plus `filterList` membership preservation. Verified with 8424 valid. |
| **assertNextSortedContainsCoprime(seq, value)** | `0 <= value < seq.head * seq.modulus` ∧ `SieveUtils.isCoprime(value, seq.head :: seq.primes.tail)` ⇒ `SieveSequenceNextLevel.nextSorted(seq).list.contains(value)` | Public reverse-direction sorted-pipeline lemma. Uses filtered membership plus sort membership preservation. Verified with 8424 valid. |
| **assertNextSortedOnlyContainsFiltered(seq, value)** | `SieveSequenceNextLevel.nextSorted(seq).list.contains(value)` ⇒ `SieveSequenceNextLevel.nextFiltered(seq).contains(value)` | Public forward-direction sorted-pipeline lemma. Proves sorting does not invent survivor values by exposing local induction lemmas for `insertSorted` and `sortFiltered`. Verified with 8456 valid. |
| **assertExpandedValueCoprimeViaPrefix(r, i, modulus, primes, prefixProd)** | `i >= 0` ∧ `modulus == prefixProd * product(primes)` ∧ `isCoprime(r, primes)` ⇒ `isCoprime(r + i * modulus, primes)` | Private arithmetic backbone for expanded-stage soundness. Exposes as a postcondition the fact that adding a multiple of the full modulus preserves coprimality with every remaining prime. Verified with 8503 valid. |
| **assertExpandedValueCoprime(r, i, modulus, primes)** | `i >= 0` ∧ `modulus == product(primes)` ∧ `isCoprime(r, primes)` ⇒ `isCoprime(r + i * modulus, primes)` | Private natural-shape wrapper around the prefix lemma. Intended as the arithmetic step for a future list-level expanded-membership soundness proof. Verified with 8513 valid. |
| **assertGeneratedOffsetContainsOnlyCoprime(modulus, primes, value, from, i)** | `value ∈ addOffset(generateResidues(from, modulus, primes), i * modulus)` ⇒ `isCoprime(value, primes)` | Private structural soundness lemma for one generated-offset block. Recurses over `generateResidues(from, ...)` and calls `assertExpandedValueCoprime` only when the residue was kept by the coprime filter. Verified with 8556 valid. |

**Source**: `src/main/scala/v1/chapter6/seq/sieve/SpecCycleSieveEquivalence.scala`

---

## 5.7 SieveSequenceProperties (`v1.seq.sieve.properties.SieveSequenceProperties`)

> **NOTE**: This file does not yet exist. Properties listed below are aspirational.

| Property                 | Statement              | Notes |
|--------------------------|------------------------|-------|
| **assertS1HeadIsThree**  | S_1().head == 3
| **assertS1PrimesLength** | S_1().primes.size == 2

**Source**: `src/main/scala/v1/chapter6/seq/sieve/properties/SieveSequenceProperties.scala` (not yet implemented)

---

## How CycleSieveSequence Chains Together

```
CycleSieveSequence
├── primes: List[BigInt]               (all > 0)
├── gapCycle: GapCycle
│   ├── values: MinBoundList           (allGreaterThan > 0)
│   ├── memCycle: MemCycle
│   │   └── cycle: ModCycle
│   │       └── values: List[BigInt]   (allGreaterThan > 0 via GapCycle)
│   └── integral: CycleIntegral
│       └── cycle → memCycle (same object)
├── integral: CycleIntegral           (initialValue = head, cycle = gapCycle.memCycle)
│   └── apply(k) = head + sum(gapCycle.gaps(0..k-1))
└── apply(k) = head if k=0 else integral(k-1)
```

**Key consequence**: `seq.integral.cycle` and `seq.gapCycle.memCycle` are the **same object**.
So `allGreaterThan(seq.integral.cycle.values, 0)` is provable from `GapCycle`'s invariant.

---

# Domain 6: Prime

## 6.1 Prime (`v1.prime.Prime`)

Prime number type with primality verification at construction.

| Field/Method      | Definition                            | Notes                     |
|-------------------|---------------------------------------|---------------------------|
| **value**         | `inputValue`                          | `BigInt`, guaranteed prime |
| **apply()**       | `value`                               | Accessor                  |
| **isPrime(n)**    | `n > 1 && noDivisorInRange(n, 2, n)`  | Companion object method   |
| **noDivisorInRange** | Checks `[from, to)` for divisors   | `@tailrec`, requires `n >= 0` |

### Lemmas

| Lemma | Statement | Preconditions |
|-------|-----------|---------------|
| **noDivisorInRangeExcludesValue** | From `noDivisorInRange(n, from, to)` and `value ∈ [from, to)` derives `mod(n, value) != 0` | `n >= 0`, `from >= 1`, `to >= from`, `value >= from`, `value < to` |

**Invariant**: `Prime.isPrime(inputValue)` holds at construction.

**Source**: `src/main/scala/v1/chapter5/prime/Prime.scala`

## 6.2 PrimeUtils (`v1.prime.PrimeUtils`)

Utility functions over lists of primes.

| Function                        | Signature                                         | Notes                         |
|---------------------------------|---------------------------------------------------|-------------------------------|
| **primorial(primes)**           | Product of all prime values                       | Empty → `1`                   |
| **biggerPrime(primes)**         | Largest prime in non-empty list                   | Structural recursion          |
| **isMultiple(value, primes)**   | Check divisibility by any prime in list           | `@tailrec`, requires `value > 1` |
| **primeValues(primes)**         | Extract `List[BigInt]` from `List[Prime]`         | —                             |

### Lemmas

| Lemma                    | Statement                                          | Preconditions |
|--------------------------|----------------------------------------------------|---------------|
| **primorialUnfold**      | `primorial(p :: ps) == p.value * primorial(ps)`     | —             |
| **primorialPositive**    | `primorial(primes) > 0`                            | —             |
| **primeIsCoprimeWithSmallerList** | `isPrime(v) ∧ descending(primes) ∧ head.value < v` ⇒ `isCoprime(v, primeValues(primes))` | `v > 1`, `primes.nonEmpty`, `isDescending(primes)`, `head.value < v` |

**Source**: `src/main/scala/v1/chapter5/prime/PrimeUtils.scala`

## 6.3 PrimeProperties (`v1.prime.properties.PrimeProperties`)

Euclid's theorem formalization: proving that given any non-empty list of primes,
there exists a prime not in that list.

### Public API

| Function                     | Statement                                  | Preconditions    |
|------------------------------|--------------------------------------------|------------------|
| **primorialPlusOneModAny**   | `mod(primorial(primes) + 1, p) != 0` for every p in primes | —       |
| **newPrimeFromEuclid**      | Constructs a new `Prime` not in `primes`   | `primes.nonEmpty` |
| **euclidTheorem**           | Returns `true` (there exists a new prime)  | `primes.nonEmpty` |
| **newPrimeNotInList**       | `valueNotMatchesAny(primes, p.value)` for the Euclid result `p` | `primes.nonEmpty` |
| **notContainsFromValueNotMatchesAny** | `valueNotMatchesAny(primes, d)` ⇒ `!contains(d, sortedList)` | `sortedList.list == primes` |
| **euclidPrimeGreaterThanHead** | Euclid prime `d > sortedList.head.value` for complete prefix | `sortedList.nonEmpty`, `allPrimesSoFar(sortedList)` |
| **assertHeadIsPrime**       | Every `head` of a sieve sequence is prime  | `head > 1`, `isCoprime`, `checkAllPositive`, `assertAllNotCoprimeInRange` |
| **assertSmallestDivisorAtMostSqrt** | `!isPrime(n)` ⇒ `d*d ≤ n` for smallest divisor d | `n > 1`, `!isPrime(n)` |
| **assertCompositeSmallestPrimeDivisor** | Returns `d` with `d < n`, `isPrime(d)`, `d*d ≤ n` | `n > 1`, `!isPrime(n)` |
| **acceptedBelowHeadSquaredIsPrime** | `isCoprime(v, F)` ∧ `v < h²` ⇒ `isPrime(v)` | `h ≥ 2`, `checkAllPositive(F)`, `isCoprime(v, F)`, `assertAllNotCoprimeInRange(h, 2, F)` |

### Internal Lemmas

| Lemma                                    | Statement                                           | Preconditions |
|-------------------------------------------|-----------------------------------------------------|---------------|
| **findSmallestDivisor**                   | Smallest d in `[from, n)` with `mod(n, d) == 0`, or n | `n > 1`, `from >= 2`, `from <= n` |
| **findSmallestDivisorEquiv**              | `res == n ∨ mod(n, res) == 0`                       | Same |
| **findSmallestDivisorIsNImpliesNoDivisorInRange** | `res == n ⇒ noDivisorInRange(n, from, n)`  | Same + `res == n` |
| **assertModZeroImpliesDivTimesBEqualsA** | `mod(a, b) == 0 ⇒ div(a, b) * b == a`              | `b != 0` |
| **findSmallestDivisorReturnsFromIfZero** | `mod(n, from) == 0 ⇒ findSmallestDivisor(n, from) == from` | `from < n` |
| **findSmallestDivisorResultModZero**     | `findSmallestDivisor(n, 2) == d ∧ d < n ⇒ mod(n, d) == 0` | `d >= 2`, `d < n` |
| **assertSmallestDivisorIsPrime**          | `findSmallestDivisor(n, 2) == d` with `d < n` ⇒ `isPrime(d)` | Same |
| **primorialPlusOneTailLoop**             | Core engine behind `primorialPlusOneModAny`         | — |
| **valueNotMatchesAny**                   | `primes.head.value != v ∧ ...` for all primes       | — |
| **euclidTailLoop**                       | Core engine behind `euclidTheorem`                  | `v > 1`, `n == primorialSoFar * primorial(primes) + 1`, `mod(n, v) == 0` |
| **assertNoDivisorInRangeFromHelper**     | `Prime.noDivisorInRange(n, from, to)` using sieve completeness | `checkAllPositive`, `isCoprime`, `assertAllNotCoprimeInRange` |
| **assertHeadIsPrime**                    | `Prime.isPrime(head)` from sieve properties         | `head > 1`, `checkAllPositive`, `isCoprime`, `assertAllNotCoprimeInRange` |
| **assertFindSmallestDivisorAtMost**      | `Calc.mod(n, q) == 0` ∧ `q ≥ from` ⇒ `findSmallestDivisor(n, from) ≤ q` | `n > 1`, `from ≥ 2`, `q ≥ from`, `q < n` |
| **assertCompositeHasDivisorStrictlyBelowN** | `!isPrime(n)` ⇒ `findSmallestDivisor(n, 2) < n` ∧ `mod(n, d) == 0` | `n > 1`, `!isPrime(n)` |
| **assertDivisibleByFactorListNotCoprime** | `mod(n, d) == 0` ∧ `!isCoprime(d, primes)` ⇒ `!isCoprime(n, primes)` | `n > 1`, `d ≥ 2`, `checkAllPositive`, `mod(n, d) == 0` |
| **assertDivisorBelowHead**               | `d * d < head * head` ⇒ `d < head`                    | `d ≥ 2`, `head ≥ 2` |

### Key Insight

Assertions inside `.holds` lemmas are cached by Stainless and become available to callers.
This is how `primorialPlusOneModAny` feeds modular facts into `euclidTheorem` without
explicit postcondition enrichment. See §4 of [articles/euclid-theorem.md](articles/draft/draft-euclid-theorem.md).

**Source**: `src/main/scala/v1/chapter5/prime/properties/PrimeProperties.scala`

---

## 6.4 FilterPreservesPrimesProperties (`v1.prime.properties.FilterPreservesPrimesProperties`)

Proves that filtering out multiples of a prime preserves all primes in a list.
This is the inductive step of the sieve's correctness proof.

### Public API

| Lemma                                      | Statement                                          | Preconditions |
|--------------------------------------------|----------------------------------------------------|---------------|
| **assertPrimeNotDivisibleByDistinctPrime** | `isPrime(q) ∧ isPrime(p) ∧ q ≠ p ⟹ mod(q, p) ≠ 0` | `q >= 2`, `p >= 2` |
| **assertFilterPreservesAllPrimes**         | `isPrime(q) ∧ q ≠ filterPrime ⟹ mod(q, filterPrime) ≠ 0` | `q >= 2`, `filterPrime >= 2`, `isPrime(q)`, `isPrime(filterPrime)`, `q ≠ filterPrime` |
| **assertFilteredContainsAllPrimes**        | `q ∈ originalPrimes ∧ isPrime(q) ∧ q ≠ filterPrime ⟹ q ∈ filteredPrimes` | `filterPrime >= 2`, `isPrime(filterPrime)`, `q >= 2`, `isPrime(q)`, `q ≠ filterPrime`, `originalPrimes.contains(q)` |

### Internal Lemmas

| Lemma                                      | Statement                                          | Preconditions |
|--------------------------------------------|----------------------------------------------------|---------------|
| **noDivisorInRangeImpliesModNonZero**      | `noDivisorInRange(n, from, to) ∧ d ∈ [from, to) ⟹ mod(n, d) ≠ 0` | `n >= 0`, `from >= 1`, `to >= from`, `d >= from`, `d < to` |

### Key Insight

The helper lemma `noDivisorInRangeImpliesModNonZero` bridges the gap between the recursive
`noDivisorInRange` predicate and a specific modulo check. The SMT solver can't automatically
connect a value `p` to the range `[2, q)` in `noDivisorInRange(q, 2, q)`, so we prove it
explicitly by induction on `to - from`.

**Source**: `src/main/scala/v1/chapter5/prime/properties/FilterPreservesPrimesProperties.scala`

---

## 6.5 SortedPrimeList (`v1.prime.SortedPrimeList`)

Descending sorted list of `Prime` values (strictly descending: each element > next).

### Public API

| Field/Method      | Definition                            | Notes                     |
|-------------------|---------------------------------------|---------------------------|
| **list**          | `List[Prime]`                         | Underlying list           |
| **isEmpty**       | `list.isEmpty`                        |                           |
| **nonEmpty**      | `list.nonEmpty`                       |                           |
| **size**          | `list.size`                           |                           |
| **head**          | `list.head`                           | Requires non-empty        |
| **last**          | `list.last`                           | Requires non-empty        |
| **apply(i)**      | `list(i)`                             | Valid index               |
| **insert(x)**     | Insert preserving descending order    | Returns new SortedPrimeList |
| **remove(i)**     | Remove at index preserving order      | Valid index               |
| **tail**          | `SortedPrimeList(list.tail)`          | Requires non-empty        |

### Companion Object Lemmas

| Lemma                              | Statement                                      | Preconditions |
|------------------------------------|------------------------------------------------|---------------|
| **isDescending(list)**             | Strictly descending check                      | —             |
| **assertSortFilteredDescending**   | `isDescending(sortFiltered(list))`             | —             |
| **assertInsertSortedDescending**   | `isDescending(list)` ⇒ `isDescending(insertSorted(x, list))` | — |
| **assertTailDescending**           | `isDescending(list)` ∧ `nonEmpty` ⇒ `isDescending(list.tail)` | — |
| **assertRemoveKeepsDescending**    | `isDescending(list)` ⇒ `isDescending(removeAt(list, i))` | Valid index |

**Invariant**: `SortedPrimeList.isDescending(list)` holds at construction.

**Source**: `src/main/scala/v1/chapter5/prime/SortedPrimeList.scala`

---

## 6.6 AllPrimesSoFarList (`v1.prime.AllPrimesSoFarList`)

Stores a complete prefix of discovered primes in descending order. The `allPrimesSoFar` invariant guarantees that every prime value at or below the head is contained in the list.

### Class API

| Field/Method      | Definition                            | Notes                     |
|-------------------|---------------------------------------|---------------------------|
| **list**          | `SortedPrimeList`                     | Underlying descending list |
| **isEmpty**       | `list.isEmpty`                        |                           |
| **size**          | `list.size`                           |                           |
| **head**          | `list.head`                           | Requires non-empty        |
| **last**          | `list.last`                           | Requires non-empty        |
| **apply(i)**      | `list(i)`                             | Valid index               |
| **insert(p)**     | Insert if `allPrimesSoFar(list.insert(p))` | Returns new AllPrimesSoFarList |
| **tail**          | `AllPrimesSoFarList(list.tail)`       | Requires non-empty        |
| **nextPrime**     | Bounded linear search for next prime  | Requires non-empty        |
| **next**          | Returns new `AllPrimesSoFarList` with next prime prepended | Requires non-empty |

### Companion Object API

| Function                                | Statement                                   | Preconditions |
|-----------------------------------------|---------------------------------------------|---------------|
| **allPrimesSoFar(list)**                | Complete-prefix invariant check             | —             |
| **noPrimesBetween(from, to)**           | `∀ n ∈ [from, to): ¬isPrime(n)`             | `from >= 0`, `to >= from` |
| **noPrimesBetweenExcludesValue**        | `noPrimesBetween(from, to) ∧ value ∈ [from, to)` ⇒ `¬isPrime(value)` | Same + `value >= from`, `value < to` |
| **primeAtOrBelowHeadIsContained**       | `allPrimesSoFar(list) ∧ isPrime(v) ∧ v ≤ head.value` ⇒ `contains(v, list)` | `nonEmpty`, `v >= 0` |
| **searchNextPrimeUpTo(current, upper)** | First prime in `[current, upper.value]`, carries `noPrimesBetween(current, result.value)` | `current >= 0`, `current ≤ upper.value` |

**Invariant**: `AllPrimesSoFarList.allPrimesSoFar(list)` holds at construction.

**Source**: `src/main/scala/v1/chapter5/prime/AllPrimesSoFarList.scala`

---

# Domain 7: CycleIntegralOnes

## 7.1 CycleIntegralOnesProperties (`v1.cycle.integral.recursive.properties.CycleIntegralOnesProperties`)

Proves that a CycleIntegral with a constant cycle of [1] produces natural numbers.
This is the base case of the sieve's correctness proof.

### Public API

| Lemma                                      | Statement                                          | Preconditions |
|--------------------------------------------|----------------------------------------------------|---------------|
| **assertCycleIntegralOfOnes**              | `CI(init, [1]).apply(n) == init + n + 1`           | `pos >= 0`, `init >= 0` |
| **assertCycleIntegralOfOnesStrictlyIncreasing** | `b > a ⟹ CI(init, [1]).apply(b) > CI(init, [1]).apply(a)` | `a >= 0`, `b > a`, `init >= 0` |

### Key Insight

A constant cycle of 1s produces an arithmetic progression with step 1.
For S_0: `init = 2`, so `S_0(n) = n + 2`, giving us 2, 3, 4, 5, ...

**Source**: `src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralOnesProperties.scala`

---

# Domain 8: Additional Utilities

## 7.1 ConsecutiveIntegers (`v1.div.properties.ConsecutiveIntegers`)

Properties about consecutive integer sequences.

**Source**: `src/main/scala/v1/chapter2/div/properties/ConsecutiveIntegers.scala`

---

## 7.2 Summary (`v1.div.properties.Summary`)

Aggregated properties for easy verification.

**Source**: `src/main/scala/v1/chapter2/div/properties/Summary.scala`

---

# Article References

Each article in the `articles/` directory formalizes and proves properties of the objects above.

| Article                                           | Topic                        | File                     |
|---------------------------------------------------|------------------------------|--------------------------|
| [modulo.md](./articles/modulo.md)                 | Division & Modulo Properties | Division, Mod, DivMod    |
| [list.md](./articles/list.md)                     | Lists from First Principles  | ListUtils, Integral      |
| [integral.md](./articles/integral.md)             | Discrete Integration         | Integral (bounded)       |
| [cycle.md](./articles/cycle.md)                   | Unbounded Lists (Cycles)     | ModCycle, RecursiveCycle |
| [integral-cycle.md](./articles/integral-cycle.md) | Cycle Integral Properties    | CycleIntegral            |
| [sieve-sequence.md](./articles/draft-sieve-sequence) | Sieve Sequence Properties    | CycleSieveSequence       |
| [euclid-theorem.md](articles/draft/draft-euclid-theorem.md) | Euclid's Theorem             | PrimeProperties           |

---

*End of OBJECTS.md*
