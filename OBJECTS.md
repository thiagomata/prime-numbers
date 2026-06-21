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

**Source**: `src/main/scala/v1/div/properties/ModSmallDividend.scala:11`

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

**Source**: `src/main/scala/v1/div/properties/ModIdentity.scala:9`

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

**Source**: `src/main/scala/v1/div/properties/ModIdempotence.scala`

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

**Source**: `src/main/scala/v1/div/properties/AdditionAndMultiplication.scala`

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

**Source**: `src/main/scala/v1/div/properties/ModOperations.scala`

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

**Source**: `src/main/scala/v1/div/properties/ModSum.scala`

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

**Source**: `src/main/scala/v1/list/ListUtils.scala`

---

## 2.2 ListBoundUtils (`v1.list.ListBoundUtils`)

Bounds checking for lists.

| Function                                   | Statement                   | Notes                            |
|--------------------------------------------|-----------------------------|----------------------------------|
| **allGreaterThan(list, v)**                | All elements > v
| **allPositive(list)**                      | All elements > 0            | Alias for `allGreaterThan(_, 0)` |
| **assertGreaterThanAtIndex(list, v, pos)** | `list(pos) > v`             | Requires allGreaterThan          |
| **assertAppendGreaterThan(a, b, v)**       | `allGreaterThan(a ++ b, v)` | If both > v                      |

**Source**: `src/main/scala/v1/list/ListBoundUtils.scala`

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

**Source**: `src/main/scala/v1/list/integral/Integral.scala`

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

**Source**: `src/main/scala/v1/list/integral/properties/IntegralProperties.scala`

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

**Source**: `src/main/scala/v1/list/properties/SliceEquivalenceLemmas.scala`

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

**Source**: `src/main/scala/v1/list/properties/ListUtilsProperties.scala`

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

**Source**: `src/main/scala/v1/list/properties/ListProduct.scala`

---

## 2.8 ListProductDiv (`v1.list.properties.ListProductDiv`)

Divisibility lemmas: every element of a list divides the product of the list.

| Lemma                              | Statement                                                       | Preconditions |
|------------------------------------|-----------------------------------------------------------------|---------------|
| **ListProductDiv**                 | `mod(product(elements), elements.head) == 0`                    | `elements.nonEmpty`, `allGreaterThan(elements, 0)` |
| **allElementsDivideProduct**       | `mod(product(elements), x) == 0` for every `x in elements`      | `allGreaterThan(elements, 0)` |
| **insertedElementDividesProduct**  | `mod(product(prefix ++ List(e) ++ suffix), e) == 0`             | `e > 0`, `allGreaterThan(prefix ++ suffix, 0)` |

**Source**: `src/main/scala/v1/list/properties/ListProductDiv.scala`

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

**Source**: `src/main/scala/v1/cycle/mod/ModCycle.scala`

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

**Source**: `src/main/scala/v1/cycle/memory/MemCycle.scala`

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

**Source**: `src/main/scala/v1/cycle/recursive/RecursiveCycle.scala`

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

**Source**: `src/main/scala/v1/cycle/properties/CycleProperties.scala`

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

**Source**: `src/main/scala/v1/cycle/memory/properties/MemCycleProperties.scala`

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

**Source**: `src/main/scala/v1/cycle/integral/recursive/CycleIntegral.scala`

---

## 4.2 ClassicCycleIntegral (`v1.cycle.integral.classic.ClassicCycleIntegral`)

Classic recursive definition of cycle integral.

**Source**: `src/main/scala/v1/cycle/integral/classic/ClassicCycleIntegral.scala`

---

## 4.3 ModCycleIntegral (`v1.cycle.integral.mod.ModCycleIntegral`)

Modulo-based cycle integral formula.

```
apply(k) = (k div size) * sum + integralValues(k mod size) + initialValue
```

**Source**: `src/main/scala/v1/cycle/integral/mod/ModCycleIntegral.scala`

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

**Source**: `src/main/scala/v1/cycle/integral/recursive/properties/CycleIntegralProperties.scala`

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

**Source**: `src/main/scala/v1/cycle/integral/classic/properties/ClassicCycleIntegralProperties.scala`

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

**Source**: `src/main/scala/v1/cycle/integral/mod/ModCycleIntegralProperties.scala`

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

**Source**: `src/main/scala/v1/seq/sieve/SieveUtils.scala`

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

**Source**: `src/main/scala/v1/cycle/gap/GapCycle.scala`

---

## 5.3 SieveSequenceV2 (`v1.seq.sieve.SieveSequenceV2`)

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
| **next**     | Builds next V0 stage with `primes.next`         | Returns SieveSequenceV0     |

**Critical Chain**:

- `seq.integral.initialValue = seq.head > 0` ✓
- `seq.integral.cycle.values = seq.gapCycle.memCycle.values`
- `seq.gapCycle` requires `allGreaterThan(values.list, 0)` ✓
- So `assertCycleIntegralPositive(seq.integral, pos)` is **provable**!

**Source**: `src/main/scala/v1/seq/sieve/SieveSequenceV2.scala`

---

## 5.4 SieveSequenceV0 (`v1.seq.sieve.SieveSequenceV0`)

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
| **next** | Builds next stage with `primes.next` | Returns SieveSequenceV0 |

### Gap Lemmas (proved)

| Lemma | Statement | Notes |
|---|---|---|
| **assertGapPositive(k)** | `apply(k+1) - apply(k) > 0` | Uses `applyStrictlyIncreases(k)`. Public `.holds`. |
| **assertGapPeriodic(k, p)** | `apply(k+1+p) - apply(k+p) == apply(k+1) - apply(k)` where `p = indexOfAccepted(head+M)` | Uses `assertBlockShift` at `k` and `k+1`. Public `.ensuring`. |
| **assertGapSum(p)** | `sum_{i=0}^{p-1} (apply(i+1)-apply(i)) == M` | Via `sumGap` (private) + `assertSumGapTelescopes` (private). Public `.holds`. |
| **assertFilterPreservesNextPosition(nextSeq, k)** | `nextSeq.filterValues.tail == filterValues` ∧ `nextSeq.accepts(apply(k))` ∧ `Calc.mod(apply(k+1), p) ≠ 0` ⇒ `nextSeq(indexOfAccepted(V)+1) == apply(k+1)` | Proves that adding a filter prime preserves the next-position relationship between two V0 sequences. Uses `nextDoesNotPassAcceptedValue` bidirectionally. 6379 valid. |

### Filter Bridge Lemmas

Bridges between old-filter acceptance and next-filter acceptance for `SieveSequenceV0.next()`.

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
| **assertApplyMonotonic(from, until)** | `from ≤ until ⇒ apply(from) ≤ apply(until)` | Public wrapper for `applyIndexOrderPreservesValues`. Public `.holds`. |

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
| **assertSkipUntilNonMultiple(nextSeq, k, period)** | `nextSeq(vIdx+1) == apply(m)` where `m = findFirstNonMultipleAfter(k, p, bound)` and `bound = k + p*period` | Period-based public gap-merge wrapper. Uses block shifting to build a finite non-multiple endpoint, then delegates to the bounded skip-to-first-survivor equality. Public `.holds`. |

### Filter Membership Lemmas

Proving that a prime divisor below `head` appears in `filterValues`, using parallel scans of the sorted prime list and its value list.

| Lemma | Statement | Notes |
|---|---|---|
| **assertFilterValuesContainsInTail(d, tail, tailFilterValues, n)** | `contains(d, tail)` ∧ `tailFilterValues == primeValues(tail.list)` ∧ `mod(n, d) == 0` ⇒ `tailFilterValues.head == d` when found | Scans a prime tail and its value list in parallel, proving matching element positions. Private `.holds`. |
| **assertFilterValuesContains(d)** | `contains(d, primes.list.tail)` ∧ `mod(apply(1), d) == 0` ⇒ d is in `filterValues` | Uses `assertFilterValuesContainsInTail` for the recursive step. Proves d's value appears in the filter list by scanning the tail primes. Private `.holds`. |

### Prime Bridge Lemmas

Cross-object lemmas bridging `AllPrimesSoFarList` prime search with `SieveSequenceV0` generation.

| Lemma | Statement | Notes |
|---|---|---|
| **assertApplyOneAtOrBeforeAccepted(value)** | `accepts(value)` ∧ `value > head.value` ⇒ `apply(1) ≤ value` | First-step completeness: the first generated value cannot jump past any accepted value beyond the head. Public `.holds`. |
| **assertNextPrimePassesV0Filter(primes)** | `AllPrimesSoFarList.nextPrime(primes.list).value` is coprime to `PrimeUtils.primeValues(primes.list.tail.list)` | The next prime after the list head passes the V0 tail filter. Uses `PrimeUtils.primeIsCoprimeWithSmallerList`. Public `.holds`. |

### P4 (Period equals residue count) — SKIPPED

The property `indexOfAccepted(head+M) == residues(M, filterValues).size` is mathematically true (by interval periodicity) but the Stainless proof requires a counting lemma that timed out. Left as open problem.

### Source

`src/main/scala/v1/seq/sieve/SieveSequenceV0.scala`

---

## 5.5 SieveSequenceProperties (`v1.seq.sieve.properties.SieveSequenceProperties`)

> **NOTE**: This file does not yet exist. Properties listed below are aspirational.

| Property                 | Statement              | Notes |
|--------------------------|------------------------|-------|
| **assertS1HeadIsThree**  | S_1().head == 3
| **assertS1PrimesLength** | S_1().primes.size == 2

**Source**: `src/main/scala/v1/seq/sieve/properties/SieveSequenceProperties.scala` (not yet implemented)

---

## How SieveSequenceV2 Chains Together

```
SieveSequenceV2
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

**Source**: `src/main/scala/v1/prime/Prime.scala`

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

**Source**: `src/main/scala/v1/prime/PrimeUtils.scala`

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

**Source**: `src/main/scala/v1/prime/properties/PrimeProperties.scala`

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

**Source**: `src/main/scala/v1/prime/properties/FilterPreservesPrimesProperties.scala`

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

**Source**: `src/main/scala/v1/prime/SortedPrimeList.scala`

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

**Source**: `src/main/scala/v1/prime/AllPrimesSoFarList.scala`

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

**Source**: `src/main/scala/v1/cycle/integral/recursive/properties/CycleIntegralOnesProperties.scala`

---

# Domain 8: Additional Utilities

## 7.1 ConsecutiveIntegers (`v1.div.properties.ConsecutiveIntegers`)

Properties about consecutive integer sequences.

**Source**: `src/main/scala/v1/div/properties/ConsecutiveIntegers.scala`

---

## 7.2 Summary (`v1.div.properties.Summary`)

Aggregated properties for easy verification.

**Source**: `src/main/scala/v1/div/properties/Summary.scala`

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
| [sieve-sequence.md](./articles/draft-sieve-sequence) | Sieve Sequence Properties    | SieveSequenceV2          |
| [euclid-theorem.md](articles/draft/draft-euclid-theorem.md) | Euclid's Theorem             | PrimeProperties           |

---

*End of OBJECTS.md*
