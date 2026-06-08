# Key Objects & Proved Properties

## Quick Reference Table

| Property                                         | File                                 | Domain     | Line      |
|--------------------------------------------------|--------------------------------------|------------|-----------|
| **Division & Modulo**                            |                                      |            |           |
| `modSmallDividend`                               | ModSmallDividend.scala               | Div/Mod    | #11       |
| `modIdentity`                                    | ModIdentity.scala                    | Div/Mod    | #9        |
| `longProof`                                      | ModIdentity.scala                    | Div/Mod    | #14       |
| `modIdempotence`                                 | ModIdempotence.scala                 | Div/Mod    | #9        |
| `modIdempotencePositiveA`                        | ModIdempotence.scala                 | Div/Mod    | #27       |
| `modUniqueDiv`                                   | ModIdempotence.scala                 | Div/Mod    | #51       |
| `modUnique`                                      | ModIdempotence.scala                 | Div/Mod    | #61       |
| `modModPlus`                                     | ModIdempotence.scala                 | Div/Mod    | #95       |
| `modModMinus`                                    | ModIdempotence.scala                 | Div/Mod    | #168      |
| `APlusBSameModPlusDiv`                           | AdditionAndMultiplication.scala      | Div/Mod    | #25       |
| `ALessBSameModDecreaseDiv`                       | AdditionAndMultiplication.scala      | Div/Mod    | #102      |
| `ATimesBSameMod`                                 | AdditionAndMultiplication.scala      | Div/Mod    | #174      |
| `APlusMultipleTimesBSameMod`                     | AdditionAndMultiplication.scala      | Div/Mod    | #203      |
| `ALessMultipleTimesBSameMod`                     | AdditionAndMultiplication.scala      | Div/Mod    | #235      |
| `assertDivModWithMoreDivAndLessModSameSolution`  | AdditionAndMultiplication.scala      | Div/Mod    | #268      |
| `assertDivModWithLessDivAndMoreModSameSolution`  | AdditionAndMultiplication.scala      | Div/Mod    | #333      |
| `MoreDivLessModManyTimes`                        | AdditionAndMultiplication.scala      | Div/Mod    | #361      |
| `LessDivMoreModManyTimes`                        | AdditionAndMultiplication.scala      | Div/Mod    | #402      |
| `modAdd`                                         | ModOperations.scala                  | Div/Mod    | #22       |
| `modZeroPlusC`                                   | ModOperations.scala                  | Div/Mod    | #115      |
| `modLess`                                        | ModOperations.scala                  | Div/Mod    | #142      |
| `addOne`                                         | ModOperations.scala                  | Div/Mod    | #226      |
| `sumSymmetricalMods`                             | ModSum.scala                         | Div/Mod    | #9        |
| `checkAllPreviousValues`                         | ModSum.scala                         | Div/Mod    | #19       |
| `sumAllValues`                                   | ModSum.scala                         | Div/Mod    | #33       |
| `sumAllMods`                                     | ModSum.scala                         | Div/Mod    | #45       |
| `sumAllModsEqualSumOfAllSmallValues`             | ModSum.scala                         | Div/Mod    | #58       |
| `checkValueShift`                                | ModSum.scala                         | Div/Mod    | #64       |
| **Lists**                                        |                                      |            |           |
| `listSumAddValue`                                | ListUtilsProperties.scala            | Lists      | #22       |
| `listCombine`                                    | ListUtilsProperties.scala            | Lists      | #37       |
| `listSwap`                                       | ListUtilsProperties.scala            | Lists      | #65       |
| `listAddValueTail`                               | ListUtilsProperties.scala            | Lists      | #84       |
| `assertAppendToSlice`                            | ListUtilsProperties.scala            | Lists      | #105      |
| `assertTailShiftLeft`                            | ListUtilsProperties.scala            | Lists      | #127      |
| `accessTailShiftRight`                           | ListUtilsProperties.scala            | Lists      | #154      |
| `assertLastEqualsLastPosition`                   | ListUtilsProperties.scala            | Lists      | #168      |
| `checkAllBiggerThanValueAtIndex`                 | ListUtilsProperties.scala            | Lists      | #193      |
| `checkAllBiggerThanValueHeadTail`                | ListUtilsProperties.scala            | Lists      | #209      |
| `headRecursiveSlice`                             | SliceEquivalenceLemmas.scala         | Lists      | #26       |
| `indexRangeValues`                               | SliceEquivalenceLemmas.scala         | Lists      | #49       |
| `sliceEqualsSpec`                                | SliceEquivalenceLemmas.scala         | Lists      | #78       |
| `appendOne`                                      | SliceEquivalenceLemmas.scala         | Lists      | #103      |
| `appendCons`                                     | SliceEquivalenceLemmas.scala         | Lists      | #118      |
| `tailHeadAndIndexRangeSlicesAreEqual`            | SliceEquivalenceLemmas.scala         | Lists      | #142      |
| `assertHeadValueMatchDefinition`                 | IntegralProperties.scala             | Lists      | #22       |
| `assertAccDifferenceEqualsTailHead`              | IntegralProperties.scala             | Lists      | #42       |
| `assertAccDiffMatchesList`                       | IntegralProperties.scala             | Lists      | #76       |
| `assertAccMatchesApply`                          | IntegralProperties.scala             | Lists      | #125      |
| `assertSizeAccEqualsSizeList`                    | IntegralProperties.scala             | Lists      | #181      |
| `assertLastEqualsSum`                            | IntegralProperties.scala             | Lists      | #219      |
| `assertIntegralEqualsSum`                        | IntegralProperties.scala             | Lists      | #257      |
| `assertLast`                                     | IntegralProperties.scala             | Lists      | #303      |
| **Cycles**                                       |                                      |            |           |
| `findValueInCycle`                               | CycleProperties.scala                | Cycles     | #22       |
| `smallValueInCycle`                              | CycleProperties.scala                | Cycles     | #38       |
| `valueMatchAfterManyLoops`                       | CycleProperties.scala                | Cycles     | #55       |
| `valueMatchAfterManyLoopsInBoth`                 | CycleProperties.scala                | Cycles     | #75       |
| `propagateModFromValueToCycle`                   | CycleProperties.scala                | Cycles     | #103      |
| `assertCycleOfPosEqualsCycleOfModPos`            | CycleProperties.scala                | Cycles     | #111      |
| `cycleValuePositiveOrZero`                       | CycleProperties.scala                | Cycles     | #125      |
| `rotateAtValue`                                  | CycleProperties.scala                | Cycles     | #136      |
| `findValueInCycle`                               | MemCycleProperties.scala             | Cycles     | #23       |
| `smallValueInCycle`                              | MemCycleProperties.scala             | Cycles     | #39       |
| `valueMatchAfterManyLoops`                       | MemCycleProperties.scala             | Cycles     | #56       |
| `valueMatchAfterManyLoopsInBoth`                 | MemCycleProperties.scala             | Cycles     | #76       |
| `propagateModFromValueToCycle`                   | MemCycleProperties.scala             | Cycles     | #104      |
| `assertCycleOfPosEqualsCycleOfModPos`            | MemCycleProperties.scala             | Cycles     | #112      |
| **Cycle Integrals**                              |                                      |            |           |
| `assertCycleIntegralEqualsSumFirstPosition`      | CycleIntegralProperties.scala        | CycleInteg | #26       |
| `assertCycleIntegralEqualsSumSmallPositions`     | CycleIntegralProperties.scala        | CycleInteg | #47       |
| `assertCycleIntegralEqualsSliceSum`              | CycleIntegralProperties.scala        | CycleInteg | #92       |
| `assertNextPosition`                             | CycleIntegralProperties.scala        | CycleInteg | #107      |
| `assertDiffEqualsCycleValue`                     | CycleIntegralProperties.scala        | CycleInteg | #123      |
| `assertSameDiffAfterCycle`                       | CycleIntegralProperties.scala        | CycleInteg | #142      |
| `assertLastElementBeforeLoop`                    | CycleIntegralProperties.scala        | CycleInteg | #165      |
| `assertSumModValueAsListEqualsCycleIntegralLoop` | CycleIntegralProperties.scala        | CycleInteg | #186      |
| `assertCycleIntegralEqualsSumOfModValuesAsList`  | CycleIntegralProperties.scala        | CycleInteg | #224      |
| `getFirstValuesAsSlice`                          | CycleIntegralProperties.scala        | CycleInteg | #231      |
| `getModValuesAsList`                             | CycleIntegralProperties.scala        | CycleInteg | #269      |
| `assertFirstValuesAsSliceEqualsModValuesAsList`  | CycleIntegralProperties.scala        | CycleInteg | #295      |
| `assertCycleValuePositive`                       | CycleIntegralProperties.scala        | CycleInteg | #327      |
| `assertCycleIntegralPositive`                    | CycleIntegralProperties.scala        | CycleInteg | #341      |
| `assertCycleIntegralEqualsSumFirstPosition`      | ClassicCycleIntegralProperties.scala | CycleInteg | #23       |
| `assertCycleIntegralEqualsSumSmallPositions`     | ClassicCycleIntegralProperties.scala | CycleInteg | #44       |
| `assertCycleIntegralEqualsSliceSum`              | ClassicCycleIntegralProperties.scala | CycleInteg | #89       |
| `assertNextPosition`                             | ClassicCycleIntegralProperties.scala | CycleInteg | #104      |
| `assertDiffEqualsCycleValue`                     | ClassicCycleIntegralProperties.scala | CycleInteg | #120      |
| `assertSameDiffAfterCycle`                       | ClassicCycleIntegralProperties.scala | CycleInteg | #139      |
| `assertLastElementBeforeLoop`                    | ClassicCycleIntegralProperties.scala | CycleInteg | #162      |
| `assertSumModValueAsListEqualsCycleIntegralLoop` | ClassicCycleIntegralProperties.scala | CycleInteg | #183      |
| `assertCycleIntegralEqualsSumOfModlValuesAsList` | ClassicCycleIntegralProperties.scala | CycleInteg | #221      |
| `getFirstValuesAsSlice`                          | ClassicCycleIntegralProperties.scala | CycleInteg | #228      |
| `getModValuesAsList`                             | ClassicCycleIntegralProperties.scala | CycleInteg | #266      |
| `assertFirstValuesAsSliceEqualsModValuesAsList`  | ClassicCycleIntegralProperties.scala | CycleInteg | #292      |
| `assertFirstValuesMatchIntegral`                 | ModCycleIntegralProperties.scala     | CycleInteg | #22       |
| `assertSimplifiedDiffValuesMatchCycle`           | ModCycleIntegralProperties.scala     | CycleInteg | #46       |
| `assertModCycleEqualsCycleIntegral`              | ModCycleIntegralProperties.scala     | CycleInteg | #260      |
| `assertCycleIntegralMatchModCycleDef`            | ModCycleIntegralProperties.scala     | CycleInteg | #346      |
| **Sieve**                                        |                                      |            |           |
| `product`                                        | SieveUtils.scala                     | Sieve      | (utility) |
| `isCoprime`                                      | SieveUtils.scala                     | Sieve      | (utility) |
| `residues`                                       | SieveUtils.scala                     | Sieve      | (utility) |
| `filterList`                                     | SieveUtils.scala                     | Sieve      | (utility) |
| `calculateGaps`                                  | SieveUtils.scala                     | Sieve      | (utility) |
| `rotateAt`                                       | SieveUtils.scala                     | Sieve      | (utility) |
| `assertRotateAtPreservesNonEmpty`                | SieveUtils.scala                     | Sieve      | (utility) |
| `allGreaterThan`                                 | ListBoundUtils.scala                 | Sieve      | (utility) |
| `allPositive`                                    | ListBoundUtils.scala                 | Sieve      | (utility) |
| `assertGreaterThanAtIndex`                       | ListBoundUtils.scala                 | Sieve      | (utility) |
| `assertAppendGreaterThan`                        | ListBoundUtils.scala                 | Sieve      | (utility) |

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
| **allGreaterThan(list, v)**                | All elements > v            |                                  |
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
| **apply(k)** | Cumulative sum up to k |                         |
| **last**     | `init + sum(list)`     | Final accumulated value |
| **size**     | `list.size`            |                         |

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

# Domain 3: Cycles

## 3.1 ModCycle (`v1.cycle.mod.ModCycle`)

Lowest-level cycle using modulo indexing.

```
apply(k) = values(k % size)
```

| Field/Method | Definition         | Notes                 |
|--------------|--------------------|-----------------------|
| **values**   | `List[BigInt]`     | Non-empty, stored raw |
| **size**     | `values.size`      |                       |
| **apply(k)** | `values(k % size)` | Unbounded access      |
| **sum**      | Sum of all values  |                       |

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
| **size**     | `cycle.size`   |               |
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
| **size**         | `cycle.size`   |                |
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
| **assertCycleIntegralEqualsSumFirstPosition**      |                                        |               |
| **assertCycleIntegralEqualsSumSmallPositions**     |                                        |               |
| **assertCycleIntegralEqualsSliceSum**              |                                        |               |
| **assertNextPosition**                             | `ci(pos) == ci(pos-1) + ci.cycle(pos)` | `pos > 0`     |
| **assertDiffEqualsCycleValue**                     |                                        |               |
| **assertSameDiffAfterCycle**                       |                                        |               |
| **assertLastElementBeforeLoop**                    |                                        |               |
| **assertSumModValueAsListEqualsCycleIntegralLoop** |                                        |               |
| **assertCycleIntegralEqualsSumOfModlValuesAsList** |                                        |               |
| **getFirstValuesAsSlice**                          | Helper function                        |               |
| **getModValuesAsList**                             | Helper function                        |               |
| **assertFirstValuesAsSliceEqualsModValuesAsList**  |                                        |               |

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

| Function                            | Purpose                          | Notes          |
|-------------------------------------|----------------------------------|----------------|
| **product(list)**                   | Multiply all elements            |                |
| **isCoprime(value, primes)**        | Check not divisible by any prime |                |
| **residues(modulus, primes)**       | Generate coprime residues        |                |
| **filterList(list, divisor)**       | Remove multiples of divisor      |                |
| **calculateGaps(sorted, modulus)**  | Compute gaps + wrap gap          |                |
| **rotateAt(list, index)**           | Rotate list at index             |                |
| **assertRotateAtPreservesNonEmpty** | rotateAt preserves non-emptiness | `.holds` lemma |

**Source**: `src/main/scala/v1/seq/sieve/SieveUtils.scala`

---

## 5.2 GapCycle (`v1.cycle.gap.GapCycle`)

Wrapper around MinBoundList with **strict positivity** invariant.

| Field/Method                           | Definition                   | Notes             |
|----------------------------------------|------------------------------|-------------------|
| **values**                             | `MinBoundList`               | `lowerBound == 0` |
| **memCycle**                           | `MemCycle(values.list)`      | All gaps > 0      |
| **integral**                           | `CycleIntegral(0, memCycle)` |                   |
| **gap(index)**                         | `memCycle(index)`            |                   |
| **cumulativeSum(index)**               | `integral(index)`            |                   |
| **size**                               | `values.size`                |                   |
| **sum**                                | `memCycle.sum()`             |                   |
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
| **apply(k)** | `head` if k=0, else `integral(k-1)`             |                             |
| **head**     | `primes.head`                                   | Prime > 0                   |
| **modulus**  | `product(primes.tail)`                          |                             |
| **next**     | `@extern`                                       | Computes next sequence      |

**Critical Chain**:

- `seq.integral.initialValue = seq.head > 0` ✓
- `seq.integral.cycle.values = seq.gapCycle.memCycle.values`
- `seq.gapCycle` requires `allGreaterThan(values.list, 0)` ✓
- So `assertCycleIntegralPositive(seq.integral, pos)` is **provable**!

**Source**: `src/main/scala/v1/seq/sieve/SieveSequenceV2.scala`

---

## 5.4 SieveSequenceProperties (`v1.seq.sieve.properties.SieveSequenceProperties`)

| Property                 | Statement              | Notes |
|--------------------------|------------------------|-------|
| **assertS1HeadIsThree**  | S_1().head == 3        |       |
| **assertS1PrimesLength** | S_1().primes.size == 2 |       |

**Source**: `src/main/scala/v1/seq/sieve/properties/SieveSequenceProperties.scala`

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

# Domain 6: Additional Utilities

## ConsecutiveIntegers (`v1.div.properties.ConsecutiveIntegers`)

Properties about consecutive integer sequences.

**Source**: `src/main/scala/v1/div/properties/ConsecutiveIntegers.scala`

---

## Summary (`v1.div.properties.Summary`)

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
| [sieve-sequence.md](./articles/sieve-sequence.md) | Sieve Sequence Properties    | SieveSequenceV2          |

---

*End of OBJECTS.md*