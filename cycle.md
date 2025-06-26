# Using Formal Verification to Prove Properties of Unbound Lists and Integrals

**Author:** Mata, T. H.
Independent Researcher  
**Email:** [thiago.henrique.mata@email.com](mailto:thiago.mata@email.com)  
**GitHub:** [@thiagomata](https://github.com/thiagomata)

## Abstract

<div align="justify">
<p style="text-align: justify">
In previous articles, we defined bounded Lists and Integrals of <code>BigInt</code>
from scratch, relying only on core type constructs and recursion, 
with no prior knowledge of Scala's collections required.
From that, we proved and formally verify some properties related to them as size, append, concat,
slice and sum.
This article use that as foundation to define Cycles - unbounded List of Integers
created from a bounded List, where the values of the Cycle are the values of the
List in repetition using recursion - and Cycle Integral that is the discrete integral of the Cycles.
Then, we formally defined and verify key properties such as ... using the Stainless verification system. 
All properties are expressed and proved within a minimal framework using only elementary arithmetic,
 recursion, and pure Scala code.
This work bridges mathematical foundations and executable verification, offering a self-contained, verifiable
 treatment of modular arithmetic.
 </p>
</div>

# Introduction

Unbounded lists in cycles, are a fundamental concept in computer science and mathematics, often used to model
repetitive structures or processes. They can be thought of as infinite lists that repeat a finite sequence of elements.

```math
L = [x_0, x_1, x_2, \ldots, x_{n-1}]  \mid x_n \in 𝕊, L \in 𝕃\\
\text{Cycle}(L) = [x_0, x_1, x_2, \ldots, x_{n-1}, x_0, x_1, \ldots] \\
```
In this article, we present a discrete definition of Cycle and Cycle Integral 
operations over finite integer lists, defined recursively and verified some of 
its properties using the Stainless system.
Our approach follows a zero-prior-knowledge philosophy, building on a previously 
verified foundation for recursive list and integral structures and summation.
The result is a verified, from-scratch implementation of cycle and cycle integral 
suitable as a foundation for higher-level numeric reasoning over unbounded lists.

## 2. Preliminaries

We reuse several basic list and integral operations and their verified properties from the companion articles [Using Formal Verification to Prove Properties of Lists Recursively Defined](
https://github.com/thiagomata/prime-numbers/blob/master/list.md
) [[1]](#ref1) and [Formal Verification of Discrete Integration Properties from First Principles](integral.md) [[2]](#ef2).

These articles also defined and verified their properties using the same zero-prior-knowledge methodology,
and are treated here as foundational primitives.


### List Definitions and Properties

For any list $L$ of numeric values $x_i \in 𝕊$ where $𝕊$ is a set of all numeric values,
$𝕃$ is the the set of all lists, 
and $n$ is the size of the list, we define:

```math
\begin{aligned}
L_{e} & \in 𝕃 \\
L_{e} & = [] \\
\end{aligned}
```

```math
\begin{aligned}
&\text{ head } &\in 𝕊 \\
&\text{ tail } &\in 𝕃 \\
&L_{node}(\text{head}, \text{tail}) \in 𝕃_{node} \\
\end{aligned}
```
```math
\begin{aligned}
&𝕃 &= \{ L_e \}  \cup \{ L_{node}(\text{head}, \text{tail}) &\mid \text{head} \in 𝕊,\ \text{tail} \in 𝕃 \} \\
\end{aligned}
```

```math
\begin{aligned}
L = [x_0, x_1, \dots, x_{n-1}] \in 𝕊^n \\
\end{aligned}
```

```math
\begin{aligned}
& &\text{size}(L) &:= \begin{cases}
0 & \text{ if } L = L_{e} \\\
1 + \text{size}(tail(L)) & \text{otherwise} \\
\end{cases} \\
& &sum(L) &:= \begin{cases}
0 & \text{if } L = L_e \\
head(L) + sum(tail(L)) & \text{otherwise} \\
\end{cases} \\
|L| > 0 &\implies &\text{last}(L) &:= \begin{cases}
\text{head}(L) & \text{if } |L| = 1 \\
\text{last}(\text{tail}(L)) & \text{otherwise} \\
\end{cases} \\
|L| > 0 &\implies &\text{slice}(L, f, t) &:=  \begin{cases} \\
[ L_j ] & \text{if } f = t \\
\text{slice}(L, f, t - 1) ⧺ [ L_t ] & \text{if } f < t \\
\end{cases}
\forall \ f, t \in ℕ \text{ where } 0 \leq f \leq t \\
& &A ⧺ B &:= \begin{cases}
B & \text{if } A = L_e \\
L_{node}(head(A), tail(A) ⧺ B) & \text{otherwise} \\
\end{cases}
\forall \ L, A, B \in  𝕃 \\
\end{aligned}
```

From these definitions, the authors [[1]](#ref1) mathematically proves and formally verifies the following properties of lists:

```math
\begin{aligned}
&\forall\, L, A, B \in  𝕃,\quad &\forall\, v \in 𝕊,\quad &\forall\, i, f, t \in ℕ \\
\end{aligned}
```
```math
\begin{aligned}
f > t, \quad 0 \leq i < |L|\\
\\
\end{aligned}
```
```math
\begin{aligned}
&|L| &> 0 &\implies \text{tail}(L) &= &L[x_1, x_2, \dots, x_{n-1}] \quad &\text{[Tail Identity]} \\
&|L| &> 0 &\implies L_{0} &= &\text{ }\text{head}(L) \quad &\text{[Head Identity]} \\
&|L| &> 0 &\implies L_{|L|-1} &= &\text{ }\text{last}(L) \quad &\text{[Last Element Identity]} \\
&|L| - 1 &> i > 0 &\implies L_i &= &\text{ }\text{tail}(L)_{i-1} \quad &\text{[Access Tail Shift Left]} \\
&|L| - 2 &> i > 1 \text{ } &\implies \text{tail}(L)_i &= &L_{i+1} \quad &\text{[Access Tail Shift Right]} \\
\end{aligned}
```
```math
\begin{aligned}
&|L| &= &\text{size}(L)                        \quad &\text{[Size Identity]} \\
&\sum L &= &\text{sum}(L)                      \quad &\text{[Sum matches Summation]} \\
&\sum ([v] ⧺ L) &= &v + \sum L                 \quad &\text{[Left Append Preserves Sum]} \\
&\sum (A ⧺ B) &= &\sum A + \sum B              \quad &\text{[Sum over Concatenation]} \\
&\sum (A ⧺ B) &= &\sum (B ⧺ A)                 \quad &\text{[Commutativity of Sum over Concatenation]} \\
&L[f \dots t] &= &L[f \dots {(t - 1)}] ⧺ [L_t] \quad &\text{[Slice Append Consistency]} \\
\end{aligned}
```

### Integral Definition Properties

Similarly, the article [Formal Verification of Discrete Integration Properties from First Principles](./integral.md) [[1]](#ref1)
defines and construct bounded discrete integrals of <code>BigInt</code> values
from scratch, relying only on recursion and core type constructs. 

$$
\begin{aligned}
init &\in 𝕊 \\
I &= [v_0, v_1, \dots, v_{n-1}] = \text{Integral}(L, init) \\
n &= |L| \\
k &\in [0, n - 1]
\end{aligned}
$$

```math
\begin{aligned}
&I_k &:= &\begin{cases}
L_0 + init & \text{if } k = 0 \\
\text{Integral}(\text{tail}(L),\ \text{head}(L) + init)_{(k - 1)} & \text{if } k > 0 \\
\end{cases} \\
&acc &:= &\begin{cases}
L_e & \text{if } L = L_e \\
\text{acc}(\text{Integral}(\text{tail}(L),\ \text{head}(L) + init)) & \text{otherwise} \\
\end{cases} \\
\end{aligned}
```

From these definitions, the authors [[2]](#ref2) mathematically proves and formally verifies the following properties related to discrete integrals:

```math
\begin{aligned}
 I_0 &= x_0 + init & \text{[Head Value Matches Definition]} \\
 I_k &= init + \sum_{i=0}^k x_i & \text{[Integral Equals Sum Until Position]} \\
 I_{n-1} &= init + \sum_{i=0}^{n-1} x_i & \text{[Final Element Equals Full Sum]} \\
 I_{p+1} - I_p &= x_{p+1} & \text{[Incremental Change Matches List]} \\
 I_k &= acc_k & \text{[Element Consistency]} \\
  \text{last}(I) &= acc_{n-1} = I_{n-1} & \text{[Integral-Accumulation Last Agreement]} \\
 acc_{p+1} - acc_p &= x_{p+1} & \text{[Integral-Accumulation Delta Consistency]} \\
 |acc| &= |L| & \text{[Integral-Accumulation Size Agreement]} \\
\end{aligned}
```

## 3. Cycle Definition and Properties

Building on the definitions and properties of lists and integrals, we now define Cycles and Cycle Integrals.

### Cycle Definition

A Cycle is an unbounded list that repeats a finite sequence of elements from a bounded list.

In this study, we restrict our universe of values $𝕊$ to be the set of non-negative integers, i.e., $𝕊 = ℕ_0$.

### Recursive Cycle Definition

```math
\begin{aligned}
\forall \ L \in  𝕃, \quad \forall \ v &\in ℕ_0,\quad \forall \ i \in ℕ_0 \\
L &:= [v_0, v_1, \dots, v_{n-1}] \in ℕ_0^n \\
n &= |L| \\
\text{RecCycle}_i &= \begin{cases}
L_i & \text{if } i < n \\
\text{RecCycle}_{i - n} & \text{if } i \geq n \\
\end{cases} \ , |L| > 0 \\
\therefore \\
RecCycle &= [v_0, v_1, \dots, v_{n-1}, v_0, v_1, \dots] \\
\end{aligned}
```

Defined at [RecursiveCycle](
    ./src/main/scala/v1/cycle/recursive/RecursiveCycle.scala
) as follows:

<details>
<summary> Scala Doc </summary>

```scala
/**
 * RecursiveCycle is a recursive cycle of list values.
 *
 * @param values List A non-empty list of BigInt 
 *  non-negative values that form the cycle.
 */
```
</details>

```scala
case class RecursiveCycle(values: List[BigInt]) {
  require(values.nonEmpty)
  require(CycleUtils.checkPositiveOrZero(values))

  def size: BigInt = values.size
```

<details>
<summary> Scala Doc </summary>

```scala
  /**
    * Applies the recursive cycle to the given position
    *  by returning the value at the list position or
    *  calling the previous equivalent value from a 
    *  smaller position in the cycle.
    * 
    * In other words,
    * 
    * RecursiveCycle(position) = if position < RecursiveCycle.size 
    *   then RecursiveCycle.values(position) 
    *   else RecursiveCycle(position - values.size)
    *
    * @param position BigInt The non-negative position in the cycle.
    * @return BigInt The value at the given position in the cycle.
    */
  ````
  </details>

  ```scala
  def apply(position: BigInt): BigInt = {
    decreases(position)
    require(position >= 0)

    if (position < size) {
      values(position)
    } else {
      apply(position - values.size)
    }
  }
} 
```
### Modulo Cycle Definition

A Cycle can also be defined using modulo arithmetic, which is a common approach in computer science to handle cyclic structures.

```math
\begin{aligned}
\forall \ L \in  𝕃, \quad \forall \ v
&\in ℕ_0,\quad \forall \ i \in ℕ_0 \\
L &:= [v_0, v_1, \dots, v_{n-1}] \in ℕ_0^n \\
n &= |L| \\
\text{ModCycle}_i &= L[i \text{ mod } n] \ , |L| > 0 \\
\therefore \\
\text{ModCycle} &= [v_0, v_1, \dots, v_{n-1}, v_0, v_1, \dots] \\
\end{aligned}
```

Defined at [ModCycle](
    ./src/main/scala/v1/cycle/mod/ModCycle.scala
) as follows:

<details>
<summary> Scala Doc </summary>

```scala
/**
  * ModCycle represents a cycle of values that can be accessed using a modulo operation.
  *  This cycle is defined by a list of non-negative BigInt values.
  *
  * @param values A non-empty list of BigInt values that form the cycle.
  */
```
</details>

```scala
case class ModCycle(values: List[BigInt]) {
  require(CycleUtils.checkPositiveOrZero(values))
  require(values.nonEmpty)
```
<details>
<summary> Scala Doc </summary>

```scala
  /**
    * Applies the modulo operation to the given value and 
    * returns the corresponding value from the cycle.
    *
    * In other words,
    * ModCycle(position) = ModCycle.values[position % ModCycle.size]
    * 
    * @param position The BigInt value to be used for accessing the cycle.
    * @return The value from the cycle corresponding to the modulo of the input value.
    */
```
</details>

```scala
  def apply(position: BigInt): BigInt = {
    require(position >= 0)
    val index = Calc.mod(position, values.size)
    assert(index >= 0)
    assert(index < values.size)
    values(index)
  }

  def size: BigInt = values.size

  def sum(): BigInt = ListUtils.sum(values)
}
```

### Proving Cycle Equivalence

Let's prove that both definitions of Cycle are equivalent, i.e., they produce the same sequence of values.

```math
\begin{aligned}
\forall \ L \in  𝕃, \quad \forall \ v
&\in ℕ_0,\quad \forall \ i \in ℕ_0 \\
L &:= [v_0, v_1, \dots, v_{n-1}] \in ℕ_0^n \\
n &= |L| \\
\text{ModCycle}_i &= L[i \text{ mod } n] \ , |L| > 0 \\
\text{RecCycle}_i &= \begin{cases}
L_i & \text{if } i < n \\
\text{RecCycle}_{i - n} & \text{if } i \geq n \\
\end{cases} \ , |L| > 0 \\
\end{aligned}
```


#### Base Case

```math
\forall \ L \in  𝕃, \quad \forall \ i \in  \mathbb{N}_0 \, \ i < n \\
```
```math
\begin{aligned}
i < n \implies i \text{ mod } n &= i                  \quad &\text{[Trivial Mod For Small Dividend]} \\
\text{ModCycle}_i &= L_{(i \text{ mod } n)}           \quad &\text{[ModCycle Definition]} \\
                  &= L_i                              \quad &\text{[Since } i < n \text{, } i \text{ mod } n = i \text{]} \\
\text{RecCycle}_i &= L_i                              \quad &\text{[Since } i < n \text{, by RecCycle Definition]} \\
\therefore \\
i < n \implies\text{ModCycle}_i &= \text{RecCycle}_i  \quad &\text{[Q.E.D.]} \\
\end{aligned}
``` 

[Trivial Mod for Small Dividend](./modulo.md#trivial-case) was proved and verified in the article [Proving Properties of Division and Modulo using Formal Verification](./modulo.md)[[3]](#ref3).

#### Inductive Step

```math
\forall \ L \in  𝕃, \quad \forall \ i \
\in  \mathbb{N}_0 \, \ i \geq n \\
```
```math
\begin{aligned}
\text{ModCycle}_{(i - n)}           &= \text{RecCycle}(i - n)   \quad &\text{[By Induction Step]} \\
i \geq n \implies i \text{ mod } n  &= i \text{ mod }  (i - n)  \quad &\text{[Quotient Invariance Under Linear Shift]} \\
\text{ModCycle}_i   &= L_{(i \text{ mod } n)}        \quad &\text{[ModCycle Definition]} \\
                    &= L_{((i - n) \text{ mod } n)}  \quad &\text{[Since } i \geq n \text{, } i \text{ mod } n = i - n \text{]} \\
                    &= \text{ModCycle}_{(i - n)}     \quad &\text{[By Definition]} \\
                    &= \text{RecCycle}_{(i - n)}     \quad &\text{[By Substitution]} \\
\text{RecCycle}_{i} &= \text{RecCycle}_{(i - n)}     \quad &\text{[By RecCycle Definition]} \\
                    &= \text{ModCycle}_{i}           \quad &\text{[By Substitution]} \\
\therefore \\
i \geq n \implies \text{ModCycle}_i &= \text{RecCycle}_i  \quad &\text{[Q.E.D.]} \\
\end{aligned}
``` 

[Quotient Invariance Under Linear Shift](./modulo.md#quotient-invariance-under-linear-shift) was proved and verified in the article [Proving Properties of Division and Modulo using Formal Verification](./modulo.md)[[3]](#ref3).

This property is also proved and scala code at [](
  ./src/main/scala/v1/cycle/recursive/properties/RecursiveCycleMatchesModCycle.scala
)

<details>

<summary> Scala Doc </summary>

```scala
/**
 * Proves that modulo cycle and recursive cycle match for all positions.
 *
 * The recursive cycle is defined as follows:
 * RecursiveCycle(position) = if position < size then values(position) else RecursiveCycle(position - size)
 *
 * The cycle is defined as follows:
 * Cycle(position) = values(position % size)
 */

```
</details>


```scala
object RecursiveCycleMatchesModCycle {
````

<details>
<summary> Scala Doc </summary>


```scala
  /**
   * lemma: For values between zero and the list size,
   * recursive cycle and cycle from the same list match.
   *
   * in other words:
   *
   * for all position in [0, size),
   * recursiveCycle(position) == cycle(position)
   *
   * @param cycle Cycle
   * @param position BigInt
   * @return Boolean true if the property holds
   */
```
</details>

```scala
  def assertCycleAndRecursiveCycleMathForSmallValues(
    cycle: ModCycle,
    position: BigInt
  ): Boolean = {
    val list = cycle.values

    require(position >= 0)
    require(position < list.size)

    val recursiveCycle = RecursiveCycle(list)
    assert(position >= 0)
    assert(position < list.size)
    assert(list.size == cycle.size)
    assert(list.size == recursiveCycle.size)
    assert(ModSmallDividend.modSmallDividend(position, list.size))
    assert(Calc.mod(position, list.size) == position)
    cycle(position) == recursiveCycle(position)
  }.holds
```
<details>
<summary> Scala Doc </summary>

```scala
  /**
   * lemma: For any position greater than or equal to zero,
   * recursive cycle and cycle from the same list match
   *
   * in other words:
   *
   * for all position >= 0,
   * recursiveCycle(position) == cycle(position)
   *
   * Therefore, the recursive cycle is a valid cycle
   *
   * @param cycle Cycle
   * @param position BigInt
   * @return Boolean true if the property holds
   */
```
</details>

```scala
  def assertCycleAndRecursiveCycleMathForAnyValues(
    cycle: ModCycle,
    position: BigInt
  ): Boolean = {
    decreases(position)
    val list = cycle.values

    require(position >= 0)
    require(list.size > 0)

    val recCycle = RecursiveCycle(list)

    if (position < list.size) {
      // base case
      assertCycleAndRecursiveCycleMathForSmallValues(cycle, position)
    } else {
      // inductive step
      assertCycleAndRecursiveCycleMathForAnyValues(cycle, position - list.size)
      assert(cycle(position - list.size) == recCycle(position - list.size))
      assert(ModSum.checkValueShift(position, list.size))
      assert(Calc.mod(position, list.size) == Calc.mod(position - list.size, list.size))
      assert(cycle(position) == cycle(position - list.size))
      assert(recCycle(position) == recCycle(position - list.size))
    }
    assert(cycle(position) == recCycle(position))
  }
}
```
