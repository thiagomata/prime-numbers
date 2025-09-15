# WIP

**Author:** Mata, T. H.
Independent Researcher  
**Email:** [thiago.henrique.mata@email.com](mailto:thiago.mata@email.com)  
**GitHub:** [@thiagomata](https://github.com/thiagomata)

## Abstract

<div align="justify">
<p style="text-align: justify">
In previous articles, we defined bounded Lists, Integrals of Lists, and unbounded Cycles of Integers
from scratch, relying only on core type constructs and recursion, 
with no prior knowledge of Scala's collections required.
From that, we proved and formally verified some properties related to them.
This article uses that as a foundation to define Integral of Cycles.
Then, we formally defined and verified key properties using the Stainless verification system. 
All properties are expressed and proved within a minimal framework using only elementary arithmetic,
recursion, and pure Scala code.
This work bridges mathematical foundations and executable verification, 
offering a self-contained, verifiable approach of modular arithmetic.
 </p>
</div>

## Introduction

Cycles are a powerful concept in computer science and mathematics, representing unbounded lists that repeat a finite sequence of elements. When we integrate cycles, we obtain a list of cumulative sums with some unique properties that we will explore in this article.

```math
\begin{aligned}
L &= [l_0, l_1, l_2, \ldots, l_{n-1}]  \mid &l_n &\in 𝕊, L \in 𝕃\\
\text{Cycle}(L) &= [l_0, l_1, l_2, \ldots, l_{n-1}, l_0, l_1, \ldots] = [v_0, v_1, v_2, \dots] = \mid &v_i &= L[i \text{ mod } n] \\
\text{Integral}(L, init) &= [y_0, y_1, y_2, \ldots, y_{n-1}] \mid &y_k &= \sum_{i=0}^{k} x_i + init \\
\text{CycleIntegral}(L, init) &= [w_0, w_1, w_2, \ldots] \mid &w_k &= \sum_{i=0}^{k} \text{Cycle}(L)_i + init
\end{aligned}
```

In this article, we present discrete definition of Cycle Integral
over finite integer lists, defined recursively and verified some of 
its properties using the Stainless system.
Our approach follows a zero-prior-knowledge philosophy, building on a previously 
verified foundation for recursive list and integral structures and summation.
The result is a verified, from-scratch implementation of cycle integral 
suitable as a foundation for higher-level numeric reasoning over unbounded lists.

## 2. Preliminaries

We reuse several basic list, cycle and integral operations and their verified properties from the companion articles 
[Using Formal Verification to Prove Properties of Lists Recursively Defined](
https://github.com/thiagomata/prime-numbers/blob/master/articles/list.md
) [[1]](#ref1), [Formal Verification of Discrete Integration Properties from First Principles](
https://github.com/thiagomata/prime-numbers/blob/master/articles/integral.md
) [[2]](#ef2), and [Using Formal Verification to Prove Properties of Unbound Lists] (
https://github.com/thiagomata/prime-numbers/blob/master/articles/cyc;e.md
) [[3]](#ref3). We also reuse some modulo properties previously defined and verified in the article [Proving Properties of Division and Modulo using Formal Verification](
httos://github.com/thiagomata/prime-numbers/blob/master/articles/modulo.md
) [[4]](#ref4).


These articles also defined and verified their properties using the same zero-prior-knowledge methodology,
and are treated here as foundational primitives.

## 3. Integral Cycle Definition

$$
\forall \ i \in ℕ_0, \ init \in ℕ_0, L \in 𝕃, n = |L| \\
\text{CycleIntegral}(L, init) := [w_0, w_1, w_2, \ldots]
$$
$$
\begin{aligned}
0 \leq i < n \implies w_i ≟ \sum_{j=0}^i L_j + init \quad &\text{[Sum Property]} \\
0 < i < n \implies  \ w_i - w_{i-1} ≟ L_{(i \bmod n)}
\quad &\text{[Step Property]} \\
\end{aligned}
$$

Once both properties hold, equivalence follows from induction.

#### Induction

$$
\forall \ i \in ℕ_0, \ init \in ℕ_0, L \in 𝕃 \mid 0 \leq i < n  \implies \\
$$
$$
\begin{aligned}
i &= i \bmod n \quad &\text{[By Modulo Property]}\\
w_i &= \sum_{j=0}^i L_j + init 
\quad &\text{[Base Case]} \\
&= \sum_{j=0}^i L_{(j \bmod n)} + init 
\quad &\text{[Substitution]} \\
\\
\end{aligned}
$$

$$
\forall \ i \in ℕ \mid \ w_i - w_{i-1} = L_{(i \bmod n)} \implies \\
$$

$$
\begin{aligned}
w_{i-1} &= \sum_{j=0}^{i-1} L_{(j \bmod n)} + init \quad &\text{[Induction Step]} \\
w_i - w_{i-1} &= L_{(i \bmod n)}
\quad &\text{[By definition]} \\
w_i  &= L_{(i \bmod n)} + w_{i-1} 
\quad &\text{[Transposition]} \\
&=  L_{(i \bmod n)} + \sum_{j=0}^{i-1} L_{(j \bmod n)} + init
\quad &\text{[By Step Property]} \\
&= \sum_{j=0}^{i} L_{(j \bmod n)} + init \quad &\text{[Summation Re-indexing]} \\
\end{aligned}
$$

$$
\therefore
$$
$$
% \forall \ i \in ℕ_0, \ init \in ℕ_0, L \in 𝕃 \mid \text{CycleIntegral}(L, init) = [w_0, w_1, w_2, \ldots] \\
$$

$$
\begin{aligned}
\quad w_i &= \sum_{j=0}^i L_{(j \bmod n)} + init \ \blacksquare  \quad &\text{[Q.E.D.]} \\
\end{aligned}
$$

### 3.1 Classic Cycle Integral

```math
\begin{aligned}
\text{Cycle}(L)_i &= L_{(i \bmod n)} \\
\text{ClassicCycleIntegral}(L, init)_k &= \sum_{i=0}^k \text{Cycle}(L)_i + init
\end{aligned}
```

#### Base Case

$$
\begin{aligned}
i < n \implies Cycle(L)_i &= L_i \\
i < n \implies ClassicCycleIntegral(L, init)_i &= \sum_{j=0}^i Cycle(L)_i + init \quad &\text{[By Definition]}\\
 &= \sum_{j=0}^i L_j + init \quad &\text{[Substitution]}\\
\end{aligned}
$$

$$
\begin{aligned}
\therefore \forall \ i < n, \quad ClassicCycleIntegral(L, init)_i &= \sum_{j=0}^i L_j + init  \quad &\text{[Q.E.D.]} \\
\end{aligned}
$$



#### Step Property

$$
\forall \ i \in ℕ_0,\ init \in ℕ_0, L \in 𝕃
$$

$$
\begin{aligned}
w_i &= ClassicCycleIntegral(L, init)_i \quad &\text{[By Definition]} \\
w_{i-1} &= ClassicCycleIntegral(L, init)_{i-1} \quad &\text{[By Definition]} \\
w_i - w_{i-1} &= \left(\sum_{j=0}^i L_j + init\right) - \left(\sum_{j=0}^{i-1} L_j + init\right)  \quad &\text{[By Definition]} \\
&= \sum_{j=0}^i L_j + init - \sum_{j=0}^{i-1} L_j - init \quad &\text{[Association]} \\
&= \sum_{j=0}^i L_j - \sum_{j=0}^{i-1} L_j \quad &\text{[Canceling init]} \\
&= L_i \quad &\text{[Simplification]} \\
&= L_{(i \bmod n)} \quad &\text{[By Modulo Property]} \\
\end{aligned}
$$
$$
\therefore \ w_i - w_{i-1} = \text{Cycle}(L)_i = L_{(i \bmod n)} \quad \text{[Q.E.D.]}
$$


### 3.2 Recursive Cycle Integral


```math
\begin{aligned}
\text{RecCycle}(L) &= [v_0, v_1, \dots] \mid v_i =
\begin{cases}
  L[i] & i < n \\
  v_{i - n} & i \geq n
\end{cases} \\
\text{RecCycleIntegral}(L, init) &= [w_0, w_1, \dots] \mid w_i =
\begin{cases}
  init + w_0 & i = 0 \\
  v_i + w_{i - 1} & i > 0
\end{cases}
\end{aligned}
```

**Recursive Cycle Equivalence**:

Recursive Cycle is equivalent to the Mod Cycle, 
as proven in the article [Using Formal Verification to Prove Properties of Unbound Lists](
https://github.com/thiagomata/prime-numbers/blob/master/articles/cyc;e.md
) [[3]](#ref3).


```math
\begin{aligned}
RecCycle(L)_i &=  ModCycle(L)_i \quad &\text{[Cycle Equivalence]} \\
  &= L_{(i \bmod n)} \quad &\text{[Mod Cycle Definition]} \\
\end{aligned}
```

**Sum Property**:


$$
\begin{aligned}
v_0  &= L_0  \quad &\text{[Base Case]} \\
&= L_{(0 \bmod n)} \quad &\text{[By Modulo Property]} \\
&= \sum_{j=0}^0 L_j \quad &\text{[Summation Re-indexing]} \\
\\
i < n \implies \\
w_0 &= init + v_0 \quad &\text{[Base Case]} \\
&= init + \sum_{j=0}^i L_j  \quad &\text{[Summation Re-indexing]} \\
i > 0 \implies \\
w_i &= init + v_0 + \sum_{j=1}^i v_j \quad &\text{[By Definition]}\\
&= init + v_0 + \sum_{j=1}^i L_j \quad &\text{[Mod of Small Values Property]} \\
&= init + \sum_{j=0}^i v_j \quad &\text{[Summation Re-indexing]} \\
\therefore w_i &= init + \sum_{j=0}^i L_j \quad &\text{[Q.E.D.]} \\
\end{aligned}
$$

**Step Property**:

$$
\begin{aligned}
w_i - w_{i-1} &= v_i + w_{i-1} - w_{i-1} \quad &\text{[By Definition]} \\
&= v_i \quad &\text{[Simplification]} \\
&= L_{(i \bmod n)} \quad &\text{[Substitution]} \\
\end{aligned}
$$

### 3.3 Modulo Cycle Integral

```math
\begin{aligned}
\text{ModCycle}(L)_i &:= L_{(i \bmod n)} = [w_0, w_1, \dots ] \\
I_k &:= \sum_{j=0}^{k} L_j \quad (0 \leq k < n) \quad &\text{[Integral of L]} \\
S &:= I_{n-1} \quad &\text{[One full cycle sum]} \\
\text{ModCycleIntegral}(L, init)_i &:= (i \text{ div } n)\cdot S + I_{(i \bmod n)} + init
\end{aligned}
```

#### Sum Property

```math
i < n \implies w_i ≟ \sum_{j=0}^i L_j + init \quad \text{[Claim to Prove]}
```

```math
\begin{aligned}
i < n \implies  \\
i \text{ div } n 
      \quad &= 0 \quad 
      &\text{[By Div of Small Values Property]} \\
w_i &= (i \text{ div } n)\cdot S + I_{(i \bmod n)} + init \quad 
      &\text{[Definition]} \\
&= 0 \cdot S + I_i + init \quad &\text{[Substitution}] \\
&= \sum_{j=0}^i L_j + init \quad &\text{[By definition of } I_i]
\end{aligned}
```

$$
\therefore \
\forall \ i < n,\quad w_i = \sum_{j=0}^i L_j + init \quad \text{[Q.E.D.]}
$$

#### Step Property


```math
w_i - w_{i-1} ≟ L_{\, i \bmod n}, \quad i>0,\, n>0
\quad \text{[Claim to Prove]}
```

**$i \bmod n > 0 \implies$**

$$
\begin{aligned}
i \bmod n &= ((i-1) \bmod n) + 1
&&\text{[By Modulo Properties]} \\
i \text{ div } n &= (i-1) \text{ div } n
&&\text{[By Division Properties]} \\
w_i &= (i \text{ div } n)\,S + I_{\,i\bmod n} + init
&&\text{[Definition]} \\
&= (i-1 \text{ div } n)\,S + I_{\,((i-1)\bmod n)+1} + init
&&\text{[Div/Mod property]} \\
w_{i-1} &= (i-1 \text{ div } n)\,S + I_{\, (i-1)\bmod n} + init
&&\text{[Definition]} \\
w_i-w_{i-1}
    &= I_{\,((i-1)\bmod n)+1} - I_{\, (i-1)\bmod n}
&&\text{[Cancellation]} \\
    &= \Big(\sum_{j=0}^{(i-1)\bmod n} L_j + L_{((i-1)\bmod n)+1}\Big)
       - \sum_{j=0}^{(i-1)\bmod n} L_j
&&\text{[Expand sum]} \\
    &= L_{((i-1)\bmod n)+1}
&&\text{[Cancellation]} \\
    &= L_{\,i \bmod n}
&&\text{[Modulo property]}.
\end{aligned}
$$

**$i \bmod n = 0 \implies$**

$$
\begin{aligned}
w_i &= (i \text{ div } n)\,S + L_0 + init
&&\text{[Definition]} \\
w_{i-1} &= (i \text{ div } n -1)\,S + I_{\,n-1} + init
&&\text{[Div/Mod property]} \\
w_i-w_{i-1}
    &= (i \text{ div } n)\,S + L_0 + init
       - \big((i \text{ div } n -1)\,S + I_{\,n-1} + init\big)
&&\text{[Substitution]} \\
    &= S + L_0 - I_{\,n-1}
&&\text{[Simplification]} \\
    &= L_0
&&\text{[Since } S = I_{\,n-1}] \\
    &= L_{\,i \bmod n}
&&\text{[Modulo property]}.
\end{aligned}
$$

$$
\therefore \
w_i - w_{i-1} = L_{\, i \bmod n}, \quad \forall \ i > 0 \quad \text{[Q.E.D.]}
$$

### 3.4 Equivalence of Definitions

Since all definitions of Cycle Integral satisfy the same properties, we can conclude that they are equivalent. The Cycle Integral can be defined using any of the three approaches: Classic, Recursive, or Modulo. 

```math
\begin{aligned}
\text{CycleIntegral}(L, init) &= \text{ClassicCycleIntegral}(L, init) \\
&= \text{RecCycleIntegral}(L, init) \\
&= \text{ModCycleIntegral}(L, init) \\
&= [w_0, w_1, w_2, \ldots] \mid w_i =& \sum_{j=0}^i L_{(j \bmod n)} + init \ \blacksquare \quad \\

\end{aligned}
```

## 4. Properties

### 

cycleIntegral(x) == sum(cycle(0), cycle(1), ..., Cycle(position))

```scala
  /**
   * The sum of the values of the cycle integral until that position is equal to
   * the current value of the cycle integral.
   *
   * In other words:
   * CycleIntegral(position) == sum(cycle(0), cycle(1), ..., Cycle(position))
   *
   * @param cycleIntegral CycleIntegral any cycle integral
   * @return Boolean true if the property holds
   */
  def assertCycleIntegralEqualsSumFirstPosition(cycleIntegral: CycleIntegral): Boolean = {
    val smallList = List(cycleIntegral.initialValue) ++ List(cycleIntegral.cycle(0))
    assert(ListUtils.sum(List()) == BigInt(0))
    ListUtilsProperties.listAddValueTail(List(), cycleIntegral.initialValue)
    ListUtilsProperties.listAddValueTail(List(cycleIntegral.initialValue), cycleIntegral.cycle(0))
    assert(ListUtils.sum(smallList) == cycleIntegral.initialValue + cycleIntegral.cycle(0))
    assert(cycleIntegral(0) == cycleIntegral.initialValue + cycleIntegral.cycle(0))
    assert(smallList == getFirstValuesAsSlice(cycleIntegral, 0))
    ListUtils.sum(getFirstValuesAsSlice(cycleIntegral, 0)) == cycleIntegral(0)
  }.holds
  ```

### 

cycleIntegral(pos + 1) - cycleIntegral(pos) == cycleIntegral.cycle(pos + 1)

```scala
  /**
   * Lemmas: The difference between two consecutive values in the cycle
   * pos and pos + 1 is equal to cycle.values at pos + 1.
   *
   * in other words
   * cycleIntegral(pos + 1) - cycleIntegral(pos) == cycleIntegral.cycle(pos + 1)
   *
   * @param cycleIntegral CycleIntegral any cycle integral
   * @param position BigInt any position bigger than or equals to zero
   * @return true if the property holds
   */
  def assertDiffEqualsCycleValue(cycleIntegral: CycleIntegral, position: BigInt): Boolean = {
    require(position >= 0)
    assert(cycleIntegral(position + 1) == cycleIntegral(position) + cycleIntegral.cycle(position + 1))
    cycleIntegral(position + 1) - cycleIntegral(position) == cycleIntegral.cycle(position + 1)
  }.holds
```

#### 

cycleIntegral(pos + 1) - cycleIntegral(pos) == cycleIntegral(pos + size + 1) - cycleIntegral(pos + size)

```scala
  /**
   * Lemmas: The difference between two consecutive values in the cycle
   * pos and pos + 1 is equal to the difference of the cycle values at the
   * pos + size and pos + size + 1.
   *
   * in other words
   * size == cycleIntegral.size
   * cycleIntegral(pos + 1) - cycleIntegral(pos) == cycleIntegral(pos + size + 1) - cycleIntegral(pos + size)
   *
   * @param iCycle CycleIntegral any cycle integral
   * @param position BigInt any position bigger than or equals to zero
   * @return Boolean true if the property holds
   */
  def assertSameDiffAfterCycle(iCycle: CycleIntegral, position: BigInt): Boolean = {
    require(position >= 0)

    val a = position
    val b = position + 1
    val c = a + iCycle.size
    val d = b + iCycle.size

    assertDiffEqualsCycleValue(cycleIntegral = iCycle, position = a)
    assert(iCycle(b) - iCycle(a) == iCycle.cycle(b))

    assertDiffEqualsCycleValue(cycleIntegral = iCycle, position = c)
    assert(iCycle(d) - iCycle(c) == iCycle.cycle(d))

    MemCycleProperties.valueMatchAfterManyLoopsInBoth(iCycle.cycle, a, 0, 1)
    MemCycleProperties.valueMatchAfterManyLoopsInBoth(iCycle.cycle, b, 0, 1)

    assert(iCycle.cycle(d) == iCycle.cycle(b))
    assert(iCycle.cycle(c) == iCycle.cycle(a))

    iCycle(b) - iCycle(a) == iCycle(d) - iCycle(c)
  }.holds

  def assertLastElementBeforeLoop(iCycle: CycleIntegral): Boolean = {
    assertCycleIntegralEqualsSliceSum(iCycle, iCycle.size - 1)
    iCycle(iCycle.size - 1) == ListUtils.sum(getFirstValuesAsSlice(iCycle, iCycle.size - 1))
  }.holds
```

### 

cycleIntegral(position) ==  div(position, size) * modCycleIntegral.integralValues.last + modCycleIntegral.integralValues(mod(position, size)) + cycleIntegral.initialValue


```scala
  /**
   * Since the cycle accumulator and cycle integral are equal at any position,
   * we can use this lemma to prove that cycle integral is equal to the cycle accumulator
   * definition.
   *
   * In other words:
   *
   * cycleIntegral(position) ==
   *   div(position, size) * modCycleIntegral.integralValues.last +
   *   modCycleIntegral.integralValues(mod(position, size)) + cycleIntegral.initialValue
   *
   * @param modCycle ModCycle any ModCycle
   * @param cycleIntegral CycleIntegral any CycleIntegral with same cycle and initialValue
   * @param position BigInt any position bigger than or equal to 0
   * @return Boolean true if the properties hold
   */
  def assertCycleIntegralMatchModCycleDef(
                                           modCycleIntegral: ModCycleIntegral,
                                           cycleIntegral: CycleIntegral,
                                           position: BigInt,
  ): Boolean = {
    require(position >= 0)
    require(modCycleIntegral.mCycle.values.nonEmpty)
    require(cycleIntegral.cycle.values.nonEmpty)
    require(modCycleIntegral.mCycle.values == cycleIntegral.cycle.values)
    require(modCycleIntegral.mCycle.size   == cycleIntegral.cycle.size)
    require(modCycleIntegral.initialValue == cycleIntegral.initialValue)
    decreases(position)

    assertModCycleEqualsCycleIntegral(
      modCycleIntegral,
      cycleIntegral,
      position
    )
    val size = modCycleIntegral.mCycle.size
    
    assert(modCycleIntegral(position) == cycleIntegral(position))
    assert(
      modCycleIntegral(position) == div(position, size) * modCycleIntegral.integralValues.last + 
      modCycleIntegral.integralValues(mod(position, size)) + modCycleIntegral.initialValue
    )
    
    cycleIntegral(position) == 
      div(position, size) * modCycleIntegral.integralValues.last +
        modCycleIntegral.integralValues(mod(position, size)) + cycleIntegral.initialValue
  }.holds
```

## 100. Conclusion

This article presented the definitions and properties of Cycles, a fundamental concept in computer science that allows for the representation of repeating sequences of values.
We defined Cycles using two approaches: a recursive definition and a modulo-based definition. We proved that both definitions are equivalent, producing the same sequence of values.
We also explored several properties of Cycles, including element access, value consistency after multiple loops, and the propagation of modulo operations from values to cycles.

```math
\begin{aligned}
&\forall \ L \in  𝕃, \quad \forall \ v \in ℕ_0,\quad \forall \ i, m_1, m_2 \in ℕ_0 \\
L &:= [v_0, v_1, \dots, v_{n-1}] \in ℕ_0^n, |L| > 0 \\
Cycle &:= [v_0, v_1, \dots, v_{n-1}, v_0, v_1, \dots] \\
n &= |L| \\
\text{ModCycle}_i &= \text{RecCycle}_i = \text{Cycle}_i \quad &\text{[Cycle Equivalence]} \\
\text{ModCycle}_{(i + n \cdot m_1)} &= L  [i \text{ mod } n] \quad &\text{[Value Match After Many Loops]} \\
\text{ModCycle}_{(i + n \cdot m_2)} &= L  [i \text{ mod } n] \quad &\text{[Value Match After Many Loops]} \\
\text{Cycle}_{(i + n \cdot m_1)} &= \text{Cycle}_{(i + n \cdot m_2)} = L  [i \text{ mod } n] \quad &\text{[Propagate Modulo from Value to Cycle
]} \\
\end{aligned}
``` 

These properties were formally verified using Scala Stainless, ensuring their correctness and reliability.

## 5. Future Work

Future work may include exploring more complex properties of Cycles, such as their behavior under various operations like concatenation and filtering, and their applications in algorithms and data structures. Additionally, we can investigate discret integration of Cycles, similar to the work done for lists [[1]](#ref1) and integrals [[2]](#ref2).

## References

<a name="ref1" id="ref1" href="#ref1">[1]</a> 
Mata, T. H. (2025). *Using Formal Verification to Prove Properties of Lists Recursively Defined*. Unpublished manuscript.  
Available at: [
  https://github.com/thiagomata/prime-numbers/blob/master/articles/list.md](
  https://github.com/thiagomata/prime-numbers/blob/master/articles/list.md)

<a name="ref2" id="ref2" href="#ref2">[2]</a>
Mata, T. H. (2025). *Formal Verification of Discrete Integration Properties from First Principles*. Unpublished manuscript.  
Available at: [
  https://github.com/thiagomata/prime-numbers/blob/master/articles/integral.md](
  https://github.com/thiagomata/prime-numbers/blob/master/articles/integral.md)

<a name="ref3" id="ref3" href="#ref3">[3]</a>
Mata, T. H. (2025). *Proving Properties of Division and Modulo using Formal Verification*. Unpublished manuscript.  
Available at: [
  https://github.com/thiagomata/prime-numbers/blob/master/articles/modulo.md
)(https://github.com/thiagomata/prime-numbers/blob/master/articles/modulo.md)


