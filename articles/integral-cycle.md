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
\end{aligned}

```
```math
\begin{aligned}
\text{Cycle}(L)               &= [l_0, l_1, l_2, \ldots, l_{n-1}, l_0, l_1, \ldots] \\
                              &= [v_0, v_1, v_2, \dots] \mid &v_i &= L[i \text{ mod } n] \\
\text{Integral}(L, init)      &= [y_0, y_1, y_2, \ldots, y_{n-1}] \mid &y_k &= \sum_{i=0}^{k} x_i + init \\
\text{CycleIntegral}(L, init) &= [w_0, w_1, w_2, \ldots] \mid          &w_k &= \sum_{i=0}^{k} \text{Cycle}(L)_i + init
\end{aligned}
```

In this article, we present a discrete definition of Cycle Integral
over finite integer lists, defined recursively and verified some of its properties using the Stainless system.
Our approach follows a zero-prior-knowledge philosophy, building on a previously 
verified foundation for recursive list and integral structures and summation.
The result is a verified, from-scratch implementation of the cycle integral 
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

```math
\forall \ i \in ℕ_0, \ init \in ℕ_0, L \in 𝕃, n = |L| \\
\text{CycleIntegral}(L, init) := [w_0, w_1, w_2, \ldots]
```
```math
\begin{aligned}
0 \leq i < n \implies w_i ≟ \sum_{j=0}^i L_j + init \quad &\text{[Sum Property]} \\
0 < i < n \implies  \ w_i - w_{i-1} ≟ L_{(i \text{ mod } n)}
\quad &\text{[Step Property]} \\
\end{aligned}
```

Once both properties hold, equivalence follows from induction.

#### Induction

```math
\forall \ i \in ℕ_0, \ init \in ℕ_0, L \in 𝕃 \mid 0 \leq i < n  \implies
```

```math
\begin{aligned}
&i &= i \text{ mod } n \quad &\text{[By Modulo Property]}\\
&w_i &= \sum_{j=0}^i L_j + init  \quad &\text{[Base Case]} \\
&&= \sum_{j=0}^i L_{(j \text{ mod } n)} + init  \quad &\text{[Substitution]} \\
\end{aligned}
```

```math
\forall \ i \in ℕ \mid \ w_i - w_{i-1} = L_{(i \text{ mod } n)} \implies
```

```math
\begin{aligned}
&w_{i-1} &= \sum_{j=0}^{i-1} L_{(j \text{ mod } n)} + init \quad &\text{[Induction Step]} \\
&w_i - w_{i-1} &= L_{(i \text{ mod } n)}
\quad &\text{[By definition]} \\
&w_i  &= L_{(i \text{ mod } n)} + w_{i-1} 
\quad &\text{[Transposition]} \\
&&=  L_{(i \text{ mod } n)} + \sum_{j=0}^{i-1} L_{(j \text{ mod } n)} + init
\quad &\text{[By Step Property]} \\
&&= \sum_{j=0}^{i} L_{(j \text{ mod } n)} + init \quad &\text{[Summation Re-indexing]} \\
\end{aligned}
```

```math
\therefore
```
```math
\forall \ i \in ℕ_0, \ init \in ℕ_0, L \in 𝕃 \mid \text{CycleIntegral}(L, init) = [w_0, w_1, w_2, \ldots] \\
```

```math
\begin{aligned}
\quad w_i &= \sum_{j=0}^i L_{(j \text{ mod } n)} + init \ \blacksquare  \quad &\text{[Q.E.D.]} \\
\end{aligned}
```


### 3.1 Classic Cycle Integral

```math
\begin{aligned}
\text{Cycle}(L)_i &= L_{(i \text{ mod } n)} \\
\text{ClassicCycleIntegral}(L, init)_k &= \sum_{i=0}^k \text{Cycle}(L)_i + init
\end{aligned}
```

As defined in the code at [
  ClassicCycleIntegral.scala
](
  ../src/main/scala/v1/cycle/integral/classic/ClassicCycleIntegral.scala
)

```scala
case class ClassicCycleIntegral(
  initialValue: BigInt,
  cycle: MemCycle
) {

  def apply(position: BigInt): BigInt = {
    require(position >= 0)
    decreases(position)

    if (position == 0 ) {
      cycle(0) + initialValue
    } else {
      cycle(position) + apply(position - 1)
    }
  }

  def size: BigInt = cycle.size

  def sum: BigInt = cycle.sum()
}
```

#### Base Case

```math
\begin{aligned}
i < n \implies Cycle(L)_i &= L_i \\
i < n \implies ClassicCycleIntegral(L, init)_i &= \sum_{j=0}^i Cycle(L)_i + init \quad &\text{[By Definition]}\\
 &= \sum_{j=0}^i L_j + init \quad &\text{[Substitution]}\\
\end{aligned}
```

```math
\begin{aligned}
\therefore \forall \ i < n, \quad ClassicCycleIntegral(L, init)_i &= \sum_{j=0}^i L_j + init  \quad &\text{[Q.E.D.]} \\
\end{aligned}
```

This property is verified in the [
  ClassicCycleIntegralProperties::assertCycleIntegralEqualsSumSmallPositions
](
  ../src/main/scala/v1/cycle/integral/classic/properties/ClassicCycleIntegralProperties.scala
)


#### Step Property

```math
\forall \ i \in ℕ_0,\ init \in ℕ_0, L \in 𝕃
```

```math
\begin{aligned}
&w_i &= ClassicCycleIntegral(L, init)_i \quad &\text{[By Definition]} \\
&w_{i-1} &= ClassicCycleIntegral(L, init)_{i-1} \quad &\text{[By Definition]} \\
&w_i - w_{i-1} &= \left(\sum_{j=0}^i L_j + init\right) - \left(\sum_{j=0}^{i-1} L_j + init\right)  \quad &\text{[By Definition]} \\
&&= \sum_{j=0}^i L_j + init - \sum_{j=0}^{i-1} L_j - init \quad &\text{[Association]} \\
&&= \sum_{j=0}^i L_j - \sum_{j=0}^{i-1} L_j \quad &\text{[Canceling init]} \\
&&= L_i \quad &\text{[Simplification]} \\
&&= L_{(i \text{ mod } n)} \quad &\text{[By Modulo Property]} \\
\end{aligned}
```
```math
\therefore \ w_i - w_{i-1} = \text{Cycle}(L)_i = L_{(i \text{ mod } n)} \quad \text{[Q.E.D.]}
```


This property is verified in the [
  ClassicCycleIntegralProperties::assertDiffEqualsCycleValue
](
  ../src/main/scala/v1/cycle/integral/classic/properties/ClassicCycleIntegralProperties.scala
)

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
  &= L_{(i \text{ mod } n)} \quad &\text{[Mod Cycle Definition]} \\
\end{aligned}
```

**Sum Property**:


```math
\begin{aligned}
v_0  &= L_0  \quad &\text{[Base Case]} \\
&= L_{(0 \text{ mod } n)} \quad &\text{[By Modulo Property]} \\
&= \sum_{j=0}^0 L_j \quad &\text{[Summation Re-indexing]} \\
\end{aligned}
```

```math
\begin{aligned}
i < n \implies \\
w_0 &= init + v_0 \quad &\text{[Base Case]} \\
&= init + \sum_{j=0}^i L_j  \quad &\text{[Summation Re-indexing]} \\
i > 0 \implies \\
w_i &= init + v_0 + \sum_{j=1}^i v_j \quad &\text{[By Definition]}\\
&= init + v_0 + \sum_{j=1}^i L_j \quad &\text{[Mod of Small Values Property]} \\
&= init + \sum_{j=0}^i v_j \quad &\text{[Summation Re-indexing]} \\
\therefore w_i &= init + \sum_{j=0}^i L_j \quad &\text{[Q.E.D.]} \\
\end{aligned}
```

These properties are also verified at
[
  CycleIntegralProperties::assertCycleIntegralEqualsSumSmallPositions
](
  ../src/main/scala/v1/cycle/integral/recursive/properties/CycleIntegralProperties.scala#assertCycleIntegralEqualsSumSmallPositions
).


**Step Property**:

```math
\begin{aligned}
w_i - w_{i-1} &= v_i + w_{i-1} - w_{i-1} \quad &\text{[By Definition]} \\
&= v_i \quad &\text{[Simplification]} \\
&= L_{(i \text{ mod } n)} \quad &\text{[Substitution]} \\
\end{aligned}
```

This property is also verified at
[
  CycleIntegralProperties::assertDiffEqualsCycleValue
](
  ../src/main/scala/v1/cycle/integral/recursive/properties/CycleIntegralProperties.scala#assertDiffEqualsCycleValue
).

### 3.3 Modulo Cycle Integral

```math
\begin{aligned}
&\text{ModCycle}(L)_i &:= L_{(i \text{ mod } n)} = [w_0, w_1, \dots ] \\
&I_k &:= \sum_{j=0}^{k} L_j \quad (0 \leq k < n) \quad &\text{[Integral of L]} \\
&S &:= I_{n-1} \quad &\text{[One full cycle sum]} \\
&\text{ModCycleIntegral}(L, init)_i &:= (i \text{ div } n)\cdot S + I_{(i \text{ mod } n)} + init
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
w_i &= (i \text{ div } n)\cdot S + I_{(i \text{ mod } n)} + init \quad 
      &\text{[Definition]} \\
&= 0 \cdot S + I_i + init \quad &\text{[Substitution}] \\
&= \sum_{j=0}^i L_j + init \quad &\text{[By definition of } I_i]
\end{aligned}
```

```math
\therefore \
\forall \ i < n,\quad w_i = \sum_{j=0}^i L_j + init \quad \text{[Q.E.D.]}
```

This property is also verified at
[
  ModCycleIntegralProperties::assertFirstValuesMatchIntegral
](
../src/main/scala/v1/cycle/integral/mod/ModCycleIntegralProperties.scala#assertFirstValuesMatchIntegral
).

#### Step Property

    
```math
w_i - w_{i-1} ≟ L_{\, i \text{ mod } n}, \quad i>0,\, n>0
\quad \text{[Claim to Prove]}
```

**$i \text{ mod } n > 0 \implies$**

```math
\begin{aligned}
&i \text{ mod } n &= ((i-1) \text{ mod } n) + 1 &&\text{[By Modulo Properties]} \\
&i \text{ div } n &= (i-1) \text{ div } n &&\text{[By Division Properties]} \\
&w_i &= (i \text{ div } n)\,S + I_{\,i\text{ mod } n} + init &&\text{[Definition]} \\
     &&= (i-1 \text{ div } n)\,S + I_{\,((i-1)\text{ mod } n)+1} + init &&\text{[Div/Mod property]} \\
&w_{i-1} &= (i-1 \text{ div } n)\,S + I_{\, (i-1)\text{ mod } n} + init &&\text{[Definition]} \\
&w_i-w_{i-1} &= I_{\,((i-1)\text{ mod } n)+1} - I_{\, (i-1)\text{ mod } n} &&\text{[Cancellation]} \\
    &&= \Big(\sum_{j=0}^{(i-1)\text{ mod } n} L_j + L_{((i-1)\text{ mod } n)+1}\Big)
       - \sum_{j=0}^{(i-1)\text{ mod } n} L_j &&\text{[Expand sum]} \\
    &&= L_{((i-1)\text{ mod } n)+1} &&\text{[Cancellation]} \\
    &&= L_{\,i \text{ mod } n} &&\text{[Modulo property]}.
\end{aligned}
```

**$i \text{ mod } n = 0 \implies$**

```math
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
    &= L_{\,i \text{ mod } n}
&&\text{[Modulo property]}.
\end{aligned}
```

```math
\therefore \
w_i - w_{i-1} = L_{\, i \text{ mod } n}, \quad \forall \ i > 0 \quad \text{[Q.E.D.]}
```

This property is also verified at
[
  ModCycleIntegralProperties::assertSimplifiedDiffValuesMatchCycle
](
  ../src/main/scala/v1/cycle/integral/mod/ModCycleIntegralProperties.scala#assertSimplifiedDiffValuesMatchCycle
).

### 3.4 Equivalence of Definitions

Since all definitions of Cycle Integral satisfy the same properties, we can conclude that they are equivalent. The Cycle Integral can be defined using any of the three approaches: Classic, Recursive, or Modulo. 

```math
\begin{aligned}
\text{CycleIntegral}(L, init) &= \text{ClassicCycleIntegral}(L, init) \\
&= \text{RecCycleIntegral}(L, init) \\
&= \text{ModCycleIntegral}(L, init) \\
&= [w_0, w_1, w_2, \ldots] \mid w_i =& \sum_{j=0}^i L_{(j \text{ mod } n)} + init \ \blacksquare \quad \\

\end{aligned}
```

This property is also verified at
[
  ModCycleIntegralProperties::assertCycleIntegralMatchModCycleDef
](
../src/main/scala/v1/cycle/integral/mod/ModCycleIntegralProperties.scala#assertCycleIntegralMatchModCycleDef
).


## 4. Properties

### 4.1 Modulo Invariance Property

Let $v \in \mathbb{N}$ with $v > 0$, such that the total cycle sum is a multiple of $v$.  
Then the remainder of any Cycle Integral value depends only on the corresponding partial sum within the first cycle.
Therefore, if none of the Cycle Integral values within the first cycle are congruent to $0 \pmod v$, then no value in the Cycle Integral will ever be congruent to $0 \pmod v$.

In other words, if we define:

```math
\begin{aligned}
L &= [v_0, v_1, \dots, v_{n-1}] \in \mathbb{N}_0^n, \quad |L| > 0 \\
n &:= |L| \\
S &:= \sum_{j=0}^{n-1} v_j \\
I_k &:= \sum_{j=0}^{k} v_j \quad (0 \le k < n) \\
\end{aligned}
````

```math
\begin{aligned}
\text{CycleIntegral}(L, init)_i := (i \,\text{div}\, n)\cdot S + I_{(i \text{ mod } n)} + init
\end{aligned}
```
we have:

```math
\begin{aligned}
 &\Big( S \text{ mod } v = 0 \ \wedge \ \forall \ k \in [0,n-1],\ (I_k + init) \text{ mod } v \neq 0 \Big)\\
&\implies \forall \ i \in \mathbb{N}_0, \ \text{CycleIntegral}(L, init)_i \text{ mod } v \neq 0 \\
\end{aligned}
```

#### Proof

```math
\begin{aligned}
\text{CycleIntegral}(L, init)_i &:= (i \text{ div } n)\cdot S + I_{(i \text{ mod } n)} + init \quad &&\text{[By Definition]} \\
(\text{CycleIntegral}(L, init)_i) \text{ mod } v 
  &= \big((i \text{ div } n)\cdot S + I_{(i \text{ mod } n)} + init\big) \text{ mod } v  \quad &&\text{[Substitution]} \\
  &= \big((i \text{ div } n)\cdot S \text{ mod } v + (I_{(i \text{ mod } n)} + init) \text{ mod } v\big) \text{ mod } v 
  &&\text{[By Modulo Properties]} \\
  &= \big(0 + (I_{(i \text{ mod } n)} + init) \text{ mod } v\big) \text{ mod } v 
  &&\text{[Since } S \text{ mod } v = 0] \\
  &= (I_{(i \text{ mod } n)} + init) \text{ mod } v 
  &&\text{[Simplification of Modulo of Modulo]} \\
  &\therefore \\
  \forall \ i &\in ℕ_0 \\
  \ (I_{(i \text{ mod } n)} + init) \text{ mod } v \neq 0 &\implies CycleIntegral(L, init)_i \text{ mod } v \neq 0 \quad &&\text{[Modulo matches Integral} \neq 0 \text{]} \\
\ \ (I_{(i \text{ mod } n)} + init) \text{ mod } v = 0 &\implies CycleIntegral(L, init)_i \text{ mod } v = 0 \quad &&\text{[Modulo matches Integral $= 0$]} \\
\forall \ k \in [0,n-1],\ (I_k + init) \text{ mod } v \neq 0 &\implies CycleIntegral(L, init)_i \text{ mod } v \neq 0  \quad &&\text{[Case: all partial sums} \neq 0  \text{]} \\  
\forall \ k \in [0,n-1],\ (I_k + init) \text{ mod } v = 0 &\implies CycleIntegral(L, init)_i \text{ mod } v = 0 \quad &&\text{[Case: all partial sums $= 0$]}
\end{aligned}
```

### 4.2 Invariance by Concatenation

Let $L' \in 𝕃$ be the concatenation of $L \in 𝕃$ with itself, and let $init \in \mathbb{N}_0$ be initial value. Then the CycleIntegral of $L'$ with initial value $init$ reproduces exactly the CycleIntegral of $L$ with initial value $init$.

```math
\begin{aligned}
L' &:= L :: L, \quad init \in \mathbb{N}_0 \quad &\text{[Definition by Concatenation]} \\
\text{CycleIntegral}(L', init)_i &= \text{CycleIntegral}(L, init)_i  \quad \forall i \in \mathbb{N}_0 \quad &\text{[Exact Value Reproduction]} \\
\end{aligned}
``` 

#### Proof

```math
\begin{aligned}
 n &= |L|, \quad L = [v_0, \dots, v_{n-1}]                 &&\text{[Length of original cycle]} \\
L' &:= L :: L = [v_0, \dots, v_{n-1}, v_0, \dots, v_{n-1}]  &&\text{[Concatenate cycle with itself]} \\
m  &:= |L'| = 2 n                                           &&\text{[Length of new cycle]} \\
S  &:= \sum_{j=0}^{n-1} v_j                                 &&\text{[Original cycle sum]} \\
I'_k &:= \sum_{j=0}^{k} L'_j = 
  \begin{cases} 
    I_k & 0 \le k < n \\ 
    S + I_{k-n} & n \le k < 2n 
  \end{cases} 
  &&\text{[Partial sums of concatenated cycle]} \\
S' &:= \sum_{j=0}^{m-1} L'_j = 2 \cdot S &&\text{[Sum of concatenated cycle]} \\
I'_{i \text{ mod } 2n} &= I_{i \text{ mod } n} &&\text{[By definition of } I'_k] \\
\end{aligned}
```

```math
\begin{aligned}
\text{CycleIntegral}(L', init)_i &= (i \,\text{div}\, m)\cdot S' + I'_{i \text{ mod } m} + init &&\text{[By Definition]} \\
&= (i \,\text{div}\, 2n)\cdot (2 \cdot S) + I'_{i \text{ mod } 2n} + init &&\text{[Substitution]} \\
  &= (i \,\text{div}\, n)\cdot S + I_{i \text{ mod } n} + init &&\text{[Simplifies exactly to original values]} \\
  &= \text{CycleIntegral}(L, init)_i &&\text{[Exact value reproduction]} \\
\end{aligned}
```
```math
\therefore
```
```math
\begin{aligned}
\forall \ i \in \mathbb{N}_0 , \\
\quad \text{CycleIntegral}(L', init)_i &= \text{CycleIntegral}(L, init)_i \quad &&\text{[Q.E.D.]} \\
\end{aligned}
```

Therefore, concatenating a cycle with itself does not change its CycleIntegral.

### 4.3 Right Shift Invariance

Let $L' \in 𝕃$ be the right shift of $L \in 𝕃$ by $k$ positions, in other words:

```math
\begin{aligned}
&n &= |L|, \quad L = [v_0, \dots, v_{n-1}] &&\text{[Length of original cycle]} \\
&L' &:= [v_1, v_2, \dots, v_{n-1}, v_0]  &&\text{[Right shift by k positions]} \\
&L'_k &:= case \begin{cases}
  L_{(k + 1)} & k < n - 1 \\
  L_0 & k = n - 1 \\
\end{cases} &&\text{[Element definition after right shift]} \\
&|L'| &= n &&\text{[Length of shifted cycle]} \\
&S &:= \sum_{j=0}^{n-1} L_j &&\text{[Original cycle sum]} \\
&&= v_0 + v_1 + \dots + v_{n-1} &&\text{[Original elements]} \\
&S' &:= \sum_{j=0}^{n-1} L'_j \\
&&= v_1 + v_2 + \dots + v_{n-1} + v_0 &&\text{[Shifted elements]} \\
&&= v_0 + v_1 + \dots + v_{n-1}  &&\text{[Rearrangement of sum]} \\
&&= S &&\text{[Sum remains unchanged]} \\
\end{aligned}
```

We also note that the elements of $L$ and $L'$ are related by by modulo as follows:

```math
\begin{aligned}
\forall \ i \in \mathbb{N}_0 , \\
L'{(i \text{ mod } n)} &= L_{((i + 1) \text{ mod } n)} \quad &\text{[Right Shift Definition]} \\
L{(i \text{ mod } n)} &= L'_{((i - 1 + n) \text{ mod } n)} \quad &\text{[Inverse Right Shift Definition]} \\
\end{aligned}
```
Since:

```math
\begin{aligned}
&S' &= S \quad &\text{[Cycle Sum Invariance]} \\
&r  &:= i \text{ mod } n \\
&L'_r &= \begin{cases}
  L_{(r + 1)} & r < n - 1 \\
  L_0 & r = n - 1 \\
\end{cases} \quad &\text{[Right Shift Definition]} \\
\end{aligned}
```
```math
\begin{aligned}
r < n - 1 &\implies \quad (i + 1) \text{ mod } n = ((i \text{ mod } n) + (1 \text{ mod } n)) \text{ mod } n \quad &\text{[By Modulo Property]} \\
          &\implies \quad (i + 1) \text{ mod } n = r + 1 \quad &\text{[Since } 1 < n \text{]} \\
          &\implies \quad L'_r = L_{(r + 1)} \quad &\text{[Right Shift Definition]} \\
          &\implies \quad L'_(i \text{ mod } n) = L_{((i + 1) \text{ mod } n)}  \quad &\text{[By Modulo Property]} \\
r = n - 1 &\implies \quad (i + 1) \text{ mod } n = 0 \quad &\text{[By Modulo Property]} \\
          &\implies \quad L'_r = L_0  \quad &\text{[Right Shift Definition]} \\
          &\implies \quad L'_(i \text{ mod } n) = L_{((i + 1) \text{ mod } n)}  \quad &\text{[By Modulo Property]} \\
\end{aligned}
```
```math
\begin{aligned}
\therefore \\
\forall \ i &\in \mathbb{N}_0 , \\
L'_{(i \text{ mod } n)} &= L_{((i + 1) \text{ mod } n)} \quad \blacksquare \quad &\text{[Q.E.D.]} \\
\end{aligned}
```

Let the shifted initial value be defined as:

```math
\begin{aligned} 
init' &:= init + L_0 \\
\end{aligned}
```

Then the CycleIntegral of $L'$ with initial value $init'$ reproduces exactly the CycleIntegral of $L$ with initial value $init$.

```math
\begin{aligned}
\text{CycleIntegral}(L, init)_i &= \text{CycleIntegral}(L', init')_{i-1}  \quad \forall i \in \mathbb{N}_0 \quad &\text{[Shifted Value Reproduction]} \\
\end{aligned}
```

#### Proof

#####  Base Case
```math
\begin{aligned}
&A &:= \text{CycleIntegral}(L, init)_i &\text{[By Definition]} \\
&B &:= \text{CycleIntegral}(L', init')_{i}  &\text{[By Definition]} \\
&A_0 &= init + L_0 &\text{[By Definition]} \\
&A_1 &= init + L_0 + L_1 &\text{[By Definition]} \\ 
&B_0 &= init' + L'_0 &\text{[By Definition]} \\
    &&= (init + L_0) + L'_0 &\text{[Since } init' = init + L_0 \text{]} \\
    &&= init + L_0 + L_1 &\text{[By Right Shift Definition]} \\
    &&= A_1 &\text{[Base Case Equality]} \\
\end{aligned}
```
```math
\begin{aligned}
\therefore \\
A_1 &= B_0 \quad &\text{[Q.E.D.]} \\
\end{aligned}
```

##### Induction Step

```math
\begin{aligned}
&B_{i-1} &= A_i &\text{[Induction Hypothesis]} \\
&\implies \\
&A_{i+1} &= A_i + L_{((i + 1) \text{ mod } n)} &\text{[By Definition]} \\
&B_i &= B_{i-1} + L'_{(i \text{ mod } n)} &\text{[By Definition]} \\
&&= A_i + L_{((i + 1) \text{ mod } n)} &\text{[By Induction Hypothesis]} \\
&&= A_{i+1} &\text{[By Definition of } A_{i+1} \text{]} \\
\end{aligned}
```
```math
\begin{aligned}
\therefore \\
\end{aligned}
```

```math
\begin{aligned}
\forall \ i &\in \mathbb{N}_0 , \\
A_{i+1} &= B_{i}
\end{aligned}
```
```math
\begin{aligned}
\text{CycleIntegral}(L, init)_{i+1} &= \text{CycleIntegral}(L', init')_{i} \quad \blacksquare &&\text{[Q.E.D.]} \\
\end{aligned}
```

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


