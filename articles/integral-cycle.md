# Formal Verification of Cycle Integral Properties from First Principles

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
This article uses that as a foundation to define Integral of Cycles
using three equivalent variants: a <b>Classic</b> recursive definition, a <b>Recursive</b> cycle-based definition,
and a <b>Modulo</b> closed-form definition.
For each variant, we formally verify the sum property (integral equals cumulative cycle sum)
and the step property (difference between consecutive values equals the corresponding cycle element)
using the Stainless verification system.
We also prove equivalence of all three definitions.
All properties are expressed and proved within a minimal framework using only elementary arithmetic,
recursion, and pure Scala code.
This work bridges mathematical foundations and executable verification, 
offering a self-contained, verifiable approach for reasoning about infinite periodic accumulations.
 </p>
</div>

## Properties Index

| # | Property | Statement | Verifier |
|---|----------|-----------|----------|
| 3.1 | Classic Sum (small positions) | `ClassicCI(L, init)_i = sum_{j=0}^i L_j + init` | [ClassicCycleIntegralProperties::assertCycleIntegralEqualsSumSmallPositions](#A1) |
| 3.1 | Classic Step | `ClassicCI(L, init)_{i+1} - ClassicCI(L, init)_i = Cycle(L)_{i+1}` | [ClassicCycleIntegralProperties::assertDiffEqualsCycleValue](#A2) |
| 3.2 | Recursive Sum (small positions) | `CI(L, init)_i = sum_{j=0}^i L_j + init` | [CycleIntegralProperties::assertCycleIntegralEqualsSumSmallPositions](#A1) |
| 3.2 | Recursive Step | `CI(L, init)_{i+1} - CI(L, init)_i = Cycle(L)_{i+1}` | [CycleIntegralProperties::assertDiffEqualsCycleValue](#A2) |
| 3.3 | Mod First Values | `ModCI(L, init)_i = I_i + init` | [ModCycleIntegralProperties::assertFirstValuesMatchIntegral](#A3) |
| 3.3 | Mod Step | `ModCI(L, init)_{i+1} - ModCI(L, init)_i = L_{((i+1) mod n)}` | [ModCycleIntegralProperties::assertSimplifiedDiffValuesMatchCycle](#A4) |
| 3.4 | Equivalence | `ModCI(L, init)_i = CI(L, init)_i` | [ModCycleIntegralProperties::assertCycleIntegralMatchModCycleDef](#A5) |

## 1. Introduction

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
[Using Formal Verification to Prove Properties of Lists Recursively Defined](https://github.com/thiagomata/prime-numbers/blob/master/articles/list.md) [[1]](#ref1),
[Formal Verification of Discrete Integration Properties from First Principles](https://github.com/thiagomata/prime-numbers/blob/master/articles/integral.md) [[2]](#ref2),
and [Formal Verification of Cyclic Lists](https://github.com/thiagomata/prime-numbers/blob/master/articles/cycle.md) [[3]](#ref3).
We also reuse some modulo properties previously defined and verified in the article
[Proving Properties of Division and Modulo using Formal Verification](https://github.com/thiagomata/prime-numbers/blob/master/articles/modulo.md) [[4]](#ref4).

These articles also defined and verified their properties using the same zero-prior-knowledge methodology,
and are treated here as foundational primitives.

### Dependency Map

The following diagram shows how verified lemmas from the companion articles support the properties in this article:

```
[Modulo Properties]  [List Properties]  [Cycle Properties]
         |                  |                   |
         v                  v                   v
    [Integral Properties]  -->  [Cycle Integral Properties]
                                       |
                          +-----------+-----------+
                          |           |           |
                          v           v           v
                     Classic      Recursive     Modulo
                    CycleIntegral CycleIntegral CycleIntegral
```

## 3. Cycle Integral Definitions

```math
\forall \ i \in ℕ_0, \ init \in ℕ_0, L \in 𝕃, n = |L| \\
\text{CycleIntegral}(L, init) := [w_0, w_1, w_2, \ldots]
```

```math
\begin{aligned}
0 \leq i < n \implies w_i = \sum_{j=0}^i L_j + init \quad &\text{[Sum Property]} \\
i > 0 \implies  \ w_i - w_{i-1} = L_{(i \text{ mod } n)}
\quad &\text{[Step Property]} \\
\end{aligned}
```

### 3.1 Classic Cycle Integral

```math
\begin{aligned}
\text{Cycle}(L)_i &= L_{(i \text{ mod } n)} \\
\text{ClassicCycleIntegral}(L, init)_k &= \sum_{i=0}^k \text{Cycle}(L)_i + init
\end{aligned}
```

As defined at [ClassicCycleIntegral.scala](../src/main/scala/v1/chapter4/cycle/integral/classic/ClassicCycleIntegral.scala):

```scala
case class ClassicCycleIntegral(
  initialValue: BigInt,
  cycle: MemCycle
) {
  def apply(position: BigInt): BigInt = {
    require(position >= 0)
    decreases(position)
    if (position == 0) {
      cycle(0) + initialValue
    } else {
      cycle(position) + apply(position - 1)
    }
  }
  def size: BigInt = cycle.size
  def sum: BigInt = cycle.sum()
}
```

#### Sum Property

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
  ../src/main/scala/v1/chapter4/cycle/integral/classic/properties/ClassicCycleIntegralProperties.scala
). The full Scala verification code is in Appendix A.1.

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
  ../src/main/scala/v1/chapter4/cycle/integral/classic/properties/ClassicCycleIntegralProperties.scala
). The full Scala verification code is in Appendix A.2.

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

**Recursive Cycle Equivalence**: Recursive Cycle is equivalent to Mod Cycle, as proven in the article [Formal Verification of Cyclic Lists](https://github.com/thiagomata/prime-numbers/blob/master/articles/cycle.md) [[3]](#ref3).

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

This property is verified in the [
  CycleIntegralProperties::assertCycleIntegralEqualsSumSmallPositions
](
  ../src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralProperties.scala
). The full Scala verification code is in Appendix A.1 (same property structure as the Classic variant).

**Step Property**:

```math
\begin{aligned}
w_i - w_{i-1} &= v_i + w_{i-1} - w_{i-1} \quad &\text{[By Definition]} \\
&= v_i \quad &\text{[Simplification]} \\
&= L_{(i \text{ mod } n)} \quad &\text{[Substitution]} \\
\end{aligned}
```

This property is verified in the [
  CycleIntegralProperties::assertDiffEqualsCycleValue
](
  ../src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralProperties.scala
). The full Scala verification code is in Appendix A.2 (same property structure as the Classic variant).

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
i < n \implies w_i = \sum_{j=0}^i L_j + init \quad \text{[Claim to Prove]}
```

```math
\begin{aligned}
i < n \implies  \\
i \text{ div } n 
      \quad &= 0 \quad 
      &\text{[By Div of Small Values Property]} \\
w_i &= (i \text{ div } n)\cdot S + I_{(i \text{ mod } n)} + init \quad 
      &\text{[Definition]} \\
&= 0 \cdot S + I_i + init \quad &\text{[Substitution]} \\
&= \sum_{j=0}^i L_j + init \quad &\text{[By definition of } I_i]
\end{aligned}
```

```math
\therefore \
\forall \ i < n,\quad w_i = \sum_{j=0}^i L_j + init \quad \text{[Q.E.D.]}
```

This property is verified in the [
  ModCycleIntegralProperties::assertFirstValuesMatchIntegral
](
  ../src/main/scala/v1/chapter4/cycle/integral/mod/ModCycleIntegralProperties.scala
). The full Scala verification code is in Appendix A.3.

#### Step Property

```math
w_i - w_{i-1} = L_{\, i \text{ mod } n}, \quad i>0,\, n>0
\quad \text{[Claim to Prove]}
```

**Case $i \text{ mod } n > 0$:**

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

**Case $i \text{ mod } n = 0$:**

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

This property is verified in the [
  ModCycleIntegralProperties::assertSimplifiedDiffValuesMatchCycle
](
  ../src/main/scala/v1/chapter4/cycle/integral/mod/ModCycleIntegralProperties.scala
). The full Scala verification code is in Appendix A.4.

### 3.4 Equivalence of Definitions

Since all definitions of Cycle Integral satisfy the same sum and step properties, they are equivalent. The Cycle Integral can be defined using any of the three approaches: Classic, Recursive, or Modulo.

```math
\begin{aligned}
\text{CycleIntegral}(L, init) &= \text{ClassicCycleIntegral}(L, init) \\
&= \text{RecCycleIntegral}(L, init) \\
&= \text{ModCycleIntegral}(L, init) \\
&= [w_0, w_1, w_2, \ldots] \mid w_i =& \sum_{j=0}^i L_{(j \text{ mod } n)} + init \ \blacksquare
\end{aligned}
```

This property is verified in the [
  ModCycleIntegralProperties::assertCycleIntegralMatchModCycleDef
](
  ../src/main/scala/v1/chapter4/cycle/integral/mod/ModCycleIntegralProperties.scala
). The full Scala verification code is in Appendix A.5.

## 4. Core Verified Properties

### 4.1 Next Position

For any positive position, the cycle integral at that position equals the previous value plus the current cycle element.

```math
\forall \ i > 0: \ CI(L, init)_i = CI(L, init)_{i-1} + Cycle(L)_i
```

This follows directly from the recursive definitions of both the Classic and Recursive Cycle Integral variants.

This property is verified in the [
  CycleIntegralProperties::assertNextPosition
](
  ../src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralProperties.scala
) and the equivalent lemma in ClassicCycleIntegralProperties.

### 4.2 Same Difference After Full Cycle

The difference between consecutive values is invariant under adding a full cycle size to both positions.

```math
\forall \ i \geq 0: \ CI(L, init)_{i+1} - CI(L, init)_i = CI(L, init)_{i+size+1} - CI(L, init)_{i+size}
```

This property is verified in the [
  CycleIntegralProperties::assertSameDiffAfterCycle
](
  ../src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralProperties.scala
). The full Scala verification code is in Appendix A.6.

### 4.3 Sum of Mod Values as List

The cycle integral at any position equals the sum of a constructed list containing the initial value and all cycle values up to that position (using modular indexing for positions beyond one cycle).

```math
\forall \ i \geq 0: \ CI(L, init)_i = \text{sum}([init] + [Cycle(L)_0, Cycle(L)_1, \dots, Cycle(L)_i])
```

This property is verified in the [
  CycleIntegralProperties::assertSumModValueAsListEqualsCycleIntegralLoop
](
  ../src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralProperties.scala
). The full Scala verification code is in Appendix A.7.

## 5. Extended Properties [Draft]

The following properties have mathematical proofs but do **not** yet have corresponding Stainless-verified Scala code. They are marked as drafts and represent candidates for future formal verification.

### 5.1 Modulo Invariance Property [Draft]

Let $v \in \mathbb{N}$ with $v > 0$, such that the total cycle sum is a multiple of $v$. Then the remainder of any Cycle Integral value depends only on the corresponding partial sum within the first cycle.

```math
\begin{aligned}
L &= [v_0, v_1, \dots, v_{n-1}] \in \mathbb{N}_0^n, \quad |L| > 0 \\
n &:= |L| \\
S &:= \sum_{j=0}^{n-1} v_j \\
I_k &:= \sum_{j=0}^{k} v_j \quad (0 \le k < n) \\
\end{aligned}
```

```math
\begin{aligned}
\text{CycleIntegral}(L, init)_i := (i \,\text{div}\, n)\cdot S + I_{(i \text{ mod } n)} + init
\end{aligned}
```

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
  \ (I_{(i \text{ mod } n)} + init) \text{ mod } v \neq 0 &\implies CycleIntegral(L, init)_i \text{ mod } v \neq 0 \quad &&\text{[Modulo matches Integral]} \\
\end{aligned}
```

**Status**: Mathematically proven. Stainless verification pending.

### 5.2 Invariance by x-fold Concatenation [Draft]

Let $L^{(x)}$ be the $x$-fold concatenation of a list $L \in 𝕃$. Then the CycleIntegral of $L^{(x)}$ with initial value $init$ reproduces exactly the CycleIntegral of $L$ with initial value $init$.

```math
\begin{aligned}
n &= |L|, \quad L = [v_0, \dots, v_{n-1}] 
  &&\text{[Length of original cycle]} \\
L^{(x)} 
&:= \underbrace{L :: \dots :: L}_{x \text{ copies}} 
  &&\text{[Concatenate $x$ copies]} \\
m &:= |L^{(x)}| = x \cdot n 
  &&\text{[Length of new cycle]} \\
T &:= \sum_{j=0}^{n-1} v_j 
  &&\text{[Original cycle sum]} \\
\end{aligned}
```

```math
\begin{aligned}
\text{CycleIntegral}(L^{(x)}, init)_i 
&= (i \,\text{div}\, m)\cdot T^{(x)} + I^{(x)}_{i \bmod m} + init 
  &&\text{[By Definition]} \\
&= (i \,\text{div}\, (x \cdot n))\cdot (x \cdot T) + I^{(x)}_{i \bmod (x \cdot n)} + init 
  &&\text{[Substitution]} \\
&= (i \,\text{div}\, n)\cdot T + I_{i \bmod n} + init 
  &&\text{[Exact simplification]} \\
&= \text{CycleIntegral}(L, init)_i 
  &&\text{[Exact value reproduction]} \\
\end{aligned}
```

```math
\therefore \ \forall \ i \in \mathbb{N}_0: \ \text{CycleIntegral}(L^{(x)}, init)_i = \text{CycleIntegral}(L, init)_i \quad \blacksquare
```

**Status**: Mathematically proven. Stainless verification pending.

### 5.3 Right Index Shift [Draft]

Let $L' \in 𝕃$ be the right shift of $L \in 𝕃$ by one position, and $init' := init + L_0$ be the shifted initial value. Then the CycleIntegral of $L'$ with $init'$ reproduces the CycleIntegral of $L$ with $init$, shifted by one position.

```math
\begin{aligned}
n &= |L|, \quad L = [v_0, \dots, v_{n-1}] \\
L' &:= [v_1, v_2, \dots, v_{n-1}, v_0] \\
S' &= S \quad &\text{[Cycle Sum Invariance]} \\
init' &:= init + L_0 \\
\end{aligned}
```

```math
\begin{aligned}
\text{CycleIntegral}(L, init)_{i+1} &= \text{CycleIntegral}(L', init')_{i} \quad \forall i \in \mathbb{N}_0
\end{aligned}
```

#### Base Case

```math
\begin{aligned}
A &:= \text{CycleIntegral}(L, init)_i \\
B &:= \text{CycleIntegral}(L', init')_{i} \\
A_0 &= init + L_0 \\
A_1 &= init + L_0 + L_1 \\ 
B_0 &= init' + L'_0 = (init + L_0) + L'_0 = init + L_0 + L_1 = A_1 \\
\end{aligned}
```

#### Induction Step

```math
\begin{aligned}
B_{i-1} &= A_i \quad &\text{[Induction Hypothesis]} \\
A_{i+1} &= A_i + L_{((i + 1) \text{ mod } n)} \quad &\text{[By Definition]} \\
B_i &= B_{i-1} + L'_{(i \text{ mod } n)} \quad &\text{[By Definition]} \\
    &= A_i + L_{((i + 1) \text{ mod } n)} \quad &\text{[By Induction Hypothesis]} \\
    &= A_{i+1} \quad &\text{[By Definition]} \\
\end{aligned}
```

```math
\therefore \ \forall \ i \in \mathbb{N}_0: \ \text{CycleIntegral}(L, init)_{i+1} = \text{CycleIntegral}(L', init')_{i} \quad \blacksquare
```

**Status**: Mathematically proven. Stainless verification pending.

### 5.4 Left Index Shift [Draft]

Let $L'' \in 𝕃$ be the left shift of $L \in 𝕃$ by one position ($|L| > 1$), and $init'' := init + L_0 - L_{n-1}$ be the shifted initial value. Then the CycleIntegral of $L''$ with $init''$ reproduces the CycleIntegral of $L$ with $init$, shifted by one position in the opposite direction.

```math
\begin{aligned}
n &= |L|, \quad L = [v_0, \dots, v_{n-1}], \quad n > 1 \\
L'' &:= [v_{n-1}, v_0, v_1, \dots, v_{n-2}] \\
S'' &= S \quad &\text{[Cycle Sum Invariance]} \\
init'' &:= init + L_0 - L_{n-1} \\
\end{aligned}
```

```math
\begin{aligned}
\text{CycleIntegral}(L, init)_i &= \text{CycleIntegral}(L'', init'')_{i+1} \quad \forall i \in \mathbb{N}_0
\end{aligned}
```

#### Base Case

```math
\begin{aligned}
C &:= \text{CycleIntegral}(L'', init'')_{i} \\
C_1 &= init'' + L''_0 = (init + L_0 - L_{n-1}) + L''_0 \\
    &= init + L_0 - L_{n-1} + L_{n-1} = init + L_0 = A_0 \\
\end{aligned}
```

#### Induction Step

```math
\begin{aligned}
C_{i+1} &= A_i \quad &\text{[Induction Hypothesis]} \\
A_{i+1} &= A_i + L_{((i + 1) \text{ mod } n)} \quad &\text{[By Definition]} \\
C_{i+1} &= C_{i} + L''_{(i \text{ mod } n)} \quad &\text{[By Definition]} \\
       &= A_i + L_{((i - 1 + n) \text{ mod } n)} \quad &\text{[By Induction Hypothesis]} \\
       &= A_{i+1} \quad &\text{[By Definition]} \\
\end{aligned}
```

```math
\therefore \ \forall \ i \in \mathbb{N}_0: \ \text{CycleIntegral}(L, init)_{i+1} = \text{CycleIntegral}(L'', init'')_{i} \quad \blacksquare
```

**Status**: Mathematically proven. Stainless verification pending.

## 6. Conclusion

This article extends the previously verified foundations for recursive lists,
discrete integrals, modulo arithmetic, and cycles to define and reason about
Cycle Integrals. Starting from a finite non-empty list, the construction treats
the list as a repeating cycle and describes the accumulated value at any
non-negative index using the cycle sum, modular position, and initial value.

We defined three equivalent variants of Cycle Integral:

1. **ClassicCycleIntegral** — recursive sum over cycle elements (Section 3.1)
2. **RecursiveCycleIntegral** — recursive cycle with cycle-based indexing (Section 3.2)
3. **ModCycleIntegral** — closed-form using division and modulo (Section 3.3)

For each variant, we verified the sum property (integral equals cumulative cycle sum) and the step property (difference between consecutive values equals the corresponding cycle element). We also proved equivalence of all three definitions.

The main established properties are:

```math
\begin{aligned}
&\forall \ L \in 𝕃,\quad \forall \ init \in \mathbb{N}_0,\quad \forall \ i \in \mathbb{N}_0 \\
L &= [v_0, v_1, \dots, v_{n-1}], \quad n = |L|,\quad n > 0 \\
T &= \sum_{j=0}^{n-1} v_j \\
\text{CycleIntegral}(L, init)_i
&= (i \ \text{div}\ n) \cdot T + I_{i \text{ mod } n} + init
\quad &\text{[Modulo Cycle Integral]} \\
\end{aligned}
```

The verified definitions provide a reusable foundation for reasoning about infinite periodic
accumulations using finite list structures and machine-checked Scala code.

## 7. Future Work

Future work may include:
- Formal verification of the extended properties in Section 5 (index shifts, x-fold concatenation, modulo invariance)
- Applications to prime number detection and distribution analysis
- Extensions to multi-dimensional cycles and integrals
- Integration with other mathematical structures like polynomials or matrices

## References

<a name="ref1" id="ref1" href="#ref1">[1]</a> 
Mata, T. H. (2026). *Using Formal Verification to Prove Properties of Lists Recursively Defined*. Unpublished manuscript.  
Available at: [https://github.com/thiagomata/prime-numbers/blob/master/articles/list.md](https://github.com/thiagomata/prime-numbers/blob/master/articles/list.md)

<a name="ref2" id="ref2" href="#ref2">[2]</a>
Mata, T. H. (2026). *Formal Verification of Discrete Integration Properties from First Principles*. Unpublished manuscript.  
Available at: [https://github.com/thiagomata/prime-numbers/blob/master/articles/integral.md](https://github.com/thiagomata/prime-numbers/blob/master/articles/integral.md)

<a name="ref3" id="ref3" href="#ref3">[3]</a>
Mata, T. H. (2026). *Formal Verification of Cyclic Lists*. Unpublished manuscript.  
Available at: [https://github.com/thiagomata/prime-numbers/blob/master/articles/cycle.md](https://github.com/thiagomata/prime-numbers/blob/master/articles/cycle.md)

<a name="ref4" id="ref4" href="#ref4">[4]</a>
Mata, T. H. (2026). *Proving Properties of Division and Modulo using Formal Verification*. Unpublished manuscript.  
Available at: [https://github.com/thiagomata/prime-numbers/blob/master/articles/modulo.md](https://github.com/thiagomata/prime-numbers/blob/master/articles/modulo.md)

## Appendix A: Scala Verification Code

### A.1 Sum Property for Small Positions — assertCycleIntegralEqualsSumSmallPositions

Source: [ClassicCycleIntegralProperties::assertCycleIntegralEqualsSumSmallPositions](../src/main/scala/v1/chapter4/cycle/integral/classic/properties/ClassicCycleIntegralProperties.scala)

The recursive `CycleIntegralProperties` variant at [CycleIntegralProperties::assertCycleIntegralEqualsSumSmallPositions](../src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralProperties.scala) follows the same structure.

```scala
def assertCycleIntegralEqualsSumSmallPositions(
  classicCycleIntegral: ClassicCycleIntegral,
  position: BigInt
): Boolean = {
  require(position < classicCycleIntegral.size)
  require(position > 0)
  require(ListUtils.sum(getFirstValuesAsSlice(
    classicCycleIntegral, position - 1)) == classicCycleIntegral(position - 1))

  assert(assertNextPosition(classicCycleIntegral, position))
  assert(classicCycleIntegral(position) ==
    classicCycleIntegral.cycle(position) + classicCycleIntegral(position - 1))
  assert(MemCycleProperties.smallValueInCycle(
    classicCycleIntegral.cycle, position))
  assert(classicCycleIntegral.cycle(position) ==
    classicCycleIntegral.cycle.values(position))
  assert(ListUtils.sum(getFirstValuesAsSlice(
    classicCycleIntegral, position - 1)) == classicCycleIntegral(position - 1))

  val prev = getFirstValuesAsSlice(classicCycleIntegral, position - 1)
  val prevSum = ListUtils.sum(prev)
  assert(prevSum == classicCycleIntegral(position - 1))

  val currentList = List(classicCycleIntegral.cycle.values(position)) ++ prev
  val currentValue = classicCycleIntegral.cycle(position)
  val currentSum = ListUtils.sum(prev) + currentValue
  assert(ListUtilsProperties.listAddValueTail(prev, currentValue))
  assert(ListUtils.sum(prev) + currentValue == ListUtils.sum(currentList))
  assert(assertNextPosition(
    classicCycleIntegral = classicCycleIntegral, position = position))

  ListUtils.sum(getFirstValuesAsSlice(
    classicCycleIntegral, position)) == classicCycleIntegral(position)
}.holds
```

### A.2 Step Property — assertDiffEqualsCycleValue

Source: [ClassicCycleIntegralProperties::assertDiffEqualsCycleValue](../src/main/scala/v1/chapter4/cycle/integral/classic/properties/ClassicCycleIntegralProperties.scala)

The recursive `CycleIntegralProperties` variant at [CycleIntegralProperties::assertDiffEqualsCycleValue](../src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralProperties.scala) follows the same structure.

```scala
def assertDiffEqualsCycleValue(
  classicCycleIntegral: ClassicCycleIntegral,
  position: BigInt
): Boolean = {
  require(position >= 0)
  assert(classicCycleIntegral(position + 1) ==
    classicCycleIntegral(position) + classicCycleIntegral.cycle(position + 1))
  classicCycleIntegral(position + 1) - classicCycleIntegral(position) ==
    classicCycleIntegral.cycle(position + 1)
}.holds
```

### A.3 Mod First Values Match Integral — assertFirstValuesMatchIntegral

Source: [ModCycleIntegralProperties::assertFirstValuesMatchIntegral](../src/main/scala/v1/chapter4/cycle/integral/mod/ModCycleIntegralProperties.scala)

```scala
def assertFirstValuesMatchIntegral(
  modCycleIntegral: ModCycleIntegral,
  position: BigInt
): Boolean = {
  require(position >= 0)
  require(position < modCycleIntegral.integralValues.size)
  assert(ModSmallDividend.modSmallDividend(
    position, modCycleIntegral.integralValues.size))
  assert(Calc.mod(
    position, modCycleIntegral.integralValues.size) == position)
  assert(Calc.div(
    position, modCycleIntegral.integralValues.size) == 0)

  modCycleIntegral.apply(position) ==
    modCycleIntegral.integralValues(position) + modCycleIntegral.initialValue
}.holds
```

### A.4 Mod Step Diff — assertSimplifiedDiffValuesMatchCycle

Source: [ModCycleIntegralProperties::assertSimplifiedDiffValuesMatchCycle](../src/main/scala/v1/chapter4/cycle/integral/mod/ModCycleIntegralProperties.scala)

```scala
def assertSimplifiedDiffValuesMatchCycle(
  modCycleIntegral: ModCycleIntegral,
  position: BigInt
): Boolean = {
  require(position >= 0)
  assert(modCycleIntegral.integralValues.size ==
    modCycleIntegral.mCycle.size)
  ModOperations.addOne(
    position, modCycleIntegral.integralValues.size)

  if (Calc.mod(position, modCycleIntegral.integralValues.size) ==
      modCycleIntegral.integralValues.size - 1) {
    // ... boundary case: position mod size == size - 1
    // (full proof omitted for brevity — see source file)
  } else {
    // ... non-boundary case
    // (full proof omitted for brevity — see source file)
  }

  modCycleIntegral.apply(position + 1) -
    modCycleIntegral.apply(position) ==
    modCycleIntegral.mCycle.values(
      Calc.mod(position + 1, modCycleIntegral.integralValues.size))
}.holds
```

### A.5 Equivalence of Definitions — assertCycleIntegralMatchModCycleDef

Source: [ModCycleIntegralProperties::assertCycleIntegralMatchModCycleDef](../src/main/scala/v1/chapter4/cycle/integral/mod/ModCycleIntegralProperties.scala)

```scala
def assertCycleIntegralMatchModCycleDef(
  modCycleIntegral: ModCycleIntegral,
  cycleIntegral: CycleIntegral,
  position: BigInt,
): Boolean = {
  require(position >= 0)
  require(modCycleIntegral.mCycle.values.nonEmpty)
  require(cycleIntegral.cycle.values.nonEmpty)
  require(modCycleIntegral.mCycle.values == cycleIntegral.cycle.values)
  require(modCycleIntegral.mCycle.size == cycleIntegral.cycle.size)
  require(modCycleIntegral.initialValue == cycleIntegral.initialValue)
  decreases(position)

  assertModCycleEqualsCycleIntegral(
    modCycleIntegral, cycleIntegral, position)
  val size = modCycleIntegral.mCycle.size

  assert(modCycleIntegral(position) == cycleIntegral(position))
  assert(
    modCycleIntegral(position) ==
      div(position, size) * modCycleIntegral.integralValues.last +
      modCycleIntegral.integralValues(mod(position, size)) +
      modCycleIntegral.initialValue
  )

  cycleIntegral(position) ==
    div(position, size) * modCycleIntegral.integralValues.last +
    modCycleIntegral.integralValues(mod(position, size)) +
    cycleIntegral.initialValue
}.holds
```

### A.6 Same Difference After Full Cycle — assertSameDiffAfterCycle

Source: [CycleIntegralProperties::assertSameDiffAfterCycle](../src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralProperties.scala)

```scala
def assertSameDiffAfterCycle(
  iCycle: CycleIntegral,
  position: BigInt
): Boolean = {
  require(position >= 0)

  val a = position
  val b = position + 1
  val c = a + iCycle.size
  val d = b + iCycle.size

  assertDiffEqualsCycleValue(cycleIntegral = iCycle, position = a)
  assert(iCycle(b) - iCycle(a) == iCycle.cycle(b))

  assertDiffEqualsCycleValue(cycleIntegral = iCycle, position = c)
  assert(iCycle(d) - iCycle(c) == iCycle.cycle(d))

  MemCycleProperties.valueMatchAfterManyLoopsInBoth(
    iCycle.cycle, a, 0, 1)
  MemCycleProperties.valueMatchAfterManyLoopsInBoth(
    iCycle.cycle, b, 0, 1)

  assert(iCycle.cycle(d) == iCycle.cycle(b))
  assert(iCycle.cycle(c) == iCycle.cycle(a))

  iCycle(b) - iCycle(a) == iCycle(d) - iCycle(c)
}.holds
```

### A.7 Sum of Mod Values as List — assertSumModValueAsListEqualsCycleIntegralLoop

Source: [CycleIntegralProperties::assertSumModValueAsListEqualsCycleIntegralLoop](../src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralProperties.scala)

```scala
def assertSumModValueAsListEqualsCycleIntegralLoop(
  iCycle: CycleIntegral,
  position: BigInt
): Boolean = {
  require(position >= 0)
  decreases(position)

  if (position == 0) {
    assert(iCycle(position) ==
      ListUtils.sum(getModValuesAsList(iCycle, position)))
    iCycle(position) == iCycle.cycle(0) + iCycle.initialValue &&
      iCycle(position) ==
        ListUtils.sum(getModValuesAsList(iCycle, position))
  } else {
    if (position > iCycle.size) {
      assertSameDiffAfterCycle(iCycle, position - iCycle.size)
      // ... inductive step details
    }
    assertSumModValueAsListEqualsCycleIntegralLoop(
      iCycle, position - 1)
    assert(iCycle(position - 1) ==
      ListUtils.sum(getModValuesAsList(iCycle, position - 1)))
    assert(ListUtilsProperties.listAddValueTail(
      getModValuesAsList(iCycle, position - 1), iCycle.cycle(position)))
    iCycle(position) == iCycle.cycle(position) + iCycle(position - 1) &&
      iCycle(position) ==
        ListUtils.sum(getModValuesAsList(iCycle, position))
  }
}.holds
```

## Appendix B: Stainless Verification Log Output

The latest `just verify` run verifies all the described properties without errors. The full log output is available at: [logs/verify.log](../logs/verify.log)