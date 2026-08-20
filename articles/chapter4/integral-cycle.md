# Formal Verification of Cycle Integral Properties from First Principles

**Author:** Mata, T. H.
Independent Researcher  
**Email:** [thiago.henrique.mata@gmail.com](mailto:thiago.henrique.mata@gmail.com)  
**GitHub:** [@thiagomata](https://github.com/thiagomata)  
**License:** [CC BY 4.0](../LICENSE)

## Abstract

<div align="justify">
<p style="text-align: justify">
In previous articles, we defined bounded Lists, Integrals of Lists, and unbounded Cycles of Integers
from scratch, relying only on core type constructs and recursion, 
with no prior knowledge of Scala's collections required.
From that, we proved and formally verified some properties related to them.
This article uses that as a foundation to define Integral of Cycles using two
presentations: the canonical recursive `CycleIntegral` definition and a
`ModCycleIntegral` closed-form definition.
For both presentations, we formally verify the sum property (integral equals
cumulative cycle sum) and the step property (difference between consecutive
values equals the corresponding cycle element) using the Stainless verification
system.
We also prove that the recursive and modulo definitions are extensionally
equivalent.
All properties are expressed and proved within a minimal framework using only elementary arithmetic,
recursion, and pure Scala code.
This work bridges mathematical foundations and executable verification, 
offering a self-contained, verifiable approach for reasoning about infinite periodic accumulations.
 </p>
</div>

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

This article verifies:

- Two equivalent definitions: recursive and modulo-based — [§3.1](#31-recursive-cycle-integral)–[3.3](#33-equivalence-of-definitions)
- Core properties: next position, same difference after cycle, sum of mod values — [§4.1](#41-next-position)–[4.3](#43-sum-of-mod-values-as-list)
- Extended properties: modulo periodicity, cycle-period shifts, gap telescoping, rotation, survivor filtering, residue classification — [§5.1](#51-modulo-invariance-property)–[5.9](#59-cycle-residue-classification)

## 2. Preliminaries

We reuse several basic list, cycle and integral operations and their verified properties from the companion articles
[Using Formal Verification to Prove Properties of Lists Recursively Defined](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter3/list.md) [[1]](#ref1),
[Formal Verification of Discrete Integration Properties from First Principles](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter4/integral.md) [[2]](#ref2),
and [Formal Verification of Cyclic Lists](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter4/cycle.md) [[3]](#ref3).
We also reuse some modulo properties previously defined and verified in the article
[Division and Modulo from Recursive Normalization](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter2/modulo.md) [[4]](#ref4).

These articles also defined and verified their properties using the same zero-prior-knowledge methodology,
and are treated here as foundational primitives.

## 3. Cycle Integral Definitions

The cycle integral extends the finite integral to unbounded repeating sequences. Two equivalent definitions are proven.

- Recursive: recurrence on the cycle position — [§3.1](#31-recursive-cycle-integral)
- Modulo: closed-form using `div` and `mod` — [§3.2](#32-modulo-cycle-integral)
- The two definitions are extensionally equivalent — [§3.3](#33-equivalence-of-definitions)

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

### 3.1 Recursive Cycle Integral

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

**Recursive Cycle Equivalence**: Recursive Cycle is equivalent to Mod Cycle, as proven in the article [Formal Verification of Cyclic Lists](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter4/cycle.md) [[3]](#ref3).

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
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralProperties.scala). A key Scala verification excerpt is in Appendix A.1; the complete proof is linked in the source reference.

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
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralProperties.scala). A key Scala verification excerpt is in Appendix A.2; the complete proof is linked in the source reference.

### 3.2 Modulo Cycle Integral

```math
\begin{aligned}
&\text{ModCycle}(L)_i &:= L_{(i \text{ mod } n)} = [w_0, w_1, \dots ] \\
&I_k &:= \sum_{j=0}^{k} L_j \quad (0 \leq k < n) \quad &\text{[Integral of L]} \\
&S &:= I_{n-1} \quad &\text{[One full cycle sum]} \\
&\text{ModCycleIntegral}(L, init)_i &:= (i \text{ div } n)\cdot S + I_{(i \text{ mod } n)} + init
\end{aligned}
```

**Sum Property**:

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
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/mod/ModCycleIntegralProperties.scala). A key Scala verification excerpt is in Appendix A.3; the complete proof is linked in the source reference.

**Step Property**:

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
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/mod/ModCycleIntegralProperties.scala). A key Scala verification excerpt is in Appendix A.4; the complete proof is linked in the source reference.

### 3.3 Equivalence of Definitions

The nontrivial equivalence proved here is between the recursive `CycleIntegral`
definition and the closed-form `ModCycleIntegral` definition.

```math
\begin{aligned}
\text{CycleIntegral}(L, init)
&= \text{ModCycleIntegral}(L, init) \\
&= [w_0, w_1, w_2, \ldots] \mid w_i =& \sum_{j=0}^i L_{(j \text{ mod } n)} + init \ \blacksquare
\end{aligned}
```

This property is verified in the [
ModCycleIntegralProperties::assertCycleIntegralMatchModCycleDef
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/mod/ModCycleIntegralProperties.scala). A key Scala verification excerpt is in Appendix A.5; the complete proof is linked in the source reference.

## 4. Core Verified Properties

The fundamental properties of the cycle integral that hold for every position.

- Next position: $CI_{i+1} = CI_i + Cycle(L)_{i+1}$ — [§4.1](#41-next-position)
- Full cycle shift: adding one cycle period advances by the total sum — [§4.2](#42-same-difference-after-full-cycle)
- Sum of mod values: the modulo definition matches the list sum — [§4.3](#43-sum-of-mod-values-as-list)

### 4.1 Next Position

For any positive position, the cycle integral at that position equals the previous value plus the current cycle element.

```math
\forall \ i > 0: \ CI(L, init)_i = CI(L, init)_{i-1} + Cycle(L)_i
```

This follows directly from the recursive definition of `CycleIntegral`.

This property is verified in the [
CycleIntegralProperties::assertNextPosition
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralProperties.scala).

### 4.2 Same Difference After Full Cycle

The difference between consecutive values is invariant under adding a full cycle size to both positions.

```math
\forall \ i \geq 0: \ CI(L, init)_{i+1} - CI(L, init)_i = CI(L, init)_{i+size+1} - CI(L, init)_{i+size}
```

This property is verified in the [
CycleIntegralProperties::assertSameDiffAfterCycle
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralProperties.scala). A key Scala verification excerpt is in Appendix A.6; the complete proof is linked in the source reference.

### 4.3 Sum of Mod Values as List

The cycle integral at any position equals the sum of a constructed list containing the initial value and all cycle values up to that position (using modular indexing for positions beyond one cycle).

```math
\forall \ i \geq 0: \ CI(L, init)_i = \text{sum}([init] + [Cycle(L)_0, Cycle(L)_1, \dots, Cycle(L)_i])
```

This property is verified in the [
CycleIntegralProperties::assertSumModValueAsListEqualsCycleIntegralLoop
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralProperties.scala). A key Scala verification excerpt is in Appendix A.7; the complete proof is linked in the source reference.

## 5. Extended Properties

Properties 5.3 and 5.4 have mathematical proofs but are not yet Stainless-verified. Property 5.1, property 5.2, properties 5.5-5.9, and [§6](#6-modularity-and-survivor-filtering) are fully verified.

- Modulo invariance: finite-period classification lifts to all positions — [§5.1](#51-modulo-invariance-property)
- x-fold cycle expansion: physical period changes while the represented stream is preserved — [§5.2](#52-x-fold-cycle-expansion)
- Index shifts: right and left — [§5.3](#53-right-index-shift)-[§5.4](#54-left-index-shift)
- Gap arithmetic: telescoping, periodicity, cycle shifts, rotation — [§5.5](#55-gap-telescoping)-[§5.8](#58-gap-rotation-with-head-adjustment)
- Survivor filtering: exactness and structure — [§6](#6-modularity-and-survivor-filtering)
- Residue classification: all-zero, some-zero, none-zero — [§5.9](#59-cycle-residue-classification)

### 5.1 Modulo Invariance Property

Let $v \in \mathbb{N}$ with $v > 0$, such that the total cycle sum is a multiple of $v$. Then the remainder of any Cycle Integral value depends only on the corresponding partial sum within the first cycle. In the implementation, `MemCycle` bookkeeps finite-period zero classifications for stored cycle values, with classification-correctness lemmas verified in `CycleCheckMod` (e.g. `ifInAllModAll`, `ifInSomeModSome`, `ifInNoneModNone`), and `GapProperties::assertModIsPeriodic` proves the corresponding period lift for accumulated Cycle Integral values.

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

**Proof.**

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

Together, the classification lemmas and the unbounded periodicity proof
establish the same finite-period discipline at both levels used by the sieve:
stored cycles carry all/none/some modulo classifications, and accumulated
Cycle Integral residues repeat from one period to all positions whenever the
cycle sum is zero modulo the divisor.

The finite classification data structure is [
MemCycle
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/memory/MemCycle.scala), and its
per-call classification correctness is verified by [
CycleCheckMod
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/memory/properties/CycleCheckMod.scala)
(`ifInAllModAll`, `ifInSomeModSome`, `ifInNoneModNone`). The unbounded periodic
lift is verified in [
GapProperties::assertModIsPeriodic
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/GapProperties.scala). The core Scala verification code for the periodic lift is in Appendix A.11.

### 5.2 x-fold Cycle Expansion

Let $L^{(x)}$ be the $x$-fold concatenation of a list $L \in 𝕃$. This
operation changes the physical backing cycle, but it does not change the
unbounded stream represented by the cycle.

The values that change are the finite storage properties:

```math
\begin{aligned}
|L^{(x)}| &= x \cdot |L|
  \quad &&\text{[Expanded physical period]} \\
\sum L^{(x)} &= x \cdot \sum L
  \quad &&\text{[Expanded physical sum]}
\end{aligned}
```

The period equation is verified in [
RepeatedGapIntegralProperties::assertRepeatedPeriodIsMultiplied
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/RepeatedGapIntegralProperties.scala).

The values that do not change are the semantic stream properties:

```math
\begin{aligned}
L^{(x)}_i &= L_{(i \text{ mod } |L|)}
  \quad &&\text{[Same cycle lookup]} \\
\text{CycleIntegral}(L^{(x)}, init)_i
  &= \text{CycleIntegral}(L, init)_i
  \quad &&\text{[Same integral stream]}
\end{aligned}
```

The cycle lookup equation is verified in [
RepeatedGapIntegralProperties::assertReplicatedCycleValueEqual
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/RepeatedGapIntegralProperties.scala).

So the expansion is not an invariance of the finite cycle object itself. It is
an invariance of the infinite stream that the cycle object represents.

```math
\begin{aligned}
n &= |L|, \quad L = [v_0, \dots, v_{n-1}]
  &&\text{[Length of original cycle]} \\
L^{(x)}
&:= \underbrace{L \mathbin{\texttt{++}} \dots \mathbin{\texttt{++}} L}_{x \text{ copies}}
  &&\text{[Concatenate $x$ copies]} \\
m &:= |L^{(x)}| = x \cdot n
  &&\text{[Length of new cycle]} \\
T &:= \sum_{j=0}^{n-1} v_j
  &&\text{[Original cycle sum]} \\
\end{aligned}
```

The list-level repetition is defined by applying the original list at the original index modulo $n$:

```math
\begin{aligned}
L^{(x)}_i &= L_{(i \text{ mod } n)}
  \quad &&\text{for } 0 \le i < x \cdot n \\
\sum L^{(x)} &= x \cdot \sum L
  \quad &&\text{[Repeated sum]}
\end{aligned}
```

These list-level properties are verified by `RepeatedList` and `ListRepeatProperties`: the repeated list size is $x \cdot n$, the repeated value at index $i$ is the original value at $i \text{ mod } n$, and the repeated sum is $x$ times the original sum. See [
RepeatedList
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/RepeatedList.scala), [
RepeatedListProperties::assertSumMultiplier
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/RepeatedListProperties.scala), and [
ListRepeatProperties::assertRepeatedIndex
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/properties/ListRepeatProperties.scala).

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

This property is verified in the [
CycleIntegralProperties::assertRepeatedValuesIntegralMatches
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralProperties.scala). The full Scala verification code is in Appendix A.8.

### 5.3 Right Index Shift

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

**Base Case**:

```math
\begin{aligned}
A &:= \text{CycleIntegral}(L, init)_i \\
B &:= \text{CycleIntegral}(L', init')_{i} \\
A_0 &= init + L_0 \\
A_1 &= init + L_0 + L_1 \\
B_0 &= init' + L'_0 = (init + L_0) + L'_0 = init + L_0 + L_1 = A_1 \\
\end{aligned}
```

**Induction Step**:

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

The one-period `CycleIntegral` wrapper is verified directly. If the shifted
cycle uses the one-step rotation of the original backing values and the shifted
initial value is advanced by the original first gap, then the shifted integral
at position `i` equals the original integral at position `i + 1` for every
stored-period index with `i + 1 < period`.

This property is verified in [
GapProperties::assertRotateOneCycleIntegralShiftsByOne
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/GapProperties.scala). The full Scala verification code is in Appendix A.9.

The article's mathematical statement above is the all-position version. The
verified lemma proves the stored-period core; packaging the universal
all-position wrapper only needs the already verified full-cycle shift law.

### 5.4 Left Index Shift

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

**Base Case**:

```math
\begin{aligned}
C &:= \text{CycleIntegral}(L'', init'')_{i} \\
C_1 &= init'' + L''_0 = (init + L_0 - L_{n-1}) + L''_0 \\
    &= init + L_0 - L_{n-1} + L_{n-1} = init + L_0 = A_0 \\
\end{aligned}
```

**Induction Step**:

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

### 5.5 Gap Telescoping

Two consecutive gaps telescope to the integral difference across both steps.
By applying the one-step difference lemma twice, the gap values at positions
`k` and `k + 1` add up to the integral span from `k - 1` to `k + 1`. This is
the step-lemma that underlies merging adjacent gap ranges.

```math
\begin{aligned}
\text{ci}(k + 1) - \text{ci}(k - 1) = \text{cycle}(k) + \text{cycle}(k + 1)
\quad \text{for } k \geq 1 \quad &\text{[Q.E.D.]}
\end{aligned}
```

This property is verified in the [
CycleIntegralProperties::assertConsecutiveGapSumEqualsDiff
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralProperties.scala). The full Scala verification code is in Appendix A.10.

### 5.6 Modulo Periodicity

When the total sum of a cycle's values is a multiple of `m`, the residue
`mod(ci(pos), m)` depends only on `pos % ci.period` — it repeats every cycle
period. When `m` is a product of coprime values, the Chinese Remainder
Theorem [[5]](#ref5) implies the periodicity holds simultaneously for each factor: the
cycle period serves as a common period for all residues. This is the
arithmetic backbone of Eratosthenes' sieve [[5]](#ref5).

```math
\begin{aligned}
\text{mod}(\text{sum}(ci),\; m) = 0 \;\implies\;
\text{mod}(\text{ci}(\text{pos}),\; m) = \text{mod}(\text{ci}(\text{pos} \bmod \text{period}(ci)),\; m)
\quad &\text{[Q.E.D.]}
\end{aligned}
```

**Proof.** Decreasing `pos` by one full cycle at a time via
`ci(k + size) == ci(k) + ci.sum`. Since `ci.sum` is `0 mod m`, adding one
full cycle does not change the residue. When `pos < size`, the reduction
terminates.

This property is verified in the [
GapProperties::assertModIsPeriodic
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/GapProperties.scala). The full Scala verification code is in Appendix A.11.

The companion div/mod decomposition `ci(pos) == ci(pos % size) + (pos / size) * ci.sum`
is verified in `GapProperties::assertCIModDivFormula`.

### 5.7 Cycle-Period Shifts

After a full cycle period, the integral advances by the cycle's total sum.
This is the termination bound for scanning: a survivor is always found
within one cycle period because the integral advances by a fixed, positive
amount.

```math
\begin{aligned}
\text{ci}(k + \text{period}(ci)) - \text{ci}(k) &= \text{sum}(ci)
  && \text{[One-period shift]} \\
\text{ci}(\text{pos} + \text{period}(ci)) &= \text{ci}(\text{pos}) + \text{sum}(ci)
  && \text{[Full-cycle shift]} \\
\text{ci}(\text{pos} + \text{period}(ci) \cdot m) &= \text{ci}(\text{pos}) + m \cdot \text{sum}(ci)
  && \text{[Multi-cycle shift, by induction on } m \text{]}
\end{aligned}
```

These properties are verified in [
GapProperties::assertPeriodicShift
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/GapProperties.scala),
`assertFullCycleShift`, and `assertMultiCycleShift`. The core Scala verification code is in Appendix A.12.

### 5.8 Gap Rotation with Head Adjustment

Rotating a gap cycle by one position and adjusting the head shifts the
entire integral by one position.

```math
\begin{aligned}
\text{GapList}(\text{head} + \text{gaps}_0,\; \text{tail}(\text{gaps}) \mathbin{\texttt{++}} (\text{gaps}_0 :: L_e))_i
  = \text{GapList}(\text{head},\; \text{gaps})_{i + 1}
  \quad &\text{[Q.E.D.]}
\end{aligned}
```

This property is verified in [
GapProperties::assertRotateOneShiftsIntegralByOne
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/GapProperties.scala). It delegates to the verified `ShiftedList.assertShiftedApplyIsOriginalPlusOne`; the full source is linked there rather than repeated inline.

### 5.9 Cycle Residue Classification

For any cycle and modulus `d > 0`, the values of the cycle fall into exactly
one of three residue categories modulo `d`:

```math
\begin{aligned}
\text{all-zero:} &\quad \forall k,\; \text{mod}(\text{cycle}(k), d) = 0
  && \text{[Filter removes everything]} \\
\text{none-zero:} &\quad \forall k,\; \text{mod}(\text{cycle}(k), d) \neq 0
  && \text{[Filter has no effect]} \\
\text{some-zero:} &\quad \exists k_0 : \text{mod}(\text{cycle}(k_0), d) = 0
  \;\land\; \exists k_1 : \text{mod}(\text{cycle}(k_1), d) \neq 0
  && \text{[Filter removes specific positions]}
\end{aligned}
```

These three states are detected by `MemCycle.checkMod(d)` and stored in lists
(`modIsZeroForAllValues`, `modIsZeroForNoneValues`, `modIsZeroForSomeValues`).
The evaluation is idempotent — the cycle's values list never changes, only the
classification metadata is updated. Ten lemmas in `CycleCheckMod.scala` prove
the classification is correct, mutually exclusive, and exhaustive.

These properties are verified in the [
CycleCheckMod
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/memory/properties/CycleCheckMod.scala) module.

## 6. Modularity and Survivor Filtering

The survivor scan `survivorValues(ci, filterValue, start, count)` collects
every value in the half-open range `[start, start + count)` whose remainder
modulo `filterValue` is nonzero — the cycle-integral equivalent of an
Eratosthenes sieve step [[5]](#ref5): values divisible by a modulus are crossed out,
and only the non-multiples survive. Ten verified lemmas in
`GapProperties.scala` characterize this operation.

### 6.1 Survivor Exactness

The survivor scan is exact: it retains exactly the non-multiples and excludes
exactly the multiples. Soundness says every retained value satisfies `mod != 0`;
completeness says every scanned value with `mod != 0` appears in the result.

```math
\begin{aligned}
\text{value} \in \text{survivorValues}(\text{ci}, \text{f}, \text{start}, \text{count}) &\Rightarrow
  \text{mod}(\text{value}, \text{f}) \neq 0
  && \text{[Soundness]} \\
\text{start} \leq \text{pos} < \text{start} + \text{count}
  \;\land\; \text{mod}(\text{ci}(\text{pos}), \text{f}) \neq 0 &\Rightarrow
  \text{ci}(\text{pos}) \in \text{survivorValues}(\ldots)
  && \text{[Completeness]}
\end{aligned}
```

Together these form the exactness statement: the survivor list is precisely the
sub-sequence of scanned values that are coprime to the filter.

These properties are verified in [
GapProperties::assertSurvivorValuesContainsOnlyNonMultiples
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/GapProperties.scala) and [`assertSurvivorValuesContainsNonMultipleAtPosition`](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/GapProperties.scala). The exclusion corollary (`assertSurvivorValuesExcludesMultipleAtPosition`)
and the type-level non-emptiness guarantee (`assertSurvivorsNonEmpty`) follow
directly.

### 6.2 Survivor Structure

When the scan prefix `[start, pos)` consists entirely of multiples, the first
survivor is `ci(pos)`. This lemma, together with its structural-split companion,
enables peeling one survivor at a time without rediscovering why the
prefix was filtered out.

```math
\begin{aligned}
\text{allMultiplesInRange}(\text{ci}, \text{f}, \text{start}, \text{pos})
  \;\land\; \text{mod}(\text{ci}(\text{pos}), \text{f}) \neq 0
  &\Rightarrow
  \text{survivorValues}(\ldots).\text{head} = \text{ci}(\text{pos})
  && \text{[First survivor]} \\
\text{survivorValues}(\text{ci}, \text{f}, \text{start}, \text{count})
  &= \text{ci}(\text{pos}) \,::\,
     \text{survivorValues}(\ldots, \text{pos} + 1, \text{remaining})
  && \text{[Structural split]}
\end{aligned}
```

The first/last bracket lemma (`assertFirstSurvivorIsHead` and
`assertLastSurvivorIsLastScanned`)
guarantees `survivors.last - survivors.head == ci(last) - ci(first)`, and
`assertFilteredSumEqualsOriginalSum` proves that filtering one full period
preserves the total gap sum — `survivors.last - survivors.head == ci.sum`.

The structural theorem `assertMergedGapPositive` proves that the gap between
two consecutive survivors (after filtering out multiples) is strictly positive
— this is the gap-level guarantee that underpins the `GapCycle` type invariant
(`allGreaterThan(gaps, 0)`).

All survivor-structure properties are verified in [
GapProperties::assertFirstSurvivorIsHead
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/GapProperties.scala), [`assertFilteredSumEqualsOriginalSum`](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/GapProperties.scala), and the eight companion lemmas in the same module.

## 7. Conclusion

This article extends the previously verified foundations for recursive lists,
discrete integrals, modulo arithmetic, and cycles to define and reason about
Cycle Integrals. Starting from a finite non-empty list, the construction treats
the list as a repeating cycle and describes the accumulated value at any
non-negative index using the cycle sum, modular position, and initial value.

We defined two equivalent presentations of Cycle Integral: **CycleIntegral**,
a recursive accumulation over a memory-backed cycle ([§3.1](#31-recursive-cycle-integral)),
and **ModCycleIntegral**, a closed-form definition using division and modulo
([§3.2](#32-modulo-cycle-integral)).

For both presentations, we verified the sum property (integral equals cumulative cycle sum) and the step property (difference between consecutive values equals the corresponding cycle element). We also proved equivalence of the recursive and modulo definitions.

Beyond these core definitions, the article verifies several reusable
cycle-integral laws: repeating a backing cycle preserves the represented
integral stream; adjacent gaps telescope into integral differences; residues
are periodic when the cycle sum is zero modulo the chosen modulus; full-cycle
shifts advance the integral by the cycle sum; rotating a gap cycle with the
corresponding head adjustment shifts the represented integral by one position;
survivor scans retain exactly the non-multiples needed for filtering; and
cycle residue classification is correct, exclusive, and exhaustive. The
open extension points are the index-shift laws in Sections 5.3 and 5.4.

The main established properties are:

```math
\begin{aligned}
&\forall \ L \in 𝕃,\quad \forall \ init \in \mathbb{N}_0,\quad \forall \ i \in \mathbb{N}_0 \\
L &= [v_0, v_1, \dots, v_{n-1}], \quad n = |L|,\quad n > 0 \\
T &= \sum_{j=0}^{n-1} v_j \\
\end{aligned}
```

```math
\begin{aligned}
\text{CycleIntegral}(L, init)_i
&= \left(i \ \text{div}\ n\right) \cdot T
 + \text{CycleIntegral}(L, init)_{i \text{mod} n}
\quad &\text{[Modulo Cycle Integral]} \\
\text{CycleIntegral}(L, init)_i
&= \text{ModCycleIntegral}(L, init)_i
\quad &\text{[Definition Equivalence]} \\
\text{CycleIntegral}(L, init)_{i+1}
&- \text{CycleIntegral}(L, init)_i
= \text{Cycle}(L)_i
\quad &\text{[Step Property]} \\
\end{aligned}
```

```math
\begin{aligned}
\text{CycleIntegral}(L^{\langle x\rangle}, init)_i
&= \text{CycleIntegral}(L, init)_i
\quad &\text{[Repeated-Cycle Invariance]} \\
\text{CycleIntegral}(G,h)_{k+1}
&- \text{CycleIntegral}(G,h)_{k-1}
= G_{k-1} + G_k
\quad &\text{[Two-Gap Telescoping]} \\
T \equiv 0 \pmod m
&\implies
\text{CycleIntegral}(L, init)_{i+n}
\equiv \text{CycleIntegral}(L, init)_i \pmod m
\quad &\text{[Modulo Periodicity]} \\
\end{aligned}
```

```math
\begin{aligned}
\text{rotateAt}(G,1)\text{ with head }h+G_0
&\implies
I'_{i}=I_{i+1}
\quad &\text{[Rotation Shift]} \\
\text{survivors}(I,m)
&= \{ I_i \mid I_i \not\equiv 0 \pmod m \}
\quad &\text{[Survivor Exactness]} \\
\text{classify}(I_i,m)
&\in \{\text{zero},\text{nonzero}\}
\quad &\text{[Residue Classification]} \\
\end{aligned}
```

The verified definitions provide a reusable foundation for reasoning about infinite periodic
accumulations using finite list structures and machine-checked Scala code.

## 8. Future Work

The nearest continuation is to close the remaining index-shift properties in
Section 5. Those statements already have mathematical derivations in the
article, but they still sit at the boundary between the verified cycle-integral
library and the stronger shift reasoning needed for later sieve arguments.

After that, the same finite-period machinery can support more specialized
prime-sieve properties: detecting accepted residues, tracking gap evolution
across filters, and relating local survivor windows to complete-cycle
structure. More distant extensions, such as multi-dimensional cycles or
integration over richer algebraic structures, would require new definitions
rather than a direct continuation of the present proof.

## References

<a name="ref1" id="ref1" href="#ref1">[1]</a>
Mata, T. H. (2026). _Using Formal Verification to Prove Properties of Lists Recursively Defined_. Available at: [https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter3/list.md](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter3/list.md)

<a name="ref2" id="ref2" href="#ref2">[2]</a>
Mata, T. H. (2026). _Formal Verification of Discrete Integration Properties from First Principles_. Available at: [https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter4/integral.md](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter4/integral.md)

<a name="ref3" id="ref3" href="#ref3">[3]</a>
Mata, T. H. (2026). _Formal Verification of Cyclic Lists_. Available at: [https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter4/cycle.md](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter4/cycle.md)

<a name="ref4" id="ref4" href="#ref4">[4]</a>
Mata, T. H. (2026). _Division and Modulo from Recursive Normalization_. Available at: [https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter2/modulo.md](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter2/modulo.md)

<a name="ref5" id="ref5" href="#ref5">[5]</a>
Hardy, G. H. & Wright, E. M. (1979). _An Introduction to the Theory of Numbers_ (5th ed.). Oxford University Press. §5.4 (Chinese Remainder Theorem), §15.1 (Sieve of Eratosthenes).

## Appendix A: Scala Verification Code

### A.1 Sum Property for Small Positions — assertCycleIntegralEqualsSumSmallPositions

Source: [CycleIntegralProperties::assertCycleIntegralEqualsSumSmallPositions](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralProperties.scala)

```scala
def assertCycleIntegralEqualsSumSmallPositions(
  cycleIntegral: CycleIntegral,
  position: BigInt
): Boolean = {
  require(position < cycleIntegral.period)
  require(position > 0)
  require(ListUtils.sum(getFirstValuesAsSlice(
    cycleIntegral, position - 1)) == cycleIntegral(position - 1))

  assert(assertNextPosition(cycleIntegral, position))
  assert(cycleIntegral(position) ==
    cycleIntegral.cycle(position) + cycleIntegral(position - 1))
  assert(MemCycleProperties.smallValueInCycle(
    cycleIntegral.cycle, position))
  assert(cycleIntegral.cycle(position) ==
    cycleIntegral.cycle.values(position))
  assert(ListUtils.sum(getFirstValuesAsSlice(
    cycleIntegral, position - 1)) == cycleIntegral(position - 1))

  val prev = getFirstValuesAsSlice(cycleIntegral, position - 1)
  val prevSum = ListUtils.sum(prev)
  assert(prevSum == cycleIntegral(position - 1))

  val currentList = List(cycleIntegral.cycle.values(position)) ++ prev
  val currentValue = cycleIntegral.cycle(position)
  val currentSum = ListUtils.sum(prev) + currentValue
  assert(ListUtilsProperties.listAddValueTail(prev, currentValue))
  assert(ListUtils.sum(prev) + currentValue == ListUtils.sum(currentList))
  assert(assertNextPosition(
    cycleIntegral = cycleIntegral, position = position))

  ListUtils.sum(getFirstValuesAsSlice(
    cycleIntegral, position)) == cycleIntegral(position)
}.holds
```

### A.2 Step Property — assertDiffEqualsCycleValue

Source: [CycleIntegralProperties::assertDiffEqualsCycleValue](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralProperties.scala)

```scala
def assertDiffEqualsCycleValue(
  cycleIntegral: CycleIntegral,
  position: BigInt
): Boolean = {
  require(position >= 0)
  assert(cycleIntegral(position + 1) ==
    cycleIntegral(position) + cycleIntegral.cycle(position + 1))
  cycleIntegral(position + 1) - cycleIntegral(position) ==
    cycleIntegral.cycle(position + 1)
}.holds
```

### A.3 Mod First Values Match Integral — assertFirstValuesMatchIntegral

Source: [ModCycleIntegralProperties::assertFirstValuesMatchIntegral](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/mod/ModCycleIntegralProperties.scala)

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

Source: [ModCycleIntegralProperties::assertSimplifiedDiffValuesMatchCycle](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/mod/ModCycleIntegralProperties.scala)

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

Source: [ModCycleIntegralProperties::assertCycleIntegralMatchModCycleDef](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/mod/ModCycleIntegralProperties.scala)

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

Source: [CycleIntegralProperties::assertSameDiffAfterCycle](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralProperties.scala)

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

Source: [CycleIntegralProperties::assertSumModValueAsListEqualsCycleIntegralLoop](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralProperties.scala)

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

### A.8 x-fold Cycle Expansion — assertRepeatedValuesIntegralMatches

Source: [CycleIntegralProperties::assertRepeatedValuesIntegralMatches](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralProperties.scala)

```scala
def assertRepeatedValuesIntegralMatches(
  cycleIntegral: CycleIntegral,
  repeatedCycleIntegral: CycleIntegral,
  times: BigInt,
  position: BigInt
): Boolean = {
  require(times > BigInt(0))
  require(position >= BigInt(0))
  require(cycleIntegral.cycle.period > BigInt(0))
  require(repeatedCycleIntegral.initialValue == cycleIntegral.initialValue)
  require(repeatedCycleIntegral.cycle.values ==
    ListRepeatProperties.repeat(cycleIntegral.cycle.values, times))
  RepeatedGapIntegralProperties.assertRepeatedValuesIntegralMatches(
    cycleIntegral, repeatedCycleIntegral, times, position
  )
}.holds
```

### A.9 Right Index Shift Core — assertRotateOneCycleIntegralShiftsByOne

Source: [GapProperties::assertRotateOneCycleIntegralShiftsByOne](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/GapProperties.scala)

```scala
def assertRotateOneCycleIntegralShiftsByOne(
  originalCI: CycleIntegral,
  shiftedCI: CycleIntegral,
  i: BigInt
): Boolean = {
  require(i >= 0)
  require(i + 1 < originalCI.period)
  require(shiftedCI.initialValue == originalCI.initialValue + originalCI.cycle(0))
  require(shiftedCI.cycle.values == ListUtils.rotateAt(originalCI.cycle.values, BigInt(1)))
  decreases(i)

  assert(originalCI.cycle.values.nonEmpty)
  assert(RotationProperties.assertRotateSameSize(originalCI.cycle.values, BigInt(1)))
  assert(shiftedCI.period == originalCI.period)
  assert(RotationProperties.assertRotatedAtIndexPlusOne(originalCI.cycle.values, i))
  assert(shiftedCI.cycle(i) == originalCI.cycle(i + 1))

  if (i == BigInt(0)) {
    assert(shiftedCI(i) == shiftedCI.initialValue + shiftedCI.cycle(0))
    assert(originalCI(i + 1) == originalCI(i) + originalCI.cycle(i + 1))
    assert(originalCI(i) == originalCI.initialValue + originalCI.cycle(0))
    assert(shiftedCI(i) == originalCI(i + 1))
  } else {
    assert(assertRotateOneCycleIntegralShiftsByOne(originalCI, shiftedCI, i - BigInt(1)))
    assert(shiftedCI(i - BigInt(1)) == originalCI(i))
    assert(shiftedCI(i) == shiftedCI(i - BigInt(1)) + shiftedCI.cycle(i))
    assert(originalCI(i + 1) == originalCI(i) + originalCI.cycle(i + 1))
    assert(shiftedCI(i) == originalCI(i + 1))
  }

  shiftedCI(i) == originalCI(i + 1)
}.holds
```

### A.10 Gap Telescoping — assertConsecutiveGapSumEqualsDiff

Source: [CycleIntegralProperties::assertConsecutiveGapSumEqualsDiff](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralProperties.scala)

```scala
def assertConsecutiveGapSumEqualsDiff(
  ci: CycleIntegral,
  k: BigInt
): Boolean = {
  require(k >= BigInt(1))
  require(ci.cycle.period > k + BigInt(1))
  require(ci.cycle.values.nonEmpty)

  assert(assertDiffEqualsCycleValue(ci, k - BigInt(1)))
  assert(assertDiffEqualsCycleValue(ci, k))

  ci(k + BigInt(1)) - ci(k - BigInt(1)) ==
    ci.cycle(k) + ci.cycle(k + BigInt(1))
}.holds
```

### A.11 Modulo Periodicity — assertModIsPeriodic

Source: [GapProperties::assertModIsPeriodic](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/GapProperties.scala)

```scala
def assertModIsPeriodic(
  ci: CycleIntegral,
  m: BigInt,
  pos: BigInt
): Boolean = {
  require(ci.period > 0)
  require(m > 0)
  require(pos >= 0)
  require(Calc.mod(ci.sum, m) == BigInt(0))
  require(ci(ci.period) - ci(BigInt(0)) == ci.sum)
  decreases(pos)

  val size = ci.period
  val r = Calc.mod(pos, size)

  if (pos < size) {
    assert(ModSmallDividend.modSmallDividend(pos, size))
    assert(r == pos)
    assert(Calc.mod(ci(pos), m) == Calc.mod(ci(r), m))
  } else {
    val previous = pos - size
    val previousR = Calc.mod(previous, size)

    assert(previous >= BigInt(0))
    assert(previous < pos)
    assert(previous + size == pos)
    assert(AdditionAndMultiplication.APlusBSameModPlusDiv(previous, size))
    assert(Calc.mod(previous + size, size) == Calc.mod(previous, size))
    assert(r == previousR)

    assert(assertModIsPeriodic(ci, m, previous))
    assert(Calc.mod(ci(previous), m) == Calc.mod(ci(previousR), m))

    assert(CycleIntegralFilterProperties.assertCIShiftEqualsSum(ci, previous))
    assert(ci(previous + size) - ci(previous) == ci.sum)
    assert(ci(pos) - ci(previous) == ci.sum)
    assert(ci(pos) == ci(previous) + ci.sum)

    assert(assertAddZeroModValuePreservesMod(ci(previous), ci.sum, m))
    assert(Calc.mod(ci(previous) + ci.sum, m) == Calc.mod(ci(previous), m))
    assert(Calc.mod(ci(pos), m) == Calc.mod(ci(previous), m))
    assert(Calc.mod(ci(pos), m) == Calc.mod(ci(previousR), m))
    assert(Calc.mod(ci(pos), m) == Calc.mod(ci(r), m))
  }

  Calc.mod(ci(pos), m) == Calc.mod(ci(r), m)
}.holds
```

### A.12 Cycle-Period Shifts — assertPeriodicShift, assertFullCycleShift, assertMultiCycleShift

Source: [GapProperties cycle-period shift lemmas](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/GapProperties.scala)

```scala
def assertPeriodicShift(
  ci: CycleIntegral,
  k: BigInt
): Boolean = {
  require(ci.period > 0)
  require(k >= 0)
  require(ci(ci.period) - ci(BigInt(0)) == ci.sum)
  CycleIntegralFilterProperties.assertCIShiftEqualsSum(ci, k)
}.holds

def assertFullCycleShift(
  ci: CycleIntegral,
  pos: BigInt
): Boolean = {
  require(ci.period > 0)
  require(pos >= 0)
  require(ci(ci.period) - ci(BigInt(0)) == ci.sum)
  CycleIntegralFilterProperties.assertCIShiftEqualsSum(ci, pos)
}.holds

def assertMultiCycleShift(
  ci: CycleIntegral,
  pos: BigInt,
  m: BigInt
): Boolean = {
  require(ci.period > 0)
  require(pos >= 0)
  require(m >= 0)
  require(ci(ci.period) - ci(BigInt(0)) == ci.sum)
  decreases(m)

  val period = ci.period
  val totalGaps = ci.sum

  if (m == BigInt(0)) {
    ci(pos) == ci(pos) + totalGaps * BigInt(0)
  } else {
    assert(assertFullCycleShift(ci, pos + period * (m - BigInt(1))))
    assert(ci(pos + period * (m - BigInt(1)) + period) ==
      ci(pos + period * (m - BigInt(1))) + totalGaps)

    assert(assertMultiCycleShift(ci, pos, m - BigInt(1)))
    assert(ci(pos + period * (m - BigInt(1))) ==
      ci(pos) + totalGaps * (m - BigInt(1)))

    ci(pos + period * m) == ci(pos) + totalGaps * m
  }
}.holds
```

## Appendix B: Stainless Verification Log Output

The latest `just verify` run verifies all the described properties without errors. The full log output is available at: [logs/verify.log](https://github.com/thiagomata/prime-numbers/blob/master/articles/logs/verify.log)
