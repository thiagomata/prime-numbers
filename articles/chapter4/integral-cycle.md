# Formal Verification of Cycle Integral Properties from First Principles

**Author:** Thiago Henrique Ramos da Mata
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
- Core properties: next position, same difference after cycle, sum of mod values, strictly increasing, positivity — [§4.1](#41-next-position)–[4.5](#45-cycle-integral-positivity)
- Persistent and periodic properties: how a fixed cycle integral's residues behave forever, and how it advances across full periods — [§5.1](#51-cycle-period-shifts)–[5.6](#56-cycle-residue-classification)
- Deriving new cycle integrals: expansion, index shifts, rotation, survivor filtering, and merge-based reconstruction — [§6.1](#61-x-fold-cycle-expansion)–[6.10](#610-filtered-result-has-no-multiples)

### Related work

Lean's Mathlib provides a general formal theory of periodic functions. It proves
that a periodic function remains periodic under integer multiples of a period,
and that a finite sum of periodic functions is periodic [[6]](#ref6). Mathlib
also represents a finite cycle as a list modulo cyclic rotation [[7]](#ref7).
These results give formal context for the finite period and shift structure
used by the present construction.

This article studies a different object: the cumulative integral of a concrete
periodic integer list. Its central verified results are the equivalence of a
recursive integral and a quotient–remainder closed form, together with the
resulting step, full-period, residue, and reconstruction properties. The
existing periodicity and finite-cycle developments therefore enrich the
setting without standing in for this two-presentation cycle-integral proof.

## 2. Preliminaries

We reuse several basic list, cycle and integral operations and their verified properties from the companion articles
[Using Formal Verification to Prove Properties of Lists Recursively Defined](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter3/list.md) [[1]](#ref1),
[Formal Verification of Discrete Integration Properties from First Principles](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter4/integral.md) [[2]](#ref2),
and [Formal Verification of Cyclic Lists](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter4/cycle.md) [[3]](#ref3).
We also reuse some modulo properties previously defined and verified in the article
[Division and Modulo from Recursive Normalization](http://ai.viXra.org/abs/2609.0009) [[4]](#ref4).

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
- Strictly increasing: positive base values force a strictly growing integral — [§4.4](#44-cycle-integral-strictly-increasing)
- Positivity: a non-negative start and positive base values keep the integral positive everywhere — [§4.5](#45-cycle-integral-positivity)

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

### 4.4 Cycle Integral Strictly Increasing

When the initial value is non-negative and every base-list value is
positive, the cycle integral is strictly increasing: a later position
always produces a larger value.

```math
\begin{aligned}
init \geq 0 \;\land\; (\forall x \in L,\ x > 0) \;\land\; b > a \implies
\text{CycleIntegral}(L, init)_b > \text{CycleIntegral}(L, init)_a
\end{aligned}
```

**Proof.** Induct on $b-a$. The base case is one positive step; the
inductive step adds one more positive cycle value.

```math
\begin{aligned}
b=a+1 &\implies CI_b-CI_a=\text{Cycle}(L)_b>0 &&\text{[§3.1 and cycle positivity]} \\
       &\implies CI_b>CI_a, \\
CI_{b-1}>CI_a,\quad CI_b-CI_{b-1}=\text{Cycle}(L)_b>0
       &\implies CI_b>CI_{b-1}>CI_a \\
\therefore\ CI_b &> CI_a.
  \quad \blacksquare\ \text{[Q.E.D.]}
\end{aligned}
```

This property is verified in the [
CycleIntegralProperties::assertCycleIntegralIncreasing
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralProperties.scala).

### 4.5 Cycle Integral Positivity

When the initial value is non-negative and every base-list value is
positive, the cycle integral is positive at every position.

```math
\begin{aligned}
init \geq 0 \;\land\; (\forall x \in L,\ x > 0) \implies
\text{CycleIntegral}(L, init)_i > 0
\end{aligned}
```

**Proof.** At the first position, the non-negative initial value and a
positive cycle value give a positive integral. Every later position adds one
more positive cycle value.

```math
\begin{aligned}
CI_0 &= init+\text{Cycle}(L)_0>0, \\
CI_{i-1}>0,\quad CI_i-CI_{i-1}=\text{Cycle}(L)_i>0
  &\implies CI_i>0 \\
\therefore\ CI_i &> 0.
  \quad \blacksquare\ \text{[Q.E.D.]}
\end{aligned}
```

This property is verified in the [
CycleIntegralProperties::assertCycleIntegralPositive
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralProperties.scala).

## 5. Persistent and Periodic Properties

These properties describe a single, fixed cycle integral: how its residues
behave forever, and how it advances across full periods. All six
properties are fully Stainless-verified, except Properties 5.3 and 5.4,
which are direct corollaries of Property 5.2.

- Cycle-period shifts: a full period advances the integral by the cycle sum — [§5.1](#51-cycle-period-shifts)
- General residue periodicity: any residue depends only on the position within one cycle period — [§5.2](#52-general-residue-periodicity)
- Persistent non-zero residue: if no residue in one period is zero, none ever is — [§5.3](#53-persistent-non-zero-residue)
- Persistent zero residue: if every residue in one period is zero, every residue always is — [§5.4](#54-persistent-zero-residue)
- Gap telescoping: two consecutive gaps sum to the integral span across both — [§5.5](#55-gap-telescoping)
- Residue classification: all-zero, some-zero, none-zero — [§5.6](#56-cycle-residue-classification)

### 5.1 Cycle-Period Shifts

After a full cycle period, the integral advances by the cycle's total sum.
This is the termination bound for scanning: a survivor is always found
within one cycle period because the integral advances by a fixed, positive
amount.

Both quantities below belong to the finite backing cycle that $ci$
accumulates over, not to $ci$'s own output stream — which is unbounded
and, by [§4.4](#44-cycle-integral-strictly-increasing), strictly
increasing and never repeats:

```math
\begin{aligned}
n &:= \text{period}(ci)
  &&\text{[Length of the finite backing cycle]} \\
\text{periodSum}(ci) &:= \sum_{j=0}^{n-1} \text{cycle}(j)
  &&\text{[Total of one period's gap values]}
\end{aligned}
```

```math
\begin{aligned}
\text{ci}(\text{pos} + \text{period}(ci)) &= \text{ci}(\text{pos}) + \text{periodSum}(ci)
  && \text{[Full-cycle shift]} \\
\text{ci}(\text{pos} + \text{period}(ci) \cdot m) &= \text{ci}(\text{pos}) + m \cdot \text{periodSum}(ci)
  && \text{[Multi-cycle shift, by induction on } m \text{]}
\end{aligned}
```

**Proof.**

**Step 0 (base identity, $pos = 0$).** Unfolding the recursive definition
of $ci$ across one full period, using the cycle's own periodicity
($\text{cycle}(\text{period}(ci)) = \text{cycle}(0)$, by definition of a
cycle — [§1](#1-introduction)) and reordering the resulting finite sum:

```math
\begin{aligned}
ci(\text{period}(ci)) - ci(0)
&= \text{cycle}(1) + \dots + \text{cycle}(\text{period}(ci) - 1) + \text{cycle}(\text{period}(ci))
  &&\text{[Telescoping the recursive definition]} \\
&= \text{cycle}(1) + \dots + \text{cycle}(\text{period}(ci) - 1) + \text{cycle}(0)
  &&\text{[Cycle periodicity]} \\
&= \text{cycle}(0) + \text{cycle}(1) + \dots + \text{cycle}(\text{period}(ci) - 1)
  &&\text{[Reorder terms]} \\
&= \text{periodSum}(ci)
  &&\text{[By Definition of periodSum(ci)]}
\end{aligned}
```

```math
\therefore \ ci(\text{period}(ci)) = ci(0) + \text{periodSum}(ci) \quad \blacksquare
```

**Full-cycle shift, by induction on $pos$.**

**Base Case** ($pos = 0$): shown in Step 0.

**Induction Step** ($pos > 0$):

```math
\begin{aligned}
ci(\text{pos} - 1 + \text{period}(ci)) &= ci(\text{pos} - 1) + \text{periodSum}(ci)
  &&\text{[Induction Hypothesis]} \\
\text{cycle}(\text{pos} + \text{period}(ci)) &= \text{cycle}(\text{pos})
  &&\text{[Cycle periodicity]} \\
ci(\text{pos} + \text{period}(ci)) &= ci(\text{pos} - 1 + \text{period}(ci)) + \text{cycle}(\text{pos} + \text{period}(ci))
  &&\text{[By Definition]} \\
&= \big(ci(\text{pos} - 1) + \text{periodSum}(ci)\big) + \text{cycle}(\text{pos})
  &&\text{[Substitution]} \\
&= \big(ci(\text{pos} - 1) + \text{cycle}(\text{pos})\big) + \text{periodSum}(ci)
  &&\text{[Regroup]} \\
&= ci(\text{pos}) + \text{periodSum}(ci)
  &&\text{[By Definition]}
\end{aligned}
```

```math
\therefore \ \forall \ \text{pos} \in \mathbb{N}_0,\ ci(\text{pos} + \text{period}(ci)) = ci(\text{pos}) + \text{periodSum}(ci) \quad \blacksquare
```

**Multi-cycle shift, by induction on $m$.**

**Base Case** ($m = 0$):

```math
ci(\text{pos} + \text{period}(ci) \cdot 0) = ci(\text{pos}) = ci(\text{pos}) + 0 \cdot \text{periodSum}(ci)
```

**Induction Step** ($m > 0$):

```math
\begin{aligned}
ci(\text{pos} + \text{period}(ci) \cdot (m - 1)) &= ci(\text{pos}) + (m - 1) \cdot \text{periodSum}(ci)
  &&\text{[Induction Hypothesis]} \\
ci\big((\text{pos} + \text{period}(ci) \cdot (m - 1)) + \text{period}(ci)\big) &= ci(\text{pos} + \text{period}(ci) \cdot (m - 1)) + \text{periodSum}(ci)
  &&\text{[Full-cycle shift]} \\
ci(\text{pos} + \text{period}(ci) \cdot m) &= \big(ci(\text{pos}) + (m - 1) \cdot \text{periodSum}(ci)\big) + \text{periodSum}(ci)
  &&\text{[Substitution]} \\
&= ci(\text{pos}) + m \cdot \text{periodSum}(ci)
  &&\text{[Arithmetic]}
\end{aligned}
```

```math
\therefore \ \forall \ m \in \mathbb{N}_0,\ ci(\text{pos} + \text{period}(ci) \cdot m) = ci(\text{pos}) + m \cdot \text{periodSum}(ci) \quad \blacksquare
```

The full-cycle shift identity is verified twice under different names —
[GapProperties::assertPeriodicShift](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/GapProperties.scala)
and `assertFullCycleShift` — both thin wrappers over the same
`CycleIntegralFilterProperties::assertCIShiftEqualsSum` lemma; the article
proves the one identity above rather than two. The multi-cycle
generalization is verified separately as `assertMultiCycleShift`. The core
Scala verification code is in Appendix A.12.

### 5.2 General Residue Periodicity

When the total sum of a cycle's values is a multiple of `m`, the residue
`mod(ci(pos), m)` depends only on `pos % ci.period` — it repeats every cycle
period. When `m` is a product of coprime values, the Chinese Remainder
Theorem [[5]](#ref5) implies the periodicity holds simultaneously for each factor: the
cycle period serves as a common period for all residues. This is the
arithmetic backbone of Eratosthenes' sieve [[5]](#ref5).

```math
\begin{aligned}
\text{mod}(\text{periodSum}(ci),\; m) = 0 \;\implies\;
\text{mod}(\text{ci}(\text{pos}),\; m) = \text{mod}(\text{ci}(\text{pos} \bmod \text{period}(ci)),\; m)
\end{aligned}
```

**Proof.** By strong induction on `pos`, subtracting one full cycle period at a time.

**Base Case** ($\text{pos} < \text{period}(ci)$):

```math
\begin{aligned}
\text{pos} \bmod \text{period}(ci) &= \text{pos}
  &&\text{[Mod of a value smaller than the divisor]} \\
\text{mod}(ci(\text{pos}), m) &= \text{mod}(ci(\text{pos} \bmod \text{period}(ci)), m)
  &&\text{[Substitution]}
\end{aligned}
```

**Induction Step** ($\text{pos} \geq \text{period}(ci)$): let $\text{previous} := \text{pos} - \text{period}(ci)$. By
the one-period shift identity proven in [§5.1](#51-cycle-period-shifts),
$ci(\text{previous} + \text{period}(ci)) = ci(\text{previous}) + \text{periodSum}(ci)$, i.e. $ci(\text{pos}) = ci(\text{previous}) + \text{periodSum}(ci)$:

```math
\begin{aligned}
\text{previous} \bmod \text{period}(ci) &= \text{pos} \bmod \text{period}(ci)
  &&\text{[Subtracting a full period does not change the position's residue]} \\
\text{mod}(ci(\text{previous}), m) &= \text{mod}(ci(\text{previous} \bmod \text{period}(ci)), m)
  &&\text{[Induction Hypothesis]} \\
ci(\text{pos}) &= ci(\text{previous}) + \text{periodSum}(ci)
  &&\text{[Full-cycle shift, §5.1]} \\
\text{mod}(ci(\text{pos}), m) &= \text{mod}(ci(\text{previous}) + \text{periodSum}(ci), m)
  &&\text{[Substitution]} \\
&= \text{mod}(ci(\text{previous}), m)
  &&\text{[Since } \text{mod}(\text{periodSum}(ci), m) = 0 \text{]} \\
&= \text{mod}(ci(\text{previous} \bmod \text{period}(ci)), m)
  &&\text{[By Induction Hypothesis]} \\
&= \text{mod}(ci(\text{pos} \bmod \text{period}(ci)), m)
  &&\text{[By the residue equality above]}
\end{aligned}
```

```math
\therefore \ \text{mod}(\text{periodSum}(ci), m) = 0 \implies \forall \ \text{pos} \in \mathbb{N}_0,\ \text{mod}(ci(\text{pos}), m) = \text{mod}(ci(\text{pos} \bmod \text{period}(ci)), m) \quad \blacksquare\ \text{[Q.E.D.]}
```

This property is verified in the [
GapProperties::assertModIsPeriodic
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/GapProperties.scala). The full Scala verification code is in Appendix A.11.

The companion div/mod decomposition `ci(pos) == ci(pos % size) + (pos / size) * ci.sum`
is verified in `GapProperties::assertCIModDivFormula`.

### 5.3 Persistent Non-Zero Residue

Let $v \in \mathbb{N}$, $v > 0$, with $\text{mod}(\text{periodSum}(ci), v) = 0$. If
none of the $n$ residues in one full period is zero mod $v$, then the
residue is never zero at any position, forever.

```math
\begin{aligned}
\text{mod}(\text{periodSum}(ci), v) = 0 \;\land\; \big(\forall\, k \in [0, n),\ \text{mod}(ci(k), v) \neq 0\big)
\implies \forall\, i \in \mathbb{N}_0,\ \text{mod}(ci(i), v) \neq 0
\end{aligned}
```

**Proof.** By [§5.2](#52-general-residue-periodicity), $\text{mod}(ci(i), v)
= \text{mod}(ci(i \bmod n), v)$ for every position $i$. Since $i \bmod n$
always falls in $[0, n)$, and none of those $n$ residues is zero by
hypothesis, the residue at any position $i$ cannot be zero either.

```math
\begin{aligned}
\text{mod}(ci(i),v) &= \text{mod}(ci(i \bmod n),v) &&\text{[§5.2]} \\
                      &\neq 0 &&\text{[In-period hypothesis]} \\
\therefore\ \text{mod}(ci(i),v) &\neq 0.
  \quad \blacksquare\ \text{[Q.E.D.]}
\end{aligned}
```

This is a direct corollary of the periodicity lemma [
GapProperties::assertModIsPeriodic
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/GapProperties.scala) used in [§5.2](#52-general-residue-periodicity); no separate lemma is needed once every in-period residue is checked. The full Scala verification code is in Appendix A.11.

### 5.4 Persistent Zero Residue

The mirror-image case: if every residue in one full period is zero mod $v$,
then the residue stays zero at every position, forever.

```math
\begin{aligned}
\text{mod}(\text{periodSum}(ci), v) = 0 \;\land\; \big(\forall\, k \in [0, n),\ \text{mod}(ci(k), v) = 0\big)
\implies \forall\, i \in \mathbb{N}_0,\ \text{mod}(ci(i), v) = 0
\end{aligned}
```

**Proof.** Identical to [§5.3](#53-persistent-non-zero-residue), with the
inequality reversed: by [§5.2](#52-general-residue-periodicity),
$\text{mod}(ci(i), v) = \text{mod}(ci(i \bmod n), v)$, and $i \bmod n$
always falls among the $n$ in-period residues, all of which are zero by
hypothesis.

```math
\begin{aligned}
\text{mod}(ci(i),v) &= \text{mod}(ci(i \bmod n),v) &&\text{[§5.2]} \\
                      &= 0 &&\text{[In-period hypothesis]} \\
\therefore\ \text{mod}(ci(i),v) &= 0.
  \quad \blacksquare\ \text{[Q.E.D.]}
\end{aligned}
```

This is the same corollary of [
GapProperties::assertModIsPeriodic
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/GapProperties.scala) as [§5.3](#53-persistent-non-zero-residue), applied to the opposite hypothesis. The full Scala verification code is in Appendix A.11.

### 5.5 Gap Telescoping

Two consecutive gaps telescope to the integral difference across both steps.
By applying the one-step difference lemma twice, the gap values at positions
`k` and `k + 1` add up to the integral span from `k - 1` to `k + 1`. This is
the step-lemma that underlies merging adjacent gap ranges.

```math
\begin{aligned}
\text{ci}(k + 1) - \text{ci}(k - 1) = \text{cycle}(k) + \text{cycle}(k + 1)
\quad \text{for } 1 \leq k \text{ and } k + 1 < \text{period}(\text{ci}).
\end{aligned}
```

**Proof.** The one-step property at positions $k-1$ and $k$ gives

```math
\begin{aligned}
\text{ci}(k) - \text{ci}(k-1) &= \text{cycle}(k), \\
\text{ci}(k+1) - \text{ci}(k) &= \text{cycle}(k+1).
\end{aligned}
```

Adding these equalities cancels $\text{ci}(k)$, so

```math
\begin{aligned}
\therefore\ \text{ci}(k+1) - \text{ci}(k-1)
= \text{cycle}(k) + \text{cycle}(k+1)
\quad \blacksquare\ \text{[Q.E.D.]}
\end{aligned}
```

This property is verified in the [
CycleIntegralProperties::assertConsecutiveGapSumEqualsDiff
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralProperties.scala). The full Scala verification code is in Appendix A.10.

### 5.6 Cycle Residue Classification

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

## 6. Deriving New Cycle Integrals

These properties describe how to build a new cycle integral from an
existing one: replicating its backing list, shifting its index, rotating
its gaps, filtering out multiples of a value, and reconstructing the
filtered result directly. Properties 6.1, 6.4–6.10 are fully
Stainless-verified; Properties 6.2 and 6.3 have mathematical proofs but are
not yet Stainless-verified.

- x-fold cycle expansion: the physical period changes while the represented stream is preserved — [§6.1](#61-x-fold-cycle-expansion)
- Index shifts: right and left — [§6.2](#62-right-index-shift)–[6.3](#63-left-index-shift)
- Gap rotation with head adjustment: rotating the gap cycle shifts the represented integral by one position — [§6.4](#64-gap-rotation-with-head-adjustment)
- Survivor filtering: exactness and structure of the scan that retains non-multiples — [§6.5](#65-survivor-exactness)–[6.6](#66-survivor-structure)
- Filter-merge reconstruction: the resulting gap cycle after removing a multiple — [§6.7](#67-merge-shift-law)–[6.10](#610-filtered-result-has-no-multiples)

### 6.1 x-fold Cycle Expansion

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

### 6.2 Right Index Shift

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

### 6.3 Left Index Shift

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

### 6.4 Gap Rotation with Head Adjustment

Rotating a gap cycle by one position and adjusting the head shifts the
entire integral by one position.

```math
\begin{aligned}
\text{GapList}(\text{head} + \text{gaps}_0,\; \text{tail}(\text{gaps}) \mathbin{\texttt{++}} (\text{gaps}_0 :: L_e))_i
  = \text{GapList}(\text{head},\; \text{gaps})_{i + 1}
  \quad \text{for } 0 \leq i \text{ and } i + 1 < |\text{gaps}|.
\end{aligned}
```

**Proof.** At $i=0$, the adjusted head is
$\text{head}+\text{gaps}_0$, which is the original integral at position
$1$. For $i>0$, assume the shifted integral at $i-1$ equals the original
integral at $i$. The rotated gap at $i$ is the original gap at $i+1$;
applying the one-step property to both integrals gives

```math
\begin{aligned}
I'_i &= I'_{i-1} + \text{gaps}'_{i-1} \\
     &= I_i + \text{gaps}_i \\
     &= I_{i+1}. \\
\therefore\ I'_i &= I_{i+1}
\quad \blacksquare\ \text{[Q.E.D.]}
\end{aligned}
```

This property is verified in [
GapProperties::assertRotateOneShiftsIntegralByOne
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/GapProperties.scala). It delegates to the verified `ShiftedList.assertShiftedApplyIsOriginalPlusOne`; the full source is linked there rather than repeated inline.

For a filter value $f$ and a range $[start, start + count)$, the survivor
sequence is the sub-sequence of $ci$'s values at those positions whose
remainder modulo $f$ is nonzero — the cycle-integral analogue of one
Eratosthenes sieve step [[5]](#ref5), where positions divisible by $f$ are
removed and only the non-multiples remain:

```math
S := \text{survivorValues}(ci, f, start, count) :=
\big[\, ci(pos) \mid start \le pos < start + count,\ \text{mod}(ci(pos), f) \neq 0 \,\big]
```

Ten verified lemmas in `GapProperties.scala` characterize this sequence.

### 6.5 Survivor Exactness

$S$ is exact by construction: it is defined as exactly the non-multiples of
$f$ in range, nothing more and nothing less. The recursive Scala
implementation of `survivorValues` is verified to compute exactly this
specification.

This is verified in [
GapProperties::assertSurvivorValuesContainsOnlyNonMultiples
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/GapProperties.scala) and [`assertSurvivorValuesContainsNonMultipleAtPosition`](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/GapProperties.scala).

### 6.6 Survivor Structure

When every value in $[start, pos)$ is a multiple of $f$ and $ci(pos)$
itself is not, $ci(pos)$ is the first survivor, and $S$ decomposes as that
value followed by the survivors of the rest of the range, $(pos, end)$
where $end := start + count$:

```math
\begin{aligned}
\big(\forall\, q \in [start, pos),\ \text{mod}(ci(q), f) = 0\big)
  \;\land\; \text{mod}(ci(pos), f) \neq 0
  &\implies \text{head}(S) = ci(pos)
  && \text{[First survivor]} \\
S &= ci(pos) :: \big[\, ci(q) \mid pos < q < end,\ \text{mod}(ci(q), f) \neq 0 \,\big]
  && \text{[Structural split]}
\end{aligned}
```

At the endpoints of a range that itself survives, the first and last
elements of $S$ are exactly the endpoint values, and over one complete
period the difference between them equals the cycle's total gap sum —
filtering does not change how far the integral advances across a full
period:

```math
\begin{aligned}
\text{mod}(ci(start), f) \neq 0
  &\implies \text{head}(S) = ci(start) \\
\text{mod}(ci(start + count - 1), f) \neq 0
  &\implies \text{last}(S) = ci(start + count - 1) \\
\text{mod}(ci(0), f) \neq 0 \;\land\; \text{mod}(ci(n), f) \neq 0
  &\implies \text{last}(S) - \text{head}(S) = \text{periodSum}(ci)
\end{aligned}
```

The gap between two consecutive survivors, once every intervening multiple
has been filtered out, is strictly positive:

```math
\text{mod}(ci(from), f) \neq 0 \;\land\; \text{mod}(ci(to), f) \neq 0
\;\land\; \big(\forall\, q \in (from, to),\ \text{mod}(ci(q), f) = 0\big)
\implies ci(to) - ci(from) > 0
```

All survivor-structure properties are verified in [
GapProperties::assertFirstSurvivorAtPosition
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/GapProperties.scala), [`assertSurvivorValuesSplitAtFirstPosition`](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/GapProperties.scala), [`assertFirstSurvivorIsHead`](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/GapProperties.scala), [`assertLastSurvivorIsLastScanned`](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/GapProperties.scala), [`assertFilteredSumEqualsOriginalSum`](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/GapProperties.scala), and [`assertMergedGapPositive`](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/GapProperties.scala).

Filtering removes a value; the surviving values must still form a valid
cycle-integral gap list. This section proves that removing one multiple by
merging its two neighboring gaps produces exactly the cycle integral that
a fresh construction from the survivor list would produce, and that the
result contains no multiples of the filter value anywhere.

### 6.7 Merge Shift Law

Let $ci$ be a cycle integral with period $n$, and let $m$ be a merge index
with $0 \le m$ and $m + 1 < n$. Let $ci'$ be a cycle integral with period
$n - 1$, the same initial value, and a gap cycle equal to $ci$'s except
that the gaps at $m$ and $m + 1$ are combined into one:

```math
\begin{aligned}
\text{cycle}'(i) &= \text{cycle}(i)
  &&\text{for } i < m \\
\text{cycle}'(m) &= \text{cycle}(m) + \text{cycle}(m + 1) \\
\text{cycle}'(i) &= \text{cycle}(i + 1)
  &&\text{for } i > m
\end{aligned}
```

Then $ci'$ agrees with $ci$ before the merge point, and agrees with $ci$
one position ahead at and after it:

```math
\begin{aligned}
pos < m &\implies ci'(pos) = ci(pos)
  &&\text{[Before merge]} \\
ci'(m) &= ci(m + 1)
  &&\text{[At merge]} \\
pos > m &\implies ci'(pos) = ci(pos + 1)
  &&\text{[After merge]} \\
ci'(n - 1) &= ci(n)
  &&\text{[Period boundary]}
\end{aligned}
```

**Proof.** By induction on the position, using the step property
([§3.1](#31-recursive-cycle-integral)) in each of three cases split at the
merge point.

**Case 1: Before the merge** ($pos < m$), by induction on $pos$.

**Base Case** ($pos = 0$):

```math
\begin{aligned}
ci'(0) &= init + \text{cycle}'(0)
  &&\text{[By Definition]} \\
&= init + \text{cycle}(0)
  &&\text{[Same initial value; unchanged gap before merge]} \\
&= ci(0)
  &&\text{[By Definition]}
\end{aligned}
```

**Induction Step** ($0 < pos < m$):

```math
\begin{aligned}
ci'(pos - 1) &= ci(pos - 1)
  &&\text{[Induction Hypothesis]} \\
ci'(pos) &= ci'(pos - 1) + \text{cycle}'(pos)
  &&\text{[By Definition]} \\
&= ci(pos - 1) + \text{cycle}(pos)
  &&\text{[Substitution; unchanged gap before merge]} \\
&= ci(pos)
  &&\text{[By Definition]}
\end{aligned}
```

```math
\therefore \ pos < m \implies ci'(pos) = ci(pos) \quad \blacksquare
```

**Case 2: At the merge** ($pos = m$). For $m > 0$, using Case 1 at $m - 1$:

```math
\begin{aligned}
ci'(m) &= ci'(m - 1) + \text{cycle}'(m)
  &&\text{[By Definition]} \\
&= ci(m - 1) + \big(\text{cycle}(m) + \text{cycle}(m + 1)\big)
  &&\text{[Case 1; merged-gap definition]} \\
&= \big(ci(m - 1) + \text{cycle}(m)\big) + \text{cycle}(m + 1)
  &&\text{[Regroup]} \\
&= ci(m) + \text{cycle}(m + 1)
  &&\text{[By Definition]} \\
&= ci(m + 1)
  &&\text{[By Definition]}
\end{aligned}
```

For $m = 0$, the same identity holds directly, with no Case 1 dependency:
$ci'(0) = init + \text{cycle}'(0) = init + \text{cycle}(0) + \text{cycle}(1) = ci(1)$.

```math
\therefore \ ci'(m) = ci(m + 1) \quad \blacksquare
```

**Case 3: After the merge** ($pos > m$), by induction on $pos$.

**Base Case** ($pos = m + 1$), using Case 2:

```math
\begin{aligned}
ci'(m + 1) &= ci'(m) + \text{cycle}'(m + 1)
  &&\text{[By Definition]} \\
&= ci(m + 1) + \text{cycle}(m + 2)
  &&\text{[Case 2; shifted-gap definition]} \\
&= ci(m + 2)
  &&\text{[By Definition]}
\end{aligned}
```

**Induction Step** ($pos > m + 1$):

```math
\begin{aligned}
ci'(pos - 1) &= ci(pos)
  &&\text{[Induction Hypothesis]} \\
ci'(pos) &= ci'(pos - 1) + \text{cycle}'(pos)
  &&\text{[By Definition]} \\
&= ci(pos) + \text{cycle}(pos + 1)
  &&\text{[Substitution; shifted-gap definition]} \\
&= ci(pos + 1)
  &&\text{[By Definition]}
\end{aligned}
```

```math
\therefore \ pos > m \implies ci'(pos) = ci(pos + 1) \quad \blacksquare
```

The period boundary case is the last instance of Case 3, at $pos = n - 1$:
$ci'(n - 1) = ci(n)$.

This property is verified in [
CycleIntegralFilterProperties::assertSameBeforeMerge
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralFilterProperties.scala), [`assertShiftAtMerge`](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralFilterProperties.scala), [`assertShiftAfterMerge`](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralFilterProperties.scala), and [`assertNewCIAtSizeEqualsOld`](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralFilterProperties.scala). The full Scala verification code is in Appendix A.13.

### 6.8 Removing a Multiple

When the value at the merge point is a multiple of a filter value $f$,
merging its two neighboring gaps removes it from the sequence entirely:
the new integral's value at that position is the old integral's next
value, which by construction is not itself a multiple.

```math
\begin{aligned}
\text{mod}(ci(0), f) \neq 0 \;\land\; \text{mod}(ci(m), f) = 0
&\implies ci'(m) = ci(m + 1)
&&\text{[Multiple removed]} \\
\text{mod}(ci(m + 1), f) \neq 0
&\implies \text{mod}(ci'(m), f) \neq 0
&&\text{[Result is not a multiple]}
\end{aligned}
```

**Proof.** The first identity is the merge shift law's "at merge" case
([§6.7](#67-merge-shift-law)) applied directly: $ci'(m) = ci(m + 1)$
regardless of whether $ci(m)$ was a multiple. The second follows because
equal values satisfy the same modulo condition.

This property is verified in [
CycleIntegralFilterProperties::assertRemoveOneMultiple
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralFilterProperties.scala) and [`assertRemoveMultipleModNotZero`](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralFilterProperties.scala). The full Scala verification code is in Appendix A.14.

### 6.9 Direct Construction from Survivors

Rather than merging gaps one multiple at a time, a filtered cycle integral
can be built directly from the survivor list ([§6.5](#65-survivor-exactness)):
its initial value is the first survivor, and its gap cycle is the list of
differences between consecutive survivors. This direct construction
reproduces exactly what repeated merging would produce.

```math
\begin{aligned}
S &:= \text{survivorValues}(ci, f, 0, n) \\
ci''\text{'s initial value} &= S_0,\quad \text{cycle}''(i) = S_{i+1} - S_i \\
\implies ci''(k) &= S_{k + 1}
&&\text{[Direct construction matches survivors]}
\end{aligned}
```

**Proof.** By induction on $k$. The base case follows directly from the
integral's own definition applied to the first gap. The inductive step
adds the $k$-th constructed gap, which by definition equals
$S_{k+1} - S_k$, to the inductive hypothesis $ci''(k-1) = S_k$, giving
$ci''(k) = S_{k+1}$.

This property is verified in [
CycleIntegralFilterProperties::assertNewCIGeneratesFiltered
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralFilterProperties.scala), [`assertNewCIMatchesSurvivors`](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralFilterProperties.scala), and [`assertGapsFromSurvivorsMatchCI`](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralFilterProperties.scala). The full Scala verification code is in Appendix A.15.

### 6.10 Filtered Result Has No Multiples

The cycle integral constructed directly from the survivor list contains no
multiples of the filter value at any position — its values are, by
construction, exactly the survivors.

```math
\begin{aligned}
\text{mod}(ci(0), f) \neq 0 \implies
\text{mod}(ci''(k), f) \neq 0
\quad \text{for every valid } k
\end{aligned}
```

**Proof.** By [§6.9](#69-direct-construction-from-survivors), $ci''(k)$
equals the survivor $S_{k+1}$, and every element of the survivor list is
already known not to be a multiple of $f$
([§6.5](#65-survivor-exactness)).

```math
\begin{aligned}
ci''(k) &= S_{k+1} &&\text{[§6.9]} \\
\text{mod}(S_{k+1},f) &\neq 0 &&\text{[§6.5]} \\
\therefore\ \text{mod}(ci''(k),f) &\neq 0.
  \quad \blacksquare\ \text{[Q.E.D.]}
\end{aligned}
```

This property is verified in [
CycleIntegralFilterProperties::assertFilterMergeComposition
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralFilterProperties.scala) and [`assertNextGapsValid`](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralFilterProperties.scala). The full Scala verification code is in Appendix A.16.

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

For both presentations, we verified the sum property (integral equals cumulative cycle sum) and the step property (difference between consecutive values equals the corresponding cycle element). We also proved equivalence of the recursive and modulo definitions, that the integral is strictly increasing under positive base values, and that it stays positive everywhere given a non-negative start.

Beyond these core definitions, the article verifies several reusable
cycle-integral laws. Within a fixed cycle integral: residues are periodic
when the cycle sum is zero modulo the chosen modulus, with the persistent
non-zero and persistent zero cases following as immediate corollaries;
adjacent gaps telescope into integral differences; full-cycle shifts advance
the integral by the cycle sum; and cycle residue classification is correct,
exclusive, and exhaustive. Building new cycle integrals from existing ones:
repeating a backing cycle preserves the represented integral stream;
rotating a gap cycle with the corresponding head adjustment shifts the
represented integral by one position; survivor scans retain exactly the
non-multiples needed for filtering; and merging the two gaps around a
removed multiple reconstructs exactly the cycle integral that a fresh
construction from the survivor list would produce, with no multiples of
the filter value remaining anywhere in the result. The open extension
points are the index-shift laws in Sections 6.2 and 6.3.

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
= \text{Cycle}(L)_{i+1}
\quad &\text{[Step Property]} \\
\text{CycleIntegral}(L, init)_{i+1}
&- \text{CycleIntegral}(L, init)_i \\
&= \text{CycleIntegral}(L, init)_{i+n+1}
 - \text{CycleIntegral}(L, init)_{i+n}
\quad &\text{[Same Difference After Full Cycle]} \\
\text{CycleIntegral}(L, init)_i
&= \text{sum}([init] \mathbin{\texttt{++}}
 [\text{Cycle}(L)_0, \ldots, \text{Cycle}(L)_i])
\quad &\text{[Sum of Mod Values as List]} \\
init \geq 0 \land (\forall x \in L,\ x > 0) \land b > a
&\implies
\text{CycleIntegral}(L, init)_b > \text{CycleIntegral}(L, init)_a
\quad &\text{[Strictly Increasing]} \\
init \geq 0 \land (\forall x \in L,\ x > 0)
&\implies
\text{CycleIntegral}(L, init)_i > 0
\quad &\text{[Positivity]} \\
\end{aligned}
```

```math
\begin{aligned}
ci(pos + \text{period}(ci))
&= ci(pos) + \text{periodSum}(ci)
\quad &\text{[Cycle-Period Shift]} \\
\text{mod}(\text{periodSum}(ci), m) = 0
&\implies
\text{mod}(ci(pos), m) = \text{mod}(ci(pos \bmod n), m)
\quad &\text{[General Residue Periodicity]} \\
\text{mod}(\text{periodSum}(ci), m) = 0 \land \big(\forall\, k \in [0,n),\ \text{mod}(ci(k), m) \neq 0\big)
&\implies
\forall\, i,\ \text{mod}(ci(i), m) \neq 0
\quad &\text{[Persistent Non-Zero Residue]} \\
\text{mod}(\text{periodSum}(ci), m) = 0 \land \big(\forall\, k \in [0,n),\ \text{mod}(ci(k), m) = 0\big)
&\implies
\forall\, i,\ \text{mod}(ci(i), m) = 0
\quad &\text{[Persistent Zero Residue]} \\
\text{CycleIntegral}(G,h)_{k+1}
&- \text{CycleIntegral}(G,h)_{k-1}
= G_{k-1} + G_k
\quad &\text{[Two-Gap Telescoping]} \\
\text{classify}(I_i,m)
&\in \{\text{zero},\text{nonzero}\}
\quad &\text{[Residue Classification]} \\
\end{aligned}
```

```math
\begin{aligned}
\text{CycleIntegral}(L^{\langle x\rangle}, init)_i
&= \text{CycleIntegral}(L, init)_i
\quad &\text{[Repeated-Cycle Invariance]} \\
\text{rotateAt}(G,1)\text{ with head }h+G_0
&\implies
I'_{i}=I_{i+1}
\quad &\text{[Rotation Shift]} \\
\text{survivors}(I,m)
&= \{ I_i \mid I_i \not\equiv 0 \pmod m \}
\quad &\text{[Survivor Exactness]} \\
\big(\forall\, q \in [start,pos),\ \text{mod}(ci(q),f)=0\big) \land \text{mod}(ci(pos),f)\neq 0
&\implies
\text{head}(S) = ci(pos)
\quad &\text{[Survivor Structure]} \\
\end{aligned}
```

```math
\begin{aligned}
ci'(m) &= ci(m + 1)
\quad &\text{[Merge Shift Law]} \\
\text{mod}(ci(m), f) = 0 \implies ci'(m) &= ci(m + 1)
\quad &\text{[Removing a Multiple]} \\
ci''\text{'s initial value} = S_0 \land \text{cycle}''(i) = S_{i+1} - S_i
&\implies ci''(k) = S_{k+1}
\quad &\text{[Direct Construction from Survivors]} \\
\text{mod}(ci(0), f) \neq 0 &\implies \text{mod}(ci''(k), f) \neq 0
\quad &\text{[Filtered Result Has No Multiples]} \\
\end{aligned}
```

The verified definitions provide a reusable foundation for reasoning about infinite periodic
accumulations using finite list structures and machine-checked Scala code.

## 8. Future Work

The nearest continuation is to close the remaining index-shift properties in
Section 6. Those statements already have mathematical derivations in the
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
Mata, T. H. (2026). _Division and Modulo from Recursive Normalization_. Available at: [http://ai.viXra.org/abs/2609.0009](http://ai.viXra.org/abs/2609.0009)

<a name="ref5" id="ref5" href="#ref5">[5]</a>
Hardy, G. H. & Wright, E. M. (1979). _An Introduction to the Theory of Numbers_ (5th ed.). Oxford University Press. §5.4 (Chinese Remainder Theorem), §15.1 (Sieve of Eratosthenes).

<a name="ref6" id="ref6" href="#ref6">[6]</a>
The Lean Community. *Mathlib: Periodic Functions*.
Available at: [https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Ring/Periodic.html](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Ring/Periodic.html)

<a name="ref7" id="ref7" href="#ref7">[7]</a>
The Lean Community. *Mathlib: Cycles of Lists*.
Available at: [https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/List/Cycle.html](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/List/Cycle.html)

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

### A.13 Merge Shift Law — assertShiftAtMerge

Source: [CycleIntegralFilterProperties::assertShiftAtMerge](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralFilterProperties.scala)

```scala
def assertShiftAtMerge(
  oldIntegral: CycleIntegral,
  newIntegral: CycleIntegral,
  mergeIndex: BigInt
): Boolean = {
  require(mergeIndex >= 0)
  require(mergeIndex + 1 < oldIntegral.period)
  require(newIntegral.period == oldIntegral.period - 1)
  require(oldIntegral.initialValue == newIntegral.initialValue)
  require(newIntegral.cycle(mergeIndex) ==
    oldIntegral.cycle(mergeIndex) +
      oldIntegral.cycle(mergeIndex + 1))
  require(allGapsMatchBeforeMerge(
    oldIntegral, newIntegral, mergeIndex, mergeIndex - 1))
  if (mergeIndex == 0) {
    assert(newIntegral(0) ==
      newIntegral.initialValue + newIntegral.cycle(0))
    assert(oldIntegral(1) ==
      oldIntegral.cycle(0) + oldIntegral.cycle(1) +
        oldIntegral.initialValue)
  } else {
    assertSameBeforeMerge(
      oldIntegral, newIntegral, mergeIndex, mergeIndex - 1)
    assert(newIntegral(mergeIndex - 1) ==
      oldIntegral(mergeIndex - 1))
    assert(newIntegral(mergeIndex) ==
      newIntegral(mergeIndex - 1) +
        newIntegral.cycle(mergeIndex))
    assert(oldIntegral(mergeIndex + 1) ==
      oldIntegral(mergeIndex) +
        oldIntegral.cycle(mergeIndex + 1))
  }
  newIntegral(mergeIndex) == oldIntegral(mergeIndex + 1)
}.holds
```

### A.14 Removing a Multiple — assertRemoveOneMultiple

Source: [CycleIntegralFilterProperties::assertRemoveOneMultiple](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralFilterProperties.scala)

```scala
def assertRemoveOneMultiple(
  oldIntegral: CycleIntegral,
  newIntegral: CycleIntegral,
  filterValue: BigInt,
  multiplePosition: BigInt
): Boolean = {
  require(filterValue > 0)
  require(multiplePosition > 0)
  require(multiplePosition + 1 < oldIntegral.period)
  require(newIntegral.period == oldIntegral.period - 1)
  require(oldIntegral.initialValue == newIntegral.initialValue)
  require(Calc.mod(oldIntegral(multiplePosition), filterValue) ==
    BigInt(0))
  require(Calc.mod(oldIntegral(0), filterValue) != BigInt(0))
  require(allGapsMatchBeforeMerge(
    oldIntegral, newIntegral, multiplePosition, multiplePosition - 1))
  require(newIntegral.cycle(multiplePosition) ==
    oldIntegral.cycle(multiplePosition) +
      oldIntegral.cycle(multiplePosition + 1))
  require(allGapsMatchAfterMerge(
    oldIntegral, newIntegral, multiplePosition, multiplePosition))
  assertShiftAtMerge(oldIntegral, newIntegral, multiplePosition)
  newIntegral(multiplePosition) ==
    oldIntegral(multiplePosition + 1)
}.holds
```

### A.15 Direct Construction from Survivors — assertNewCIGeneratesFiltered

Source: [CycleIntegralFilterProperties::assertNewCIGeneratesFiltered](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralFilterProperties.scala)

```scala
def assertNewCIGeneratesFiltered(
  filteredIntegral: CycleIntegral,
  survivorList: List[BigInt],
  position: BigInt
): Boolean = {
  require(survivorList.size > position + 1)
  require(filteredIntegral.period > position)
  require(position >= 0)
  require(filteredIntegral.initialValue == survivorList.head)
  require(allGapsMatch(filteredIntegral, survivorList, position))
  decreases(position)
  if (position == 0) {
    assert(filteredIntegral(0) ==
      filteredIntegral.initialValue + filteredIntegral.cycle(0))
  } else {
    assert(allGapsMatch(filteredIntegral, survivorList, position - 1))
    assertNewCIGeneratesFiltered(
      filteredIntegral, survivorList, position - 1)
    assert(filteredIntegral(position - 1) ==
      survivorList(position))
    assert(filteredIntegral(position) ==
      filteredIntegral(position - 1) + filteredIntegral.cycle(position))
  }
  filteredIntegral(position) == survivorList(position + 1)
}.holds
```

### A.16 Filtered Result Has No Multiples — assertFilterMergeComposition

Source: [CycleIntegralFilterProperties::assertFilterMergeComposition](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter4/cycle/integral/recursive/properties/CycleIntegralFilterProperties.scala)

```scala
def assertFilterMergeComposition(
  originalCI: CycleIntegral,
  newCI: CycleIntegral,
  survivors: List[BigInt],
  filterValue: BigInt,
  maxIndex: BigInt
): Boolean = {
  require(filterValue > 0)
  require(originalCI.period > 0)
  require(Calc.mod(originalCI(0), filterValue) != BigInt(0))
  require(survivors == survivorValues(originalCI, filterValue,
    BigInt(0), originalCI.period))
  require(!survivors.isEmpty)
  require(newCI.initialValue == survivors.head)
  require(newCI.cycle.values == gapsFromValues(survivors))
  require(maxIndex >= 0)
  require(maxIndex < newCI.period)
  require(survivors.size > maxIndex + 1)
  decreases(maxIndex + 1)

  assertNewCIMatchesSurvivors(survivors, newCI, maxIndex)
  assertSurvivorAtNotMultiple(originalCI, filterValue,
    BigInt(0), originalCI.period, maxIndex + 1)

  if (maxIndex > 0) {
    assertFilterMergeComposition(originalCI, newCI,
      survivors, filterValue, maxIndex - 1)
  }
  Calc.mod(newCI(maxIndex), filterValue) != BigInt(0)
}.holds
```

## Appendix B: Stainless Verification Log Output

The latest `just verify` run verifies all the described properties without errors. The full log output is available at: [logs/verify.log](https://github.com/thiagomata/prime-numbers/blob/master/articles/logs/verify.log)
