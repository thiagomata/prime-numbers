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

In this stydy, we restrict our universe of values $𝕊$ to be the set of non-negative integers, i.e., $𝕊 = ℕ_0$.

### Recursive Cycle Definition

```math
\begin{aligned}
\forall \ L \in  𝕃, \quad \forall \ v &\in ℕ_0,\quad \forall \ i \in ℕ_0 \\
L &:= [v_0, v_1, \dots, v_{n-1}] \in ℕ_0^n \\
n &= |L| \\
\text{Cycle}_i &= \begin{cases}
L_i & \text{if } i < n \\
\text{Cycle}_{i - n} & \text{if } i \geq n \\
\end{cases} \ , |L| > 0
\end{aligned}
```

Defined at [RecursiveCycle](
    ./src/main/scala/v1/cycle/recursiveCycle/RecursiveCycle.scala
) as follows:

<details>
<summary> Scala Doc </summary>

```scala
/**
 * Represents a recursive cycle of values.
 *
 * @param values List A non-empty list of BigInt 
 * non-negative values that form the cycle.
 */
```
</details>

```scala
case class RecursiveCycle(values: List[BigInt]) {
  require(values.nonEmpty)
  require(CycleUtils.checkPositiveOrZero(values))

  def size: BigInt = values.size

  def apply(key: BigInt): BigInt = {
    decreases(key)
    require(key >= 0)

    if (key < size) {
      values(key)
    } else {
      apply(key - values.size)
    }
  }
}
```
