# Formal Verification of Discrete Integration Properties from First Principles

**Author:** Mata, T. H.
Independent Researcher  
**Email:** [thiago.henrique.mata@gmail.com](mailto:thiago.henrique.mata@gmail.com)  
**GitHub:** [@thiagomata](https://github.com/thiagomata)

## Abstract

<p style="text-align: justify">
We formalize and verify the discrete integral operation over finite lists of integers using a recursive, from-scratch 
construction grounded in a zero-prior-knowledge methodology.
This operation is implemented in pure Scala and verified using the Stainless formal verification system.
The work builds on a previously verified model of lists and summation &mdash; themselves constructed without domain-specific 
assumptions &mdash; extending that foundation to list-based accumulation.
The result is a verified and mathematically rigorous definition of discrete integration with static correctness guarantees.
</p>

## 1. Introduction

Accumulation is a central operation in mathematics and computing &mdash; from prefix sums in algorithms to integral 
transforms in signal processing. In functional programming, accumulation often appears as a fold or scan, but such 
constructs are rarely defined from first principles in a formally verified setting.

In this article, we present a discrete integral operation over finite integer lists, defined recursively and verified 
some of its properties using the Stainless system. Our approach follows a zero-prior-knowledge philosophy, building on 
a previously verified foundation for recursive list structures and summation. The result is a verified, from-scratch 
implementation of discrete integration, suitable as a foundation for higher-level numeric reasoning over lists.

This article verifies:

- Core integral properties: head value, cumulative sum, incremental change, final sum, strictly increasing, gaps positivity — §4
- Implementation consistency: element/acc/delta/last/size agreement between the recursive and accumulated representations — §5

## 2. Preliminaries and Notation

Let $L = [x_0, x_1, \dots, x_{n-1}] \in \mathbb{Z}^n$ be a finite, non-empty list of $n$ integers, where $n = |L|$,
and let $init \in \mathbb{Z}$ be an initial value.

We reuse several basic list operations and their verified properties from a companion article on recursive list 
construction &mdash; [Using Formal Verification to Prove Properties of Lists Recursively Defined](
https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter3/list.md
) [[1]](#ref1).  
These include the following functions:

- $\text{sum}(L)$: recursively computes the total sum of elements in a list.
- $\text{head}(L)$: returns the first element of a non-empty list.
- $\text{tail}(L)$: returns the list without its first element.
- $A \mathbin{\texttt{++}} B$: concatenates two lists $A$ and $B$.

These operations were defined and verified using the same zero-prior-knowledge methodology [[1]](#ref1), 
and are treated here as foundational primitives.

Proofs in this article are written in Scala and verified using the Stainless system with `BigInt` used to represent 
unbounded integers.

## 3. Definition of Discrete Integral

The discrete integral accumulates list values into partial sums from a given initial value. Two representations are equivalent.

- Mathematical: $I_k = init + \sum_{i=0}^k L_i$ — the specification
- Recursive: $I_0 = L_0 + init$, $I_{k+1} = I_k + L_{k+1}$ — the implementation

### 3.1 Mathematical Definition

We define the **discrete integral** $I = Integral(L, init)$ as a list of partial sums such that:

$$
\begin{aligned}
\text{for } k \in [0, n - 1] \\
I_{k} = init + \sum_{i=0}^{k} L_i \\
\end{aligned}
$$

### 3.2 Recursive Definition

$$
\begin{aligned}
I &= \text{Integral}(L, init) \\
n &= |L| \\
k &\in [0, n - 1]
\end{aligned}
$$

The value of the $k\text{-th}$ element in the integral $I$ is defined recursively as:

$$
I_k =
\begin{cases}
L_0 + init & \text{if } k = 0 \\
\text{Integral}(\text{tail}(L),\ \text{head}(L) + init)_{(k - 1)} & \text{if } k > 0
\end{cases}
$$

In Scala, this is encoded at [Integral.scala](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/integral/Integral.scala):

```scala
case class Integral(list: List[BigInt], init: BigInt = 0) {
  def apply(position: BigInt): BigInt = {
    require(list.nonEmpty)
    require(position >= 0 && position < list.size)
    if (position == 0) this.head else Integral(list.tail, this.head).apply(position - 1)
  }
  def head: BigInt = {
    require(list.nonEmpty)
    list.head + init
  }
  // ... additional methods omitted
}
```

## 4. Core Integral Properties

- Head value: $I_0 = L_0 + init$ — §4.1
- Cumulative sum: $I_k = init + \sum_{i=0}^k L_i$ — §4.2
- Incremental change: $I_{p+1} - I_p = L_{p+1}$ — §4.3
- Final sum: $I_{n-1} = init + \text{sum}(L)$ — §4.4

### 4.1 Head Value Matches Definition

The first element of the Integral equals the first element of the original list plus the initial value.

$$
I_0 = x_0 + init
$$

Since:

$$
\begin{aligned}
I & \ne L_e                               & \qquad \text{[By definition: Integral is not an empty list]} \\
I_0 & = \text{head}(I)                    & \qquad \text{[List element access and indexing]} \\
\text{head}(I) & = \text{head}(L) + init  & \qquad \text{[By definition of Integral]} \\
L_0 & = \text{head}(L)                    & \qquad \text{[List element access and indexing]} \\
L_0 & = x_0                               & \qquad \text{[By definition of List]} \\
\text{head}(I) & = L_0 + init             & \qquad \text{[Substitute head}(L) \text{ by } L_0] \\
I_0 & = L_0 + init                        & \qquad \text{[Substitute head}(I) \text{ by } I_0] \\
I_0 & = x_0 + init                        & \qquad \text{[Substitute } L_0 \text{ by } x_0] \\
I_0 & = x_0 + init \quad \blacksquare     & \qquad \text{[Q.E.D.]}
\end{aligned}
$$

This property is verified in the [
  IntegralProperties::assertHeadValueMatchDefinition
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/integral/properties/IntegralProperties.scala). The full Scala verification code is in Appendix A.1.

### 4.2 Integral Equals Sum Until Position

The integral at position $k$ equals the sum of all elements in the list up to that position, plus the initial value:

$$
\forall\ k \in [0, n-1]:\ I_k = \mathit{init} + \sum_{i=0}^{k} x_i
$$

**Proof by Induction on $k$**

#### Base case: $k = 0$

$$
\begin{aligned}
\sum_{i=0}^{0} x_i &= x_0 \qquad & \text{[By definition of sum]} \\
I_0 & = \mathit{init} + x_0 \qquad & \text{[By definition of integral]} \\
    & = \mathit{init} + \sum_{i=0}^{0} x_i & \qquad \text{[Substituting } x_0] \\
\end{aligned}
$$
$$ \therefore $$
$$
I_0 = \mathit{init} + \sum_{i=0}^{0} x_i \qquad \text{[Q.E.D.]}
$$

#### Inductive step: Assume the property holds for $k-1$

$$
I_{k-1} = \mathit{init} + \sum_{i=0}^{k-1} x_i \implies I_k = \mathit{init} + \sum_{i=0}^{k} x_i
$$
$$
\begin{aligned}
I_{k-1} & = \mathit{init} + \sum_{i=0}^{k-1} x_i                     \qquad & \text{[By induction]} \\ 
I_k & = I_{k-1} + L_k                                                \qquad & \text{[By definition of integral]} \\
    &= \left(\mathit{init} + \sum_{i=0}^{k-1} x_i\right) + x_k       \qquad & \text{[By induction and } L_k = x_k]  \\
    &= \mathit{init} + \left(\sum_{i=0}^{k-1} x_i + x_k\right)       \qquad & \text{[Distributivity]} \\
    &= \mathit{init} + \sum_{i=0}^{k} x_i                            \qquad & \text{[By definition of sum]} \\
\end{aligned}
$$
$$ \therefore $$
$$
\begin{aligned}
I_k = \mathit{init} + \sum_{i=0}^{k} x_i \quad \blacksquare \qquad \text{[Q.E.D.]} \\
\end{aligned}
$$

This property is verified in the [
  IntegralProperties::assertIntegralEqualsSum
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/integral/properties/IntegralProperties.scala). The full Scala verification code is in Appendix A.2.

### 4.3 Incremental Change Matches List Value

The difference between two consecutive values in the Integral equals the corresponding value in the original list $L$.

$$
\begin{aligned}
\forall \text{ } p & \in [0,\ n-2]: \\
I_{p+1} - I_p & = L_{p+1}
\end{aligned}
$$

#### Proof of the Base Case $I_1 - I_0 = x_1$

$$
\begin{aligned}
I_1    &= \text{Integral}(\text{tail}(L),\ I_0)_0           & \qquad \text{[By recursive definition for a non-first element]} \\
       &= \text{Integral}([x_1, \dots, x_n],\ I_0)_0        & \qquad \text{[By tail definition]} \\
       &= \text{head}([x_1, \dots, x_n]) + I_0              & \qquad \text{[By recursive Integral definition for the first element]} \\
       &= x_1 + I_0                                         & \qquad \text{[By head definition]} \\
I_1 - I_0 &= (x_1 + I_0) - I_0                              & \qquad \text{[Substituting for } I_1, I_0] \\
          &= x_1 + I_0 - I_0                                 & \qquad \text{[Distributivity]} \\
          &= x_1                                             & \qquad \text{[Cancellation of terms]} \\
          & \therefore \\
I_1 - I_0 &= x_1                                            & \qquad \text{[Q.E.D.]} \\
\end{aligned}
$$

#### Proof of the Inductive Step $I_{p+1} - I_p = L_{p+1}$

$$
\begin{aligned}
L &= x_0 :: \text{tail}(L)                                                                                     & \qquad \text{[List decomposition]} \\
I &= I_0 :: \text{tail}(I)                                                                                     & \qquad \text{[Integral decomposition]} \\
I_{p+1} &= I_{\text{tail},\ p}                                                             & \qquad \text{[By indexing: tail of } I \text{ at position } p] \\
I_{p+2} &= I_{\text{tail},\ p+1}                                                           & \qquad \text{[By indexing: tail of } I \text{ at position } p + 1] \\
I_{\text{tail},\ p+1} &= L_{\text{tail},\ p+1} + I_{\text{tail},\ p}                       & \qquad \text{[By recursive definition of Integral]} \\
I_{p+2} - I_{p+1} &= I_{\text{tail},\ p+1} - I_{\text{tail},\ p}                           & \qquad \text{[Substituting for } I_{p+2}, I_{p+1}] \\
                   &= (L_{\text{tail},\ p+1} + I_{\text{tail},\ p}) - I_{\text{tail},\ p}   & \qquad \text{[Substituting for } I_{\text{tail},\ p+1}] \\
                   &= L_{\text{tail},\ p+1}                                                 & \qquad \text{[Cancellation of terms]} \\
L_{p+2} &= L_{\text{tail},\ p+1}                                                           & \qquad \text{[By indexing: tail of } L \text{ at position } p + 1] \\
& \therefore \\
I_{p+2} - I_{p+1} &= L_{p+2} \quad \blacksquare                                            & \qquad \text{[Q.E.D.]} \\
\end{aligned}
$$

This property is verified in the [
  IntegralProperties::assertAccDiffMatchesList
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/integral/properties/IntegralProperties.scala). The full Scala verification code is in Appendix A.3.

### 4.4 Final Element Equals Full Sum

The last element of the Integral equals the sum of all elements in the List plus the initial value.

$$
I_{n-1} = init + \sum_{i=0}^{n-1} x_i
$$

This follows directly from [Section 4.2](#42-integral-equals-sum-until-position), which proves $I_k = init + \sum_{i=0}^{k} x_i$ for all $k$:

$$
k = n - 1 \implies I_{n-1} = init + \sum_{i=0}^{n-1} x_i \\
\therefore \\
I_{n-1} = init + \sum_{i=0}^{n-1} x_i \quad \blacksquare
$$

This property is verified in the [
  IntegralProperties::assertLastEqualsSum
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/integral/properties/IntegralProperties.scala). The full Scala verification code is in Appendix A.4.

### 4.5 Strictly Increasing Integral

When every value in the list is positive, the integral is strictly increasing:
a later position always produces a larger value. This is the monotonicity
theorem — the integral grows with every step.

```math
\begin{aligned}
(\forall x \in L,\ x > 0) \;\land\; b > a \;\implies\; I_b > I_a
  \quad \text{[Q.E.D.]}
\end{aligned}
```

**Proof.** By induction on $b - a$. Base case $b = a + 1$: §4.3 gives
$I_{a+1} - I_a = L_{a+1} > 0$. Inductive step: $I_b > I_{b-1} > I_a$ by
transitivity.

### Stainless Verification

```scala
def assertIntegralStrictlyIncreasing(
  integral: Integral, a: BigInt, b: BigInt
): Boolean = {
  require(a >= 0); require(b > a); require(b < integral.list.size)
  require(ListBoundUtils.allGreaterThan(integral.list, BigInt(0)))
  integral.apply(b) > integral.apply(a)
}.holds
```

This property is verified in the [
  IntegralProperties::assertIntegralStrictlyIncreasing
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/integral/properties/IntegralProperties.scala).

### 4.6 Gaps Positivity

If the integral increases between consecutive positions, the corresponding
list element is positive. The gap (difference between adjacent integral values)
has the same sign as the underlying list element.

```math
\begin{aligned}
I_{p+1} > I_p \;\implies\; L_{p+1} > 0
  \quad \text{[Q.E.D.]}
\end{aligned}
```

**Proof.** By §4.3, $I_{p+1} - I_p = L_{p+1}$. If $I_{p+1} > I_p$, the
difference is strictly positive, so $L_{p+1} > 0$.

### Stainless Verification

```scala
def assertGapsPositive(integral: Integral, pos: BigInt): Boolean = {
  require(pos >= 0); require(pos + 1 < integral.list.size)
  require(integral.apply(pos + 1) > integral.apply(pos))
  integral.list(pos + 1) > BigInt(0)
}.holds
```

This property is verified in the [
  IntegralProperties::assertGapsPositive
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/integral/properties/IntegralProperties.scala).

## 5. Implementation Consistency Lemmas

These lemmas verify that the recursive implementation and its accumulated representation agree internally. They do not introduce new mathematical properties but are essential for formal software consistency.

- Element consistency: $I_k = acc_k$ — §5.2
- Accumulated delta consistency: $acc_{p+1} - acc_p = L_{p+1}$ — §5.3
- Last element agreement: $\text{last}(I) = acc_{n-1} = I_{n-1}$ — §5.4
- Size agreement: $|acc| = |L|$ — §5.5

### 5.1 Accumulated List Definition

The accumulated list represents the discrete integral as a full list of partial sums rather than element-by-element access.

Let:

$$
\begin{aligned}
& acc(L, init) \in \mathbb{Z}^{|L|} \\
& L = [x_0, x_1, \dots, x_{n-1}]
\end{aligned}
$$

Then, the accumulated list is defined recursively as:

$$
acc(L, init) =
\begin{cases}
L_e & \text{if } L = L_e \\
(\text{head}(L) + init) :: acc(\text{tail}(L),\ \text{head}(L) + init) & \text{otherwise}
\end{cases}
$$

The full Integral implementation including the `acc` method is at [Integral.scala](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/integral/Integral.scala):

```scala
case class Integral(list: List[BigInt], init: BigInt = 0) {
  def apply(position: BigInt): BigInt = {
    require(list.nonEmpty)
    require(position >= 0 && position < list.size)
    if (position == 0) this.head else Integral(list.tail, this.head).apply(position - 1)
  }
  def acc: List[BigInt] = {
    decreases(list.size)
    if (list.isEmpty) list else List(this.head) ++ Integral(list.tail, this.head).acc
  }
  def head: BigInt = {
    require(list.nonEmpty)
    list.head + init
  }
  def tail: List[BigInt] = {
    require(list.nonEmpty)
    Integral(list.tail, this.head).acc
  }
  def last: BigInt = {
    require(list.nonEmpty)
    acc.last
  }
}
```

### 5.2 Element Consistency

The $k\text{-th}$ element of the Integral equals the $k\text{-th}$ element of the accumulated list.

$$
\forall \text{ } k \in [0, n-1]:\ I_k = acc_k
$$

```math
\begin{aligned}
&L &= x_0 :: \text{tail}(L)                                                           & \qquad \text{[List decomposition]} \\
&I &= (x_0 + i) :: \text{tail}(I)                                                     & \qquad \text{[Integral decomposition]} \\
&\text{acc}(L, i) &= (x_0 + i) :: \text{acc}(\text{tail}(L),(x_0 + i))                & \qquad \text{[Definition of } \text{acc}] \\
&I_0 &= x_0 + i = \text{acc}_0                                                        & \qquad \text{[Base case]} \\
&I_{(p+1)} &= \text{tail}(I)_p                                                        & \qquad \text{[Tail Access Shift Left]} \\
&\text{acc}_{(p+1)} &= \text{acc}(\text{tail}(L),(x_0 + i))_p                         & \qquad \text{[Recursive accumulation]} \\
&\text{tail}(L)_p &= \text{acc}(\text{tail}(L), (x_0 + i))_p                          & \qquad \text{[Inductive hypothesis]} \\
&\implies \quad I_{p+1} &= \text{acc}_{p+1}                                           & \qquad \text{[By substitution]} \\
&& \therefore \\
&\forall p \in [0..n-1], \quad I_p &= \text{acc}_p \quad \blacksquare                 & \qquad \text{[Q.E.D.]}
\end{aligned}
```

This property is verified in the [
  IntegralProperties::assertAccMatchesApply
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/integral/properties/IntegralProperties.scala). The full Scala verification code is in Appendix A.5.

### 5.3 Accumulated Delta Consistency

The difference between two consecutive accumulated values in Acc equals the corresponding value from the original list.

$$
\forall\ p \in [0, n-2]:\ \text{acc}_{p+1} - \text{acc}_p = L_{p+1}
$$

```math
\begin{aligned}
&L &= [x_0, x_1, \dots, x_{n-1} ]                                                           & \qquad \text{[List definition]} \\
&L &= x_0 :: \text{tail}(L)                                                                 & \qquad \text{[List decomposition]} \\
&\text{acc}(L, i) &= (x_0 + i) :: \text{acc}(\text{tail}(L), x_0 + i)                       & \qquad \text{[Definition of acc]} \\
&\text{acc}_0 &= x_0 + i                                                                    & \qquad \text{[Base case]} \\
&\text{acc}_1 &= x_1 + \text{acc}_0                                                         & \qquad \text{[Recursive accumulation]} \\
&\implies \quad \text{acc}_1 - \text{acc}_0 &= x_1 = L_1                                    & \qquad \text{[Cancellation]} \\
&\text{acc}_{p+1} &= x_{p+1} + \text{acc}_p                                                 & \qquad \text{[Recursive accumulation]} \\
&\implies \quad \text{acc}_{p+1} - \text{acc}_p &= x_{p+1} = L_{p+1}                        & \qquad \text{[By subtraction]} \\
\end{aligned}
```
```math
\therefore
```
```math
\begin{aligned}
\forall p \in [0..n-2],\quad \text{acc}_{p+1} - \text{acc}_p &= L_{p+1} \quad \blacksquare & \qquad \text{[Q.E.D.]}
\end{aligned}
```

This property is verified in the [
  IntegralProperties::assertAccDiffMatchesList
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/integral/properties/IntegralProperties.scala). The full Scala verification code is in Appendix A.6.

### 5.4 Last Element Agreement

The last element of the accumulated list equals the last element of the integral, which is the element at position $n-1$.

$$
\begin{aligned}
acc_{(n - 1)} & = \text{last}(I) \\
acc_{(n - 1)} & = I_{(n - 1)} \\
\end{aligned}
$$

```math
\begin{aligned}
&L &= [x_0, x_1, \dots, x_{n-1}]                                               & \qquad \text{[List definition]} \\
&\text{last}(L) &= \begin{cases}
&x_0 & \text{if } |L| = 1 \\
&\text{last}(\text{tail}(L)) & \text{if } |L| > 1
\end{cases}                                                                 & \qquad \text{[Definition of last]} \\
&\text{acc}(L, i) &= (x_0 + i) :: \text{acc}(\text{tail}(L), x_0 + i)        & \qquad \text{[Definition of accumulation]} \\
&I &= \text{acc}(L, i)                                                       & \qquad \text{[Integral as accumulated list]} \\
\end{aligned}
```

#### Base case: $|L| = 1$

```math
\begin{aligned}
&L &= [x_0]                                                                   & \qquad \text{[Singleton list]} \\
&\text{acc}(L, i) &= [x_0 + i]                                                & \qquad \text{[By definition]} \\
&I &= [x_0 + i]                                                               & \qquad \text{[Integral is acc]} \\
&\text{last}(I) &= x_0 + i = acc_0 = I_0                                      & \qquad \text{[last on singleton]} \\
\end{aligned}
```

#### Inductive step: $|L| > 1$

```math
\begin{aligned}
&L &= x_0 :: \text{tail}(L)                                                   & \qquad \text{[List decomposition]} \\
&I &= (x_0 + i) :: \text{acc}(\text{tail}(L), x_0 + i)                        & \qquad \text{[Recursive definition]} \\
&\text{tail}(I) &= \text{acc}(\text{tail}(L), x_0 + i)                        & \qquad \text{[Tail of integral]} \\
&\text{last}(I) &= \text{last}(\text{tail}(I))                                & \qquad \text{[Recursive last]} \\
&\text{last}(\text{tail}(I)) &= \text{acc}(\text{tail}(L), x_0 + i)_{(n - 2)} & \qquad \text{[Inductive hypothesis]} \\
& &= acc_{(n - 1)}                                                            & \qquad \text{[Shifted indexing]} \\
&\implies \ \text{last}(I) &= acc_{(n - 1)} = I_{(n - 1)}                     & \qquad \text{[By substitution]} \\
\end{aligned}
```
```math
\therefore
```
```math
\begin{aligned}
\text{last}(I) &= acc_{(n - 1)} = I_{(n - 1)} \quad \blacksquare              & \qquad \text{[Q.E.D.]}
\end{aligned}
```

This property is verified in the [
  IntegralProperties::assertLast
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/integral/properties/IntegralProperties.scala). The full Scala verification code is in Appendix A.7.

### 5.5 Size Agreement

The size of the accumulated list equals the size of the original list.

$$
|acc| = |L|
$$

```math
\begin{aligned}
&L &= [x_0, x_1, \dots, x_{n-1}]                                           & \qquad \text{[List definition]} \\
&\text{acc}(L, i) &= (x_0 + i) :: \text{acc}(\text{tail}(L), x_0 + i)      & \qquad \text{[Recursive accumulation]} \\
\end{aligned}
```

#### Empty List: $|L| = 0$

```math
\begin{aligned}
&L &= []                                                                  & \qquad \text{[Empty list]} \\
&\text{acc}(L, i) &= []                                                   & \qquad \text{[By definition]} \\
&|\text{acc}(L, i)| &= 0 = |L|                                            & \qquad \text{[Equal size]} \\
\end{aligned}
```

#### Singleton List: $|L| = 1$

```math
\begin{aligned}
&L &= [x_0]                                                               & \qquad \text{[Singleton list]} \\
&\text{acc}(L, i) &= [x_0 + i]                                            & \qquad \text{[By definition]} \\
&|\text{acc}(L, i)| &= 1 = |L|                                            & \qquad \text{[Equal size]} \\
\end{aligned}
```

#### Inductive step: $|L| > 1$

```math
\begin{aligned}
&L &= x_0 :: \text{tail}(L)                                               & \qquad \text{[Decomposition]} \\
&\text{acc}(L, i) &= (x_0 + i) :: \text{acc}(\text{tail}(L), x_0 + i)     & \qquad \text{[Recursive call]} \\
&|\text{acc}(\text{tail}(L), x_0 + i)| &= |\text{tail}(L)|                & \qquad \text{[Inductive hypothesis]} \\
&|\text{acc}(L, i)| &= 1 + |\text{tail}(L)| = |L|                         & \qquad \text{[Cons adds 1]} \\
& & \therefore \\
&|\text{acc}(L, i)| &= |L| \quad \blacksquare                             & \qquad \text{[Q.E.D.]}
\end{aligned}
```

This property is verified in the [
  IntegralProperties::assertSizeAccEqualsSizeList
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/integral/properties/IntegralProperties.scala). The full Scala verification code is in Appendix A.8.

## 6. Limitations

This article builds upon the foundational assumptions and constraints established in the earlier work
[Using Formal Verification to Prove Properties of Lists Recursively Defined](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter3/list.md) [[1]](#ref1).

Specifically:

* The focus remains on lists of unbounded integers (`BigInt`), without support for generalized numeric types via abstraction or type classes.
* Recursive functions such as $sum$, $head$, $tail$, and concatenation are reused from the prior work [[1]](#ref1) and are not redefined here.
* Due to the recursive nature of these definitions, stack overflows may occur with extensive lists, but correctness and verifiability take priority over performance.

## 7. Conclusion

This article formally defined and verified the discrete integral operation over finite integer lists using a zero-prior-knowledge methodology.

From the recursive definition of $I = \text{Integral}(L, init)$, we proved and verified:

```math
\begin{aligned}
I_0 &= x_0 + init & \text{[Head Value Matches Definition]} \\
I_k &= init + \sum_{i=0}^k x_i & \text{[Integral Equals Sum Until Position]} \\
I_{n-1} &= init + \sum_{i=0}^{n-1} x_i & \text{[Final Element Equals Full Sum]} \\
I_{p+1} - I_p &= x_{p+1} & \text{[Incremental Change Matches List]} \\
I_k &= acc_k & \text{[Element Consistency]} \\
\text{last}(I) &= acc_{n-1} = I_{n-1} & \text{[Last Element Agreement]} \\
acc_{p+1} - acc_p &= x_{p+1} & \text{[Accumulated Delta Consistency]} \\
|acc| &= |L| & \text{[Size Agreement]} \\
(\forall x \in L,\ x > 0) \;\land\; b > a &\implies I_b > I_a & \text{[Strictly Increasing]} \\
I_{p+1} > I_p &\implies L_{p+1} > 0 & \text{[Gaps Positivity]} \\
\end{aligned}
```

These results establish that the recursive discrete integral exactly corresponds to the cumulative sum of list elements plus the given initial value. The integral is strictly increasing when the list values are positive, and a positive gap between consecutive integral values implies the underlying list element is positive. The construction preserves list length, and the differences between consecutive integral elements recover the original list entries, confirming the correctness of the accumulation process.

All properties were formally verified in Scala using the Stainless verification system. The full verification code is in Appendix A.

## 8. Future Work

Extending the finite integral to repeating sequences of values would capture the relationship between modular arithmetic and 
gap-period decomposition — the foundation for reasoning about cumulative sums over cyclic structures.

## 9. References

<a name="ref1" id="ref1" href="#ref1">[1]</a>  
Mata, T. H. (2026). *Using Formal Verification to Prove Properties of Lists Recursively Defined*. Unpublished manuscript.  
Available at: [https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter3/list.md](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter3/list.md)

## Appendix A: Scala Verification Code

### A.1 Head Value Matches Definition — assertHeadValueMatchDefinition

Source: [IntegralProperties::assertHeadValueMatchDefinition](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/integral/properties/IntegralProperties.scala)

```scala
def assertHeadValueMatchDefinition(integral: Integral): Boolean = {
  require(integral.list.nonEmpty)
  assert(integral.head == integral.list.head + integral.init)
  assert(integral.apply(0) == integral.head)
  assert(integral.acc(0) == integral.head)
  assert(integral.acc(0) == integral.apply(0))
  integral.head == integral.list.head + integral.init
}.holds
```

### A.2 Integral Equals Sum Until Position — assertIntegralEqualsSum

Source: [IntegralProperties::assertIntegralEqualsSum](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/integral/properties/IntegralProperties.scala)

```scala
def assertIntegralEqualsSum(integral: Integral, position: BigInt): Boolean = {
  require(integral.list.nonEmpty)
  require(position >= 0 && position < integral.list.size)
  require(integral.list.size > 1)
  decreases(position)

  assert(assertSizeAccEqualsSizeList(integral.list, integral.init))

  if (position == 0) {
    // base case
    assert(assertHeadValueMatchDefinition(integral))
    assert(ListUtils.slice(integral.list, 0, position) == List(integral.list.head))
    assert(integral.apply(0) == integral.init + ListUtils.sum(List(integral.list.head)))
    assert(integral.apply(0) == integral.init + ListUtils.sum(ListUtils.slice(integral.list, 0, position)))
  } else {
    // Inductive step
    assert(assertIntegralEqualsSum(integral, position - 1))
    assert(position > 0)
    assert(position < integral.list.size)
    assert(position - 1 < integral.list.size - 1)
    assert(integral.list.size == integral.acc.size)
    assert(integral.list.size > 1)
    assert(assertAccDiffMatchesList(integral, position - 1))

    val prevList = ListUtils.slice(integral.list, 0, position - 1)
    val prevSum = ListUtils.sum(prevList)
    assert(integral.apply(position - 1) == integral.init + prevSum)
    assert(integral.apply(position) == integral.apply(position - 1) + integral.list(position))
    assert(integral.apply(position) == integral.init + prevSum + integral.list(position))
    assert(ListUtils.listSumAddValue(integral.list, integral.list(position)))
    assert(ListUtilsProperties.assertAppendToSlice(integral.list, 0, position))
    assert(ListUtils.slice(integral.list, 0, position) == ListUtils.slice(integral.list, 0, position - 1) ++ List(integral.list(position)))
    assert(integral.apply(position) == integral.init + ListUtils.sum(ListUtils.slice(integral.list, 0, position)))
  }
  integral.apply(position) == integral.init + ListUtils.sum(ListUtils.slice(integral.list, 0, position))
}.holds
```

### A.3 Incremental Change — assertAccDiffMatchesList

Source: [IntegralProperties::assertAccDiffMatchesList](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/integral/properties/IntegralProperties.scala)

```scala
def assertAccDiffMatchesList(integral: Integral, position: BigInt): Boolean = {
  require(integral.list.size > 1)
  require(position >= 0 && position < integral.list.size - 1)
  decreases(position)

  if (position == 0) {
    // base case
    assert(IntegralProperties.assertAccDifferenceEqualsTailHead(integral))
    assert(integral.apply(0) == integral.acc(0))
    assert(integral.apply(1) == integral.acc(1))
    assert(
      integral.acc(position + 1) - integral.acc(position) == integral.list(position + 1) &&
        integral.acc(position) == integral.apply(position)
    )
  } else {
    assert(position > 0)
    assert(position < integral.list.size - 1)
    assert(position - 1 < integral.list.size)

    // Inductive step
    val next = Integral(integral.list.tail, integral.head)
    assert(next.size == integral.size - 1)
    assert(integral.tail == next.acc)
    assert(assertAccDiffMatchesList(next, position - 1))

    // link this values and next values
    assert(integral.apply(position)     == next.apply(position - 1))
    assert(integral.apply(position + 1) == next.apply(position))

    assert(integral.apply(position) == integral.acc(position))
    assert(integral.apply(position + 1) == integral.acc(position + 1))
  }
  integral.acc(position + 1) - integral.acc(position) == integral.list(position + 1) &&
    integral.acc(position + 1) == integral.apply(position + 1) &&
    integral.acc(position) == integral.apply(position)
}.holds
```

### A.4 Final Element Equals Full Sum — assertLastEqualsSum

Source: [IntegralProperties::assertLastEqualsSum](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/integral/properties/IntegralProperties.scala)

```scala
def assertLastEqualsSum(integral: Integral): Boolean = {
  require(integral.list.nonEmpty)
  decreases(integral.list.size)

  if (integral.list.size == 1) {
    // base case
    assert(integral.last == integral.list.head + integral.init)
    assert(integral.last == integral.init + ListUtils.sum(integral.list))
  } else {
    // inductive step
    val next = Integral(integral.list.tail, integral.list.head + integral.init)
    assert(assertLastEqualsSum(next))
    assert(integral.tail == next.acc)
    assert(integral.tail.last == next.acc.last)
    assert(next.last == next.acc.last)
    assert(next.last == integral.last)
    assert(next.last == next.init + ListUtils.sum(next.list))
    assert(next.last == integral.init + integral.list.head + ListUtils.sum(next.list))
    assert(integral.last == integral.init + integral.list.head + ListUtils.sum(next.list))
    assert(ListUtils.listSumAddValue(next.list, integral.list.head))
    assert(integral.list.head + ListUtils.sum(next.list) == ListUtils.sum(List(integral.list.head) ++ integral.list.tail))
    assert(integral.list.head + ListUtils.sum(next.list) == ListUtils.sum(integral.list))
    assert(integral.last == integral.init + ListUtils.sum(integral.list))
  }
  integral.last == integral.init + ListUtils.sum(integral.list)
}.holds
```

### A.5 Element Consistency — assertAccMatchesApply

Source: [IntegralProperties::assertAccMatchesApply](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/integral/properties/IntegralProperties.scala)

```scala
def assertAccMatchesApply(integral: Integral, position: BigInt): Boolean = {
  require(integral.list.nonEmpty)
  require(position >= 0 && position < integral.list.size)
  decreases(position)

  assert(assertSizeAccEqualsSizeList(integral.list, integral.init))
  assert(integral.list.size == integral.acc.size)

  if (position == 0) {
    // base case
    assert(integral.apply(0) == integral.head)
    assert(integral.acc(0) == integral.head)
    integral.acc(position) == integral.apply(position)
  } else {
    // Inductive step
    assert(position > 0)
    assert(position < integral.list.size)
    assert(position - 1 < integral.list.size - 1)

    val next = Integral(integral.list.tail, integral.head)
    assert(integral.tail == next.acc)

    assert(integral.apply(position) == next.apply(position - 1))
    assert(integral.acc == List(integral.head) ++ next.acc)
    assert(integral.acc.tail == next.acc)

    assert(integral.acc.nonEmpty)
    assert(integral.list.size == integral.acc.size)
    assert(position < integral.acc.size)
    assert(ListBoundUtils.assertTailShiftLeft(integral.acc, position))
    assert(integral.acc.tail(position - 1) == integral.acc(position))
    assert(integral.acc(position) == integral.acc.tail(position - 1))
    assert(integral.acc.tail(position - 1) == next.acc(position - 1))

    assert(integral.acc(position) == next.acc(position - 1))
    assert(integral.apply(position) == next.apply(position - 1))

    assert(assertAccMatchesApply(next, position - 1))
    assert(next.acc(position - 1) == next.apply(position - 1))
    assert(integral.acc(position) == integral.apply(position))
  }
  integral.acc(position) == integral.apply(position)
}.holds
```

### A.6 Accumulated Delta Consistency — assertAccDiffMatchesList

Source: [IntegralProperties::assertAccDiffMatchesList](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/integral/properties/IntegralProperties.scala)

This is the same function as Appendix A.3. The property is used for both the `apply`-based delta (Section 4.3) and the `acc`-based delta (Section 5.3).

### A.7 Last Element Agreement — assertLast

Source: [IntegralProperties::assertLast](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/integral/properties/IntegralProperties.scala)

```scala
def assertLast(integral: Integral): Boolean = {
  require(integral.list.nonEmpty)
  assert(
    integral.last ==
      integral.acc.last
  )
  assert(ListUtilsProperties.assertLastEqualsLastPosition(integral.acc))
  assert(assertSizeAccEqualsSizeList(integral.list, integral.init))
  assert(
    integral.acc.last ==
      integral.acc(integral.acc.size - 1)
  )
  assertAccMatchesApply(integral, integral.size - 1)
  assert(
    integral.acc(integral.size - 1) ==
      integral.apply(integral.size - 1)
  )
  integral.apply(integral.size - 1) == integral.last
}.holds
```

### A.8 Size Agreement — assertSizeAccEqualsSizeList

Source: [IntegralProperties::assertSizeAccEqualsSizeList](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter3/list/integral/properties/IntegralProperties.scala)

```scala
def assertSizeAccEqualsSizeList(list: List[BigInt], init: BigInt = 0): Boolean = {
  decreases(list)

  val current = Integral(list, init)

  if (list.isEmpty) {
    // base case for empty list
    assert(current.list.size == 0)
    assert(current.acc.size == 0)
  }
  else if (list.size == 1) {
    // base case for single element list
    assert(current.list.size == 1)
    assert(current.acc.size == 1)
    assert(current.acc.size == current.list.size)
  } else {
    // inductive step for lists with more than one element
    val next = Integral(list.tail, current.head)

    assertSizeAccEqualsSizeList(next.list, next.init)
    assert(next.acc.size == next.list.size)
    assert(current.acc == List(current.head) ++ next.acc)
    assert(current.acc.size == 1 + next.acc.size)
    assert(1 + list.tail.size == list.size)
  }
  current.acc.size == current.list.size
}.holds
```

## Appendix B: Stainless Verification Log Output

The latest `just verify` run verifies all the described properties without errors. The full log output is available at: [logs/verify.log](https://github.com/thiagomata/prime-numbers/blob/master/logs/verify.log)
