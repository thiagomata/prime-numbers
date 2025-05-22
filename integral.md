# Formal Verification of Discrete Integration Properties from First Principles

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

## 2. Preliminaries and Notation

Let $L = [x_0, x_1, \dots, x_{n-1}] \in \mathbb{Z}^n$ be a finite, non-empty list of $n$ integers, where $n = |L|$,
and let $\text{init} \in \mathbb{Z}$ be an initial value.

We reuse several basic list operations and their verified properties from a companion article on recursive list construction [[1]](lists.md).  
These include the following functions:

- $\text{sum}(L)$: recursively computes the total sum of elements in a list.
- $\text{head}(L)$: returns the first element of a non-empty list.
- $\text{tail}(L)$: returns the list without its first element.
- $A$ &#x29FA; $B$: concatenates two lists $A$ and $B$.

These operations were defined and verified using the same zero-prior-knowledge methodology [[1]](lists.md), and are treated here as foundational primitives.

Proofs in this article are written in Scala and verified using the Stainless system, with 
`BigInt` used to represent unbounded integers.

## 3. Definition of Discrete Integral

We define the **discrete integral** $I = Integral(L, \text{init})$ as a list of partial sums such that:

$$
\begin{aligned}
\text{for } k \in [0, n - 1] \\
I_{k} = \text{init} + \sum_{i=0}^{k} L_i \\
\end{aligned}
$$
## 4. Recursive Definition


We also rely on the following notation:

$$
\begin{aligned}
I &= \text{Integral}(L, \text{init}) \\
n &= |L| \\
k &\in [0, n - 1]
\end{aligned}
$$

The value of the $k\text{-th}$ element in the integral $I$ is defined recursively as:

$$
I_k =
\begin{cases}
L_0 + \text{init} & \text{if } k = 0 \\
\text{Integral}(\text{tail}(L),\ \text{head}(L) + \text{init})_{(k - 1)} & \text{if } k > 0
\end{cases}
$$


In Scala, this is encoded as:
```scala
case class Integral(list: List[BigInt], init: BigInt = 0) {
  def apply(position: BigInt): BigInt = {
	require(list.nonEmpty)
	require(position >= 0 && position < list.size)
	if ( position == 0 ) this.head else Integral(list.tail, this.head).apply(position - 1)
  }
  def head: BigInt = {
	require(list.nonEmpty)
	list.head + init
  }
  // ... unrelated methods ommited
}
```
Defined at [Integral.scala](./src//main/scala/v1/list/integral/Integral.scala#L6).

## 4. Verified Properties

We formally verify the following mathematical and implementation-specific properties:

### 4.1 Head Value Matches Definition

Lemma: The first element of the integral is equal to the first element of the original
list plus the initial value.

$$
I_0 = x_0 + \text{init}
$$

Proved in [IntegralProperties.scala at assertHeadValueMatchDefinition](./src//main/scala/v1/list/integral/properties/IntegralProperties.scala#assertHeadValueMatchDefinition).

```scala
/**
 * Lemma: The first element of the accumulated list `acc` is equal to the
 * first element of the original list `list` plus the initial value.
 *
 * That is:
 * acc(0) == list(0) + init
 *
 * @param integral Integral the integral of the lemma
 * @return Boolean true if the property holds
 */
def assertHeadValueMatchDefinition(integral: Integral): Boolean = {
  require(integral.list.nonEmpty)
  
  // ...
  
  integral.head == integral.list.head + integral.init
}.holds
```

### 4.2 Step Increment Matches List Value

Lemma: The difference between two consecutive accumulated values in Acc
equals the corresponding value from the original list.

$$
\forall \text{ } k \in [1, n-1]:\ I_k = I_{k-1} + x_k
$$

Proved in [IntegralProperties.scala at assertAccDiffMatchesList](./src//main/scala/v1/list/integral/properties/IntegralProperties.scala#assertAccDiffMatchesList).

```scala
  /**
   * Lemma: The difference between two consecutive accumulated values in Acc
   * equals the corresponding value from the original list.
   *
   * That is:
   * acc(position + 1) - acc(position) == list(position + 1)
   *
   * Holds for all valid `position` where 0 <= position < list.size - 1.
   * @param integral Integral the integral of the lemma
   * @param position BigInt the position in the acc list
   * @return Boolean true if the property holds
   */
  def assertAccDiffMatchesList(integral: Integral, position: BigInt): Boolean = {
    require(integral.list.size > 1)
    require(position >= 0 && position < integral.list.size - 1)
    decreases(position)
    
    // ...
    
    integral.acc(position + 1) - integral.acc(position) == integral.list(position + 1) &&
      integral.acc(position + 1) == integral.apply(position + 1) &&
      integral.acc(position) == integral.apply(position)
  }
```

### 4.3 Integral Equals Sum Until Position

Lemma: The integral at position $k$ is equal to the sum of all
elements in the list up to that position, plus the initial value.

$$
\forall \text{ } k \in [0, n-1]:\ I_k = \text{init} + \sum_{i=0}^{k} x_i
$$

Proved in [IntegralProperties.scala at assertIntegralEqualsSum](./src//main/scala/v1/list/integral/properties/IntegralProperties.scala#assertIntegralEqualsSum).

```scala
/**
 * The integral of a list is defined as the sum of all elements in the list
 * plus the initial value.
 *
 * That is:
 * integral.apply(position) == init + ListUtils.sum(list[0..position])
 *
 * @param integral Integral the integral of the lemma
 * @param position BigInt the position in the list
 * @return Boolean true if the property holds
 */
  def assertIntegralEqualsSum(integral: Integral, position: BigInt): Boolean = {
    require(integral.list.nonEmpty)
    require(position >= 0 && position < integral.list.size)
    require(integral.list.size > 1)
    decreases(position)

    // ...

    integral.apply(position) == integral.init + ListUtils.sum(ListUtils.slice(integral.list, 0, position))
  }.holds
````

### 4.4 Final Element Equals Full Sum

Lemma: The last element of the integral is 
equal to the sum of all elements in the list plus the initial value.

$$
I_{n-1} = \text{init} + \sum_{i=0}^{n-1} x_i
$$

Proved in [IntegralProperties.scala at assertLastEqualsSum](./src//main/scala/v1/list/integral/properties/IntegralProperties.scala#assertLastEqualsSum).

```scala
/**
   * Lemma: The last element of the accumulated list `acc` is equal to the sum
   * of all elements in the original list `list`.
   *
   * That is:
   * acc.last == init + ListUtils.sum(list)
   *
   * @param integral Integral the integral of the lemma
   * @return Boolean true if the property holds
   */
  def assertLastEqualsSum(integral: Integral): Boolean = {
    require(integral.list.nonEmpty)
    decreases(integral.list.size)
    
    // ...
    
    integral.last == integral.init + ListUtils.sum(integral.list)
  }
```

### 5 Implementation Consistency Lemmas

Although the above define the mathematical behavior of the discrete integral, we also prove the internal consistency of different Scala representations. These lemmas do not introduce new mathematical insights but are essential for formal consistency within verified software.

### 5.1 Define Accumulated List

We now define the accumulated list, which represents the discrete integral as a full list of partial sums rather than element-by-element access.

Let:

$$
\begin{aligned}
& acc(L, \text{init}) \in \mathbb{Z}^{|L|} \\
& L = [x_0, x_1, \dots, x_{n-1}]
\end{aligned}
$$

Then, the accumulated list is defined recursively as:

$$
acc(L, \text{init}) =
\begin{cases}
[] & \text{if } L = [] \\
\text{head}(L) + \text{init} :: acc(\text{tail}(L),\ \text{head}(L) + \text{init}) & \text{otherwise}
\end{cases}
$$

As we can see in the scala code:

```scala
case class Integral(list: List[BigInt], init: BigInt = 0) {
  def apply(position: BigInt): BigInt = {
	require(list.nonEmpty)
	require(position >= 0 && position < list.size)
	if ( position == 0 ) this.head else Integral(list.tail, this.head).apply(position - 1)
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
Defined at [Integral.scala](./src//main/scala/v1/list/integral/Integral.scala#L6).

### 5.2 Element Consistency

Lemma: The $k\text{-th}$ element of the integral is equal to the $k\text{-th}$ element of the accumulated list.

$$
\forall \text{ } k \in [0, n-1]:\ I_k = acc_k
$$

Proved in [IntegralProperties.scala at assertAccMatchesApply](./src//main/scala/v1/list/integral/properties/IntegralProperties.scala#assertAccMatchesApply):


```scala
  /**
 * Lemma: The `apply(position)` method returns the same value as the value at
 * index `position` in the accumulated list `acc`.
 *
 * That is:
 * apply(position) == acc(position)
 *
 * Holds for all valid `position` in the bounds of the list.
 * @param integral Integral the integral of the lemma
 * @param position BigInt the position in the acc list
 * @return Boolean true if the property holds
 */
def assertAccMatchesApply(integral: Integral, position: BigInt): Boolean = {
  require(integral.list.nonEmpty)
  require(position >= 0 && position < integral.list.size)
  decreases(position)
  
  // ...
  
  integral.acc(position) == integral.apply(position)
}.holds
```

#### Delta Consistency

Lemma: The difference between two consecutive accumulated values in Acc
equals the corresponding value from the original list.

$$
\forall \text{ } k \in [0, n-2]:\ acc_{(k+1)} - acc_k = x_{(k+1)} = L_{(k+1)}
$$

Proved in [IntegralProperties.scala at assertAccDiffMatchesList](./src//main/scala/v1/list/integral/properties/IntegralProperties.scala#assertAccDiffMatchesList):

```scala
  /**
 * Lemma: The difference between two consecutive accumulated values in Acc
 * equals the corresponding value from the original list.
 *
 * That is:
 * acc(position + 1) - acc(position) == list(position + 1)
 *
 * Holds for all valid `position` where 0 <= position < list.size - 1.
 * @param integral Integral the integral of the lemma
 * @param position BigInt the position in the acc list
 * @return Boolean true if the property holds
 */
def assertAccDiffMatchesList(integral: Integral, position: BigInt): Boolean = {
  require(integral.list.size > 1)
  require(position >= 0 && position < integral.list.size - 1)
  decreases(position)

  // ...
  
  integral.acc(position + 1) - integral.acc(position) == integral.list(position + 1) &&
    integral.acc(position + 1) == integral.apply(position + 1) &&
    integral.acc(position) == integral.apply(position)
}.holds
```

#### Last Element Agreement

Lemma: The last element of the accumulated list is equal to the last element of the integral.
It also check if the last element of the integral is the element at the last position,  $n - 1$.

$$
\begin{aligned}
acc_{(n - 1)} & = last_{(I)} \\
acc_{(n - 1)} & = I_{(n - 1)} \\
\end{aligned}
$$

Proved in [IntegralProperties.scala at assertLast](./src//main/scala/v1/list/integral/properties/IntegralProperties.scala#assertLast):

```scala
  /**
 * Lemma: The last element of the accumulated list `acc` is equal
 * to apply in the last position (size - 1).
 *
 * That is:
 * integral.acc.last == integral.acc(size - 1)
 *
 * @param integral Integral the integral of the lemma
 * @return Boolean true if the property holds
 */
def assertLast(integral: Integral): Boolean = {
  require(integral.list.nonEmpty)

  // ...
  
  integral.apply(integral.size - 1) == integral.last
}.holds
```

#### List Size Agreement

Lemma: The size of the accumulated list is equal to the size of the original list.

$$
|acc| = |L|
$$

Proved in [IntegralProperties.scala](./src//main/scala/v1/list/integral/properties/IntegralProperties.scala#assertSizeAccEqualsSizeList):

```scala
  /**
   * Lemma: The size of the accumulated list `acc` is equal to the size of the
   * original list `list`.
   *
   * That is:
   * acc.size == list.size
   *
   * @param list List[BigInt] the original list
   * @param init BigInt the initial value for the accumulation
   * @return Boolean true if the property holds
   */
  def assertSizeAccEqualsSizeList(list: List[BigInt], init: BigInt = 0): Boolean = {
    decreases(list)
    
    // ...

    current.acc.size == current.list.size
  }.holds
```

## 5. Limitations

* The current implementation focuses exclusively on lists of unbounded integers (`BigInt`). It does not yet support generalized numeric types via abstraction or type classes.
* While the recursive definitions are mathematically correct, they may lead to stack overflows for very large lists. This work prioritizes correctness and verifiability over performance or scalability.
* The $sum$, $head$, $tail$ and concatenation &#x29FA; functions used here are reused from prior verified work [[1]](list.md) and are not redefined in this article.

## 6. Conclusion

This article defines and verifies a discrete integral operation over finite integer lists using a zero-prior-knowledge approach.
By building on a previously verified list representation, we demonstrate how recursive accumulations can be reasoned about and implemented with full static guarantees.
This continues a growing library of formally verified recursive structures in Scala using Stainless, bridging executable specifications and mathematical clarity.

## 7. Appendix

### On Generalization to Arbitrary Numeric Types

In this article, we focus on lists of `BigInt` to avoid issues of overflow and rounding and to simplify formal reasoning.
Although the discrete integral could theoretically be generalized to other numeric types (e.g., modular integers, rationals, or floats), such generalizations are not verified in this work.

Extending the integral definition to arbitrary numeric types would require defining and proving type-specific properties (e.g., associativity, identity) and encoding them using Scala type classes like `Numeric[T]`.
This direction is left for future work.

### Stainless Execution Output

<pre style="background-color: black; color: white; padding: 10px; font-family: monospace;">
<code style="color:blue">[  Info  ] </code> Finished compiling
<code style="color:blue">[  Info  ] </code> Preprocessing finished
<code style="color:blue">[  Info  ] </code> Inferring measure for sum...
<code style="color:orange">[Warning ] </code> The Z3 native interface is not available. Falling back onto smt-z3.
<code style="color:blue">[  Info  ] </code> Finished lowering the symbols
<code style="color:blue">[  Info  ] </code> Finished generating VCs
<code style="color:blue">[  Info  ] </code> Starting verification...
<code style="color:blue">[  Info  ] </code> Verified: 2781 / 2781
<code style="color:blue">[  Info  ] </code> Done in 61.79s
<code style="color:blue">[  Info  ] </code><code style="color:green">   ┌───────────────────┐</code>
<code style="color:blue">[  Info  ] </code><code style="color:green"> ╔═╡ stainless summary ╞═══════════════════════════════════════════════════════════════════════════╗</code>
<code style="color:blue">[  Info  ] </code><code style="color:green"> ║ └───────────────────┘                                                                           ║</code>
<code style="color:blue">[  Info  ] </code><code style="color:green"> ╟─────────────────────────────────────────────────────────────────────────────────────────────────╢</code>
<code style="color:blue">[  Info  ] </code><code style="color:green"> ║ total: 2781 valid: 2781 (2768 from cache, 13 trivial) invalid: 0    unknown: 0    time:    9.11 ║</code>
<code style="color:blue">[  Info  ] </code><code style="color:green"> ╚═════════════════════════════════════════════════════════════════════════════════════════════════╝</code>
<code style="color:blue">[  Info  ] </code> Verification pipeline summary:
<code style="color:blue">[  Info  ] </code>  @extern, cache, anti-aliasing, return transformation, 
<code style="color:blue">[  Info  ] </code>  imperative elimination, type encoding, choose injection, nativez3, 
<code style="color:blue">[  Info  ] </code>   non-batched
<code style="color:blue">[  Info  ] </code> Shutting down executor service.
</pre>
