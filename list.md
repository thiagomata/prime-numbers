# Proving Properties of Lists and Accumulated Sum using Formal Verification

## Abstract

Lists and summation are fundamental concepts in both mathematics and computer science. 
Whether reasoning about sequences, algorithms, or numerical methods, lists and their 
associated operations—such as summation, slicing, and indexing—play a central role.

This article formalizes and verifies properties of list concatenation and cumulative 
summation using a recursive model. A discrete integral, defined as the accumulated sum 
of a list, is introduced to model cumulative behavior. We use the Scala Stainless 
verification tool to prove lemmas about these structures, demonstrating correctness 
through mathematical reasoning and recursive definitions.

## Introduction

Lists are finite sequences of values that support a wide range of operations in 
functional and declarative programming. When combined with summation, they provide the 
backbone for definitions of sequences, recurrence, accumulation, and integration in the 
discrete domain.

We define and verify mathematical properties over two central concepts:

* The **sum** of a list, implemented recursively
* The **discrete integral** (accumulated sum) over a list

Our approach mirrors traditional recursive definitions but is formally verified 
using [Scala Stainless](https://epfl-lara.github.io/stainless/intro.html), 
ensuring that the properties hold under all inputs within the specified constraints.
These properties use previously proven lemmas and theorems to establish correctness.
In particular, some lemmas defined in the related article
[Proving Properties of Division and Modulo using Formal Verification](
    modulo.md
) are used as building blocks to establish the correctness of the properties 
in this article.

> Formal verification is the act of proving or disproving the correctness of 
> intended algorithms underlying a system with respect to a certain formal 
> specification or property, using formal methods of mathematics.
> [— Wikipedia on Formal Verification](https://en.wikipedia.org/wiki/Formal_verification)


## Limitations

The implementation and verification presented in this article are restricted to immutable, 
finite lists of integers represented using the `stainless.collection.List` data type. 
The focus is on **correctness**, not on performance or scalability. Our summation and accumulation models follow a **recursive definition**, which is faithful 
to mathematical formalism. However, this can introduce performance limitations in practical 
use over very large lists.

In particular:

- **Overflow and memory limits are not modeled**: Since we use `BigInt` and immutable lists, t
he model assumes unbounded integer arithmetic and infinite list capacity. 
This avoids issues like overflow or out-of-memory errors, but it does not reflect the constraints 
imposed by bounded integer types or limited memory in real-world systems.

- **Side-effects are excluded**: All list operations are pure and referentially transparent. 
We do not model mutation, I/O, or performance overhead.

- **No parallelism or laziness**: Unlike streaming libraries or lazy sequences, 
this model is strictly eager and sequential.

These constraints do not affect the **correctness** of the mathematical properties proved in 
this article. However, they may limit the direct applicability of this model in 
performance-critical or side-effectful environments.

Furthermore, the model treats lists and integers as conceptually unbounded, not imposing any 
restrictions on list length or memory space. 
While this allows us to reason about lists of arbitrary size and precision using `BigInt`, 
it abstracts away practical concerns such as stack overflows, memory limitations, or time 
complexity in execution.

These limitations do not invalidate the learnings from this study. 
The focus is on **mathematical properties** and **semantic validity**, not execution efficiency.


## Definitions

### Lists

We define a list as a finite ordered sequence:

```math
\begin{aligned}
L & = [a_0, a_1, \dots, a_{n-1}] \\
\text{ with } n & = |L| \text{ and } \text{ each }  a_i \in \mathbb{Z} \\
\end{aligned} 
```

Key operations:
- $ \text{head}(L) = a_0 $
- $ \text{tail}(L) = [a_1, \dots, a_{n-1}] $
- $ L(i) = a_i $
- $ L \mathbin{+\!\!+} M $: concatenation

These are implemented using the `stainless.collection.List`, a verifiable functional data structure.

### List Summation

The sum of a list is defined recursively:

```math
\text{sum}(L) = 
\begin{cases} \\
0 & 	\text{if } L = [] \\
a_0 + 	\text{sum}(	\text{tail}(L)) & \text{otherwise} \\
\end{cases}
```

In Scala, this is represented by `ListUtils.sum`.

### Discrete Integral

We define the **discrete integral** or **accumulated sum** of a list $ L $ with initial value $ I \in \mathbb{Z} $ as a new list $ A $, where:

```math
A_k = I + \sum_{i=0}^{k} a_i, \quad 	\text{for } 0 \leq k < n
```

This is implemented using the `Integral` class:

```scala
case class Integral(list: List[BigInt], init: BigInt = 0)

case class Integral(list: List[BigInt], init: BigInt = 0) {

  def apply(position: BigInt): BigInt = {
    require(list.nonEmpty)
    require(position >= 0)
    require(position < list.size)
    if (position == 0) {
      this.head
    } else {
      Integral(list.tail, this.head).apply(position - 1)
    }
  }

  def acc: List[BigInt] = {
    decreases(list.size)
    if (list.isEmpty) {
      list
    } else {
      List(this.head) ++ Integral(list.tail, this.head).acc
    }
  }

  def last: BigInt = {
    require(list.nonEmpty)
    acc.last
  }

  def head: BigInt = {
    require(list.nonEmpty)
    list.head + init
  }

  def tail: List[BigInt] = {
    require(list.nonEmpty)
    Integral(list.tail, this.head).acc
  }

  def isEmpty: Boolean = list.isEmpty

  def nonEmpty: Boolean = list.nonEmpty

  def size: BigInt = list.size
}
```

With methods:
- `acc`: returns the accumulated list $ A $
- `apply(k)`: returns the $ k $-th accumulated value
- `last`: returns $ A_{n-1} $, i.e. the total sum
- Verified lemmas that establish consistency and correctness

## Verified Properties

### Concatenation and Summation

#### Left Append Preserves Sum
```math
	\text{sum}([v] \mathbin{+\!\!+} L) = v + 	\text{sum}(L)
```
[Proof](./src/main/scala/v1/list/properties/ListUtilsProperties.scala#listSumAddValue)

#### Sum over Concatenation
```math
	\text{sum}(A \mathbin{+\!\!+} B) = 	\text{sum}(A) + 	\text{sum}(B)
```
[Proof](./src/main/scala/v1/list/properties/ListUtilsProperties.scala#listCombine)

#### Commutativity of Sum over Concatenation
```math
	\text{sum}(A \mathbin{+\!\!+} B) = 	\text{sum}(B \mathbin{+\!\!+} A)
```
[Proof](./src/main/scala/v1/list/properties/ListUtilsProperties.scala#listSwap)

### Slicing and Access

#### Slice Append Consistency
```math
	\text{slice}(L, f, t) = 	\text{slice}(L, f, t-1) \mathbin{+\!\!+} [L(t)]
```
[Proof](./src/main/scala/v1/list/properties/ListUtilsProperties.scala#assertAppendToSlice)

#### Positional Shift in Tail
```math
L(i) = 	\text{tail}(L)(i - 1), \quad i > 0
```
[Proof](./src/main/scala/v1/list/properties/ListUtilsProperties.scala#assertTailShiftPosition)

#### Tail Access Shift
```math
	\text{tail}(L)(i) = L(i + 1)
```
[Proof](./src/main/scala/v1/list/properties/ListUtilsProperties.scala#accessTailShift)

#### Last Element Identity
```math
L.last = L(L.size - 1)
```
[Proof](./src/main/scala/v1/list/properties/ListUtilsProperties.scala#assertLastEqualsLastPosition)

### Properties of the Discrete Integral

#### Base Difference Lemma
```math
A(1) - A(0) = L(1)
```
[Proof](./src/main/scala/v1/list/integral/Integral.scala#assertAccDifferenceEqualsTailHead)

#### General Difference Lemma
```math
A(k + 1) - A(k) = L(k + 1)
```
[Proof](./src/main/scala/v1/list/integral/Integral.scala#assertAccDiffMatchesList)

#### Access Matches Accumulated Value
```math
	\text{apply}(k) = A(k)
```
[Proof](./src/main/scala/v1/list/integral/Integral.scala#assertAccMatchesApply)

#### Accumulated List Length
```math
|A| = |L|
```
[Proof](./src/main/scala/v1/list/integral/Integral.scala#assertSizeAccEqualsSizeList)

#### Final Value is Total Sum
```math
A(n - 1) = I + \sum_{i=0}^{n-1} L(i)
```
[Proof](./src/main/scala/v1/list/integral/Integral.scala#assertLastEqualsSum)

#### Final Value Equals Last Access
```math
	\text{apply}(n - 1) = A(n - 1) = 	\text{last}
```
[Proof](./src/main/scala/v1/list/integral/Integral.scala#assertLast)

## Conclusion

In this article, we defined and verified properties of list concatenation, summation, and cumulative behavior using recursive definitions and the Scala Stainless verification tool.

These results confirm foundational properties such as:
- Associativity and commutativity of sum
- Structural properties of slicing and tailing
- Correctness of discrete accumulation (integral)

By grounding list operations in recursive definitions and verifying them formally, we provide a rigorous mathematical basis for reasoning about sequence-based computations in both theory and practice.