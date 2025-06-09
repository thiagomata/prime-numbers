# Formal Verification of Discrete Integration Properties from First Principles

**Author:** Mata, T. H.
Independent Researcher  
**Email:** [thiago.henrique.mata@email.com](mailto:thiago.mata@email.com)  
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

## 2. Preliminaries and Notation

Let $L = [x_0, x_1, \dots, x_{n-1}] \in \mathbb{Z}^n$ be a finite, non-empty list of $n$ integers, where $n = |L|$,
and let $init \in \mathbb{Z}$ be an initial value.

We reuse several basic list operations and their verified properties from a companion article on recursive list construction &mdash;  [Using Formal Verification to Prove Properties of Lists Recursively Defined]([https://github.com/thiagomata/prime-numbers/blob/master/list.md) [[1]](#ref1).  
These include the following functions:

- $\text{sum}(L)$: recursively computes the total sum of elements in a list.
- $\text{head}(L)$: returns the first element of a non-empty list.
- $\text{tail}(L)$: returns the list without its first element.
- $A$ &#x29FA; $B$: concatenates two lists $A$ and $B$.

These operations were defined and verified using the same zero-prior-knowledge methodology [[1]](#ref1), and are treated here as foundational primitives.

Proofs in this article are written in Scala and verified using the Stainless system with `BigInt` used to represent unbounded integers.

## 3. Definition of Discrete Integral

We define the **discrete integral** $I = Integral(L, init)$ as a list of partial sums such that:

$$
\begin{aligned}
\text{for } k \in [0, n - 1] \\
I_{k} = init + \sum_{i=0}^{k} L_i \\
\end{aligned}
$$

## 4. Recursive Definition


We also rely on the following notation:

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
  // ... unrelated methods omitted
}
```
Defined at [Integral.scala](./src//main/scala/v1/list/integral/Integral.scala#L6).

## 5. Verified Properties

We formally verify the following mathematical and implementation-specific properties:

### 5.1 Head Value Matches Definition

**Lemma:** The first element of the Integral is equal to the first element of the original
list plus the initial value.

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


Also verified in Scala Stainless in [IntegralProperties.scala on assertHeadValueMatchDefinition](./src//main/scala/v1/list/integral/properties/IntegralProperties.scala#assertHeadValueMatchDefinition).

<details>
<summary>Scala Doc</summary>

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
```
</details>

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

### 5.2 Incremental Change Matches List Value

**Lemma:** The difference between two consecutive values in the Integral List equals the corresponding value in the original List $L$.

That is, considering the previously defined List $L$ and Integral $I$:

$$
\begin{aligned}
\forall \text{ } p & \in [0,\ n-2]: \\
I_{p+1} - I_p & = L_{p+1} \\
& \text{where}  \\
n & = |L| & \text{[} n  \text{ is the size of the list } L \text{] } \\
I & = [v_0, v_1, v_2, \dots, v_{n-1} ] & \text{[Integral values can be described as a list of values }  v_{k} \text{]} \\
L & = [x_0, x_1, x_2, \dots, x_{n-1} ] & \text{[List values can be seen as a list of values } x_{k} \text{]} \\
I_{k} & = v_k & \text{[The } k \text{-th element of the integral} I \text{] } \\
L_{k} & = x_k & \text{[The } k \text{-th element of the list} L \text{] } \\
\end{aligned}
$$


#### Proof of the Base Case $I_1 - I_0 = x_1$

$$
\begin{aligned}
I_1    &= \text{Integral}(\text{tail}(L),\ I_0)_0           & \qquad \text{[By recursive definition for a non-first element]} \\
       &= \text{Integral}([x_1, \dots, x_n],\ I_0)_0        & \qquad \text{[By tail definition]} \\
       &= \text{head}([x_1, \dots, x_n]) + I_0              & \qquad \text{[By recursive Integral definition for the first element ]} \\
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
L &= x_0 ⧺ \text{tail}(L)                                                                & \qquad \text{[List decomposition]} \\
I &= v_0 ⧺ \text{tail}(L)                                                                & \qquad \text{[Integral decomposition]} \\
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

This lemma is verified in [IntegralProperties.scala at assertAccDiffMatchesList](./src//main/scala/v1/list/integral/properties/IntegralProperties.scala#assertAccDiffMatchesList).

<details>
<summary>Scala Doc</summary>

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
```
</details>

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
      assert(position > 0 )
      assert(position < integral.list.size - 1)
      assert(position - 1 < integral.list.size )

      // Inductive step
      val next = Integral(integral.list.tail, integral.head)
      assert(next.size == integral.size - 1)
      assert(integral.tail == next.acc)
      assert(assertAccDiffMatchesList(next, position - 1))

      //Link these values and the next values
      assert(integral.apply(position)     == next.apply(position - 1))
      assert(integral.apply(position + 1) == next.apply(position))

      assert(integral.apply(position) == integral.acc(position))
      assert(integral.apply(position + 1) == integral.acc(position + 1))
    }
    
    integral.acc(position + 1) - integral.acc(position) == integral.list(position + 1) &&
      integral.acc(position + 1) == integral.apply(position + 1) &&
      integral.acc(position) == integral.apply(position)
  }
```

### 5.3 Integral Equals Sum Until Position

**Lemma:** The integral at position $k$ is equal to the sum of all
elements in the list up to that position, plus the initial value:

$$
\forall\ k \in [0, n-1]:\ I_k = \mathit{init} + \sum_{i=0}^{k} x_i
$$

---

#### Proof by Induction on $k$

**Base case** $k = 0$:

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

---

**Inductive step:** Assume the property holds for $k-1$:

$$
I_{k-1} = \mathit{init} + \sum_{i=0}^{k-1} x_i \implies I_k = \mathit{init} + \sum_{i=0}^{k} x_i
$$
$$
\begin{aligned}
I_{k-1} & = \mathit{init} + \sum_{i=0}^{k-1} x_i                    \qquad & \text{[By induction]} \\ 
I_k & = I_{k-1} + L_k                                                \qquad & \text{[By definition of integral]} \\
    &= \left(\mathit{init} + \sum_{i=0}^{k-1} x_i\right) + x_k      \qquad & \text{[By induction and } L_k = x_k]  \\
    &= \mathit{init} + \left(\sum_{i=0}^{k-1} x_i + x_k\right)                 & \qquad \text{[Distributivity]} \\
    &= \mathit{init} + \sum_{i=0}^{k} x_i                           \qquad & \text{[By definition of sum]} \\
\end{aligned}
$$
$$ \therefore $$
$$
\begin{aligned}
I_k = \mathit{init} + \sum_{i=0}^{k} x_i \quad \blacksquare \qquad \text{[Q.E.D.]} \\
\end{aligned}
$$

---

This lemma is also verified in [IntegralProperties.scala at `assertIntegralEqualsSum`](./src/main/scala/v1/list/integral/properties/IntegralProperties.scala#assertIntegralEqualsSum):

<details>
<summary>Scala Doc</summary>

```scala
/**
 * The integral of a list is defined as the sum of all elements in the list
 * plus the initial value.
 *
 * That is:
 * integral.apply(position) == init + ListUtils.sum(list[0..position])
 *
 * @param integral the integral instance
 * @param position the list index to check
 * @return true if the property holds at this position
 */
```
</details>

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
    assert(position > 0 )
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
    assert(ListUtilsProperties.listSumAddValue(integral.list, integral.list(position)))
    assert(ListUtilsProperties.assertAppendToSlice(integral.list, 0, position))
    assert(ListUtils.slice(integral.list, 0, position) == ListUtils.slice(integral.list, 0, position - 1) ++ List(integral.list(position)))
    assert(integral.apply(position) == integral.init + ListUtils.sum(ListUtils.slice(integral.list, 0, position)))
  }
  integral.apply(position) == integral.init + ListUtils.sum(ListUtils.slice(integral.list, 0, position))
}.holds
```

### 5.4 Final Element Equals Full Sum

**Lemma:** The last element of the Integral is 
equal to the sum of all elements in the List plus the initial value.

$$
I_{n-1} = init + \sum_{i=0}^{n-1} x_i
$$

This proof is trivial, since at [4.3 Integral Equals Sum Until Position](#43-integral-equals-sum-until-position), we proved that $I_k = init + \sum_{i=0}^{k} x_i$.

$$
k = n - 1 \implies I_{n-1} = init + \sum_{i=0}^{n-1} x_i \\
\therefore \\
I_{n-1} = init + \sum_{i=0}^{n-1} x_i \quad \blacksquare \\
$$


Verified in [IntegralProperties.scala at assertLastEqualsSum](./src//main/scala/v1/list/integral/properties/IntegralProperties.scala#assertLastEqualsSum).

<details>
<summary>Scala Doc</summary>

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
```
</details>

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
    assert(ListUtilsProperties.listSumAddValue(next.list,integral.list.head))
    assert(integral.list.head + ListUtils.sum(next.list) == ListUtils.sum(List(integral.list.head) ++ integral.list.tail))
    assert(integral.list.head + ListUtils.sum(next.list) == ListUtils.sum(integral.list))
    assert(integral.last == integral.init + ListUtils.sum(integral.list))
  }
  integral.last == integral.init + ListUtils.sum(integral.list)
}.holds
```

## 6 Implementation Consistency Lemmas

Although the above defines the mathematical behaviour of the discrete Integral, we also prove the internal consistency of different Scala representations. These lemmas do not introduce new mathematical insights but are essential for formal consistency within verified software.

### 6.1 Define Accumulated List

We now define the accumulated list, which represents the discrete integral as a full list of partial sums rather than element-by-element access.

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
\text{head}(L) + init ⧺ acc(\text{tail}(L),\ \text{head}(L) + init) & \text{otherwise}
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

### 6.2 Element Consistency

**Lemma:** The $k\text{-th}$ element of the Integral is equal to the $k\text{-th}$ element of the accumulated List.

$$
\forall \text{ } k \in [0, n-1]:\ I_k = acc_k
$$

Thank you for the clarification. Based on your provided formal style, here is the revised and consistent proof that

$$
\forall p \in [0, n - 1]:\ I_p = \text{acc}_p
$$

where $I_p$ is defined via the `apply` logic and $\text{acc}_p$ is the accumulated value at position $p$.

---

### 6.3 Integral-Accumulation Equivalence

**Lemma:** The $p\text{-th}$ element of the Integral equals the $p\text{-th}$ element of the accumulated list.

$$
\forall \text{ } p \in [0, n-1]:\ I_p = \text{acc}_p
$$

$$
\begin{aligned}
L &= x_0 :: \text{tail}(L)                                                             & \qquad \text{[List decomposition]} \\
I &= (x_0 + i) :: \text{tail}(I)                                                      & \qquad \text{[Integral decomposition]} \\
\text{acc}(L, i) &= (x_0 + i) :: \text{acc}(\text{tail}(L),(x_0 + i))                  & \qquad \text{[Definition of } \text{acc}] \\
I_0 &= x_0 + i = \text{acc}_0                                                           & \qquad \text{[Base case]} \\
I_{(p+1)} &= \text{tail}(I)_p                                                            & \qquad \text{[Tail Access Shift Left]} \\
\text{acc}_{(p+1)} &= \text{acc}(\text{tail}(L),(x_0 + i))_p                             & \qquad \text{[Recursive accumulation]} \\
\text{tail}(L)_p &= \text{acc}(\text{tail}(L), (x_0 + i))_p                          & \qquad \text{[Inductive hypothesis]} \\
\Rightarrow \quad I_{p+1} &= \text{acc}_{p+1}                                           & \qquad \text{[By substitution]} \\
& \therefore \\
\forall p \in [0..n-1], \quad I_p &= \text{acc}_p \quad \blacksquare                   & \qquad \text{[Q.E.D.]}
\end{aligned}
$$

Verified in [IntegralProperties.scala at assertAccMatchesApply](./src//main/scala/v1/list/integral/properties/IntegralProperties.scala#assertAccMatchesApply):

<details>
<summary> Scala Doc </summary>

```scala
  /**
   * Lemma: The `apply(position)` method returns the same value as the value at
   * index `position` in the accumulated list `acc`.
   *
   * That is:
   * apply(position) == acc(position)
   *
   * Holds for all valid `positions` in the bounds of the list.
   * @param integral Integral the integral of the lemma
   * @param position BigInt the position in the acc list
   * @return Boolean true if the property holds
   */
```
</details>

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
    assert(position > 0 )
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
    assert(ListUtilsProperties.assertTailShiftLeft(integral.acc, position))
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

#### Delta Consistency

**Lemma:** The difference between two consecutive accumulated values in Acc
equals the corresponding value from the original list.

$$
\forall\ p \in [0, n-2]:\ \text{acc}_{p+1} - \text{acc}_p = L_{p+1}
$$

$$
\begin{aligned}
L &= [x_0, x_1, \dots, x_{n-1} ]                                                            & \qquad \text{[List definition]} \\
L &= x_0 :: \text{tail}(L)                                                                 & \qquad \text{[List decomposition]} \\
\text{acc}(L, i) &= (x_0 + i) :: \text{acc}(\text{tail}(L), x_0 + i)                       & \qquad \text{[Definition of acc]} \\
\text{acc}_0 &= x_0 + i                                                                    & \qquad \text{[Base case]} \\
\text{acc}_1 &= x_1 + \text{acc}_0                                                         & \qquad \text{[Recursive accumulation]} \\
\Rightarrow \quad \text{acc}_1 - \text{acc}_0 &= x_1 = L_1                                  & \qquad \text{[Cancellation]} \\
\text{acc}_{p+1} &= x_{p+1} + \text{acc}_p                                                 & \qquad \text{[Recursive accumulation]} \\
\Rightarrow \quad \text{acc}_{p+1} - \text{acc}_p &= x_{p+1} = L_{p+1}                      & \qquad \text{[By subtraction]} \\
& \therefore \\
\forall p \in [0..n-2],\quad \text{acc}_{p+1} - \text{acc}_p &= L_{p+1} \quad \blacksquare & \qquad \text{[Q.E.D.]}
\end{aligned}
$$

Verified in [IntegralProperties.scala at assertAccDiffMatchesList](./src//main/scala/v1/list/integral/properties/IntegralProperties.scala#assertAccDiffMatchesList):

<details>
<summary>Scala Doc</summary>

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
```
</details>

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
    assert(position > 0 )
    assert(position < integral.list.size - 1)
    assert(position - 1 < integral.list.size )

    // Inductive step
    val next = Integral(integral.list.tail, integral.head)
    assert(next.size == integral.size - 1)
    assert(integral.tail == next.acc)
    assert(assertAccDiffMatchesList(next, position - 1))

    // link these values and next values
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

#### Last Element Agreement

**Lemma:** The last element of the accumulated list is equal to the last element of the integral.
It also check if the last element of the integral is the element at the last position,  $n - 1$.

$$
\begin{aligned}
acc_{(n - 1)} & = last_{(I)} \\
acc_{(n - 1)} & = I_{(n - 1)} \\
\end{aligned}
$$

$$
\begin{aligned}
L &= [x_0, x_1, \dots, x_{n-1}]                                               & \qquad \text{[List definition]} \\
\text{last}(L) &= \begin{cases}
x_0 & \text{if } |L| = 1 \\
\text{last}(\text{tail}(L)) & \text{if } |L| > 1
\end{cases}                                                                 & \qquad \text{[Definition of last]} \\
\text{acc}(L, i) &= (x_0 + i) :: \text{acc}(\text{tail}(L), x_0 + i)         & \qquad \text{[Definition of accumulation]} \\
I &= \text{acc}(L, i)                                                       & \qquad \text{[Integral as accumulated list]} \\
\\
\text{Base case: } |L| = 1 \\
L &= [x_0]                                                                   & \qquad \text{[Singleton list]} \\
\text{acc}(L, i) &= [x_0 + i]                                                & \qquad \text{[By definition]} \\
I &= [x_0 + i]                                                               & \qquad \text{[Integral is acc]} \\
\text{last}(I) &= x_0 + i = acc_0 = I_0                                      & \qquad \text{[last on singleton]} \\
\\
\text{Inductive step: } |L| > 1 \\
L &= x_0 :: \text{tail}(L)                                                   & \qquad \text{[List decomposition]} \\
I &= (x_0 + i) :: \text{acc}(\text{tail}(L), x_0 + i)                        & \qquad \text{[Recursive definition]} \\
\text{tail}(I) &= \text{acc}(\text{tail}(L), x_0 + i)                        & \qquad \text{[Tail of integral]} \\
\text{last}(I) &= \text{last}(\text{tail}(I))                                & \qquad \text{[Recursive last]} \\
\text{last}(\text{tail}(I)) &= \text{acc}(\text{tail}(L), x_0 + i)_{(n - 2)} & \qquad \text{[Inductive hypothesis]} \\
&= acc_{(n - 1)}                                                            & \qquad \text{[Shifted indexing]} \\
\Rightarrow\ \text{last}(I) &= acc_{(n - 1)} = I_{(n - 1)}                   & \qquad \text{[By substitution]} \\
& \therefore \\
\text{last}_I &= acc_{(n - 1)} = I_{(n - 1)} \quad \blacksquare              & \qquad \text{[Q.E.D.]}
\end{aligned}
$$

Verified in [IntegralProperties.scala at assertLast](./src//main/scala/v1/list/integral/properties/IntegralProperties.scala#assertLast):

<details>
<summary>Scala Doc</summary>

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
```
</details>

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
    assert(ListUtilsProperties.listSumAddValue(next.list,integral.list.head))
    assert(integral.list.head + ListUtils.sum(next.list) == ListUtils.sum(List(integral.list.head) ++ integral.list.tail))
    assert(integral.list.head + ListUtils.sum(next.list) == ListUtils.sum(integral.list))
    assert(integral.last == integral.init + ListUtils.sum(integral.list))
  }
  
  integral.last == integral.init + ListUtils.sum(integral.list)
}.holds
```

#### List Size Agreement

**Lemma:** The size of the accumulated List is equal to the size of the original List.

$$
|acc| = |L|
$$

$$
\begin{aligned}
L &= [x_0, x_1, \dots, x_{n-1}]                                           & \qquad \text{[List definition]} \\
\text{acc}(L, i) &= (x_0 + i) :: \text{acc}(\text{tail}(L), x_0 + i)     & \qquad \text{[Recursive accumulation]} \\
\\
\text{Base case: } |L| = 0 \\
L &= []                                                                  & \qquad \text{[Empty list]} \\
\text{acc}(L, i) &= []                                                   & \qquad \text{[By definition]} \\
|\text{acc}(L, i)| &= 0 = |L|                                            & \qquad \text{[Equal size]} \\
\\
\text{Base case: } |L| = 1 \\
L &= [x_0]                                                               & \qquad \text{[Singleton list]} \\
\text{acc}(L, i) &= [x_0 + i]                                            & \qquad \text{[By definition]} \\
|\text{acc}(L, i)| &= 1 = |L|                                            & \qquad \text{[Equal size]} \\
\\
\text{Inductive step: } |L| > 1 \\
L &= x_0 :: \text{tail}(L)                                               & \qquad \text{[Decomposition]} \\
\text{acc}(L, i) &= (x_0 + i) :: \text{acc}(\text{tail}(L), x_0 + i)     & \qquad \text{[Recursive call]} \\
|\text{acc}(\text{tail}(L), x_0 + i)| &= |\text{tail}(L)|                & \qquad \text{[Inductive hypothesis]} \\
|\text{acc}(L, i)| &= 1 + |\text{tail}(L)| = |L|                         & \qquad \text{[Cons adds 1]} \\
& \therefore \\
|\text{acc}(L, i)| &= |L| \quad \blacksquare                             & \qquad \text{[Q.E.D.]}
\end{aligned}
$$

Verified in [IntegralProperties.scala](./src//main/scala/v1/list/integral/properties/IntegralProperties.scala#assertSizeAccEqualsSizeList):

<details>
<summary>Scala Doc</summary>

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
```
</details>

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

## 7. Limitations

* The current implementation focuses exclusively on lists of unbounded integers (`BigInt`). It does not yet support generalized numeric types via abstraction or type classes.
* While the recursive definitions are mathematically correct, they may lead to stack overflows for extensive lists. This work prioritizes correctness and verifiability over performance or scalability.
* The $sum$, $head$, $tail$ and concatenation &#x29FA; functions used here are reused from prior verified work [[1]](#ref1) and are not redefined in this article.

## 7. Limitations

This article shares many foundational assumptions and restrictions with the earlier work 
 [Using Formal Verification to Prove Properties of Lists Recursively Defined]([https://github.com/thiagomata/prime-numbers/blob/master/list.md) [[1]](#ref1).
For a detailed discussion of these limitations, please refer to that article.

Specifically:

* The focus remains on lists of unbounded integers (`BigInt`), without support for generalized numeric types via abstraction or type classes.
* Recursive functions such as $sum$, $head$, $tail$, and concatenation are reused from the prior work [[1]](#ref1) and are not redefined here.
* Due to the recursive nature of these definitions, stack overflows may occur with extensive lists, but correctness and verifiability take priority over performance.

## 8. Conclusion

This article defines and verifies a discrete integral operation over finite integer lists using a zero-prior-knowledge approach.
By building on a previously verified list representation, we demonstrate how recursive accumulations can be reasoned about and implemented with full static guarantees.
This library of formally verified recursive structures in Scala using Stainless brings executable specifications and mathematical clarity.

## 9. References

<a name="ref1" id="ref1" href="#ref1">[1]</a>  
Mata, T. H. (2025). *Using Formal Verification to Prove Properties of Lists Recursively Defined*. Unpublished manuscript.  
Available at: [https://github.com/thiagomata/prime-numbers/blob/master/list.md](https://github.com/thiagomata/prime-numbers/blob/master/list.md)

## 10. Appendix

### 10.1 Numeric Type Generalization and Limitations

In this article, we focus on lists of `BigInt` to avoid issues of overflow and rounding and to simplify formal reasoning, considering the
current limitations of Scala Stainless &mdash; at version 0.9.8.8 &mdash; to deal with more generic numeric types.
Although the discrete Integral could be generalized to other numeric types (e.g., modular integers, rationals, or floats), such generalizations are not verified in this work.

Extending the integral definition to arbitrary numeric types would require defining and proving type-specific properties (e.g., associativity, identity) and encoding them using Scala type classes like `Numeric[T]`.
This direction is left for future work.

### 10.2 Stainless Execution Output

<pre style="background-color: black; color: white; padding: 10px; font-family: monospace;">
<code style="color:blue">[  Info   ] </code> Finished compiling
<code style="color:blue">[  Info   ] </code> Preprocessing finished
<code style="color:blue">[  Info   ] </code> Inferring measure for sum...
<code style="color:orange">[ Warning ] </code> The Z3 native interface is not available. Falling back onto smt-z3.
<code style="color:blue">[  Info   ] </code> Finished lowering the symbols
<code style="color:blue">[  Info   ] </code> Finished generating VCs
<code style="color:blue">[  Info   ] </code> Starting verification...
<code style="color:blue">[  Info   ] </code> Verified: 2781 / 2781
<code style="color:blue">[  Info   ] </code> Done in 61.79s
<code style="color:blue">[  Info   ] </code><code style="color:green">   ┌───────────────────┐</code>
<code style="color:blue">[  Info   ] </code><code style="color:green"> ╔═╡ stainless summary ╞═══════════════════════════════════════════════════════════════════════════╗</code>
<code style="color:blue">[  Info   ] </code><code style="color:green"> ║ └───────────────────┘                                                                           ║</code>
<code style="color:blue">[  Info   ] </code><code style="color:green"> ╟─────────────────────────────────────────────────────────────────────────────────────────────────╢</code>
<code style="color:blue">[  Info   ] </code><code style="color:green"> ║ total: 2781 valid: 2781 (2768 from cache, 13 trivial) invalid: 0    unknown: 0    time:    9.11 ║</code>
<code style="color:blue">[  Info   ] </code><code style="color:green"> ╚═════════════════════════════════════════════════════════════════════════════════════════════════╝</code>
<code style="color:blue">[  Info   ] </code> Verification pipeline summary:
<code style="color:blue">[  Info   ] </code>  @extern, cache, anti-aliasing, return transformation, 
<code style="color:blue">[  Info   ] </code>  imperative elimination, type encoding, choose injection, nativez3, 
<code style="color:blue">[  Info   ] </code>   non-batched
<code style="color:blue">[  Info   ] </code> Shutting down executor service.
</pre>
