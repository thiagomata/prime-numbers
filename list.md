# Using Formal Verification to Prove Properties of Lists Recursively Defined

**Author:** Mata, T. H.
Independent Researcher  
**Email:** [thiago.henrique.mata@email.com](mailto:thiago.mata@email.com)  
**GitHub:** [@thiagomata](https://github.com/thiagomata)

## Abstract

<div align="justify">
<p style="text-align: justify">
In this article, we define and construct immutable finite lists of <code>BigInt</code> values
from scratch, relying only on core type 
constructs and recursion, with no prior knowledge of Scala's collections required. Core 
properties of finite integer lists are formalised and verified using recursive definitions 
aligned with functional programming principles. Lists are modelled either as empty or as 
recursively constructed pairs of head and tail. We recursively define operations such as 
indexing, concatenation, slicing, and summation both mathematically and in pure Scala.
All properties are formally verified using the Stainless verification system, ensuring 
correctness via static guarantees. This work bridges mathematical rigour and executable 
code, laying a foundation for verified reasoning over recursive data structures.
</p>
</div>

## 1. Introduction

Lists are finite sequences of values that support a wide range of operations in functional 
and declarative programming. When combined with summation, they form the backbone for 
definitions of sequences, recurrence, accumulation, and integration in the discrete domain.

Our approach mirrors traditional recursive definitions but is formally verified
using  [Scala Stainless](https://epfl-lara.github.io/stainless/intro.html) [[1]](#ref1),  
a verification framework for pure Scala programs
that uses formal verification to ensure user-defined functions satisfy 
given preconditions, postconditions, and invariants through automated proofs under all valid inputs.

> Formal verification is the act of proving or disproving the correctness of 
> intended algorithms underlying a system with respect to a certain formal 
> specification or property, using formal methods of mathematics.
> [— Wikipedia on Formal Verification](https://en.wikipedia.org/wiki/Formal_verification) [[2]](#ref2)

## 2. Definitions

### 2.1 List construction

Let $𝕃$ be the set of all lists over a set $S$.
A list is either the empty $L_{e}$ or a non-empty list $L_{node}$, as follows:

### 2.2 Empty List

Let's define an empty list $L_{e}$:

```math
\begin{aligned}
L_{e} & \in 𝕃 \\
L_{e} & = [] \\
\end{aligned}
```

### 2.3 Recursive Definition of List

```math
\begin{aligned}
&\text{ head } & \in 𝕊 \\
&\text{ tail } & \in 𝕃 \\
&L_{node}(\text{head}, \text{tail}) & \in 𝕃_{node} \\
&𝕃 = \{ L_e \}  \cup \{ L_{node}(\text{head}, \text{tail}) & \mid \text{head} \in 𝕊,\ \text{tail} \in 𝕃 \} \\
\end{aligned}
```

#### Termination and Cyclic References

Because all lists in this model are immutable, each application of $L_{\text{node}}(\text{head}, \text{tail})$ 
produces a distinct structural value without the possibility of cyclic references. 
Recursive functions over $𝕃$ terminate naturally, as a strictly decreasing structure defines size.


### 2.4 Elements Access and Indexing

```math
\begin{aligned}
\text{ if } L_{node} = [v_0, v_1, \dots, v_{n-1} ] & \implies L_{node} = (head: v_0, tail: [v_1, \dots, v_{n-1}]) \\
head(L_{node}) & = v_0 \\
tail(L_{node}) & = [v_1, \dots, v_{n-1}] \\
last(L_{node}) & = L_{node(|L| - 1)} \\
L_{node(0)} & = L_{(0)} = head(L_{node}) \\
L_{node(n)} & = L_{(n)} = tail(L_{node})({n - 1}) \text{ } \forall \text{ } n > 0 \\
\end{aligned} 
```

### 2.5 List Size

With the structure of lists defined, we now introduce a recursive definition 
for their size (or length).
We define the size of a list $L$, $|L|$ as follows:

```math
|L| = \begin{cases} \\
0 & \text{ if } L = L_{e} \\\
1 + |tail(L)| & \text{otherwise} \\
\end{cases}
```

Proved in the native stainless library in `stainless.collection.List`.


### 2.6 List Append

Let $A, B \in 𝕃$ over some set $S$. The append operation $A ⧺ B$ is defined recursively as:

```math
\begin{aligned}
A ⧺ B =
\begin{cases}
B & \text{if } A = L_e \\
L_{node}(head(A), tail(A) ⧺ B) & \text{otherwise}
\end{cases}
\end{aligned}
```

Proved in the native stainless library in `stainless.collection.List`.

### 2.7 List Slice

Let $L = [v_0, v_1, \dots, v_{n-1}]$, $i, j \in \mathbb{N}$, with $i \leq j < n$.

$$
L[i \dots j] := [ L_k \mid k \in \mathbb{N},\ i \leq k \leq j ]
$$

### 2.8 List Sum

Let $\text{sum} : 𝕃 \implies 𝕊$ be a recursively defined function:

```math
sum(L) = 
\begin{cases} \\
0 & \text{if } L = L_e \\
head(L) + sum(tail(L)) & \text{otherwise} \\
\end{cases}
```

Defined at [List Utils](
	./src/main/scala/v1/list/ListUtils.scala#sum
) as follows:

<details>
<summary> Scala Doc </summary>

```scala
  /**
   * Sums all elements in a list of BigInt.
   * Create the sum using tail recursion.
   * 
   * Assumes that the sum of an empty list is 0.
   * 
   * @param loopList List[BigInt] the list to sum
   * @return BigInt the sum of all elements in the list
   */
```

</details>

```scala
  def sum(loopList: List[BigInt]): BigInt = {
    if (loopList.isEmpty) {
      BigInt(0)
    } else {
      loopList.head + sum(loopList.tail)
    }
  }
```

## 3. Properties

Using the definitions above, we state and verify the following key properties of lists:

### 3.1 Slice Implementations are Equivalent

Let's prove and verify that the definitions of slice tail-recursive,
head-recursive and index-rage recursive are interchangeable and equivalent 
to the mathematical slice notation $L[i \dots j]$ previously defined as:

Let $L = [v_0, v_1, \dots, v_{n-1}]$, $i, j \in \mathbb{N}$, with $i \leq j < n$.

$$
L[i \dots j] := [ L_k \mid k \in \mathbb{N},\ i \leq k \leq j ]
$$


#### Tail Recursive - Specification:

$$
\forall \text{ } L \in 𝕃, \forall \text{ } i, j \in \mathbb{N},\ i \leq j < |L|
$$

$$
\text{slice}(L, i, j) := 
\begin{cases}
[ L_j ] & \text{if } i = j \\
\text{slice}(L, i, j - 1) ⧺ [ L_j ] & \text{if } i < j
\end{cases}
$$

Defined at [List Utils](
	./src/main/scala/v1/list/ListUtils.scala#slice
) as follows:

<details>
<summary> Scala Doc </summary>

```scala
  /**
   * Slices a list from index `from` to index `to`, inclusive.
   * Create the slice using tail recursion.
   * 
   * @param list List[BigInt] the list to slice
   * @param from BigInt the starting index (inclusive)
   * @param to BigInt the ending index (inclusive)
   * @return List[BigInt] the sliced list
   */
```

</details>

```scala
  def slice(list: List[BigInt], from: BigInt, to: BigInt): List[BigInt] = {
    require(from >= 0)
    require(to >= from)
    require(to < list.size)
    decreases(to)

    val current: BigInt = list(to)
    if (from == to) {
      List(current)
    } else {
      val prev = slice(list, from, to - 1)
      ListUtilsProperties.listAddValueTail(prev, current)
      prev ++ List(current)
    }
  }
```

$$
L[i \dots j] := [ L_k \mid k \in \mathbb{N},\ i \leq k \leq j ]
$$

Therefore, let's verify if this recursive implementation matches the specification of the the list definition:

**Goal**:

$$
\forall \text{ } L \in 𝕃, \forall \text{ } i, j \in \mathbb{N},\ i \leq j < |L| \implies \text{slice}(L, i, j) = L[i \dots j]
$$

##### Tail Recursive - Proof by induction on $j$, with fixed $i$

**Base case**: $j = i$

$$
\text{slice}(L, i, i) = [ L_i ] = L[i \dots i]
$$

**Inductive step**: Assume

$$
\text{slice}(L, i, j - 1) = [ L_k \mid i \leq k \leq j - 1 ]
$$

Show:

$$
\begin{aligned}
\text{slice}(L, i, j)  &= \text{slice}(L, i, j - 1) ⧺ [L_j] & \qquad \text{[by definition of slice]} \\
&= L[i \dots (j - 1)] ⧺ [L_j] & \qquad \text{[by Inductive Hypothesis]} \\
&= [ L_k \mid i \leq k \leq j - 1 ] ⧺ [L_j] & \qquad \text{[by Specification]} \\
&= [ L_k \mid i \leq k \leq j ] & \qquad \text{[by definition of Concatenation]} \\
&= L[i \dots j] & \qquad  \text{[Q.E.D]} \\
\end{aligned}
$$

$$
\therefore
$$

$$
\forall \text{ } 0 \leq i \leq j < |L|,\ \text{slice}(L, i, j) = L[i \dots j]
\quad \blacksquare
$$

##### Tail Recursive - Specification:

#### Head-Recursive Slice

Let $L = [v_0, v_1, \dots, v_{n-1}]$, $i, j \in \mathbb{N}$, with $i \leq j < n$.

$$
\forall \text{ } L \in 𝕃, \forall \text{ } i, j \in \mathbb{N},\ i \leq j < |L|
$$

$$
\text{headRecursiveSlice}(L, i, j) :=
\begin{cases}
[ L_i ] & \text{if } i = j \\
L_i ⧺ \text{headRecursiveSlice}(L, i + 1, j) & \text{if } i < j
\end{cases}
$$

Defined at [Slice Equivalence Lemmas](./src/main/scala/v1/list/properties/SliceEquivalenceLemmas.scala#L14) as follows:

<details>
    <summary>Scala Docs</summary>

```scala
/**
 * Creates a sublist of the list `list` from index `from` to index `to`, inclusive
 * using forward slice: builds from `from` to `to` using Cons.
 *
 * The precondition for this function is that:
 * 0 <= from && from <= to && to < list.length
 *
 * This function is a recursive implementation that constructs the sublist
 * by taking elements from the list `list` starting at index `from` and ending at index `to`.
 *
 * @param list the List from which to extract the sublist
 * @param from the starting index of the sublist (inclusive)
 * @param to the ending index of the sublist (inclusive)
 * @tparam A the type of elements in the list
 * @return a List[A] containing the elements from index `from` to index `to`
 */
```

</details>


```scala
def headRecursiveSlice[A](list: List[A], from: BigInt, to: BigInt): List[A] = {
  require(0 <= from && from <= to && to < list.length)
  decreases(to - from)
  if (from == to) List(list(from))
  else Cons(list(from), headRecursiveSlice(list, from + 1, to))
}
```

##### Head Recursive - Specification:

$$
L[i \dots j] := [ L_k \mid k \in \mathbb{N},\ i \leq k \leq j ]
$$

**Goal**:

$$
\forall \text{ } L \in 𝕃, \forall \text{ } i, j \in \mathbb{N},\ i \leq j < |L| \implies \text{headRecursiveSlice}(L, i, j) = L[i \dots j]
$$

##### Head Recursive - Proof by induction on $j - i$

**Base case**: $i = j$

$$
\text{headRecursiveSlice}(L, i, i) = [ L_i ] = L[i \dots i]
$$

**Inductive step**: Assume

$$
\text{headRecursiveSlice}(L, i + 1, j) = [ L_k \mid i + 1 \leq k \leq j ]
$$

Show:

$$
\begin{aligned}
\text{headRecursiveSlice}(L, i, j) &= L_i ⧺ \text{headRecursiveSlice}(L, i + 1, j) & \qquad \text{[by definition]} \\
&= L_i ⧺ L[i + 1 \dots j] & \qquad \text{[by Inductive Hypothesis]} \\
&= [ L_k \mid i \leq k \leq j ] = L[i \dots j] & \qquad \text{[by specification]} \\
\end{aligned}
$$

$$
\therefore
$$

$$
\forall \text{ } 0 \leq i \leq j < |L|,\ \text{headRecursiveSlice}(L, i, j) = L[i \dots j]
\quad \blacksquare
$$

#### Index-Range Slice

Let $L = [v_0, v_1, \dots, v_{n-1}]$, $i, j \in \mathbb{N}$, with $i \leq j < n$.

This version builds the slice directly by recursively iterating over an index range.

Defined at [Slice Equivalence Lemmas](./src/main/scala/v1/list/properties/SliceEquivalenceLemmas.scala#L39) as follows:

<details>
    <summary>Scala Docs</summary>

```scala
/**
 * Creates a sublist of the list `list` from index `from` to index `to`, inclusive
 * using index-based access: builds from i to j using index access.
 *
 * The precondition for this function is that:
 * 0 <= from && from <= to && to < list.length
 *
 * This function is a recursive implementation that constructs the sublist
 * by taking elements from the list `list` starting at index `from` and ending at index `to`.
 *
 * @param list the List from which to extract the sublist
 * @param from the starting index of the sublist (inclusive)
 * @param to the ending index of the sublist (inclusive)
 * @tparam A the type of elements in the list
 * @return a List[A] containing the elements from index `from` to index `to`
 */
```
</details>

```scala
def indexRangeValues[A](list: List[A], from: BigInt, to: BigInt): List[A] = {
  require(0 <= from && from <= to && to < list.length)
  decreases(to - from)
  if (from == to) List(list(from))
  else Cons(list(from), indexRangeValues(list, from + 1, to))
}
```

##### Index-Range Slice - Specification:

$$
L[i \dots j] := [ L_k \mid k \in \mathbb{N},\ i \leq k \leq j ]
$$

**Goal**:

$$
\forall \text{ } L \in 𝕃, \forall \text{ } i, j \in \mathbb{N},\ i \leq j < |L| \implies \text{indexRangeValues}(L, i, j) = L[i \dots j]
$$

##### Index-Range Slice - Proof by induction on $j - i$

**Base case**: $i = j$

$$
\text{indexRangeValues}(L, i, i) = [ L_i ] = L[i \dots i]
$$

**Inductive step**: Assume

$$
\text{indexRangeValues}(L, i + 1, j) = [ L_k \mid i + 1 \leq k \leq j ]
$$

Show:

$$
\begin{aligned}
\text{indexRangeValues}(L, i, j) &= L_i ⧺ \text{indexRangeValues}(L, i + 1, j) & \qquad \text{[by definition]} \\
&= L_i ⧺ L[i + 1 \dots j] & \qquad \text{[by Inductive Hypothesis]} \\
&= [ L_k \mid i \leq k \leq j ] = L[i \dots j] & \qquad \text{[by specification]} \\
\end{aligned}
$$

$$
\therefore
$$

$$
\forall \text{ } 0 \leq i \leq j < |L|,\ \text{indexRangeValues}(L, i, j) = L[i \dots j]
\quad \blacksquare
$$

#### Slice Equivalence Lemmas

We have now established that all the following slice implementations are equivalent to the
mathematical slice notation $L[i \dots j]$, and thus interchangeable for both reasoning
and implementation:

- Tail-recursive slice
- Head-recursive slice
- Index-range slice

These properties are verified at [Slice Equivalence Lemmas](
	./src/main/scala/v1/list/properties/SliceEquivalenceLemmas.scala
) as follows:

<details>
    <summary>Scala Docs</summary>

```scala
  /**
   * Lemma: For all `list: List[BigInt]` and indices `from`, `to` such that
   * 0 <= from <= to < list.length, the following three slicing strategies produce
   * the same result:
   *
   * - Tail-recursive slice: ListUtils.slice
   * - Head-recursive slice: headRecursiveSlice
   * - Index-based slice: indexRangeValues
   *
   * Formally:
   *
   * ListUtils.slice(list, from, to) == headRecursiveSlice(list, from, to)
   * ListUtils.slice(list, from, to) == indexRangeValues(list, from, to)
   * headRecursiveSlice(list, from, to) == indexRangeValues(list, from, to)
   *
   * @param list the input list of BigInt
   * @param from inclusive start index
   * @param to   inclusive end index
   * @return true if all three slices are equal
   */
```
</details>

```scala
  def tailHeadAndIndexRangeSlicesAreEqual(list: List[BigInt], from: BigInt, to: BigInt): Boolean = {
    require(0 <= from && from <= to && to < list.length)
    decreases(to - from)

    val indexSlice = indexRangeValues(list, from, to)
    val tailSlice = ListUtils.slice(list, from, to)
    val headSlice = headRecursiveSlice(list, from, to)

    if (from == to) {
      assert(indexSlice == List(list(from)))
      assert(tailSlice == List(list(from)))
      assert(headSlice == List(list(from)))
    } else {
      assert(tailHeadAndIndexRangeSlicesAreEqual(list, from, to - 1))
      assert(tailHeadAndIndexRangeSlicesAreEqual(list, from + 1, to))
      val reconstructedTail = ListUtils.slice(list, from, to - 1) ++ List(list(to))
      assert(tailSlice == reconstructedTail)
      assert(tailSlice == indexSlice)
      assert(headSlice == indexSlice)
      assert(tailSlice == headSlice)
    }
    (
      tailSlice == headSlice &&
      tailSlice == indexSlice &&
      headSlice == indexSlice
    )
  }.holds
```

### 3.2 Sum matches Summation

We can prove that the recursive `sum` function over a list $L$ matches the mathematical definition 
of the summation $\sum_{i=0}^{n-1} x_i$, where $L = [x_0, x_1, \dots, x_{n-1}]$, $|L| = n$.

#### Base Case: $|L| = 0$

```math
\begin{aligned}
\text{sum}(L) &= 0 & \text{[by definition of sum]} \\
\sum L &= 0 & \text{[summation over empty list]} \\
\implies \text{sum}(L) &= \sum L \in 𝕃
\end{aligned}
```

$$
\therefore
$$

$$
\forall \text{ } L \in 𝕃 \\
|L| = 0 \implies \text{sum}(L) = \sum L \\
$$

#### Inductive Step: $|L| > 0$

Let $P \in 𝕃$, with $P = [x_1, x_2, \dots, x_{n-1}] \in 𝕃$, and assume:

```math
\begin{aligned}
\text{sum}(P) & = \sum_{i=1}^{n-1} x_i \in & \qquad \text{[by Inductive Hypothesis]} \\
L = [x_0] ⧺ P & = [x_0, x_1, \dots, x_n]   & \qquad \text{[by Definiton of Concatenation]} \\
\end{aligned}
```

We can ensure termination, since:
```math
\begin{aligned}
&|L| &= |P| + 1  & \qquad \text{[by Size Definition]} \\
&|P| &< |L|      & \qquad \text{[Size Decreases Ensures Termination]} \\
\end{aligned}
```

Let's calculate the sum of $L$:
```math
\begin{aligned}
\text{sum}(L) &= \text{head}(L) + \text{sum}(\text{tail}(L))  & \qquad \text{[by definition of the recursive function sum]} \\
              &= x_0 + \text{sum}(P)                          & \qquad \text{[by definition of head and P]} \\
              &= x_0 + \sum_{i=1}^{n-1} x_i                   & \qquad \text{[by Inductive Hypothesis]} \\
              &= \sum_{i=0}^{n-1} x_i = \sum L                
\end{aligned}
```

$$
\therefore \\
$$

$$
\forall\text{ }  L \in 𝕃 \\
|L| > 0 \text{ } \implies \text{ sum}(L) = \sum L  \\
$$

Hence, by induction on the size of $L$:

$$
\forall \text{ } L \text{ } \in 𝕃 \\
\text{sum}(L)  = \sum L = \sum_{i=0}^{n-1} x_i  \in 𝕊  \quad \blacksquare \quad \text{[Q.E.D.]} \\
$$


### 3.3 Tail Access Shift

**Lemma:** For any list $L$ with at least two elements, accessing the $i$-th element of its tail is equivalent to accessing the $(i + 1)$-th element of the list.

```math
\forall \text{ } L,\ i,\quad 1 < |L|, 0 \le i < |\text{tail}(L)| \implies \text{tail}(L)_{(i)} = L_{(i + 1)}
```

Since:

$$
\begin{aligned}
L &= [x_0, x_1, x_2, \dots, x_{n - 1}]                                & \qquad \text{[List definition]} \\
L &= [x_0] ⧺ [x_1, x_2, \dots, x_{n - 1}]                             & \qquad \text{[Concatenation definition]} \\
L &= \text{head}(L) ⧺ \text{tail}(L)                                  & \qquad \text{[Head and Tail definition]} \\
\text{tail}(L) &= [x_1, x_2, \dots, x_{n - 1}]                        & \qquad \text{[Tail definition]} \\
L{i} &= x_i = \text{tail}(L){(i + 1)} \text{ } \forall \text{ }  0 < i < |L|  \quad \blacksquare & \qquad \text{[Q.E.D.]} \\
\end{aligned}
$$

Verified in 
[List Utils Properties - Access Tail Shift Left](
./src/main/scala/v1/list/properties/ListUtilsProperties.scala#accessTailShiftLeft
) and
[List Utils Properties - Assert Tail Shift Right](
./src/main/scala/v1/list/properties/ListUtilsProperties.scala#accessTailShiftRight
)
as follows:

#### Access Tail Shift Right

<details>
  <summary>Scala Docs</summary>

```scala
  /**
    * For every position in the list different from 0,
    * the value of the list in that position
    * is equal to the value of the tail in that position + 1.
    * 
    * list.tail(position) == list(position + 1)
    *
    * @param list List[T] any list of T non empty
    * @param position BigInt the position of the element to check
    * @return Boolean true if the property holds
    */
```

</details>

```scala
  def accessTailShiftRight[T](list: List[T], position: BigInt): Boolean = {
    require(list.nonEmpty && position >= 0 && position < list.tail.size)
    list.tail(position) == list(position + 1)
  }.holds
```

#### Assert Tail Shift Left

<details>
  <summary>Scala Docs</summary>

```scala
  /**
   * For every position in the list different from 0,
   * the value of the list in that position
   * is equal to the value of the tail in that position - 1.
   *
   * list(position) == list.tail(position - 1)
   *
   * @param list List[BigInt] any list of BigInt non empty
   * @param position BigInt the position of the element to check
   * @return true if the property holds
   */
```
</details>

```scala
  def assertTailShiftLeft[T](list: List[T], position: BigInt): Boolean = {
    require(list.nonEmpty)
    require(position >= 0 && position < list.size)
    decreases(position)

    if (position == 0 ) {
      list(position) == list.head
    } else {
      assert( list == List(list.head) ++ list.tail )
      assert( list(position) == list.apply(position) )
      assert(assertTailShiftLeft(list.tail, position - 1))
      assert(list.apply(position) == list.tail.apply(position - 1))
      list(position) == list.tail(position - 1)
    }
  }.holds
```

### 3.4 Last Element Identity

**Lemma:** The last element of a non-empty list is equal to the element at position $n - 1$, where $n = |L|$.

```math
\forall \text{ } L,\ |L| > 0 \implies \text{last}(L) = L_{(n - 1)}
```

```math
\begin{aligned}
&L &= [x_0, x_1, \dots, x_{n-1}]                                   & \qquad \text{[List definition]} \\
\end{aligned}
```

#### Base case: $|L| = 1$

```math
\begin{aligned}
&L &= [x_0]                                                        & \qquad \text{[Singleton list]} \\
&\text{last}(L) &= x_0 = L_0 = L_{(n - 1)}                         & \qquad \text{[Definition of last]} \\
\end{aligned}
```

#### Inductive step: $|L| > 1$

```math
\begin{aligned}
&L &= x_0 :: \text{tail}(L)                                        & \qquad \text{[Decomposition]} \\
&\text{last}(L) &= \text{last}(\text{tail}(L))                     & \qquad \text{[Definition of last]} \\
&\text{last}(\text{tail}(L)) &= \text{tail}(L)_{(|\text{tail}(L)| - 1)} & \qquad \text{[Inductive hypothesis]} \\
&\text{tail}(L)_{(|\text{tail}(L)| - 1)} &= L_{(|L| - 1)}          & \qquad \text{[Tail Shift Position]} \\
&\implies \ \text{last}(L) &= L_{(|L| - 1)}                      & \qquad \text{[By substitution]} \\
\end{aligned}
```

```math
\therefore
```

```math
\begin{aligned}
&\forall L,\ |L| > 0 \implies  \text{last}(L) &= L_{(|L| - 1)} \quad \blacksquare
\end{aligned}
```

Verified in [List Util Properties - Assert Last Equals Last Position](
	./src/main/scala/v1/list/properties/ListUtilsProperties.scala#assertLastEqualsLastPosition
).

<details>
<summary> Scala Doc </summary>

```scala
  /**
   * The last element of the list is equal to the last position of the list.
   * This property is true for every list of size > 0.
   *
   * list.last == list(list.size - 1)
   *
   * @param list List[BigInt] any list of BigInt non empty
   * @return true if the property holds
   */
```
</details>

```scala
  def assertLastEqualsLastPosition[T](list: List[T]): Boolean = {
    require(list.nonEmpty)
    decreases(list.size)

    if (list.size == 1) {
      assert(list.head == list.last)
    } else {
      assert(assertLastEqualsLastPosition(list.tail))
      assertTailShiftPosition(list, list.size - 1)
      assert(list.last == list(list.size - 1))
    }
    list.last == list(list.size - 1)
  }.holds
```

### 3.5 Left Append Preserves Sum

```math
\begin{aligned}
\forall \text{ } x \in 𝕊 \\
\text{sum}([x] ⧺ L ) = x + \text{sum}(L) \\
\end{aligned}
```

Proof:

$$
\begin{aligned}
A & = [x] ⧺ L  & \qquad \text{[Concatenation]} \\
\text{sum}(A) & = \text{head}(A) + \text{sum}(\text{tail}(A)) & \qquad \text{[By recursive definition of sum]} \\
              & = x + \text{sum}(L) & \qquad \text{[By recursive definition of head and tail]} \\
\end{aligned}
$$

$$
\therefore
$$

$$
\begin{aligned}
\text{sum}([x] ⧺ L) & = x + \text{sum}(L)  \quad \blacksquare &  \qquad \text{[Q.E.D.]} \\
\end{aligned}
$$


Verified in [List Utils Properties - List Sum Add Value](
./src/main/scala/v1/list/properties/ListUtilsProperties.scala#listSumAddValue
) as follows:

<details>
<summary> Scala Doc </summary>

```scala
  /**
    * for every list `list`` and every value `value``,
    * the sum of the list `list` ++ `List(value)`
    * is equal to the sum of the `list` plus the `value`.
    * 
    * sum(list ++ List(value)) == sum(list) + value
    *
    * @param list List[BigInt] any list of BigInt
    * @param value BigInt the value to add to the list
    * @return Boolean true if the property holds
    */
```

</details>

```scala
def listSumAddValue(list: List[BigInt], value: BigInt): Boolean = {
    ListUtils.sum(List(value) ++ list) == value + ListUtils.sum(list)
  }.holds
```

### 3.6 Sum over Concatenation
```math
	sum(A ⧺ B) = 	sum(A) + 	sum(B)
```

#### If List A is Empty

$$
\begin{aligned}
  A ⧺ B & = L_e ⧺ B & \text{[A is empty list]} \\
        & = B & \text{[By definition of concatenation]} \\
  \text{sum}(A) & = 0 & \text{[By definition of sum]} \\
  \text{sum}(A ⧺ B) & = \text{sum}(B) & \text{[Since A ⧺ B equals B]} \\
                    & = 0 + \text{sum}(B) \\
                    & = \text{sum}(A) + \text{sum}(B) & \text{[Since sum(A) is zero]} \\
\end{aligned}
$$

#### If list A is Non-Empty

$$
\begin{aligned}
C & = \text{tail}(A) ⧺ B \\
\text{sum}(A) & = \text{head}(A) + \text{sum}(\text{tail}(A))                & \text{[By definition of sum]} \\
C & = \text{sum}(\text{tail}(A)) + \text{sum}(B)                           & \text{[Inductive Step]} \\
A ⧺ B & = [\text{head}(A)] ⧺ (\text{tail}(A) ⧺ B)                          & \text{[By definition of head and tail]} \\
\text{sum}(A ⧺ B) & = \text{head}(A) + \text{sum}(\text{tail}(A) ⧺ B)      & \text{[By definition of sum]} \\
                  & = head(A) + \text{sum}(\text{tail}(A)) + \text{sum}(B) & \text{[By definition of C]} \\
                  & = \text{sum}(A) + \text{sum}(B)                        & \text{[Substituting]} \\
\end{aligned}
$$

$$
\therefore
$$

$$
\begin{aligned}
	sum(A ⧺ B) = 	sum(A) + 	sum(B) & \quad \blacksquare \qquad \text{[Q.E.D.]} \\
\end{aligned}
$$

Verified in [List Utils Properties - List Combine ](
./src/main/scala/v1/list/properties/ListUtilsProperties.scala#listCombine
) as follows:

<details>
<summary> Scala Doc </summary>

```scala
  /**
    * for every list A and B,
    * the sum of the list A ++ B
    * is equal to the sum of the list A plus the sum of the list B.
    * 
    * sum(listA ++ listB) == sum(listA) + sum(listB)
    *
    * @param listA List[BigInt] any list of BigInt
    * @param listB List[BigInt] any list of BigInt
    * @return Boolean true if the property holds
    */
```

</details>

```scala
  def listCombine(listA: List[BigInt], listB: List[BigInt]): Boolean = {
    decreases(listA.size)

    if (listA.isEmpty) {
      assert(ListUtils.sum(listA) == BigInt(0))
      assert(ListUtils.sum(listB) == BigInt(0) + ListUtils.sum(listB))
      assert(ListUtils.sum(listB) == ListUtils.sum(listA) + ListUtils.sum(listB))
      assert(listA ++ listB == listB)
    } else {
      listCombine(listA.tail, listB)
      val bigList = listA ++ listB
      assert(bigList == List(listA.head) ++ listA.tail ++ listB)
      listSumAddValue(listA.tail ++ listB, listA.head)
    }
    ListUtils.sum(listA ++ listB) == ListUtils.sum(listA) + ListUtils.sum(listB)
  }.holds
```

### 3.7 Commutativity of Sum over Concatenation

```math
	sum(A ⧺ B) = sum(B ⧺ A)
```
Since:
```math
\begin{aligned}
	sum(A ⧺ B) & = sum(A) + sum(B)                        & \text{[Sum over Concatenation]} \\
	sum(B ⧺ A) & = sum(B) + sum(A)                        & \text{[Sum over Concatenation]} \\
	sum(B) + sum(A) & = sum(A) + sum(B)                   & \text{[Distributive]} \\
	sum(B ⧺ A) & = sum(A ⧺ B)  \quad \blacksquare         & \text{[Q.E.D]} \\
\end{aligned}
```

Verified in [List Utils Properties - List Swap ](
./src/main/scala/v1/list/properties/ListUtilsProperties.scala#listSwap
) as follows:

<details>
<summary> Scala Docs </summary>

```scala
  /**
    * for every list A and B,
    * the sum of the list A ++ B
    * is equal to the sum of the list B plus the sum of the list A.
    * 
    * sum(listA ++ listB) == sum(listB) + sum(listA)
    *
    * @param listA List[BigInt] any list of BigInt
    * @param listB List[BigInt] any list of BigInt
    * @return Boolean true if the property holds
    */
```
</details>


```scala
  def listSwap(listA: List[BigInt], listB: List[BigInt]): Boolean = {
    listCombine(listA, listB)
    listCombine(listB, listA)
    assert(ListUtils.sum(listA ++ listB) == ListUtils.sum(listA) + ListUtils.sum(listB))
    assert(ListUtils.sum(listB ++ listA) == ListUtils.sum(listB) + ListUtils.sum(listA))
    assert(ListUtils.sum(listA) + ListUtils.sum(listB) == ListUtils.sum(listB) + ListUtils.sum(listA))
    ListUtils.sum(listA ++ listB) == ListUtils.sum(listB ++ listA)
  }.holds
```

### 3.8 Slice Append Consistency

**Lemma:** A slice of a list from index $f$ to $t$ can be expressed as the slice from $f$ to $t - 1$ concatenated with the element at index $t$, for $f \le t < |L|$.

$$
\begin{aligned}
L[f \dots t] &= \text{slice}(L, f, t) \\
             &= \text{slice}(L, f, t - 1) ⧺ [L_t] \\
             &= L[f \dots t - 1] ⧺ [L_t]  \quad \blacksquare
\end{aligned}
$$


Verified in [List Utils Properties - Assert Append to Slice ](
./src/main/scala/v1/list/properties/ListUtilsProperties.scala#assertAppendToSlice
) as follows:

<details>
<summary> Scala Docs </summary>

```scala
  /**
    * For every position in the list,
    * A slice of the list from position from i position j
    * is equal to the slice of the list from position i to j - 1
    * appending the element in position j.
    * 
    * list(i, j) == list(i, j - 1) ++ list(j)
    *
    * @param list List[BigInt] any list of BigInt
    * @param from BigInt the position of the first element to check
    * @param to BigInt the position of the last element to check
    * @return Boolean true if the property holds
    */
```

</details>

```scala
  def assertAppendToSlice(list: List[BigInt], from: BigInt, to: BigInt): Boolean = {
    require(from >= 0)
    require(from < to)
    require(to < list.size)
    
    listSumAddValue(list, list(to))
    
    ListUtils.slice(list, from, to) ==
      ListUtils.slice(list, from, to - 1) ++ List(list(to))
  }.holds
```

## 4. Conclusion

This article presents a formal framework for defining and reasoning about finite lists using a 
recursive mathematical structure aligned with functional programming principles.

These properties are:

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
|L| > 0 &\implies L_{|L|-1} &= &\text{ }\text{last}(L) \\
i > 0 &\implies L_i &= &\text{ }\text{tail}(L)_{i-1} \\
i < |L| - 1, |L| > 1 &\text{ }\implies \text{tail}(L)_i &= &L_{i+1} \\
\end{aligned}
```
```math
\begin{aligned}
&\sum L &= &\text{sum}(L)                      \quad &\text{[Sum matches Summation]} \\
&\sum ([v] ⧺ L) &= &v + \sum L                 \quad &\text{[Left Append Preserves Sum]} \\
&\sum (A ⧺ B) &= &\sum A + \sum B              \quad &\text{[Sum over Concatenation]} \\
&\sum (A ⧺ B) &= &\sum (B ⧺ A)                 \quad &\text{[Commutativity of Sum over Concatenation]} \\
&L[f \dots t] &= &L[f \dots {(t - 1)}] ⧺ [L_t] \quad &\text{[Slice Append Consistency]} \\
\end{aligned}
```

These properties are implemented in Scala using the Stainless verification system, ensuring 
the correctness of properties and recursive functions through static guarantees. 
This foundation supports further extensions in formally verified functional data structures, 
serving as a practical bridge between mathematical definitions and executable code.

We also defined the list slice using different strategies and prove them as equivalent.

The properties and definitions presented here can be extended to more complex data structures
and algorithms, providing a solid foundation for future work in formal verification and
mathematical reasoning in functional programming.

## 5. Limitations

This article restricts the implementation and verification to immutable,
 finite lists of integers represented using the `stainless.collection.List` data type. 
The focus is on **correctness**, not on performance or scalability. Our summation and
 accumulation models follow a **recursive definition**, aligned with mathematical formalism.
However, this approach may introduce performance limitations in practical applications involving large lists.

### 5.1 Overflow and Memory Limits Are Out of Scope

By using `BigInt` and immutable lists, the model assumes unbounded integer arithmetic and infinite list capacity. 
This choice avoids overflow and out-of-memory errors, but it does not reflect the constraints of fixed-size integer
 types or limited system memory in real-world environments.

### 5.2 Side Effects Are Excluded

All list operations are pure and referentially transparent. Mutation, I/O, and performance overhead are outside the 
 scope of this model.

### 5.3 No Parallelism or Laziness

Unlike streaming libraries or lazy sequences, this model is strictly eager and sequential, without support for parallel 
 computation or lazy evaluation.

### 5.4 Limitations Imposed by Stainless Verification Tool

Due to current limitations in the Scala Stainless verifier (version 0.9.8.8), formal proofs must often rely on concrete
 numeric types such as `BigInt`.
Stainless does not yet fully support generic numeric abstractions or type classes like `Numeric[T]`,
which hinders verification of implementations parameterized over arbitrary numeric types.

As a result, while the mathematical properties in this work conceptually apply to any numeric domain satisfying the 
required algebraic laws, practical verification is constrained to `BigInt`.
Overcoming these tool limitations is an important direction for future enhancements, enabling broader generality 
and more flexible formal verification.

### 5.5 Scope of Correctness

This article emphasizes the **mathematical correctness** of recursive definitions and verified properties,
 rather than runtime behavior or system-level efficiency.

The use of `BigInt` and conceptually unbounded lists abstracts away concerns like stack overflows, memory usage,
 and execution time.
It also circumvents limitations of the current version of Scala Stainless with respect to generic numeric reasoning.

While limiting practical use in some contexts, these assumptions maintain the focus on proving functional correctness
as defined by recursive specifications.

Future work may include developing alternative implementations of these data structures that explicitly address 
real-world constraints, such as bounded memory and side effects, alongside formal proofs establishing their equivalence
with the current, mathematically rigorous model.

## 6. References

<a name="ref0" id="ref0" href="#ref0">[1]</a>  
Hamza, J., Voirol, N., & Kuncak, V. (2019). *System FR: Formalized foundations for the Stainless verifier*.  
Proceedings of the ACM on Programming Languages, OOPSLA Issue.  

<a name="ref1" id="ref1" href="#ref1">[2]</a>  
Wikipedia contributors. (2024). *Formal verification*. Wikipedia.  
Available at: [https://en.wikipedia.org/wiki/Formal_verification](https://en.wikipedia.org/wiki/Formal_verification)

## 7. Appendix

### 7.1 Stainless Execution Output

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

