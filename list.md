# Using Formal Verification to Prove Properties of Lists Recursively Defined

## Abstract

In thids article, we define and construct lists from scratch, relying only on core type 
constructs and recursion, with no prior knowledge of Scala’s collections required. Core 
properties of finite integer lists are formalized and verified using recursive definitions 
aligned with functional programming principles. Lists are modeled as either empty or recursively 
constructed from a head and a tail. Operations such as indexing, concatenation, slicing, 
and summation are also recursively defined, mathematically described, and implemented in 
pure Scala. All properties are formally verified using the Stainless verification system, 
ensuring correctness through static guarantees. This work bridges mathematical rigor and 
executable code, providing a foundation for verified reasoning over recursive data structures.

## Introduction

Lists are finite sequences of values that support a wide range of operations in 
functional and declarative programming. When combined with summation, they provide the 
backbone for definitions of sequences, recurrence, accumulation, and integration in the 
discrete domain.

Our approach mirrors traditional recursive definitions but is formally verified 
using [Scala Stainless](https://epfl-lara.github.io/stainless/intro.html), 
ensuring that the properties hold under all inputs within the specified constraints.

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

- **Overflow and memory limits are not modeled**: Since we use `BigInt` and immutable lists, 
the model assumes unbounded integer arithmetic and infinite list capacity. 
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
restrictions on list size or memory space. 
While this allows us to reason about lists of arbitrary size and precision using `BigInt`, 
it abstracts away practical concerns such as stack overflows, memory limitations, or time 
complexity in execution.

These limitations do not invalidate the learnings from this study. 
The focus is on **mathematical properties** and **semantic validity**, not execution efficiency.

## Definitions

### List construction

Let $ \mathcal{L} $ be the set of all lists over a set $ S $.
A list is either the empty $ L_{e} $ or a non-empty list $ L_{node} $, as follows:

### Empty List

Let's define an empty list $ L_{e} $:

```math
\begin{aligned}
L_{e} & \in \mathcal{L} \\
L_{e} & = [] \\
isEmpty(L_{e}) & = True \\
isNonEmpty(L_{e}) & = False \\
\end{aligned}
```

### Recursive Definition of List

```math
\begin{aligned}
\forall \text{ head } & \in S, \text{ tail } \in \mathcal{L}  \\
 L_{node}(head, tail) & \in \mathcal{L}_{\text{node}} \\
\mathcal{L} = \{ L_e \}  \cup \{ L_{node}(head, tail) & \mid head \in S,\ tail \in \mathcal{L} \} \\
isEmpty(L_{node}) & = False \\
isNonEmpty(L_{node}) & = True \\
\end{aligned}
```

### Elements Access and Indexing

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

### List Size

With the structure of lists defined, we now introduce a recursive definition 
for their size (or length).
We define the size of a list $ L $, $ |L| $ as follows:

```math
|L| = 
\begin{cases} \\
0 & \text{ if } L = L_{e} \\\
1 + |tail(L)| & \text{otherwise} \\
\end{cases}
```

Proved in the native stainless library in `stainless.collection.List`.

### List Append

Let $ A, B \in \mathcal{L} $ over some set $ S $. The append operation $ A \mathbin{+\!\!+} B $ is defined recursively as:

```math
\begin{aligned}
A \mathbin{+\!\!+} B =
\begin{cases}
B & \text{if } A = L_e \\
L_{node}(head(A), tail(A) \mathbin{+\!\!+} B) & \text{otherwise}
\end{cases}
\end{aligned}
```

Proved in the native stainless library in `stainless.collection.List`.

### List Slice

Given a list $ L = [v_0, v_1, \dots, v_{n-1}] $, and integers 
$ 0 \leq i \leq j < |L| $, the slice function $ slice(L, i, j) $ 
returns a sublist of $ L $ from index $ i $ to $ j $, inclusive.

```math
\begin{aligned}
slice(L, i, j) = 
\begin{cases}
[ L_{(j)} ] & \text{if } i = j \\
slice(L, i, j - 1) \mathbin{+\!\!+} [ L_{(j)} ] & \text{if } i < j
\end{cases}
\end{aligned}
```

Defined at [List Utils](
	./src/main/scala/v1/list/ListUtils.scala#slice
) as follows:

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

### List Sum

```math
sum(L) = 
\begin{cases} \\
0 & \text{if } |L| = 0 \\
head(L) + sum(tail(L)) & \text{otherwise} \\
\end{cases}
```

Defined at [List Utils](
	./src/main/scala/v1/list/ListUtils.scala#sum
) as follows:

```scala
  def sum(loopList: List[BigInt]): BigInt = {
    if (loopList.isEmpty) {
      BigInt(0)
    } else {
      loopList.head + sum(loopList.tail)
    }
  }
```
## Properties

Using the definitions above, we state and verify the following key properties of lists:

### Tail Access Shift
```math
	tail(L)_{(i)} = L_{(i + 1)}
```
Proved in [List Utils Properties - Access Tail Shift](
./src/main/scala/v1/list/properties/ListUtilsProperties.scala#accessTailShift
) as follows:

```scala
  def accessTailShift[T](list: List[T], position: BigInt): Boolean = {
    require(list.nonEmpty && position >= 0 && position < list.tail.size)
    list.tail(position) == list(position + 1)
  }.holds
```

### Positional Shift in Tail
```math
i > 0 \implies L_{(i)} = 	tail(L)_{(i - 1)}
```

Proved in [List Util Properties - Assert Tail Shift Position](
./src/main/scala/v1/list/properties/ListUtilsProperties.scala#assertTailShiftPosition
)

```scala
  def assertTailShiftPosition[T](list: List[T], position: BigInt): Boolean = {
    require(list.nonEmpty)
    require(position >= 0 && position < list.size)
    decreases(position)

    if (position == 0 ) {
      list(position) == list.head
    } else {
      assert(list == List(list.head) ++ list.tail )
      assert(list(position) == list.apply(position) )
      assert(assertTailShiftPosition(list.tail, position - 1))
      assert(list.apply(position) == list.tail.apply(position - 1))
      list(position) == list.tail(position - 1)
    }
  }.holds
```

### Last Element Identity

```math
|L| > 0 \implies last(L) = L_{(|L| - 1)}
```
Proved in [List Util Properties - Assert Last Equals Last Position](
	./src/main/scala/v1/list/properties/ListUtilsProperties.scala#assertLastEqualsLastPosition
).

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

### Left Append Preserves Sum
```math
	sum([v] \mathbin{+\!\!+} L) = v + 	sum(L)
```

Proved in [List Utils Properties - List Sum Add Value](
./src/main/scala/v1/list/properties/ListUtilsProperties.scala#listSumAddValue
) as follows:

```scala
def listSumAddValue(list: List[BigInt], value: BigInt): Boolean = {
    ListUtils.sum(List(value) ++ list) == value + ListUtils.sum(list)
  }.holds
```


### Sum over Concatenation
```math
	sum(A \mathbin{+\!\!+} B) = 	sum(A) + 	sum(B)
```

Proved in [List Utils Properties - List Combine ](
./src/main/scala/v1/list/properties/ListUtilsProperties.scala#listCombine
) as follows:
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

### Commutativity of Sum over Concatenation
```math
	sum(A \mathbin{+\!\!+} B) = 	sum(B \mathbin{+\!\!+} A)
```

Proved in [List Utils Properties - List Swap ](
./src/main/scala/v1/list/properties/ListUtilsProperties.scala#listSwap
) as follows:

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

### Slice Append Consistency
```math
	slice(L, f, t) = 	slice(L, f, t-1) \mathbin{+\!\!+} [L(t)]
```

Proved in [List Utils Properties - Assert Append to Slice ](
./src/main/scala/v1/list/properties/ListUtilsProperties.scala#assertAppendToSlice
) as follows:

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

## Conclusion

This article presents a formal framework for defining and reasoning about finite lists using a 
recursive mathematical structure aligned with functional programming principles.

These properties are:

```math
\begin{aligned}
|L| > 0 & \implies last(L)   = L_{(|L| - 1)} \\
i > 0 	& \implies L_{(i)} 	 = tail(L)_{(i - 1)} \\
tail(L)_{(i)}                & = L_{(i + 1)} \\
sum([v] \mathbin{+\!\!+} L)  & = v + sum(L) \\
sum(A \mathbin{+\!\!+} B)    & = sum(A) + sum(B) \\
sum(A \mathbin{+\!\!+} B)    & = sum(B \mathbin{+\!\!+} A) \\
slice(L, f, t)               & = slice(L, f, t-1) \mathbin{+\!\!+} [L(t)] \\

\end{aligned}
```

These properties are implemented in Scala using the Stainless verification system,
ensuring correctness of properties and recursive functions through static guarantees.
This foundation supports further extensions in formally verified functional data structures
and serves as a practical bridge between mathematical definitions and executable code.

The properties and definitions presented here can be extended to more complex data structures
and algorithms, providing a solid foundation for future work in formal verification and
mathematical reasoning in functional programming.


