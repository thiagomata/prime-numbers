# Using Formal Verification to Prove Properties of Lists Recursively Defined

## Abstract

<div align="justify">
<p style="text-align: justify">
In this article, we define and construct lists from scratch, relying only on core type 
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

## Introduction

Lists are finite sequences of values that support a wide range of operations in functional 
and declarative programming. When combined with summation, they form the backbone for 
definitions of sequences, recurrence, accumulation, and integration in the discrete domain.

Our approach mirrors traditional recursive definitions but is formally verified 
using [Scala Stainless](https://epfl-lara.github.io/stainless/intro.html), 
ensuring that the properties hold under all inputs within the specified constraints.

> Formal verification is the act of proving or disproving the correctness of 
> intended algorithms underlying a system with respect to a certain formal 
> specification or property, using formal methods of mathematics.
> [— Wikipedia on Formal Verification](https://en.wikipedia.org/wiki/Formal_verification)

## Limitations

This article restricts the implementation and verification to immutable, 
finite lists of integers represented using the `stainless.collection.List` data type. 
The focus is on **correctness**, not on performance or scalability. Our summation and 
accumulation models follow a **recursive definition**, which is faithful to mathematical 
formalism.
However, this can introduce performance limitations in practical use when dealing 
with extensive lists.

In particular:

- **Overflow and memory limits are out of scope**: Since we use `BigInt` and immutable lists, 
the model assumes unbounded integer arithmetic and infinite list capacity. This approach avoids 
issues like overflow or out-of-memory errors, but it does not reflect the constraints 
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

Let $𝕃$ be the set of all lists over a set $S$.
A list is either the empty $L_{e}$ or a non-empty list $L_{node}$, as follows:

### Empty List

Let's define an empty list $L_{e}$:

```math
\begin{aligned}
L_{e} & \in 𝕃 \\
L_{e} & = [] \\
\end{aligned}
```

### Recursive Definition of List

```math
\begin{aligned}
\text{ head } & \in 𝕊 \\
\text{ tail } & \in 𝕃 \\
L_{node}(\text{head}, \text{tail}) & \in 𝕃_{node} \\
𝕃 = \{ L_e \}  \cup \{ L_{node}(\text{head}, \text{tail}) & \mid \text{head} \in 𝕊,\ \text{tail} \in 𝕃 \} \\
\end{aligned}
```

#### Termination and Cyclic References

Because all lists in this model are immutable, each application of $L_{\text{node}}(\text{head}, \text{tail})$ 
produces a distinct structural value without the possibility of cyclic references. 
Recursive functions over $𝕃$ terminate naturally, as size is defined by a strictly decreasing structure.


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
We define the size of a list $L$, $|L|$ as follows:

```math
|L| = \begin{cases} \\
0 & \text{ if } L = L_{e} \\\
1 + |tail(L)| & \text{otherwise} \\
\end{cases}
```

Proved in the native stainless library in `stainless.collection.List`.


### List Append

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

### List Slice

Given a list $L = [v_0, v_1, \dots, v_{n-1}]$, and integers 
$0 \leq i \leq j < |L|$, the slice function $slice(L, i, j)$ 
returns a sublist of $L$ from index $i$ to $j$, inclusive.

```math
\begin{aligned}
L[i \dots j] = slice(L, i, j) = 
\begin{cases}
[ L_{(j)} ] & \text{if } i = j \\
slice(L, i, j - 1) ⧺ [ L_{(j)} ] & \text{if } i < j
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

### Sum matches Summation

We can prove that the recursive `sum` function over a list $L$ matches the mathematical definition 
of the summation $\sum_{i=0}^{n-1} x_i$, where $L = [x_0, x_1, \dots, x_{n-1}]$, $|L| = n$.

#### Base Case: $|L| = 0$

```math
\begin{aligned}
\text{sum}(L) &= 0 & \text{[by definition of sum]} \\
\sum L &= 0 & \text{[summation over empty list]} \\
\Rightarrow \text{sum}(L) &= \sum L \in 𝕃
\end{aligned}
```

```math
\begin{aligned}
\therefore \\
\forall \text{ } L \in 𝕃 \\
|L| = 0 \implies \text{sum}(L) = \sum L \\
\end{aligned}
```

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
\forall\text{ }  L \in 𝕃 \\
|L| > 0 \text{ } \implies \text{ sum}(L) = \sum L  \\
$$

Hence, by induction on the size of $L$:

```math
\begin{aligned}
\forall \text{ } L \text{ } \in 𝕃 \\
\text{sum}(L)  = \sum L = \sum_{i=0}^{n-1} x_i  \in 𝕊 \quad \text{[Q.E.D.]} \\
\end{aligned}
```


### Tail Access Shift

```math
\forall \text{ } L,\ i,\quad |L| > 1 \land 0 \le i < |\text{tail}(L)| \implies \text{tail}(L)_{(i)} = L_{(i + 1)}
```

Since:

$$
\begin{aligned}
L_{node(n)} & = L_{(n)} = tail(L_{node})({n - 1}) \text{ } \forall \text{ } n > 0
\end{aligned}
$$


Proved in [List Utils Properties - Access Tail Shift](
./src/main/scala/v1/list/properties/ListUtilsProperties.scala#accessTailShift
) as follows:

```scala
  def accessTailShift[T](list: List[T], position: BigInt): Boolean = {
    require(list.nonEmpty && position >= 0 && position < list.tail.size)
    list.tail(position) == list(position + 1)
  }.holds
```

$$
\forall L,\ i,\quad |L| > 1 \land i > 0 \implies L_{(i)} = 	tail(L)_{(i - 1)}
$$


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
\text{sum}([x] ⧺ L) & = x + \text{sum}(L) &  \qquad \text{[Q.E.D.]} \\
\end{aligned}
$$


Verified in [List Utils Properties - List Sum Add Value](
./src/main/scala/v1/list/properties/ListUtilsProperties.scala#listSumAddValue
) as follows:

```scala
def listSumAddValue(list: List[BigInt], value: BigInt): Boolean = {
    ListUtils.sum(List(value) ++ list) == value + ListUtils.sum(list)
  }.holds
```

### Sum over Concatenation
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
	sum(A ⧺ B) = 	sum(A) + 	sum(B) &  \qquad \text{[Q.E.D.]} \\
\end{aligned}
$$

Verified in [List Utils Properties - List Combine ](
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
	sum(A ⧺ B) = 	sum(B ⧺ A)
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
	L[f, \dots, t] = slice(L, f, t) = 	slice(L, f, t-1) ⧺ [L(t)]
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
tail(L)_{(i)}                 & = L_{(i + 1)} \\
sum([v] ⧺ L)                  & = v + sum(L) \\
sum(A ⧺ B)                    & = sum(A) + sum(B) \\
sum(A ⧺ B)                    & = sum(B ⧺ A) \\
L[f, \dots, t ] = slice(L, f, t) & = slice(L, f, t-1) ⧺ [L(t)] \\

\end{aligned}
```

These properties are implemented in Scala using the Stainless verification system, ensuring 
the correctness of properties and recursive functions through static guarantees. 
This foundation supports further extensions in formally verified functional data structures, 
serving as a practical bridge between mathematical definitions and executable code.

The properties and definitions presented here can be extended to more complex data structures
and algorithms, providing a solid foundation for future work in formal verification and
mathematical reasoning in functional programming.

## Appendix

### On Generalization to Arbitrary Numeric Types

In this article, the mathematical proofs and properties were not restricted, working for any universe $𝕊$ with numberic operations.
When we verified these properties, we focused on lists of `BigInt` to avoid issues of overflow and rounding and to simplify formal reasoning.
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


