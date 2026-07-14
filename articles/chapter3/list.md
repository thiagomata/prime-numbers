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

This article verifies:

- Index and access: tail shift, last element — §3
- Slice: recursive, index-range, append consistency — §4
- Sum: definition, concatenation, commutativity — §5
- Product: definition, concatenation, commutativity, positivity — §6
- Product divisibility: head, all elements, inserted element — §7
- Bound and order: all-greater-than propagation — §8
- Slice equivalence — §9
- Shifted list: period, gap identity, gap translation — §10
- Rotation: permutation invariants (size, sum, bounds, membership) — §11

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
|L| = \begin{cases}
0 & \text{ if } L = L_{e} \\\
1 + |tail(L)| & \text{otherwise} \\
\end{cases}
```

Proved in the native stainless library in `stainless.collection.List`.


### 2.6 List Append

Let $A, B \in 𝕃$ over some set $S$. The append operation $A \mathbin{+\!+} B$ is defined recursively as:

```math
\begin{aligned}
A \mathbin{+\!+} B =
\begin{cases}
B & \text{if } A = L_e \\
L_{node}(head(A), tail(A) \mathbin{+\!+} B) & \text{otherwise}
\end{cases}
\end{aligned}
```

Proved in the native stainless library in `stainless.collection.List`.

### 2.7 List Slice

Let $L = [v_0, v_1, \dots, v_{n-1}]$, $i, j \in \mathbb{N}$, with $i \leq j < n$.

$$
L[i \dots j] := [ L_k \mid k \in \mathbb{N},\ i \leq k \leq j ]
$$

The implementation of `slice` is available in [ListUtils](
	../../src/main/scala/v1/chapter3/list/ListUtils.scala#slice
). The full Scala verification code is in Appendix A.3.

### 2.8 List Sum

Let $\text{sum} : 𝕃 \implies 𝕊$ be a recursively defined function:

```math
sum(L) = 
\begin{cases} \\
0 & \text{if } L = L_e \\
head(L) + sum(tail(L)) & \text{otherwise} \\
\end{cases}
```

The implementation of `sum` is available in [ListUtils](
	../../src/main/scala/v1/chapter3/list/ListUtils.scala#sum
). The full Scala verification code is in Appendix A.1.

### 2.9 List Product

Let $\text{product} : 𝕃 \implies 𝕊$ be a recursively defined function:

```math
product(L) = 
\begin{cases} \\
1 & \text{if } L = L_e \\
head(L) \cdot product(tail(L)) & \text{otherwise} \\
\end{cases}
```

The implementation of `product` is available in [ListProduct](
	../../src/main/scala/v1/chapter3/list/properties/ListProduct.scala
). The full Scala verification code is in Appendices A.11 through A.15.

## 3. Index and Access Properties

How positions shift when the list is decomposed into head and tail, and how the last element relates to its index.

- Tail access shift: `tail(L)(i) = L(i + 1)` for `i < |tail(L)|`
- Last element identity: `list(size - 1) = list.last`

### 3.1 Tail Access Shift

**Lemma:** For any list $L$ with at least two elements, accessing the $i$-th element of its tail is equivalent to accessing the $(i + 1)$-th element of the list.

```math
\forall \text{ } L,\ i,\quad 1 < |L|, 0 \le i < |\text{tail}(L)| \implies \text{tail}(L)_{(i)} = L_{(i + 1)}
```

Since:

$$
\begin{aligned}
L &= [x_0, x_1, x_2, \dots, x_{n - 1}]                                & \qquad \text{[List definition]} \\
L &= [x_0] \mathbin{+\!+} [x_1, x_2, \dots, x_{n - 1}]                             & \qquad \text{[Concatenation definition]} \\
L &= \text{head}(L) \mathbin{+\!+} \text{tail}(L)                                  & \qquad \text{[Head and Tail definition]} \\
\text{tail}(L) &= [x_1, x_2, \dots, x_{n - 1}]                        & \qquad \text{[Tail definition]} \\
L{i} &= x_i = \text{tail}(L){(i + 1)} \text{ } \forall \text{ }  0 < i < |L|  \quad \blacksquare & \qquad \text{[Q.E.D.]} \\
\end{aligned}
$$

This property is verified in the [
  ListUtilsProperties::accessTailShiftRight
](
  ../../src/main/scala/v1/chapter3/list/properties/ListUtilsProperties.scala
). The full Scala verification code is in Appendix A.1.

### 3.2 Last Element Identity

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

This property is verified in the [
  ListUtilsProperties::assertLastEqualsLastPosition
](
  ../../src/main/scala/v1/chapter3/list/properties/ListUtilsProperties.scala
). The full Scala verification code is in Appendix A.2.

## 4. Slice Properties

Four constructions for extracting a sublist by index range — all equivalent.

- Tail-recursive slice: builds from the end by prepending
- Head-recursive slice: builds from the front
- Index-range slice: accumulates by position within a range
- Slice append consistency: appending a singleton preserves the slice structure

### 4.1 Tail-Recursive Slice

The tail-recursive slice builds the sublist from the end, prepending elements as it recurses backward.

```math
\forall \text{ } L \in 𝕃, \forall \text{ } i, j \in \mathbb{N},\ i \leq j < |L|
```

```math
\text{slice}(L, i, j) := 
\begin{cases}
[ L_j ] & \text{if } i = j \\
\text{slice}(L, i, j - 1) \mathbin{+\!+} [ L_j ] & \text{if } i < j
\end{cases}
```

**Goal**:

```math
\forall \text{ } L \in 𝕃, \forall \text{ } i, j \in \mathbb{N},\ i \leq j < |L| \implies \text{slice}(L, i, j) = L[i \dots j]
```

**Proof by induction on $j$, with fixed $i$**

**Base case**: $j = i$

```math
\text{slice}(L, i, i) = [ L_i ] = L[i \dots i]
```

**Inductive step**: Assume

```math
\text{slice}(L, i, j - 1) = [ L_k \mid i \leq k \leq j - 1 ]
```

Show:

```math
\begin{aligned}
\text{slice}(L, i, j)  &= \text{slice}(L, i, j - 1) \mathbin{+\!+} [L_j] & \qquad \text{[by definition of slice]} \\
&= L[i \dots (j - 1)] \mathbin{+\!+} [L_j] & \qquad \text{[by Inductive Hypothesis]} \\
&= [ L_k \mid i \leq k \leq j - 1 ] \mathbin{+\!+} [L_j] & \qquad \text{[by Specification]} \\
&= [ L_k \mid i \leq k \leq j ] & \qquad \text{[by definition of Concatenation]} \\
&= L[i \dots j] & \qquad  \text{[Q.E.D]} \\
\end{aligned}
```

```math
\therefore
```

```math
\forall \text{ } 0 \leq i \leq j < |L|,\ \text{slice}(L, i, j) = L[i \dots j]
\quad \blacksquare
```

This property is verified in the [
  ListUtils::slice
](
  ../../src/main/scala/v1/chapter3/list/ListUtils.scala
). The implementation and verification code are in Appendix A.3.

### 4.2 Head-Recursive Slice

The head-recursive slice builds the sublist from the front, cons-ing elements as it recurses forward.

```math
\forall \text{ } L \in 𝕃, \forall \text{ } i, j \in \mathbb{N},\ i \leq j < |L|
```

```math
\text{headRecursiveSlice}(L, i, j) :=
\begin{cases}
[ L_i ] & \text{if } i = j \\
L_i \mathbin{+\!+} \text{headRecursiveSlice}(L, i + 1, j) & \text{if } i < j
\end{cases}
```

**Goal**:

```math
\forall \text{ } L \in 𝕃, \forall \text{ } i, j \in \mathbb{N},\ i \leq j < |L| \implies \text{headRecursiveSlice}(L, i, j) = L[i \dots j]
```

**Proof by induction on $j - i$**

**Base case**: $i = j$

```math
\text{headRecursiveSlice}(L, i, i) = [ L_i ] = L[i \dots i]
```

**Inductive step**: Assume

```math
\text{headRecursiveSlice}(L, i + 1, j) = [ L_k \mid i + 1 \leq k \leq j ]
```

Show:

```math
\begin{aligned}
\text{headRecursiveSlice}(L, i, j) &= L_i \mathbin{+\!+} \text{headRecursiveSlice}(L, i + 1, j) & \qquad \text{[by definition]} \\
&= L_i \mathbin{+\!+} L[i + 1 \dots j] & \qquad \text{[by Inductive Hypothesis]} \\
&= [ L_k \mid i \leq k \leq j ] = L[i \dots j] & \qquad \text{[by specification]} \\
\end{aligned}
```

```math
\therefore
```

```math
\forall \text{ } 0 \leq i \leq j < |L|,\ \text{headRecursiveSlice}(L, i, j) = L[i \dots j]
\quad \blacksquare
```

This property is verified in the [
  SliceEquivalenceLemmas::headRecursiveSlice
](
  ../../src/main/scala/v1/chapter3/list/properties/SliceEquivalenceLemmas.scala
). The full Scala verification code is in Appendix A.4.

### 4.3 Index-Range Slice

The index-range slice builds the sublist by direct index access, recursing forward through the index range.

```math
\forall \text{ } L \in 𝕃, \forall \text{ } i, j \in \mathbb{N},\ i \leq j < |L|
```

```math
\text{indexRangeValues}(L, i, j) :=
\begin{cases}
[ L_i ] & \text{if } i = j \\
L_i \mathbin{+\!+} \text{indexRangeValues}(L, i + 1, j) & \text{if } i < j
\end{cases}
```

**Goal**:

```math
\forall \text{ } L \in 𝕃, \forall \text{ } i, j \in \mathbb{N},\ i \leq j < |L| \implies \text{indexRangeValues}(L, i, j) = L[i \dots j]
```

**Proof by induction on $j - i$**

**Base case**: $i = j$

```math
\text{indexRangeValues}(L, i, i) = [ L_i ] = L[i \dots i]
```

**Inductive step**: Assume

```math
\text{indexRangeValues}(L, i + 1, j) = [ L_k \mid i + 1 \leq k \leq j ]
```

Show:

```math
\begin{aligned}
\text{indexRangeValues}(L, i, j) &= L_i \mathbin{+\!+} \text{indexRangeValues}(L, i + 1, j) & \qquad \text{[by definition]} \\
&= L_i \mathbin{+\!+} L[i + 1 \dots j] & \qquad \text{[by Inductive Hypothesis]} \\
&= [ L_k \mid i \leq k \leq j ] = L[i \dots j] & \qquad \text{[by specification]} \\
\end{aligned}
```

```math
\therefore
```

```math
\forall \text{ } 0 \leq i \leq j < |L|,\ \text{indexRangeValues}(L, i, j) = L[i \dots j]
\quad \blacksquare
```

This property is verified in the [
  SliceEquivalenceLemmas::indexRangeValues
](
  ../../src/main/scala/v1/chapter3/list/properties/SliceEquivalenceLemmas.scala
). The full Scala verification code is in Appendix A.5.

### 4.4 Slice Append Consistency

**Lemma:** A slice of a list from index $f$ to $t$ can be expressed as the slice from $f$ to $t - 1$ concatenated with the element at index $t$, for $f \le t < |L|$.

```math
\begin{aligned}
L[f \dots t] &= \text{slice}(L, f, t) \\
             &= \text{slice}(L, f, t - 1) \mathbin{+\!+} [L_t] \\
             &= L[f \dots t - 1] \mathbin{+\!+} [L_t]  \quad \blacksquare
\end{aligned}
```

This property is verified in the [
  ListUtilsProperties::assertAppendToSlice
](
  ../../src/main/scala/v1/chapter3/list/properties/ListUtilsProperties.scala
). The full Scala verification code is in Appendix A.6.

## 5. Sum Properties

The recursive `sum` matches the mathematical summation, and addition commutes over concatenation.

- Sum matches summation: `sum(L) = Σ L[i]` for `i = 0..size-1`
- Left append preserves sum: `sum(x :: L) = x + sum(L)`
- Sum over concatenation: `sum(A ++ B) = sum(A) + sum(B)`
- Commutativity of sum: `sum(A ++ B) = sum(B ++ A)`

### 5.1 Sum matches Summation

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

```math
\therefore
```

```math
\forall \text{ } L \in 𝕃 \\
|L| = 0 \implies \text{sum}(L) = \sum L \\
```

#### Inductive Step: $|L| > 0$

Let $P \in 𝕃$, with $P = [x_1, x_2, \dots, x_{n-1}] \in 𝕃$, and assume:

```math
\begin{aligned}
\text{sum}(P) & = \sum_{i=1}^{n-1} x_i \in & \qquad \text{[by Inductive Hypothesis]} \\
L = [x_0] \mathbin{+\!+} P & = [x_0, x_1, \dots, x_n]   & \qquad \text{[by Definition of Concatenation]} \\
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

```math
\therefore \\
```

```math
\forall\text{ }  L \in 𝕃 \\
|L| > 0 \text{ } \implies \text{ sum}(L) = \sum L  \\
```

Hence, by induction on the size of $L$:

```math
\forall \text{ } L \text{ } \in 𝕃 \\
\text{sum}(L)  = \sum L = \sum_{i=0}^{n-1} x_i  \in 𝕊  \quad \blacksquare \quad \text{[Q.E.D.]} \\
```

This property is verified in the [
  ListUtils::sum
](
  ../../src/main/scala/v1/chapter3/list/ListUtils.scala
). The implementation and verification code are in Appendix A.7.

### 5.2 Left Append Preserves Sum

The sum of a list with an element prepended equals the element plus the sum of the original list.

```math
\begin{aligned}
\forall \text{ } x \in 𝕊 \\
\text{sum}([x] \mathbin{+\!+} L ) = x + \text{sum}(L) \\
\end{aligned}
```

Proof:

```math
\begin{aligned}
A & = [x] \mathbin{+\!+} L  & \qquad \text{[Concatenation]} \\
\text{sum}(A) & = \text{head}(A) + \text{sum}(\text{tail}(A)) & \qquad \text{[By recursive definition of sum]} \\
              & = x + \text{sum}(L) & \qquad \text{[By recursive definition of head and tail]} \\
\end{aligned}
```

```math
\therefore
```

```math
\begin{aligned}
\text{sum}([x] \mathbin{+\!+} L) & = x + \text{sum}(L)  \quad \blacksquare &  \qquad \text{[Q.E.D.]} \\
\end{aligned}
```

This property is verified in the [
  ListUtilsProperties::listSumAddValue
](
  ../../src/main/scala/v1/chapter3/list/properties/ListUtilsProperties.scala
). The full Scala verification code is in Appendix A.8.

### 5.3 Sum over Concatenation

The sum of two concatenated lists equals the sum of each list added together.

```math
	sum(A \mathbin{+\!+} B) = 	sum(A) + 	sum(B)
```

#### If List A is Empty

```math
\begin{aligned}
  A \mathbin{+\!+} B & = L_e \mathbin{+\!+} B & \text{[A is empty list]} \\
        & = B & \text{[By definition of concatenation]} \\
  \text{sum}(A) & = 0 & \text{[By definition of sum]} \\
  \text{sum}(A \mathbin{+\!+} B) & = \text{sum}(B) & \text{[Since A} \mathbin{+\!+} \text{B equals B]} \\
                    & = 0 + \text{sum}(B) \\
                    & = \text{sum}(A) + \text{sum}(B) & \text{[Since sum(A) is zero]} \\
\end{aligned}
```

#### If list A is Non-Empty

```math
\begin{aligned}
C & = \text{tail}(A) \mathbin{+\!+} B \\
\text{sum}(A) & = \text{head}(A) + \text{sum}(\text{tail}(A))                & \text{[By definition of sum]} \\
C & = \text{sum}(\text{tail}(A)) + \text{sum}(B)                           & \text{[Inductive Step]} \\
A \mathbin{+\!+} B & = [\text{head}(A)] \mathbin{+\!+} (\text{tail}(A) \mathbin{+\!+} B)                          & \text{[By definition of head and tail]} \\
\text{sum}(A \mathbin{+\!+} B) & = \text{head}(A) + \text{sum}(\text{tail}(A) \mathbin{+\!+} B)      & \text{[By definition of sum]} \\
                  & = head(A) + \text{sum}(\text{tail}(A)) + \text{sum}(B) & \text{[By definition of C]} \\
                  & = \text{sum}(A) + \text{sum}(B)                        & \text{[Substituting]} \\
\end{aligned}
```

```math
\therefore
```

```math
\begin{aligned}
	sum(A \mathbin{+\!+} B) = 	sum(A) + 	sum(B) & \quad \blacksquare \qquad \text{[Q.E.D.]} \\
\end{aligned}
```

This property is verified in the [
  ListUtilsProperties::listCombine
](
  ../../src/main/scala/v1/chapter3/list/properties/ListUtilsProperties.scala
). The full Scala verification code is in Appendix A.9.

### 5.4 Commutativity of Sum over Concatenation

The order of concatenation does not affect the total sum.

```math
	sum(A \mathbin{+\!+} B) = sum(B \mathbin{+\!+} A)
```

Since:
```math
\begin{aligned}
	sum(A \mathbin{+\!+} B) & = sum(A) + sum(B)                        & \text{[Sum over Concatenation]} \\
	sum(B \mathbin{+\!+} A) & = sum(B) + sum(A)                        & \text{[Sum over Concatenation]} \\
	sum(B) + sum(A) & = sum(A) + sum(B)                   & \text{[Distributive]} \\
	sum(B \mathbin{+\!+} A) & = sum(A \mathbin{+\!+} B)  \quad \blacksquare         & \text{[Q.E.D]} \\
\end{aligned}
```

This property is verified in the [
  ListUtilsProperties::listSwap
](
  ../../src/main/scala/v1/chapter3/list/properties/ListUtilsProperties.scala
). The full Scala verification code is in Appendix A.10.

## 6. Product Properties

The product operation, from singleton identity through concatenation distributivity to positivity.

- Singleton product: `product([x]) = x`
- Product pull-out element: `product(x :: L) = x * product(L)`
- Product over concatenation: `product(A ++ B) = product(A) * product(B)`
- Commutativity of product: `product(A ++ B) = product(B ++ A)`
- Positive product: product of all-positive list is positive

### 6.1 Singleton Product

The product of a singleton list containing $x$ is $x$.

```math
\forall \text{ } x \in 𝕊 \\
\text{product}([x]) = x
```

Proof:
```math
\begin{aligned}
\text{product}([x]) &= \text{head}([x]) \cdot \text{product}(\text{tail}([x])) & \qquad \text{[by definition of product]} \\
&= x \cdot \text{product}([]) & \qquad \text{[by definition of head and tail]} \\
&= x \cdot 1 & \qquad \text{[product of empty list is 1]} \\
&= x \quad \blacksquare & \qquad \text{[Q.E.D.]} \\
\end{aligned}
```

This property is verified in the [
  ListProduct::singletonProduct
](
  ../../src/main/scala/v1/chapter3/list/properties/ListProduct.scala
). The full Scala verification code is in Appendix A.11.

### 6.2 Product Pull-Out Element

A single element can be factored out of the product of a concatenated list.

```math
\forall \text{ } listA, listB \in 𝕃, \forall \text{ } e \in 𝕊 \\
\text{product}(listA \mathbin{+\!+} [e] \mathbin{+\!+} listB) = e \cdot \text{product}(listA \mathbin{+\!+} listB)
```

**Proof by induction on $listA$**

**Base case**: $listA = L_e$

```math
\begin{aligned}
\text{product}(L_e \mathbin{+\!+} [e] \mathbin{+\!+} listB) &= \text{product}([e] \mathbin{+\!+} listB) & \qquad \text{[by definition of append]} \\
&= e \cdot \text{product}(listB) & \qquad \text{[by definition of product]} \\
&= e \cdot \text{product}(L_e \mathbin{+\!+} listB) \quad \blacksquare & \qquad \text{[Q.E.D.]} \\
\end{aligned}
```

**Inductive step**: Assume for $listA$, prove for $\text{head}(A) :: listA$.

This property is verified in the [
  ListProduct::productPullOutElement
](
  ../../src/main/scala/v1/chapter3/list/properties/ListProduct.scala
). The full Scala verification code is in Appendix A.12.

### 6.3 Product over Concatenation

Product distributes over list concatenation.

```math
\forall \text{ } listA, listB \in 𝕃 \\
\text{product}(listA \mathbin{+\!+} listB) = \text{product}(listA) \cdot \text{product}(listB)
```

**Proof by induction on $listA$**

**Base case**: $listA = L_e$

```math
\begin{aligned}
\text{product}(L_e \mathbin{+\!+} listB) &= \text{product}(listB) & \qquad \text{[by definition of append]} \\
&= 1 \cdot \text{product}(listB) & \qquad \text{[1 is multiplicative identity]} \\
&= \text{product}(L_e) \cdot \text{product}(listB) \quad \blacksquare & \qquad \text{[Q.E.D.]} \\
\end{aligned}
```

**Inductive step**: For $\text{head}(A) :: listA$, the recursive definition of product and the inductive hypothesis give the result.

This property is verified in the [
  ListProduct::productConcatLemma
](
  ../../src/main/scala/v1/chapter3/list/properties/ListProduct.scala
). The full Scala verification code is in Appendix A.13.

### 6.4 Commutativity of Product

Product is invariant under swapping concatenated blocks.

```math
\forall \text{ } listA, listB \in 𝕃 \\
\text{product}(listA \mathbin{+\!+} listB) = \text{product}(listB \mathbin{+\!+} listA)
```

Proof:
```math
\begin{aligned}
\text{product}(listA \mathbin{+\!+} listB) &= \text{product}(listA) \cdot \text{product}(listB) & \qquad \text{[Product over Concatenation]} \\
\text{product}(listB \mathbin{+\!+} listA) &= \text{product}(listB) \cdot \text{product}(listA) & \qquad \text{[Product over Concatenation]} \\
&= \text{product}(listA) \cdot \text{product}(listB) & \qquad \text{[Commutativity of multiplication]} \\
&= \text{product}(listA \mathbin{+\!+} listB) \quad \blacksquare & \qquad \text{[Q.E.D.]} \\
\end{aligned}
```

This property is verified in the [
  ListProduct::productConcatCommutative
](
  ../../src/main/scala/v1/chapter3/list/properties/ListProduct.scala
). The full Scala verification code is in Appendix A.14.

### 6.5 Positive Product

If every element of a list is strictly positive, then the product is strictly positive.

```math
\forall \text{ } elements \in 𝕃 \\
(\forall \text{ } x \in elements,\ x > 0) \implies \text{product}(elements) > 0
```

**Proof by induction on $elements$**

**Base case**: $elements = L_e$

```math
\begin{aligned}
\text{product}(L_e) &= 1 > 0 \quad \blacksquare
\end{aligned}
```

**Inductive step**: For $\text{head}(e) :: tail$, we have $e > 0$ and $\text{product}(tail) > 0$ by inductive hypothesis. The product of two positive numbers is positive.

This property is verified in the [
  ListProduct::positiveProduct
](
  ../../src/main/scala/v1/chapter3/list/properties/ListProduct.scala
). The full Scala verification code is in Appendix A.15.

## 7. Product Divisibility Properties

Every element of a list divides its total product.

- Head divides product: `product(L) mod L.head = 0`
- All elements divide product: every element divides `product(L)`
- Inserted element divides product: `x` divides `product(x :: L)`

### 7.1 Head Divides Product

The head of a positive list divides the product of the entire list.

```math
\forall \text{ } elements \in 𝕃,\ elements \neq L_e \\
(\forall \text{ } x \in elements,\ x > 0) \implies \text{product}(elements) \bmod \text{head}(elements) = 0
```

Proof:
```math
\begin{aligned}
\text{product}(elements) &= \text{head}(elements) \cdot \text{product}(\text{tail}(elements)) & \qquad \text{[by definition of product]} \\
\text{product}(elements) \bmod \text{head}(elements) &= (\text{head}(elements) \cdot \text{product}(\text{tail}(elements))) \bmod \text{head}(elements) \\
&= 0 \quad \blacksquare & \qquad \text{[by modulo identity]} \\
\end{aligned}
```

This property is verified in the [
  ListProductDiv::ListProductDiv
](
  ../../src/main/scala/v1/chapter3/list/properties/ListProductDiv.scala
). The full Scala verification code is in Appendix A.16.

### 7.2 All Elements Divide Product

Every element of a positive list divides the product of the list.

```math
\forall \text{ } elements \in 𝕃 \\
(\forall \text{ } x \in elements,\ x > 0) \implies (\forall \text{ } x \in elements,\ \text{product}(elements) \bmod x = 0)
```

**Proof by induction on $elements$**

**Base case**: $elements = L_e$ — vacuously true.

**Inductive step**: For $\text{head}(p) :: tail$, we have $\text{product}(elements) = p \cdot \text{product}(tail)$. By modulo identity, $p$ divides the product. By the inductive hypothesis, every element of $tail$ also divides $\text{product}(tail)$, and hence divides $p \cdot \text{product}(tail) = \text{product}(elements)$.

This property is verified in the [
  ListProductDiv::allElementsDivideProduct
](
  ../../src/main/scala/v1/chapter3/list/properties/ListProductDiv.scala
). The full Scala verification code is in Appendix A.17.

### 7.3 Inserted Element Divides Product

Inserting an element into a list guarantees that the resulting product is divisible by that element.

```math
\forall \text{ } prefix, suffix \in 𝕃,\ \forall \text{ } e \in 𝕊,\ e > 0 \\
(\forall \text{ } x \in prefix,\ x > 0),\ (\forall \text{ } x \in suffix,\ x > 0) \\
\implies \text{product}(prefix \mathbin{+\!+} [e] \mathbin{+\!+} suffix) \bmod e = 0
```

Proof:
```math
\begin{aligned}
\text{product}(prefix \mathbin{+\!+} [e] \mathbin{+\!+} suffix) &= e \cdot \text{product}(prefix \mathbin{+\!+} suffix) & \qquad \text{[Product Pull-Out Element]} \\
&= e \cdot k & \qquad \text{[where k = product(prefix} ++ \text{suffix)]} \\
\text{product}(prefix \mathbin{+\!+} [e] \mathbin{+\!+} suffix) \bmod e &= (e \cdot k) \bmod e = 0 \quad \blacksquare & \qquad \text{[Q.E.D.]} \\
\end{aligned}
```

This property is verified in the [
  ListProductDiv::insertedElementDividesProduct
](
  ../../src/main/scala/v1/chapter3/list/properties/ListProductDiv.scala
). The full Scala verification code is in Appendix A.18.

## 8. Bound and Order Properties

How the predicate `allGreaterThan` propagates from a whole list to its elements and through concatenation.

- All greater than at index: `allGreaterThan(L, v) ⇒ L(pos) > v`
- Append preserves all greater than: `allGreaterThan(A, v) ∧ allGreaterThan(B, v) ⇒ allGreaterThan(A ++ B, v)`
- All greater than head and tail: the head/tail decomposition propagates the bound
- Index checking lemmas: efficient bound verification

### 8.1 All Greater Than at Index

For every list where all elements are greater than a value, any element at a valid position is also greater than that value.

```math
\forall \text{ } list \in 𝕃,\ \forall \text{ } value \in 𝕊,\ \forall \text{ } pos \in ℕ \\
\text{allGreaterThan}(list, value) \wedge 0 \leq pos < |list| \implies list(pos) > value
```

This property is verified in the [
  ListBoundUtils::assertGreaterThanAtIndex
](
  ../../src/main/scala/v1/chapter3/list/ListBoundUtils.scala
). The full Scala verification code is in Appendix A.19.

### 8.2 Append Preserves All Greater Than

If both lists have all elements greater than a value, then their concatenation also has all elements greater than that value.

```math
\forall \text{ } listA, listB \in 𝕃,\ \forall \text{ } value \in 𝕊 \\
\text{allGreaterThan}(listA, value) \wedge \text{allGreaterThan}(listB, value) \\
\implies \text{allGreaterThan}(listA \mathbin{+\!+} listB, value)
```

This property is verified in the [
  ListBoundUtils::assertAppendGreaterThan
](
  ../../src/main/scala/v1/chapter3/list/ListBoundUtils.scala
). The full Scala verification code is in Appendix A.20.

### 8.3 All Greater Than Head and Tail

For a non-empty list where all elements are greater than a value, the head is greater than that value and the tail also satisfies the property.

```math
\forall \text{ } list \in 𝕃,\ list \neq L_e,\ \forall \text{ } value \in 𝕊 \\
\text{allGreaterThan}(list, value) \implies list.head > value \wedge \text{allGreaterThan}(list.tail, value)
```

This property is verified in the [
  ListBoundUtils::assertGreaterThanHeadTail
](
  ../../src/main/scala/v1/chapter3/list/ListBoundUtils.scala
). The full Scala verification code is in Appendix A.21.

### 8.4 Check All Bigger at Index

For every list where all elements are bigger than a value, any element at a valid position is also bigger.

```math
\forall \text{ } list \in 𝕃,\ \forall \text{ } value \in 𝕊,\ \forall \text{ } pos \in ℕ \\
\text{checkAllBiggerThanValue}(list, value) \wedge 0 \leq pos < |list| \implies list(pos) > value
```

This property is verified in the [
  ListUtilsProperties::checkAllBiggerThanValueAtIndex
](
  ../../src/main/scala/v1/chapter3/list/properties/ListUtilsProperties.scala
). The full Scala verification code is in Appendix A.22.

### 8.5 Check All Bigger Head and Tail

For a non-empty list where all elements are bigger than a value, the head is bigger and the tail also satisfies the property.

```math
\forall \text{ } list \in 𝕃,\ list \neq L_e,\ \forall \text{ } value \in 𝕊 \\
\text{checkAllBiggerThanValue}(list, value) \implies list.head > value \wedge \text{checkAllBiggerThanValue}(list.tail, value)
```

This property is verified in the [
  ListUtilsProperties::checkAllBiggerThanValueHeadTail
](
  ../../src/main/scala/v1/chapter3/list/properties/ListUtilsProperties.scala
). The full Scala verification code is in Appendix A.23.

## 9. Equivalence Properties

All three slice constructions produce identical results for every valid input.

- Slice equivalence: tail-recursive, head-recursive, and index-range slices are identical for all valid inputs

### 9.1 Slice Equivalence Lemma

All three slice implementations — tail-recursive, head-recursive, and index-range — produce the same result for any valid input.

```math
\forall \text{ } L \in 𝕃,\ \forall \text{ } i, j \in \mathbb{N},\ i \leq j < |L| \\
\text{slice}(L, i, j) = \text{headRecursiveSlice}(L, i, j) = \text{indexRangeValues}(L, i, j)
```

**Proof by induction on $j - i$**

**Base case**: $i = j$ — all three produce $[L_i]$.

**Inductive step**: For $i < j$, each function decomposes into a head element plus a recursive call on $(i+1, j)$ or $(i, j-1)$. By the inductive hypothesis, the recursive calls produce equal sublists, and the head element is the same, so the results are equal.

This property is verified in the [
  SliceEquivalenceLemmas::tailHeadAndIndexRangeSlicesAreEqual
](
  ../../src/main/scala/v1/chapter3/list/properties/SliceEquivalenceLemmas.scala
). The full Scala verification code is in Appendix A.24.

## 10. Shifted List Properties

A shifted list advances the head by one gap and re-indexes positions. Three lemmas characterize this operation.

- Same period: shifting does not change the period (gap list length)
- Adjacent difference equals gap: `apply(i + 1) - apply(i) = gaps(i)`
- Gap translation: shifting translates the gap sequence by one index

A shifted list is a value sequence viewed one position later, with
the head advanced by the first gap. Unlike rotation (which re-indexes without
changing values), a shift changes the head and re-indexes positions.

Shifting is the list-level operation that advances a
position in a cumulative value sequence. When a sequence of adjacent
differences is known (the gap list), advancing the head by the first gap
and rotating the gap list yields the view from the next position — without
recomputing the cumulative sums.

```math
\begin{aligned}
\text{ShiftedList}(h,\; [g_0,\dots,g_{n-1}]) &: \text{head} = h,\; \text{gaps} = [g_0,\dots,g_{n-1}] \\
\text{shift}(h,\; [g_0,\dots,g_{n-1}]) &= \text{ShiftedList}(h + g_0,\; [g_1,\dots,g_{n-1}, g_0])
\end{aligned}
```

### 10.1 Same Period

Shifting does not change the period — the gap list remains the same length. The
structural property `size == gaps.size` is an invariant of the case class.

```math
\begin{aligned}
\text{shifted.size} = \text{original.size} \quad &\text{[Q.E.D.]}
\end{aligned}
```

### Stainless Verification

```scala
def assertSamePeriod(otherSize: BigInt): Boolean = {
  require(otherSize == gaps.size)
  size == otherSize
}.holds
```

### 10.2 Adjacent Difference Equals Gap

For any valid position, the difference between consecutive values equals the
gap at that position. This is a direct consequence of the integral-style
definition of `apply`.

```math
\begin{aligned}
\text{apply}(i + 1) - \text{apply}(i) = \text{gaps}(i)
\quad \text{for } 0 \leq i < \text{size} - 1 \quad &\text{[Q.E.D.]}
\end{aligned}
```

### Stainless Verification

```scala
def assertAdjacentDifferenceEqualsGap(position: BigInt): Boolean = {
  require(position >= 0)
  require(position + 1 < size)
  apply(position + 1) - apply(position) == gaps(position)
}.holds
```

### 10.3 Gap Translation

Shifting the head and rotating the gaps by one translates the adjacent-gap
sequence by one index: the shifted sequence's gap at `i` equals the original
sequence's gap at `i + 1`. Both sides reduce to `gaps(i + 1)` because the
gap list is rotated by one position.

```math
\begin{aligned}
\text{shifted.apply}(i + 1) - \text{shifted.apply}(i)
  &= \text{orig.apply}(i + 2) - \text{orig.apply}(i + 1)
  && \text{[Gap translation]} \\
  &= \text{gaps}(i + 1)
  && \text{[By adjacent-difference identity for both views]}
\end{aligned}
```

### Stainless Verification

```scala
def assertGapTranslation(
  origHead: BigInt, gaps: List[BigInt], i: BigInt
): Boolean = {
  require(gaps.nonEmpty)
  require(i >= 0)
  require(i + 2 < gaps.size)
  val shifted = shift(origHead, gaps)
  val orig = ShiftedList(origHead, gaps)
  shifted.apply(i + 1) - shifted.apply(i) ==
    orig.apply(i + 2) - orig.apply(i + 1)
}.holds
```

These properties are verified in the [
  ShiftedList::assertSamePeriod
](
  ../../src/main/scala/v1/chapter3/list/ShiftedList.scala
), [
  ShiftedList::assertAdjacentDifferenceEqualsGap
](
  ../../src/main/scala/v1/chapter3/list/ShiftedList.scala
), and [
  ShiftedList::assertGapTranslation
](
  ../../src/main/scala/v1/chapter3/list/ShiftedList.scala
).

## 11. Rotation Properties

Cyclic permutation preserves every structural invariant: the same elements, same size, same sum, and same bounds.

- Same elements: `rotateAt(L, k).contains(x) ⇔ L.contains(x)`
- Same size and sum: `|rotateAt(L, k)| = |L|`, `sum(rotateAt(L, k)) = sum(L)`
- Bound preservation: `allGreaterThan` and `allLessThan` survive rotation
- Index shift by one: `rotateAt(L, 1)(i) = L(i + 1)`

Rotating a list at index `k` swaps the front (first `k` elements)
and back (remaining elements) — a cyclic permutation. Rotation preserves every
structural invariant: size, sum, element membership, and bound properties are
unchanged, because the multiset of elements is the same under any cyclic
reordering.

Cyclic permutations arise whenever a fixed set of values
is viewed from a different starting position — for example, shifting a
circular buffer or aligning a periodic sequence. Rotation invariance means no
structural property is lost when the viewing window moves.

```math
\begin{aligned}
\text{rotateAt}(L,\; k) &= \text{back} \mathbin{++} \text{front}
  \quad\text{where } (\text{front},\; \text{back}) = \text{splitAt}(L, k) \\
  &= [L_k, L_{k+1}, \ldots, L_{n-1}, L_0, L_1, \ldots, L_{k-1}]
\end{aligned}
```

### 11.1 Permutation Invariants

Rotation is a permutation of the underlying multiset: the same elements appear,
and every structural quantity derived from the list is preserved.

**Membership.** An element belongs to the original list if and only if it
belongs to the rotated list. Since `append` order doesn't affect membership,
swapping `front` and `back` preserves the element set.

```math
\begin{aligned}
\text{rotateAt}(L, k).\text{contains}(x) &\iff L.\text{contains}(x)
  &&\text{[Q.E.D.]}
\end{aligned}
```

**Size and sum.** The rotated list has the same length and the same total sum.
Sum over `append` is additive and commutative.

```math
\begin{aligned}
|\text{rotateAt}(L, k)| &= |L| &&\text{[Same size]} \\
\sum \text{rotateAt}(L, k) &= \sum L &&\text{[Same sum]}
\end{aligned}
```

**Bound preservation.** If every element of `L` is strictly greater than `v`
(or strictly less than `b`), the same holds after rotation.

```math
\begin{aligned}
\text{allGreaterThan}(L, v) &\implies \text{allGreaterThan}(\text{rotateAt}(L, k), v) \\
\text{allLessThan}(L, b) &\implies \text{allLessThan}(\text{rotateAt}(L, k), b)
\end{aligned}
```

### 11.2 Index Shift Under Rotation by One

Rotating by one position and looking up index `k` gives the original list's
element at index `k + 1`. This is the lemma that underlies gap translation
in `ShiftedList`.

```math
\begin{aligned}
\text{rotateAt}(L, 1)(k) = L(k + 1) \quad \text{for } k + 1 < |L| \quad &
\text{[Q.E.D.]}
\end{aligned}
```

### Stainless Verification

```scala
def assertRotateContainsForward(
  list: List[BigInt], index: BigInt, x: BigInt
): Boolean = {
  require(index >= 0); require(list.contains(x))
  ListUtils.rotateAt(list, index).contains(x)
}.holds

def assertRotateSameSize(list: List[BigInt], index: BigInt): Boolean = {
  require(index >= 0)
  ListUtils.rotateAt(list, index).size == list.size
}.holds

def assertRotateSameSum(list: List[BigInt], index: BigInt): Boolean = {
  require(index >= 0)
  ListUtils.sum(ListUtils.rotateAt(list, index)) == ListUtils.sum(list)
}.holds

def assertRotateSameLowerBound(
  list: List[BigInt], index: BigInt, value: BigInt
): Boolean = {
  require(index >= 0); require(ListBoundUtils.allGreaterThan(list, value))
  ListBoundUtils.allGreaterThan(ListUtils.rotateAt(list, index), value)
}.holds

def assertRotatedAtIndexPlusOne(list: List[BigInt], k: BigInt): Boolean = {
  require(k + 1 < list.size)
  ListUtils.rotateAt(list, BigInt(1)).apply(k) == list.apply(k + 1)
}.holds
```

These properties are verified in the [
  RotationProperties
](
  ../../src/main/scala/v1/chapter3/list/properties/RotationProperties.scala
) module (11 lemmas total). The forward/backward membership pair and the
upper/lower bound pair cover all permutation invariants; the remaining
lemmas (`assertAppendContainsLeft/Right/Decompose/Swap`) are structural
helpers consumed by the main rotation proofs.

## 12. Conclusion

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
|L| > 0 &\implies L_{|L|-1} &=~ &\text{last}(L) \\
i > 0 &\implies L_i &=~ &\text{tail}(L)_{i-1} \\
i < |L| - 1,\, |L| > 1 &\implies \text{tail}(L)_i &=~ &L_{i+1} \\
\end{aligned}
```
```math
\begin{aligned}
&\sum L &=~ &\text{sum}(L)                                   \quad &\text{[Sum matches Summation]} \\
&\sum ([v] \mathbin{+\!+} L) &=~ &v + \sum L                 \quad &\text{[Left Append Preserves Sum]} \\
&\sum (A \mathbin{+\!+} B) &=~ &\sum A + \sum B              \quad &\text{[Sum over Concatenation]} \\
&\sum (A \mathbin{+\!+} B) &=~ &\sum (B \mathbin{+\!+} A)    \quad &\text{[Commutativity of Sum over Concatenation]} \\
&L[f \dots t] &=~ &L[f \dots {(t - 1)}] \mathbin{+\!+} [L_t] \quad &\text{[Slice Append Consistency]} \\
\end{aligned}
```
```math
\begin{aligned}
&\text{product}([x]) &=~ &x                     \quad &\text{[Singleton Product]} \\
&\text{product}(A \mathbin{+\!+} [e] \mathbin{+\!+} B) &=~ &e \cdot \text{product}(A \mathbin{+\!+} B) \quad &\text{[Product Pull-Out Element]} \\
&\text{product}(A \mathbin{+\!+} B) &=~ &\text{product}(A) \cdot \text{product}(B) \quad &\text{[Product over Concatenation]} \\
&\text{product}(A \mathbin{+\!+} B) &=~ &\text{product}(B \mathbin{+\!+} A) \quad &\text{[Commutativity of Product]} \\
&(\forall x \in L,\ x > 0) &\implies &\text{product}(L) > 0 \quad &\text{[Positive Product]} \\
\end{aligned}
```
```math
\begin{aligned}
&\text{product}(L) \bmod \text{head}(L) &= &0  &\text{[Head Divides Product]} \\
&\forall x \in L,\ \text{product}(L) \bmod x &=~ &0 \quad &\text{[All Elements Divide Product]} \\
&\text{product}(P \mathbin{+\!+} [e] \mathbin{+\!+} S) \bmod e &=~ &0 \quad &\text{[Inserted Element Divides Product]} \\
\end{aligned}
```

```math
\begin{aligned}
&\text{allGreaterThan}(L, v) &\implies~ &L(\text{pos}) > v \quad &\text{[Bound at Index]} \\
&\text{allGreaterThan}(L, v) &\implies~ &\text{allGreaterThan}(\text{rotateAt}(L, k), v) \quad &\text{[Rotation Same Bounds]} \\
&\text{allGreaterThan}(A, v) \land \text{allGreaterThan}(B, v)  &\implies~ &\text{allGreaterThan}(A \mathbin{+\!+} B, v) \quad &\text{[Bound over Concatenation]} \\
\end{aligned}
```

```math
\begin{aligned}

&\text{GapList}(h, G).\text{apply}(i + 1) 
&-~ \quad 
&\text{GapList}(h, G).\text{apply}(i) \quad
&=~  \quad
&G(i) \quad 
&\text{[Adjacent Difference]} \\

&\text{rotateAt}(L, k).\text{contains}(x)
&\iff \quad
&L.\text{contains}(x) \quad 
&\quad
&\quad
&\text{[Rotation Same Elements]} \\

&|\text{rotateAt}(L, k)|
&=~   \quad
&|L|, \quad
&&&\text{[Rotation Same Size]} \\

&\sum\text{rotateAt}(L, k) 
&= \quad
&\sum L
&&&\text{[Rotation Same Sum]} \\

&\text{shift}(h, G).\text{apply}(i + 1) 
&- \quad
&\text{shift}(h, G).\text{apply}(i)
&=~ \quad
&\text{GapList}(h, G).\text{apply}(i + 2) - \text{GapList}(h, G).\text{apply}(i + 1)
&\text{[Gap Translation]} \\


&\text{slice}(L, f, t)
&=~ \quad
&\text{headRecursiveSlice}(L, f, t) 
&=  \quad
&\text{indexRangeValues}(L, f, t) \quad 
&\text{[Slice Equivalence]} \\
\end{aligned}
```


All properties are verified in the Stainless system. The full verification code is available in Appendix A.

## 13. Future Work

Extending lists via integration (cumulative sums) and derivation (gap extraction)
would formalize two dual operations that map between a list and its accumulated
or decomposed form. These operations connect the finite list algebra presented
here to the theory of discrete sequences and differences.

## 14. Limitations

This article restricts the implementation and verification to immutable,
 finite lists of integers represented using the `stainless.collection.List` data type. 
The focus is on **correctness**, not on performance or scalability. Our summation and
 accumulation models follow a **recursive definition**, aligned with mathematical formalism.
However, this approach may introduce performance limitations in practical applications involving large lists.

### 14.1 Overflow and Memory Limits Are Out of Scope

By using `BigInt` and immutable lists, the model assumes unbounded integer arithmetic and infinite list capacity. 
This choice avoids overflow and out-of-memory errors, but it does not reflect the constraints of fixed-size integer
 types or limited system memory in real-world environments.

### 14.2 Side Effects Are Excluded

All list operations are pure and referentially transparent. Mutation, I/O, and performance overhead are outside the 
 scope of this model.

### 14.3 No Parallelism or Laziness

Unlike streaming libraries or lazy sequences, this model is strictly eager and sequential, without support for parallel 
 computation or lazy evaluation.

### 14.4 Limitations Imposed by Stainless Verification Tool

Due to current limitations in the Scala Stainless verifier (version 0.9.8.8), formal proofs must often rely on concrete
 numeric types such as `BigInt`.
Stainless does not yet fully support generic numeric abstractions or type classes like `Numeric[T]`,
which hinders verification of implementations parameterized over arbitrary numeric types.

As a result, while the mathematical properties in this work conceptually apply to any numeric domain satisfying the 
required algebraic laws, practical verification is constrained to `BigInt`.
Overcoming these tool limitations is an important direction for future enhancements, enabling broader generality 
and more flexible formal verification.

### 14.5 Scope of Correctness

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

## 15. References

<a name="ref0" id="ref0" href="#ref0">[1]</a>  
Hamza, J., Voirol, N., & Kuncak, V. (2019). *System FR: Formalized foundations for the Stainless verifier*.  
Proceedings of the ACM on Programming Languages, OOPSLA Issue. 

<a name="ref1" id="ref1" href="#ref1">[2]</a>  
Wikipedia contributors. (2026). *Formal verification*. Wikipedia.  
Available at: [https://en.wikipedia.org/wiki/Formal_verification](https://en.wikipedia.org/wiki/Formal_verification)

## Appendix A: Scala Verification Code

### A.1 Tail Access Shift — accessTailShiftRight

```scala
  def accessTailShiftRight[T](list: List[T], position: BigInt): Boolean = {
    require(list.nonEmpty && position >= 0 && position < list.tail.size)
    list.tail(position) == list(position + 1)
  }.holds
```

```scala
  def assertTailShiftLeft[T](list: List[T], position: BigInt): Boolean = {
    require(list.nonEmpty)
    require(position >= 0 && position < list.size)
    decreases(position)

    if (position == 0 ) {
      list(position) == list.head
    } else {
      assert( list == List(list.head) \mathbin{+\!+} list.tail )
      assert( list(position) == list.apply(position) )
      assert(assertTailShiftLeft(list.tail, position - 1))
      assert(list.apply(position) == list.tail.apply(position - 1))
      list(position) == list.tail(position - 1)
    }
  }.holds
```

### A.2 Last Element Identity — assertLastEqualsLastPosition

```scala
  def assertLastEqualsLastPosition[T](list: List[T]): Boolean = {
    require(list.nonEmpty)
    decreases(list.size)

    if (list.size == 1) {
      assert(list.head == list.last)
    } else {
      assert(assertLastEqualsLastPosition(list.tail))
      assertTailShiftLeft(list, list.size - 1)
      assert(list.last == list(list.size - 1))
    }
    list.last == list(list.size - 1)
  }.holds
```

### A.3 Tail-Recursive Slice — slice

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
      prev \mathbin{+\!+} List(current)
    }
  }
```

### A.4 Head-Recursive Slice — headRecursiveSlice

```scala
def headRecursiveSlice[A](list: List[A], from: BigInt, to: BigInt): List[A] = {
  require(0 <= from && from <= to && to < list.length)
  decreases(to - from)
  if (from == to) List(list(from))
  else Cons(list(from), headRecursiveSlice(list, from + 1, to))
}
```

### A.5 Index-Range Slice — indexRangeValues

```scala
def indexRangeValues[A](list: List[A], from: BigInt, to: BigInt): List[A] = {
  require(0 <= from && from <= to && to < list.length)
  decreases(to - from)
  if (from == to) List(list(from))
  else Cons(list(from), indexRangeValues(list, from + 1, to))
}
```

### A.6 Slice Append Consistency — assertAppendToSlice

```scala
  def assertAppendToSlice(list: List[BigInt], from: BigInt, to: BigInt): Boolean = {
    require(from >= 0)
    require(from < to)
    require(to < list.size)
    
    listSumAddValue(list, list(to))
    
    ListUtils.slice(list, from, to) ==
      ListUtils.slice(list, from, to - 1) \mathbin{+\!+} List(list(to))
  }.holds
```

### A.7 Sum Implementation — sum

```scala
  def sum(loopList: List[BigInt]): BigInt = {
    if (loopList.isEmpty) {
      BigInt(0)
    } else {
      loopList.head + sum(loopList.tail)
    }
  }
```

### A.8 Left Append Preserves Sum — listSumAddValue

```scala
def listSumAddValue(list: List[BigInt], value: BigInt): Boolean = {
    ListUtils.sum(List(value) \mathbin{+\!+} list) == value + ListUtils.sum(list)
  }.holds
```

### A.9 Sum over Concatenation — listCombine

```scala
  def listCombine(listA: List[BigInt], listB: List[BigInt]): Boolean = {
    decreases(listA.size)

    if (listA.isEmpty) {
      assert(ListUtils.sum(listA) == BigInt(0))
      assert(ListUtils.sum(listB) == BigInt(0) + ListUtils.sum(listB))
      assert(ListUtils.sum(listB) == ListUtils.sum(listA) + ListUtils.sum(listB))
      assert(listA \mathbin{+\!+} listB == listB)
    } else {
      listCombine(listA.tail, listB)
      val bigList = listA \mathbin{+\!+} listB
      assert(bigList == List(listA.head) \mathbin{+\!+} listA.tail \mathbin{+\!+} listB)
      listSumAddValue(listA.tail \mathbin{+\!+} listB, listA.head)
    }
    ListUtils.sum(listA \mathbin{+\!+} listB) == ListUtils.sum(listA) + ListUtils.sum(listB)
  }.holds
```

### A.10 Commutativity of Sum — listSwap

```scala
  def listSwap(listA: List[BigInt], listB: List[BigInt]): Boolean = {
    listCombine(listA, listB)
    listCombine(listB, listA)
    assert(ListUtils.sum(listA \mathbin{+\!+} listB) == ListUtils.sum(listA) + ListUtils.sum(listB))
    assert(ListUtils.sum(listB \mathbin{+\!+} listA) == ListUtils.sum(listB) + ListUtils.sum(listA))
    assert(ListUtils.sum(listA) + ListUtils.sum(listB) == ListUtils.sum(listB) + ListUtils.sum(listA))
    ListUtils.sum(listA \mathbin{+\!+} listB) == ListUtils.sum(listB \mathbin{+\!+} listA)
  }.holds
```

### A.11 Singleton Product — singletonProduct

```scala
  def singletonProduct(x: BigInt): Boolean = {
    product(List(x)) == x
  }.holds
```

### A.12 Product Pull-Out Element — productPullOutElement

```scala
  def productPullOutElement(
                             listA: List[BigInt],
                             e: BigInt,
                             listB: List[BigInt]): Boolean = {
    decreases(listA.size)

    if (listA.isEmpty) {
      product(List(e) \mathbin{+\!+} listB) == e * product(listB)
    } else {
      productPullOutElement(listA.tail, e, listB)
      product(listA \mathbin{+\!+} List(e) \mathbin{+\!+} listB) ==
        e * product(listA \mathbin{+\!+} listB)
    }
  }.holds
```

### A.13 Product over Concatenation — productConcatLemma

```scala
  def productConcatLemma(
                          listA: List[BigInt],
                          listB: List[BigInt]
                        ): Boolean = {
    decreases(listA.size)

    if (listA.isEmpty) {
      assert(product(listA) == BigInt(1))
      assert(product(listB) == product(listA) * product(listB))
      assert(listA \mathbin{+\!+} listB == listB)
    } else {
      productConcatLemma(listA.tail, listB)

      val concatenated = listA \mathbin{+\!+} listB

      assert(
        concatenated ==
          List(listA.head) \mathbin{+\!+} listA.tail \mathbin{+\!+} listB
      )

      assert(
        product(concatenated) ==
          listA.head * product(listA.tail \mathbin{+\!+} listB)
      )
    }

    product(listA \mathbin{+\!+} listB) ==
      product(listA) * product(listB)
  }.holds
```

### A.14 Commutativity of Product — productConcatCommutative

```scala
  def productConcatCommutative(
                                listA: List[BigInt],
                                listB: List[BigInt]
                              ): Boolean = {

    productConcatLemma(listA, listB)
    productConcatLemma(listB, listA)

    assert(
      product(listA \mathbin{+\!+} listB) ==
        product(listA) * product(listB)
    )

    assert(
      product(listB \mathbin{+\!+} listA) ==
        product(listB) * product(listA)
    )

    assert(
      product(listA) * product(listB) ==
        product(listB) * product(listA)
    )

    product(listA \mathbin{+\!+} listB) ==
      product(listB \mathbin{+\!+} listA)
  }.holds
```

### A.15 Positive Product — positiveProduct

```scala
  def positiveProduct(elements: List[BigInt]): Boolean = {
    decreases(elements.size)

    require(ListBoundUtils.allGreaterThan(elements, 0))

    if (elements.isEmpty) {
      product(elements) > 0
    } else {
      positiveProduct(elements.tail)
      assert(product(elements.tail) > 0)
      product(elements) > 0
    }
  }.holds
```

### A.16 Head Divides Product — ListProductDiv

```scala
  def ListProductDiv(
                          elements: List[BigInt]
                        ): Boolean = {

    require(elements.nonEmpty)
    require(ListBoundUtils.allGreaterThan(elements, 0))

    val p = elements.head
    val tailProduct = ListProduct.product(elements.tail)

    assert(
      ListProduct.product(elements) ==
        p * tailProduct
    )

    assert(ModIdentity.modIdentity(p))

    assert(
      ATimesBSameMod(
        BigInt(0),
        p,
        tailProduct
      )
    )

    Calc.mod(
      ListProduct.product(elements),
      p
    ) == BigInt(0)
  }.holds
```

### A.17 All Elements Divide Product — allElementsDivideProduct

```scala
  def allElementsDivideProduct(
                                elements: List[BigInt]
                              ): Boolean = {

    require(ListBoundUtils.allGreaterThan(elements, 0))

    decreases(elements.size)

    if (elements.isEmpty) {
      true
    } else {

      val p = elements.head
      val tailProduct = ListProduct.product(elements.tail)

      assert(
        ListProduct.product(elements) ==
          p * tailProduct
      )

      assert(ModIdentity.modIdentity(p))

      assert(
        ATimesBSameMod(
          BigInt(0),
          p,
          tailProduct
        )
      )

      assert(
        Calc.mod(
          ListProduct.product(elements),
          p
        ) == BigInt(0)
      )

      allElementsDivideProduct(elements.tail)
    }
  }.holds
```

### A.18 Inserted Element Divides Product — insertedElementDividesProduct

```scala
  def insertedElementDividesProduct(
                                     prefix: List[BigInt],
                                     e: BigInt,
                                     suffix: List[BigInt]
                                   ): Boolean = {

    require(e > 0)
    require(ListBoundUtils.allGreaterThan(prefix, 0))
    require(ListBoundUtils.allGreaterThan(suffix, 0))

    ListProduct.productPullOutElement(
      prefix,
      e,
      suffix
    )

    assert(
      ListProduct.product(
        prefix \mathbin{+\!+} List(e) \mathbin{+\!+} suffix
      ) ==
        e * ListProduct.product(
          prefix \mathbin{+\!+} suffix
        )
    )

    assert(ModIdentity.modIdentity(e))

    assert(
      ATimesBSameMod(
        BigInt(0),
        e,
        ListProduct.product(prefix \mathbin{+\!+} suffix)
      )
    )

    Calc.mod(
      ListProduct.product(
        prefix \mathbin{+\!+} List(e) \mathbin{+\!+} suffix
      ),
      e
    ) == BigInt(0)
  }.holds
```

### A.19 All Greater Than at Index — assertGreaterThanAtIndex

```scala
  def assertGreaterThanAtIndex(list: List[BigInt], value: BigInt, pos: BigInt): Boolean = {
    require(allGreaterThan(list, value))
    require(pos >= 0 && pos < list.size)
    decreases(pos)
    if (pos == BigInt(0)) {
      list.head > value
    } else {
      assert(assertGreaterThanAtIndex(list.tail, value, pos - 1))
      assert(assertTailShiftLeft(list, pos))
      list(pos) > value
    }
  }.holds
```

### A.20 Append Preserves All Greater Than — assertAppendGreaterThan

```scala
  def assertAppendGreaterThan(listA: List[BigInt], listB: List[BigInt], value: BigInt): Boolean = {
    require(allGreaterThan(listA, value))
    require(allGreaterThan(listB, value))
    decreases(listA.size)
    if (listA.isEmpty) {
      allGreaterThan(listA \mathbin{+\!+} listB, value)
    } else {
      assert(assertAppendGreaterThan(listA.tail, listB, value))
      assert(allGreaterThan(listA.tail \mathbin{+\!+} listB, value))
      assert(listA.head > value)
      allGreaterThan(listA \mathbin{+\!+} listB, value)
    }
  }.holds
```

### A.21 All Greater Than Head and Tail — assertGreaterThanHeadTail

```scala
  def assertGreaterThanHeadTail(list: List[BigInt], value: BigInt): Boolean = {
    require(allGreaterThan(list, value))
    require(list.nonEmpty)
    list.head > value && allGreaterThan(list.tail, value)
  }.holds
```

### A.22 Check All Bigger at Index — checkAllBiggerThanValueAtIndex

```scala
  def checkAllBiggerThanValueAtIndex(list: List[BigInt], value: BigInt, pos: BigInt): Boolean = {
    require(ListUtils.checkAllBiggerThanValue(list, value))
    require(pos >= 0 && pos < list.size)
    ListBoundUtils.assertGreaterThanAtIndex(list, value, pos)
  }.holds
```

### A.23 Check All Bigger Head and Tail — checkAllBiggerThanValueHeadTail

```scala
  def checkAllBiggerThanValueHeadTail(list: List[BigInt], value: BigInt): Boolean = {
    require(ListUtils.checkAllBiggerThanValue(list, value))
    require(list.nonEmpty)
    ListBoundUtils.assertGreaterThanHeadTail(list, value)
  }.holds
```

### A.24 Slice Equivalence — tailHeadAndIndexRangeSlicesAreEqual

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
      val reconstructedTail = ListUtils.slice(list, from, to - 1) \mathbin{+\!+} List(list(to))
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

## Appendix B: Stainless Verification Log Output

The latest `just verify` run verifies all the described properties without errors. The full log output is available at: [logs/verify.log](../logs/verify.log)

