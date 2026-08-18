# Division and Modulo from Recursive Normalization

**Author:** Mata, T. H.
Independent Researcher  
**Email:** [thiago.henrique.mata@gmail.com](mailto:thiago.henrique.mata@gmail.com)  
**GitHub:** [@thiagomata](https://github.com/thiagomata)

## Abstract

<div align="justify">
<p style="text-align: justify">
The division and modulo operations are fundamental in mathematics and computer science,
 especially in areas such as number theory, cryptography, and algorithm design. 
In this article, we define these operations from scratch using a recursive formulation,
 without relying on built-in semantics or standard library behavior.
We mathematically prove and formally verify, using Scala Stainless, key
properties such as unique remainder, modulo idempotence, distributivity, and
one-zero-per-period density.
All properties are expressed and proved within a minimal framework using only elementary arithmetic,
 recursion, and formally verified Scala definitions.
The result is a self-contained, machine-checked foundation for modular arithmetic.
 </p>
</div>

## 1. Introduction

Integer division and modulo operations are central tools in discrete mathematics, number theory, and algorithms. 
While their properties are well known, rigorous formalization and verification, particularly via recursive definitions,
offer an interesting alternative to the traditional axiomatic model.

This article takes the recursive route. Instead of assuming native division and
modulo, it defines a state $DivMod(a,b,q,r)$ where $a = bq + r$, then proves
that normalizing the pair $(q,r)$ preserves the represented dividend and reaches
the canonical remainder interval. The familiar operations $\text{div}$ and
$\text{mod}$ are then projections from that normalized state.

The mathematical statements below are backed by Scala source verified with
[Stainless](https://epfl-lara.github.io/stainless/intro.html). The article keeps
the proof discussion centered on the properties; source links point to the
maintained verification code.

## 2. Limitations

The implementation presented in this article is limited to the division and modulo operations for integers. 
Its goal is to make available a set of lemmas and proofs that can be verified and used as a base to prove other
properties related to the division and modulo operations.
Therefore, the implementation is optimized to correctness and not to performance.

The use of BigInt in the implementation focused on unbounded integers, without the need to worry about overflow or 
underflow issues. 
But, they are still constrained by the memory available in the system. 
Similarly, some lemmas and proofs use the recursive definition of the division and modulo operations, which could 
trigger a stack overflow for large numbers. Those issues do not invalidate the mathematical properties proved in this 
article, which are the main focus of this article.

## 3. Traditional Definition

Given integers $\text{dividend}$ and $\text{divisor}$ where
$\text{divisor} \neq 0$, the division algorithm determines integers
$\text{quotient}$ and $\text{remainder}$ such that:

```math
\begin{aligned}
\forall \text{dividend},\text{divisor} \in \mathbb{Z},\;
\text{divisor} \neq 0,\;
\exists!\, \text{quotient},\text{remainder} &: \\
\text{dividend} &= \text{divisor} \cdot \text{quotient} + \text{remainder} \\
0 &\le \text{remainder} < |\text{divisor}| \\
\text{dividend} \text{ div } \text{divisor} &:= \text{quotient} \\
\text{dividend} \text{ mod } \text{divisor} &:= \text{remainder}
\end{aligned}
```

The first two lines state the division relation and the canonical remainder
range. The final two lines introduce the operation notation: division returns
the quotient, and modulo returns the remainder.

## 4. Recursive Definition

We introduce a recursive definition of division and modulo because the proof can
be built from one invariant: shifting one unit of $b$ between quotient and
remainder preserves the represented dividend. In
[Section 5](#5-divmod-solution-invariance-under-linear-shift), that invariant
connects the recursive normal form back to the traditional division equation
from [Section 3](#3-traditional-definition).

From here on, $a$ is the dividend, $b$ is the divisor, $q$ is the candidate
quotient, and $r$ is the candidate remainder. The shorter names keep the
recursive equations readable while preserving the same roles as the traditional
definition. We reserve $\text{mod}$ for the modulo operation itself.

We define $DivMod(a,b,q,r)$ such that:

```math
\begin{aligned}
\forall a,b,q,r \in \mathbb{Z} : b \neq 0,\; a = bq + r
\end{aligned}
```

The solved $DivMod$ states are those where the remainder $r$ satisfies:

```math
\begin{cases}
0 \leq r < b & \text{if } b > 0, \\
0 \leq r < -b & \text{if } b < 0.
\end{cases}
```

```math
\begin{aligned}
\text{DivMod.solve}(a,b,q,r) &:=
\begin{cases}
\text{DivMod}(a,b,q,r) & \text{if } 0 \leq r < |b|, \\
\text{DivMod.solve}(a,b,q+\text{sign}(b),r-|b|) & \text{if } r \geq |b|, \\
\text{DivMod.solve}(a,b,q-\text{sign}(b),r+|b|) & \text{if } r < 0. \\
\end{cases} \\
\end{aligned}
```

The recursive definition is implemented in [DivMod.scala](
../../src/main/scala/v1/chapter2/div/DivMod.scala
).


## 5. DivMod Solution Invariance Under Linear Shift

```math
\begin{aligned}
\forall a,b,q,r \in \mathbb{Z},\; b \neq 0,\; a &= bq + r \\
a &= b(q+1) + (r-b) \\
a &= b(q-1) + (r+b) \\
\text{DivMod}(a,b,q+1,r-b).\text{solve} &= \text{DivMod}(a,b,q,r).\text{solve} \\
\text{DivMod}(a,b,q-1,r+b).\text{solve} &= \text{DivMod}(a,b,q,r).\text{solve}
\end{aligned}
```

This invariant is verified for the [positive shift](
  ../../src/main/scala/v1/chapter2/div/properties/ModIdempotence.scala#assertDivModWithMoreDivAndLessModSameSolution
) and [negative shift](../../src/main/scala/v1/chapter2/div/properties/ModIdempotence.scala#assertDivModWithLessDivAndMoreModSameSolution).


### Creating the Division and Modulo Operations

Using the normalized `DivMod` value, [Calc.scala](
../../src/main/scala/v1/chapter2/div/Calc.scala
) defines $\text{div}$ and $\text{mod}$ as the quotient and remainder projections
of the solved state. Starting from $DivMod(a,b,0,a)$, let:

```math
\begin{aligned}
S &:= \text{DivMod}(a,b,0,a).\text{solve} \\
q &:= S.\text{div} \\
r &:= S.\text{mod} \\
\text{div}(a,b) &:= q \\
\text{mod}(a,b) &:= r
\end{aligned}
```

So $\text{div}(a,b)$ names the normalized quotient, while $\text{mod}(a,b)$
names the normalized remainder. In the source code these are the `div` and
`mod` fields of the solved `DivMod`; in the article notation, $q$ and $r$ keep
the quotient and remainder roles separate from the operation names.

The article uses both functional and infix notation for the same operations:
$\text{div}(x,y)$ and $x \text{ div } y$ are equivalent, as are
$\text{mod}(x,y)$ and $x \text{ mod } y$. Functional notation is useful when
the operation is nested inside another expression; infix notation keeps simple
algebraic identities closer to the traditional presentation.

## 6. Some Important Properties of Modulo and Division

### Trivial Case

If the dividend is smaller than a positive divisor, the candidate state
$DivMod(a,b,0,a)$ is already final. No subtraction of $b$ is needed, so the
quotient is zero and the remainder is the original dividend.

```math
\begin{aligned}
& \forall \text{ } a, b \in \mathbb{N} : b \neq 0 \\
& a < b \implies a \text{ mod } b & = a \\
& a < b \implies a \text{ div } b & = 0 \\
\end{aligned}
```

This property is verified in [
  ModSmallDividend
](../../src/main/scala/v1/chapter2/div/properties/ModSmallDividend.scala).

### Identity

The modulo of every number by itself is zero and the division of every number by itself is one.

```math
\begin{aligned}
\forall \text{ } n \in \mathbb{N} : n & \neq 0 \\
n \text{ mod } n & = 0 \\
n \text{ div } n & = 1 \\
\end{aligned}
```

The proof normalizes $DivMod(n,n,0,n)$ to $DivMod(n,n,1,0)$. The latter is
already final, so the normalized quotient is $1$ and the normalized remainder is
$0$.

This property is verified in [
  ModIdentity::modIdentity
](../../src/main/scala/v1/chapter2/div/properties/ModIdentity.scala). A longer
source proof showing the normalization path is available in [
  ModIdentity::longProof
](../../src/main/scala/v1/chapter2/div/properties/ModIdentity.scala#longProof).

### Modulo and Division by One

Modulo by one always returns zero and division by one always returns the dividend.

```math
\begin{aligned}
\forall \text{ } n \in \mathbb{N} & : \\
n \text{ mod } 1 & = 0 \\
n \text{ div } 1 & = n \\
\end{aligned}
```

Modulo by one follows because every integer is congruent to $0$ modulo $1$.
Division by one is proved by induction over $n$, using the unit-step increment
law for the successor case.

These properties are verified in [
  ModOne::modOneIsZero
](../../src/main/scala/v1/chapter2/div/properties/ModOne.scala) and [
  ModOne::divOneIsN
](../../src/main/scala/v1/chapter2/div/properties/ModOne.scala).

### Quotient Invariance Under Linear Shift

Adding or subtracting the divisor from the dividend changes the quotient by one but leaves the remainder unchanged.

```math
\begin{aligned}
\forall a,b,q,r \in \mathbb{Z} &: b \neq 0,\; a = bq + r \\
\text{mod}(a + b, b) & = \text{mod}(a, b) \\
\text{div}(a + b, b) & = \text{div}(a, b) + 1 \\
\text{mod}(a - b, b) & = \text{mod}(a, b) \\
\text{div}(a - b, b) & = \text{div}(a, b) - 1 \\
\end{aligned}
```

This property is verified for the [positive case](
../../src/main/scala/v1/chapter2/div/properties/AdditionAndMultiplication.scala#APlusBSameModPlusDiv
) and [negative case](
../../src/main/scala/v1/chapter2/div/properties/AdditionAndMultiplication.scala#ALessBSameModDecreaseDiv
).

### Quotient Invariance Under Linear Shift by Multiplier

Adding a multiple of the divisor changes the quotient by that multiplier but
leaves the remainder unchanged.

As a direct consequence of the one-step shift laws, we can also prove that:

```math
\begin{aligned}
\forall a,b,q,r,m \in \mathbb{Z} &: b \neq 0,\; a = bq + r \\
\text{mod}(a + m \cdot b, b) & = \text{mod}(a, b) \\
\text{div}(a + m \cdot b, b) & = \text{div}(a, b) + m \\
\text{mod}(a - m \cdot b, b) & = \text{mod}(a, b) \\
\text{div}(a - m \cdot b, b) & = \text{div}(a, b) - m \\
\end{aligned}
```

This property is verified for the [positive case](
../../src/main/scala/v1/chapter2/div/properties/AdditionAndMultiplication.scala#APlusMultipleTimesBSameMod
) and [negative case](
../../src/main/scala/v1/chapter2/div/properties/AdditionAndMultiplication.scala#ALessMultipleTimesBSameMod
).

### Unique Remainder

There is only one single remainder value for every $a, b$ pair.

```math
\begin{aligned}
  \forall \text{ } a, b, r & \in \mathbb{Z} \\
  \quad \exists ! \, r \mid 0 \leq r < |b| & \implies \quad  a = \left\lfloor \frac{a}{b} \right\rfloor \cdot b + r
\end{aligned}
```

in other words, two $DivMod$ instances with the same dividend $a$ and divisor $b$ will have the same solution.

```math
\begin{aligned}
\forall a,b,q_x,r_x,q_y,r_y & \in \mathbb{N}, \\
\text{where } b & \neq 0 \text{, } \\
a & = bq_x + r_x \text{ and } \\
a & = bq_y + r_y \text{ then } \\
DivMod(a,b,q_x,r_x).solve & = DivMod(a,b,q_y,r_y).solve \\
\end{aligned}
```

For every $a,b$ pair, with any candidate quotients and remainders
$(q_x,r_x)$ and $(q_y,r_y)$ representing the same dividend, normalization
reaches the same solution.
This property is verified in [
  ModIdempotence::modUnique
](
../../src/main/scala/v1/chapter2/div/properties/ModIdempotence.scala#modUnique
).

### Modulo Idempotence

Taking the modulo of a number twice gives the same result as taking it once.

```math
\begin{aligned}
\forall \text{ } a, b & \in \mathbb{Z} : b \neq 0 \\
a \text{ mod } b & = ( a \text{ mod } b ) \text{ mod } b \\
\end{aligned}
```

This property is verified in [
  ModIdempotence::modIdempotence
](../../src/main/scala/v1/chapter2/div/properties/ModIdempotence.scala#modIdempotence).

### Distributivity over Addition

The modulo operation distributes over addition, meaning that the remainder of a sum equals the remainder of the sum of remainders. This allows us to break down complex modulo operations into simpler components.

```math
\begin{aligned}
\forall \text{ } a, b, c & \in \mathbb{Z} : b \neq 0 \\
( a + c ) \text{ mod } b & = ( a \text{ mod } b + c \text{ mod } b ) \text{ mod } b \\
( a + c ) \text{ div } b & = a \text{ div } b + c \text{ div } b + ( a \text{ mod } b + c \text{ mod } b ) \text{ div } b \\
( a +  c) \text{ mod } b & = (a \text{ mod } b) + (c \text{ mod } b) - b \cdot (((a \text{ mod } b) + (c \text{ mod } b)) \text{ div } b) \\
\end{aligned}
```

This property is verified in [
  ModOperations::modAdd
](
../../src/main/scala/v1/chapter2/div/properties/ModOperations.scala#modAdd
). The third identity, isolating the multiple of $b$ subtracted
out, is proved directly in [ModIdempotence.scala#modModPlus](
../../src/main/scala/v1/chapter2/div/properties/ModIdempotence.scala#modModPlus
).

### Distribution over Subtraction

Similar to addition, the modulo operation distributes over subtraction. The remainder of a difference equals the remainder of the difference of remainders, with appropriate handling of negative values.

```math
\begin{aligned}
\forall \text{ } a, b, c & \in \mathbb{Z} : b \neq 0 \\
( a - c ) \text{ mod } b & = ( a \text{ mod } b - c \text{ mod } b ) \text{ mod } b \\
( a - c ) \text{ div } b & = a \text{ div } b - c \text{ div } b + ( a \text{ mod } b - c \text{ mod } b ) \text{ div } b \\
( a - c ) \text{ mod } b & = (a \text{ mod } b) - (c \text{ mod } b) - b \cdot (((a \text{ mod } b) - (c \text{ mod } b)) \text{ div } b) \\
\end{aligned}
```

This property is verified in [
  ModOperations::modLess
](
../../src/main/scala/v1/chapter2/div/properties/ModOperations.scala#modLess
). The third identity, isolating the multiple of $b$ subtracted
out, is proved directly in [ModIdempotence.scala#modModMinus](
../../src/main/scala/v1/chapter2/div/properties/ModIdempotence.scala#modModMinus
).

### Modular Shift Invariance under Divisible Base

When a number is a multiple of the divisor (modulo equals zero), adding any value does not change the modulo of that value. This property simplifies calculations when one operand is already divisible by the base. It holds for any integer `c`, including negative values.

```math
\begin{aligned}
\forall \text{ } a, b, c & \in \mathbb{Z} : b \neq 0 \\
a \text{ mod } b = 0 & \implies ( a + c ) \text{ mod } b = c \text{ mod } b \\
\end{aligned}
```

This property is verified in [
  ModOperations::modZeroPlusC
](
../../src/main/scala/v1/chapter2/div/properties/ModOperations.scala#modZeroPlusC
).

Substituting `-c` for `c` gives the subtraction corollary directly, since `c`
is unrestricted:

```math
\begin{aligned}
\forall \text{ } a, b, c & \in \mathbb{Z} : b \neq 0 \\
a \text{ mod } b = 0 & \implies ( a - c ) \text{ mod } b = ( -c ) \text{ mod } b \\
\end{aligned}
```

This corollary is verified by the same lemma, [
  ModOperations::modZeroPlusC
](
../../src/main/scala/v1/chapter2/div/properties/ModOperations.scala#modZeroPlusC
), called with `-c` in place of `c`.

### Symmetrical Modulo Pairs

The modulo of a value and the modulo of its complement relative to the base sum to the base.

```math
\begin{aligned}
b &> 0,\quad 0 < k < b \\
k \text{ mod } b + (b - k) \text{ mod } b & = b
\end{aligned}
```

Since both $k$ and $b-k$ already lie inside the canonical remainder interval,
their remainders are themselves. Their sum is therefore $k + (b-k) = b$.

This property is verified in [
  ModSum::sumSymmetricalMods
](../../src/main/scala/v1/chapter2/div/properties/ModSum.scala). The source
excerpt is included in [Appendix A.2](#a2-symmetrical-modulo-pairs-excerpt).

### Unit-Step Modulo-Division Increment Law

When incrementing a number by one, the modulo cycles from 0 to b-1 and resets, while the division increments only when the modulo reaches its maximum value. This captures the "carry" behavior of division when counting.

```math
\begin{aligned}
\forall \text{ } a, b & \in \mathbb{N} : b \neq 0 \\
a \text{ mod } b = b - 1    & \implies (a + 1) \text{ mod } b = 0 \\
a \text{ mod } b \neq b - 1 & \implies (a + 1) \text{ mod } b = (a \text{ mod } b) + 1 \\
a \text{ mod } b = b - 1    & \implies (a + 1) \text{ div } b = (a \text{ div } b) + 1 \\
a \text{ mod } b \neq b - 1 & \implies (a + 1) \text{ div } b = a \text{ div } b \\
\end{aligned}
```

This property is verified in [
  ModOperations::addOne
](
../../src/main/scala/v1/chapter2/div/properties/ModOperations.scala#addOne
).

### Consecutive Integers: Zero Density

In any block of $p$ consecutive integers, exactly one is divisible by $p$.
This is the basic counting form of modulo periodicity: as we advance through
consecutive integers, the remainder modulo $p$ visits zero once per complete
period.

**At most one zero per block.** If $\text{mod}(a,p)=0$ and $0 < d < p$, then
$\text{mod}(a+d,p)\neq 0$. Within any block of size $p$ starting from a
multiple, no later offset inside the same block can also be divisible by $p$.

```math
\begin{aligned}
\text{mod}(a,\; p) = 0 \;\land\; 0 < d < p &\implies \text{mod}(a + d,\; p) \neq 0
  &&\text{[nonzeroAfterZero]}
\end{aligned}
```

**At least one zero per block.** For any starting value $n$ and modulus
$p>1$, there exists a $k \in [0,p)$ such that
$\text{mod}(n+k,p)=0$. The witness is $k=0$ when $n$ is already divisible by
$p$, and $k=p-\text{mod}(n,p)$ otherwise.

```math
\begin{aligned}
\forall n \geq 0,\; p > 1,\; \exists\, k \in [0, p) &: \text{mod}(n + k,\; p) = 0
  &&\text{[existsZero]}
\end{aligned}
```

**Exactly one zero per block.** Existence gives a zero offset, while
uniqueness says two zero offsets in the same block must be equal. Together,
among $p$ consecutive integers starting from $n$, exactly one is divisible by
$p$.

```math
\begin{aligned}
\forall n \geq 0,\; p > 1,\;
\exists!\, k \in [0, p) &: \text{mod}(n + k,\; p) = 0
  &&\text{[existsZero + atMostOneZero]}
\end{aligned}
```

These properties are verified in [
  ConsecutiveIntegers::nonzeroAfterZero
](
  ../../src/main/scala/v1/chapter2/div/properties/ConsecutiveIntegers.scala
), [
  ConsecutiveIntegers::existsZero
](
  ../../src/main/scala/v1/chapter2/div/properties/ConsecutiveIntegers.scala
), [
  ConsecutiveIntegers::exactlyOneZeroInConsecutive
](
  ../../src/main/scala/v1/chapter2/div/properties/ConsecutiveIntegers.scala
), and [
  ConsecutiveIntegers::atMostOneZero
](
  ../../src/main/scala/v1/chapter2/div/properties/ConsecutiveIntegers.scala
).
The compact source shape is included in [Appendix A.3](#a3-consecutive-zero-density-excerpt).

The density lemmas, [
  ConsecutiveIntegers::densityForDivisor
](
  ../../src/main/scala/v1/chapter2/div/properties/ConsecutiveIntegers.scala
), [
  ConsecutiveIntegers::densityForFactorList
](
  ../../src/main/scala/v1/chapter2/div/properties/ConsecutiveIntegers.scala
), [
  ConsecutiveIntegers::densityPreservedAfterFiltering
](
  ../../src/main/scala/v1/chapter2/div/properties/ConsecutiveIntegers.scala
), and [
  ConsecutiveIntegers::twoFactorsDensity
](
  ../../src/main/scala/v1/chapter2/div/properties/ConsecutiveIntegers.scala
), extend these facts to
multi-filter settings, proving that the proportion of survivors after
filtering by a product of pairwise non-dividing factors is the product of the individual survival
rates. The maintained source is [
  ConsecutiveIntegers.scala
](../../src/main/scala/v1/chapter2/div/properties/ConsecutiveIntegers.scala).

## 7. Conclusion

In this article, we constructed the division and modulo operations from first principles,
 using a recursive definition that avoids reliance on any built-in semantics or library
 implementations.
Within this minimal foundation, we mathematically proved and formally verified
the following set of fundamental properties and identities:

```math
\begin{aligned}
\forall \text{ } a, b, c, m & \in \mathbb{Z} : b \neq 0 \\
b > a \geq 0 \implies a \text{ div } b & = 0 \\
b > a \geq 0 \implies a \text{ mod } b & = a \\
b \text{ mod } b                   & = 0 \\
b \text{ div } b                   & = 1 \\
( a + b \cdot m ) \text{ mod } b   & = a \text{ mod } b \\
( a - b \cdot m ) \text{ mod } b   & = a \text{ mod } b \\
(a \text{ mod } b) \text{ mod } b  & = a \text{ mod } b \\
(a + b) \text{ div } b             & = (a \text{ div } b) + 1 \\
(a - b) \text{ div } b             & = (a \text{ div } b) - 1 \\
(a + b \cdot m ) \text{ div } b    & = (a \text{ div } b) + m \\
(a - b \cdot m ) \text{ div } b    & = (a \text{ div } b) - m \\
(a + c) \text{ div } b             & = (a \text{ div } b) + (c \text{ div } b) + (((a \text{ mod } b) + (c \text{ mod } b)) \text{ div } b) \\
(a - c) \text{ div } b             & = (a \text{ div } b) - (c \text{ div } b) + (((a \text{ mod } b) - (c \text{ mod } b)) \text{ div } b) \\
(a + c) \text{ mod } b             & = ((a \text{ mod } b) + (c \text{ mod } b)) \text{ mod } b \\
(a - c) \text{ mod } b             & = ((a \text{ mod } b) - (c \text{ mod } b)) \text{ mod } b \\
(a + c) \text{ mod } b             & = (a \text{ mod } b) + (c \text{ mod } b) - b \cdot (((a \text{ mod } b) + (c \text{ mod } b)) \text{ div } b) \\
(a - c) \text{ mod } b             & = (a \text{ mod } b) - (c \text{ mod } b) - b \cdot (((a \text{ mod } b) - (c \text{ mod } b)) \text{ div } b) \\
\end{aligned}
\begin{aligned}
\forall \text{ } a, b & \in \mathbb{N} : b \neq 0 \\
a \text{ mod } b = b - 1    & \implies (a + 1) \text{ mod } b = 0 \\
a \text{ mod } b \neq b - 1 & \implies (a + 1) \text{ mod } b = (a \text{ mod } b) + 1 \\
a \text{ mod } b = b - 1    & \implies (a + 1) \text{ div } b = (a \text{ div } b) + 1 \\
a \text{ mod } b \neq b - 1 & \implies (a + 1) \text{ div } b = a \text{ div } b \\
\end{aligned}
```
```math
\begin{aligned}
b &> 0,\quad 0 < k < b \\
k \text{ mod } b + (b - k) \text{ mod } b & = b
\end{aligned}
```
```math
\begin{aligned}
\forall \text{ } n, p & \in \mathbb{N} : p > 1 \\
\exists!\, k \in [0, p) &: \text{mod}(n + k,\; p) = 0 \quad \text{[Exactly one multiple per block of p]}
\end{aligned}
```

Those formally verified properties are collected in [Summary.scala](
 ../../src/main/scala/v1/chapter2/div/properties/Summary.scala
) and supported by the individual proof modules linked above. The recursive
formulation makes the proof structure transparent: normalize $(q,r)$ without
changing $a=bq+r$, extract quotient and remainder from the final state, then
derive the algebraic laws from that normal form.
 
This work demonstrates how modular arithmetic can be derived, reasoned about, 
 and formally verified from the ground up.

## 8. Appendix

### A.1 Identity Property Excerpt

Source: [
  ModIdentity.scala
](../../src/main/scala/v1/chapter2/div/properties/ModIdentity.scala).

```scala
def modIdentity(a: BigInt): Boolean = {
  require(a != 0)
  Calc.mod(a, a) == 0 && Calc.div(a, a) == 1
}.holds
```

### A.2 Symmetrical Modulo Pairs Excerpt

Source: [
  ModSum.scala
](../../src/main/scala/v1/chapter2/div/properties/ModSum.scala).

```scala
def sumSymmetricalMods(b: BigInt, step: BigInt): Boolean = {
  require(b > 0)
  require(step > 0)
  require(step < b)
  assert(Calc.mod(step, b) == step)
  assert(Calc.mod(b - step, b) == b - step)
  assert(Calc.mod(step, b) + Calc.mod(b - step, b) == step + b - step)
  Calc.mod(step, b) + Calc.mod(b - step, b) == b
}.holds
```

### A.3 Consecutive Zero Density Excerpt

Source: [
  ConsecutiveIntegers.scala
](../../src/main/scala/v1/chapter2/div/properties/ConsecutiveIntegers.scala).

```scala
def nonzeroAfterZero(a: BigInt, p: BigInt, d: BigInt): Boolean = {
  require(p > 1)
  require(a >= 0)
  require(d > 0)
  require(d < p)
  require(Calc.mod(a, p) == 0)

  ModOperations.modAdd(a, p, d)
  ModIdempotence.modIdempotence(d, p)
  ModSmallDividend.modSmallDividend(d, p)

  Calc.mod(a + d, p) != 0
}.holds

def existsZero(n: BigInt, p: BigInt): Boolean = {
  require(p > 1)
  require(n >= 0)

  val r = Calc.mod(n, p)

  if (r == 0) {
    Calc.mod(n, p) == 0
  } else {
    val k = p - r
    ModOperations.modAdd(n, p, k)
    ModSmallDividend.modSmallDividend(k, p)
    Calc.mod(n + k, p) == 0
  }
}.holds

def atMostOneZero(n: BigInt, p: BigInt, i: BigInt, j: BigInt): Boolean = {
  require(p > 1)
  require(n >= 0)
  require(i >= 0 && i < p)
  require(j >= 0 && j < p)
  require(Calc.mod(n + i, p) == 0)
  require(Calc.mod(n + j, p) == 0)

  val smaller = if (i <= j) i else j
  val larger  = if (i <= j) j else i
  val d       = larger - smaller
  assert(d >= 0 && d < p)

  if (d > 0) {
    nonzeroAfterZero(n + smaller, p, d)
  }

  i == j
}.holds
```

### A.4 Verification Log

The project verification log is available at [logs/verify.log](../../logs/verify.log).
