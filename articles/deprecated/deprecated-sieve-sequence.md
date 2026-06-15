> **DEPRECATED — Code references may not match current source.**  
> This draft was written during an earlier iteration (v1) of the sieve sequence implementation.
> It is kept for historical guidance on the sieve proof architecture.
> The formal proof chain has since evolved: `assertHeadIsPrime` is verified at 5303 total VCs
> across 468 functions. The foundation-level properties are now documented in
> `draft-sieve-foundation.md`, which supersedes the generation/filtering lemmas in this article.
> See the ticket `article-consolidation.md` for the plan to merge both articles.

# Formal Verification of Sieve Sequence Properties from First Principles

> **DEPRECATED — Contained in [sieve-sequence.md](../sieve-sequence.md)**  
> The content of this article has been merged into the finished article `sieve-sequence.md`.  
> Please reference that article for the current, verified version of these properties.

**Author:** Mata, T. H.
Independent Researcher  
**Email:** [thiago.henrique.mata@email.com](mailto:thiago.mata@email.com)  
**GitHub:** [@thiagomata](https://github.com/thiagomata)

## Abstract

<div align="justify">
<p style="text-align: justify">
In previous articles, we defined and verified fundamental mathematical structures from scratch:
Lists, Integrals, Cycles, Cycle Integrals, and Modulo arithmetic.
This article builds on that foundation to define the Sieve Sequence &mdash;
an infinite sequence of positive integers generated via wheel factorization
that produces exactly the integers coprime to a given modulus.
We formally define the Sieve Sequence, prove its key properties including
the step property, cycle sum property, modulo invariance, and coprimality,
and verify them using the Stainless verification system.
All properties are expressed and proved within a minimal framework using only
elementary arithmetic, recursion, and pure Scala code.
This work bridges wheel factorization and formal verification,
offering a self-contained, verifiable approach to prime candidate generation.
</p>
</div>

## 1. Introduction

The Sieve of Eratosthenes is one of the oldest and most efficient algorithms for
finding all prime numbers up to a given limit. Its essence is iterative filtering:
starting with all natural numbers, repeatedly remove multiples of each discovered prime.

In this article, we formalize a key component of this sieve: the **Sieve Sequence**.
A Sieve Sequence is an infinite list of positive integers that are all coprime to a
given modulus, generated using wheel factorization. The head of each Sieve Sequence
is prime, and the sequence can be recursively refined to produce the next sieve level.

Our approach follows the zero-prior-knowledge philosophy established in previous articles,
building on verified foundations for Lists, Integrals, Cycles, and Modulo arithmetic.
The result is a verified, from-scratch implementation of Sieve Sequences,
suitable as a foundation for prime number generation and distribution analysis.

## 2. Preliminaries

We reuse several basic operations and their verified properties from companion articles:

- **Lists**: [Using Formal Verification to Prove Properties of Lists Recursively Defined](https://github.com/thiagomata/prime-numbers/blob/master/articles/list.md) [[1]](#ref1)
- **Integrals**: [Formal Verification of Discrete Integration Properties from First Principles](https://github.com/thiagomata/prime-numbers/blob/master/articles/integral.md) [[2]](#ref2)
- **Cycles**: [Using Formal Verification to Prove Properties of Unbound Lists](https://github.com/thiagomata/prime-numbers/blob/master/articles/cycle.md) [[3]](#ref3)
- **Cycle Integrals**: [Formal Verification of Cycle Integral Properties from First Principles](https://github.com/thiagomata/prime-numbers/blob/master/articles/integral-cycle.md) [[4]](#ref4)
- **Modulo Arithmetic**: [Proving Properties of Division and Modulo using Formal Verification](https://github.com/thiagomata/prime-numbers/blob/master/articles/modulo.md) [[5]](#ref5)

These articles also defined and verified their properties using the same zero-prior-knowledge methodology,
and are treated here as foundational primitives.

### 2.1 Key Definitions from Previous Work

From the Cycle article [[3]](#ref3), we reuse the concept of a Cycle as an unbounded
list that repeats a finite sequence:

```math
\text{Cycle}(L) = [v_0, v_1, \dots, v_{n-1}, v_0, v_1, \dots] \mid v_i = L[i \text{ mod } n]
```

From the Cycle Integral article [[4]](#ref4), we reuse the definition of the
Cycle Integral as the cumulative sum of a cycle:

```math
\text{CycleIntegral}(L, init)_i = \sum_{j=0}^{i} L_{(j \text{ mod } n)} + init
```

From the Modulo article [[5]](#ref5), we reuse the verified division and modulo
operations:

```math
\text{div}(a, b) = \left\lfloor \frac{a}{b} \right\rfloor, \quad
\text{mod}(a, b) = a - b \cdot \left\lfloor \frac{a}{b} \right\rfloor
```

## 3. Sieve Sequence Definition

### 3.1 Conceptual Definition

The Sieve of Eratosthenes generates prime numbers by iteratively filtering
a sequence of natural numbers. At each step, we remove all multiples of the
current smallest element (which is prime).

Let us define the sieve sequence $S_k$ recursively:

```math
\begin{aligned}
S_0 &= [2, 3, 4, 5, 6, 7, 8, \dots] \\
p_k &= S_k(0) \quad \text{(the head of } S_k\text{)} \\
S_{k+1} &= [x \in S_k \mid x > p_k \land x \bmod p_k \neq 0]
\end{aligned}
```

This produces:

```math
\begin{aligned}
S_0 &= [2, 3, 4, 5, 6, 7, 8, 9, 10, \dots] \\
p_0 &= 2 \\
S_1 &= [3, 5, 7, 9, 11, 13, 15, \dots] \\
p_1 &= 3 \\
S_2 &= [5, 7, 11, 13, 17, 19, 23, 25, \dots] \\
p_2 &= 5 \\
S_3 &= [7, 11, 13, 17, 19, 23, 29, 31, \dots]
\end{aligned}
```

The heads $p_0, p_1, p_2, \dots$ are exactly the prime numbers.

### 3.2 Wheel Factorization Representation

Each $S_k$ can be represented simply by:
- **head** ($p_k$): The first element in the sequence (a prime number)
- **cycle** ($C_k$): The cycle of gaps that generate the sequence

Where:
- **head** ($h$): The starting element - always the smallest element not filtered yet, which is always prime
- **cycle** ($C$): A MemCycle containing the gaps (differences) between consecutive elements

For example:

```math
\begin{aligned}
S_0 &: \text{head} = 2,\ C_0 = [1] \quad &\Rightarrow [2, 3, 4, 5, 6, \dots] \\
S_1 &: \text{head} = 3,\ C_1 = [2] \quad &\Rightarrow [3, 5, 7, 9, 11, \dots] \\
S_2 &: \text{head} = 5,\ C_2 = [4, 2] \quad &\Rightarrow [5, 7, 11, 13, 17, 19, \dots] \\
S_3 &: \text{head} = 7,\ C_3 = [6, 4, 2, 4, 2, 4, 6, 2] \quad &\Rightarrow [7, 11, 13, 17, 19, \dots]
\end{aligned}
```

The **gaps** are the differences between consecutive elements in the sequence. For $S_2 = [5, 7, 11, 13, \dots]$, the gaps are:
- 7 - 5 = 2
- 11 - 7 = 4
- 13 - 11 = 2
- ...

So the gaps cycle is [2, 4, 2, ...] (or written as [4, 2] when cycled).

And the sequence is generated as:

```math
S_k = \text{SieveSequence}(\text{head}_k, C_k)
```

For the examples (showing head and cycle):

```math
\begin{aligned}
S_1 &: \text{head} = 3,\ C_1 = [2] \\
S_2 &: \text{head} = 5,\ C_2 = [4, 2] \\
S_3 &: \text{head} = 7,\ C_3 = [6, 4, 2, 4, 2, 4, 6, 2]
\end{aligned}
```

### 3.3 Formal Definition

```math
\begin{aligned}
\text{SieveSequence}(h, C) &= [w_0, w_1, w_2, \dots] \\
w_i &= h + \sum_{j=0}^{i-1} C_{(j \bmod |C|)} \\
\end{aligned}
```

where:
- $h$ is the head (first element)
- $C$ is the cycle of gaps that generate the sequence

This is equivalent to the cumulative sum approach used in the `Seq` class properties.

Defined at [SieveSequence.scala](../src/main/scala/v1/seq/sieve/SieveSequence.scala) as follows:

<details>
<summary> Scala Doc </summary>

```scala
/**
 * SieveSequence represents an infinite sequence of positive integers
 * that are coprime to a given modulus, generated via wheel factorization.
 *
 * @param head The first (smallest) element in the sequence
 * @param cycle MemCycle containing the gaps that generate the sequence
 */
```
</details>

### 4.9 Head is Prime Property

**Lemma:** The head of each sieve sequence is prime.

```math
\text{isPrime}(\text{head}_k)
```

#### Proof

The proof follows from the sieve construction and uses strong induction on $k$:

1. **Induction hypothesis**: `primes.tail` contains every prime $< \text{head}$ (by pipeline construction)
2. **Coprimality**: $\text{head}$ is coprime to all `primes.tail` (by sieve construction — residues are coprime to modulus)
3. **Completeness**: For any $d \in [2, \text{head})$: $d$ has a prime factor $q \leq d < \text{head}$.
   By (1), $q \in \text{primes.tail}$. Therefore $\neg\text{isCoprime}(d, \text{primes.tail})$.
   This is expressed as $\text{assertAllNotCoprimeInRange}(\text{head}, 2, \text{primes.tail})$.
4. **Core lemma**: By $\text{assertNoDivisorByFactorList}(\text{head}, d, \text{primes.tail})$:
   $\text{mod}(\text{head}, d) \neq 0$ for every $d \in [2, \text{head})$.
5. **Conclusion**: Since no $d \in [2, \text{head})$ divides $\text{head}$, $\text{isPrime}(\text{head})$ holds ✓

#### Stainless Verification

The proof is formalized as two lemmas in `PrimeProperties.scala`:

**Bridge lemma** — proves `Prime.noDivisorInRange` from sieve completeness:

```scala
def assertNoDivisorInRangeFromHelper(
  n: BigInt,
  primes: List[BigInt],
  from: BigInt,
  to: BigInt
): Boolean = {
  require(n > 1)
  require(from >= 2)
  require(to >= from)
  require(ListUtils.checkAllPositive(primes))
  require(SieveUtils.isCoprime(n, primes))
  require(SieveUtils.assertAllNotCoprimeInRange(to, from, primes))
  decreases(to - from)
  if (from >= to) {
    Prime.noDivisorInRange(n, from, to)
  } else {
    assert(SieveUtils.hasPrimeFactorInList(from, primes))
    assert(SieveUtils.assertHasPrimeFactorImpliesNotCoprime(from, primes))
    assert(SieveUtils.assertNoDivisorByFactorList(n, from, primes))
    assert(assertNoDivisorInRangeFromHelper(n, primes, from + 1, to))
    Prime.noDivisorInRange(n, from, to)
  }
}.holds
```

**Final lemma** — wraps the proof as `Prime.isPrime`:

```scala
def assertHeadIsPrime(head: BigInt, primesTail: List[BigInt]): Boolean = {
  require(head > 1)
  require(ListUtils.checkAllPositive(primesTail))
  require(SieveUtils.isCoprime(head, primesTail))
  require(SieveUtils.assertAllNotCoprimeInRange(head, 2, primesTail))
  assertNoDivisorInRangeFromHelper(head, primesTail, 2, head)
  Prime.isPrime(head)
}.holds
```

This property completes the proof that every element of the `primes` list in a `SieveSequenceV2` is semantically prime. The full proof chain — from sieve construction through completeness assumption to primality — is verified at **5303 VCs, 0 invalid, 0 unknown**.

## 5. Implementation Consistency

### 5.1 Position Decomposition

**Lemma:** Any position can be decomposed into quotient and remainder.

```math
\forall\ i \geq 0:\ i = \left\lfloor \frac{i}{|G|} \right\rfloor \cdot |G| + (i \text{ mod } |G|)
```

This is a direct consequence of the Division Algorithm [[5]](#ref5).

Verified in [SieveSequenceProperties.scala at assertPositionDecomposition](../../src/main/scala/v1/seq/sieve/properties/SieveSequenceProperties.scala):

```scala
def assertPositionDecomposition(sieve: SieveSequence, position: BigInt): Boolean = {
  require(position >= 0)
  val gapSize = sieve.gaps.size
  val q = Calc.div(position, gapSize)
  val r = Calc.mod(position, gapSize)
  position == q * gapSize + r
}.holds
```

### 5.2 Residue Count Equals Gap Count

**Lemma:** The number of residues equals the number of gaps.

```math
|R| = |G|
```

This is maintained as an invariant of the SieveSequence construction.

Verified in [SieveSequenceProperties.scala at assertResidueCountEqualsGapCount](../../src/main/scala/v1/seq/sieve/properties/SieveSequenceProperties.scala):

```scala
def assertResidueCountEqualsGapCount(sieve: SieveSequence): Boolean = {
  sieve.residues.size == sieve.gaps.size
}.holds
```

## 6. Conclusion

This article presented the formal definition and verified properties of
Sieve Sequences, a mathematical structure for generating infinite sequences
of integers coprime to a given modulus via wheel factorization.

The main properties established are:

```math
\begin{aligned}
w_0 &= h & \text{[Head Value]} \\
w_{i+1} - w_i &= G_{(i+1) \text{ mod } |G|} & \text{[Step Property]} \\
w_{i+|G|} - w_i &= \text{cycleSum}(G) & \text{[Cycle Sum]} \\
w_i \bmod M &= R_{i \text{ mod } |R|} & \text{[Modulo Invariance]} \\
w_i > h \quad \forall i > 0 & & \text{[Head is Minimum]} \\
w_{i+1} > w_i & & \text{[Strictly Increasing]} \\
\gcd(w_i, M) = 1 & & \text{[Coprimality]} \\
\text{isPrime}(h) & & \text{[Head is Prime]} \\
\end{aligned}
```

Together, these properties show that the Sieve Sequence correctly generates
exactly the positive integers coprime to the modulus, in strictly increasing
order, starting from the head value. The head of each Sieve Sequence is prime,
and the sequence can be recursively refined to produce the next sieve level,
connecting directly to the Sieve of Eratosthenes.

The verified definitions provide a reusable foundation for prime number
generation, wheel factorization, and prime distribution analysis using
finite list structures and machine-checked Scala code.

## 7. Future Work

Future work may include:

- **Sieve of Eratosthenes**: Define the complete sieve as a recursive sequence
  of SieveSequence refinements
- **Prime Counting Function**: Use Sieve Sequences to derive bounds on $\pi(x)$
- **Optimization**: Explore more efficient representations for computational use
- **Applications**: Connect to number-theoretic results about prime distribution

## References

<a name="ref1" id="ref1" href="#ref1">[1]</a>
Mata, T. H. (2026). *Using Formal Verification to Prove Properties of Lists Recursively Defined*. Unpublished manuscript.
Available at: [https://github.com/thiagomata/prime-numbers/blob/master/articles/list.md](https://github.com/thiagomata/prime-numbers/blob/master/articles/list.md)

<a name="ref2" id="ref2" href="#ref2">[2]</a>
Mata, T. H. (2026). *Formal Verification of Discrete Integration Properties from First Principles*. Unpublished manuscript.
Available at: [https://github.com/thiagomata/prime-numbers/blob/master/articles/integral.md](https://github.com/thiagomata/prime-numbers/blob/master/articles/integral.md)

<a name="ref3" id="ref3" href="#ref3">[3]</a>
Mata, T. H. (2026). *Using Formal Verification to Prove Properties of Unbound Lists*. Unpublished manuscript.
Available at: [https://github.com/thiagomata/prime-numbers/blob/master/articles/cycle.md](https://github.com/thiagomata/prime-numbers/blob/master/articles/cycle.md)

<a name="ref4" id="ref4" href="#ref4">[4]</a>
Mata, T. H. (2026). *Formal Verification of Cycle Integral Properties from First Principles*. Unpublished manuscript.
Available at: [https://github.com/thiagomata/prime-numbers/blob/master/articles/integral-cycle.md](https://github.com/thiagomata/prime-numbers/blob/master/articles/integral-cycle.md)

<a name="ref5" id="ref5" href="#ref5">[5]</a>
Mata, T. H. (2026). *Proving Properties of Division and Modulo using Formal Verification*. Unpublished manuscript.
Available at: [https://github.com/thiagomata/prime-numbers/blob/master/articles/modulo.md](https://github.com/thiagomata/prime-numbers/blob/master/articles/modulo.md)
