# Formal Verification of Euclid's Theorem on the Infinitude of Primes

**Author:** Mata, T. H.  
Independent Researcher  
**Email:** [thiago.henrique.mata@gmail.com](mailto:thiago.henrique.mata@gmail.com)  
**GitHub:** [@thiagomata](https://github.com/thiagomata)

---

## Abstract

We present a formally verified proof of Euclid's Theorem — that there are infinitely many primes — using the Stainless verification system. The proof follows Euclid's classic construction: given any finite list of primes, compute their primorial (product) plus one, and show that this number has a prime divisor not in the original list. The formalization builds on a zero-prior-knowledge foundation of modular arithmetic and list operations, all previously verified from first principles. A key methodological insight is the `.holds` caching mechanism: assertions inside `.holds` lemmas are cached by Stainless and become available to callers, eliminating the need to enrich postconditions explicitly. The described theorem and supporting lemmas are machine-checked using a minimal, self-contained framework.

---

## 1. Introduction

Euclid's theorem — first proved in Euclid's *Elements* (c. 300 BC) — states that there are infinitely many prime numbers. The proof is elegantly simple:

> Given any finite list of primes $p_1, p_2, \dots, p_k$, let $N = p_1 \cdot p_2 \cdot \dots \cdot p_k + 1$.
> Then $N$ is either prime itself, or has a prime divisor $d$ that is not among $p_1, \dots, p_k$.
> In either case, a new prime is found, proving the list cannot contain all primes.

In this article, we formalize and verify this proof using [Scala Stainless](https://epfl-lara.github.io/stainless/intro.html) [[1]](#ref1), a verification framework for pure Scala programs. Our approach follows the zero-prior-knowledge methodology established in earlier articles: modular arithmetic [[2]](#ref2), lists [[3]](#ref3), and prime utilities are all defined from scratch and verified independently.

This article verifies:

- Primorial-plus-one coprime to all list primes — §3.1
- New prime found via the Euclid construction — §3.2
- The new prime is not in the original list — §3.3
- Euclid's theorem: primes are infinite — §3.4
- Downstream consequences: locating the next prime — §3.5
- Primality testing: sqrt-bound and composite detection — §3.6
- `.holds` caching eliminates explicit postcondition enrichment — §4

## 2. Preliminaries

We reuse several basic operations and their verified properties from companion articles:

- **Modular Arithmetic** [[2]](#ref2): Division, modulo, quotient invariance, mod idempotence
- **Lists** [[3]](#ref3): Size, append, sum, slicing, tail shift
- **Prime Utilities** (defined in the project): Primorial computation, primality testing

### 2.1 Key Definitions

Let $L = [p_1, p_2, \dots, p_k] \in \mathbb{N}^k$ be a non-empty list of primes, with $p_i > 1$ for all $i$.

We define the **primorial** of a list of primes as the product of all primes in the list:

```math
\text{primorial}(L) = \prod_{i=1}^{k} p_i
```

A number $n$ is **prime** if it is greater than 1 and has no positive divisors other than 1 and itself.

## 3. The Proof Strategy

Euclid's theorem is formalized as the following lemma:

```math
\forall\ \text{primes} \in \text{List[Prime]},\ \text{primes.nonEmpty} \implies
\exists\ p \notin \text{primes} : \text{isPrime}(p)
```

In the code, this is expressed as the function `euclidTheorem` (shown in full in Section 3.4).

- Stage 1: `primorial + 1` is coprime to every prime in the list (§3.1)
- Stage 2: find a prime divisor of `primorial + 1` via `findSmallestDivisor` (§3.2)
- Stage 3: the new prime is not in the original list (§3.3)
- Main theorem: combine stages 1-3 into Euclid's theorem (§3.4)
- Downstream consequences: locating the next prime (§3.5)
- Primality testing: sqrt-bound and composite detection (§3.6)

The proof proceeds in three stages:

1. **Primorial-plus-one is not divisible by any prime in the list**: Show that $\text{primorial}(L) + 1 \bmod p_i = 1 \neq 0$ for every $p_i \in L$.
2. **Smallest divisor is a new prime**: Find the smallest divisor $d > 1$ of $\text{primorial}(L) + 1$. Prove $d$ is prime and is not in the original list.
3. **Construct the result**: Return either $d$ (if $d < \text{primorial}(L) + 1$) or $\text{primorial}(L) + 1$ itself (if it is prime).

### 3.1 Stage 1: Primorial-plus-one Modulo All Primes

The first stage is captured by the lemma `primorialPlusOneModAny`. For any prime $p$ in the list, we prove:

```math
\begin{aligned}
\text{primorial}(L) &\equiv 0 \pmod p \quad &\text{[since } p \text{ divides the product]} \\
\text{primorial}(L) + 1 &\equiv 1 \pmod p \quad &\text{[by modular shift]} \\
1 \bmod p &= 1 \neq 0 \quad &\text{[since } p > 1] \\
\therefore\ \text{primorial}(L) + 1 &\not\equiv 0 \pmod p
\end{aligned}
```

The core of the proof is the helper `primorialPlusOneTailLoop`, which iterates over the list and uses three key modular lemmas:

```scala
private def primorialPlusOneTailLoop(previous: List[Prime], current: List[Prime]): Boolean = {
  decreases(current.size)
  if (current.isEmpty) true
  else {
    val p = current.head.value
    val tailPrimorial = PrimeUtils.primorial(current.tail)
    val previousPrimorial = PrimeUtils.primorial(previous)
    val primorialAll = previousPrimorial * p * tailPrimorial
    // Prove: mod(primorialAll, p) == 0
    assert(ModSmallDividend.modSmallDividend(BigInt(0), p))
    AdditionAndMultiplication.ATimesBSameMod(BigInt(0), p, previousPrimorial * tailPrimorial)
    assert(Calc.mod(primorialAll, p) == BigInt(0))
    // Prove: mod(primorialAll + 1, p) == mod(1, p)
    ModOperations.modZeroPlusC(primorialAll, p, BigInt(1))
    // Prove: mod(1, p) == 1 (since p > 1)
    assert(ModSmallDividend.modSmallDividend(BigInt(1), p))
    assert(Calc.mod(primorialAll + 1, p) != BigInt(0))
    Calc.mod(primorialAll + 1, p) != BigInt(0) &&
      primorialPlusOneTailLoop(previous :+ current.head, current.tail)
  }
}.holds
```

The `.holds` annotation tells Stainless to verify that this function returns `true` for all valid inputs. The three lemmas used are:

1. **`ModSmallDividend.modSmallDividend(a, b)`**: If $0 \leq a < b$, then $a \bmod b = a$. Used to prove $0 \bmod p = 0$ and $1 \bmod p = 1$.
2. **`AdditionAndMultiplication.ATimesBSameMod(a, b, m)`**: If $a \bmod b = 0$, then $a \cdot m \bmod b = 0$. Used to propagate zero-mod through multiplication.
3. **`ModOperations.modZeroPlusC(m, b, c)`**: If $m \bmod b = 0$, then $(m + c) \bmod b = c \bmod b$. Used to add 1 after proving the primorial is divisible by $p$.

### 3.2 Stage 2: Finding a New Prime

Once we know $\text{primorial}(L) + 1$ is not divisible by any prime in $L$, we find its smallest divisor $d > 1$ using `findSmallestDivisor`. Two key lemmas are established:

1. **`findSmallestDivisorIsNImpliesNoDivisorInRange`**: If the smallest divisor of $n$ starting from $k$ is $n$ itself, then $n$ has no divisor in $[k, n-1]$. This implies $n$ is prime.
2. **`assertSmallestDivisorIsPrime`**: If the smallest divisor $d$ of $n$ is less than $n$, then $d$ is prime. (Proof: any divisor of $d$ would also divide $n$ and be smaller than $d$, contradicting minimality.)

### 3.3 Stage 3: Proving the New Prime is Not in the List

The final and most subtle step is proving that the newly found prime $d$ (or $n$ itself) is **not** in the original list. This is handled by `euclidTailLoop`:

```scala
private def euclidTailLoop(
  primes: List[Prime],
  v: BigInt,
  n: BigInt,
  primorialSoFar: BigInt
): Boolean = {
  require(v > 1)
  require(n == primorialSoFar * PrimeUtils.primorial(primes) + BigInt(1))
  require(Calc.mod(n, v) == BigInt(0))
  decreases(primes.size)

  if (primes.isEmpty) true
  else {
    val p = primes.head.value
    PrimeUtils.primorialUnfold(primes)
    val k = primorialSoFar * PrimeUtils.primorial(primes.tail)
    assert(n == p * k + BigInt(1))
    assert(ModSmallDividend.modSmallDividend(BigInt(0), p))
    AdditionAndMultiplication.ATimesBSameMod(BigInt(0), p, k)
    assert(Calc.mod(p * k, p) == BigInt(0))
    ModOperations.modZeroPlusC(p * k, p, BigInt(1))
    assert(ModSmallDividend.modSmallDividend(BigInt(1), p))
    assert(Calc.mod(n, p) != BigInt(0))
    assert(p != v)
    p != v && euclidTailLoop(primes.tail, v, n, primorialSoFar * p)
  }
}.ensuring(res => res && valueNotMatchesAny(primes, v))
```

The logic is:

```math
\begin{aligned}
n &= \text{primorial}(\text{primes}) + 1 \\
  &= p \cdot k + 1 \quad &\text{[unfolding the primorial]} \\
n \bmod p &= (p \cdot k + 1) \bmod p \\
          &= (0 + 1) \bmod p \quad &\text{[since } p \cdot k \equiv 0 \pmod p] \\
          &= 1 \neq 0 \\
\therefore p &\neq v \quad &\text{[since } n \bmod v = 0, n \bmod p \neq 0]
\end{aligned}
```

The `ensuring` clause captures that the result implies `valueNotMatchesAny(primes, v)` — none of the primes in the list equal the divisor $v$.

### 3.4 The Main Theorem

The main theorem `euclidTheorem` brings everything together:

```scala
def euclidTheorem(primes: List[Prime]): Boolean = {
  require(primes.nonEmpty)

  primorialPlusOneModAny(primes)
  PrimeUtils.primorialPositive(primes)
  val n = PrimeUtils.primorial(primes) + 1
  val d = findSmallestDivisor(n, 2)

  if (d == n) {
    findSmallestDivisorIsNImpliesNoDivisorInRange(n, 2)
    assert(euclidTailLoop(primes, n, n, BigInt(1)))
    valueNotMatchesAny(primes, n)
  } else {
    assertSmallestDivisorIsPrime(n, d)
    findSmallestDivisorResultModZero(n, d)
    assert(euclidTailLoop(primes, d, n, BigInt(1)))
    valueNotMatchesAny(primes, d)
  }
}.holds
```

The postcondition `.holds` asserts that `euclidTheorem` always returns `true` — i.e., given any non-empty list of primes, there exists a prime not in that list.

### 3.5 Downstream Consequences: Locating the Next Prime

Stage 3 (§3.3) proves the new prime is not in the original `List[Prime]`. Three
further lemmas turn that fact into what the sieve construction elsewhere in
the codebase actually needs: a prime strictly greater than the current head,
suitable as a search upper bound.

**Restating non-membership as a cached fact.** `newPrimeNotInList` re-derives
`newPrimeFromEuclid`'s result together with `euclidTheorem`, linking the two
internal computations of the smallest divisor so that the non-membership
fact is available as a cached `.holds` result to callers, rather than
requiring them to redo the Euclid construction themselves.

**Bridging to `SortedPrimeList`.** The Euclid construction works over a plain
`List[Prime]`, but the sieve's running prime list is a `SortedPrimeList`.
`notContainsFromValueNotMatchesAny` proves the two membership predicates agree
by structural induction: since both recurse over the same sequence of prime
values in the same order, `valueNotMatchesAny` on the list implies
`!contains` on the sorted list.

**The strict inequality.** `euclidPrimeGreaterThanHead` combines the above
with `PrimeListUtils.primeAtOrBelowHeadIsContained` (any prime at or below the
list's head must already be contained in a complete `allPrimesSoFar` list):
since the Euclid-constructed prime is *not* contained, it cannot be at or
below the head, so it must be strictly greater.

```math
\begin{aligned}
\text{sortedList.nonEmpty} \;\land\; \text{allPrimesSoFar}(\text{sortedList})
  &\implies d > \text{sortedList.head.value}
  &&\text{[Q.E.D.]}
\end{aligned}
```

where $d$ is the value of `newPrimeFromEuclid(sortedList.list)`. This is the
exact inequality that makes the Euclid-constructed prime usable as the upper
bound in `searchNextPrimeUpTo`.

These properties are verified in the [
  PrimeProperties::newPrimeNotInList
](../../src/main/scala/v1/chapter5/prime/properties/PrimeProperties.scala), [
  PrimeProperties::notContainsFromValueNotMatchesAny
](../../src/main/scala/v1/chapter5/prime/properties/PrimeProperties.scala), and [
  PrimeProperties::euclidPrimeGreaterThanHead
](../../src/main/scala/v1/chapter5/prime/properties/PrimeProperties.scala).

### 3.6 Primality Testing: Sqrt-Bound and Composite Detection

The primality test used in Euclid's proof relies on `findSmallestDivisor(n, 2)`,
which scans candidates from 2 upward until it finds the smallest divisor of `n`.
Two lemmas characterize why this scan is both correct and efficient.

**Composite has a divisor below n.** If `n` is composite and `d` is its smallest
non-trivial divisor, then `d < n`. This is immediate from the definition of
composite — there exists a proper divisor — but must be proved against the
`findSmallestDivisor` algorithm, which scans upward until a divisor is found
or `n` itself is reached.

```math
\begin{aligned}
n > 1 \;\land\; \neg \text{isPrime}(n) &\Rightarrow \\
\exists\, d = \text{findSmallestDivisor}(n, 2) &: 2 \leq d < n \;\land\; \text{Calc.mod}(n, d) = 0
  &&\text{[Q.E.D.]}
\end{aligned}
```

**Smallest divisor is at most sqrt(n).** When `n` is composite with smallest
divisor `d`, the factor `q = n / d` satisfies `q ≥ d`. Then `d · d ≤ d · q = n`,
so `d² ≤ n`. This means the scan only needs to check divisors up to `sqrt(n)`
— any divisor beyond that would have a co-factor below `d`, violating
minimality.

```math
\begin{aligned}
n > 1 \;\land\; \neg \text{isPrime}(n) &\Rightarrow \\
d = \text{findSmallestDivisor}(n, 2) &: d \cdot d \leq n
  &&\text{[Q.E.D.]}
\end{aligned}
```

**Proof.** From the composite assumption, `assertCompositeHasDivisorStrictlyBelowN(n)`
gives `d < n` with `mod(n, d) = 0`. Let `q = n / d`, so `q · d = n`. If `q < d`,
then `q` is a divisor of `n` smaller than `d`, contradicting `d` being the
smallest divisor. Therefore `q ≥ d`, and `d · d ≤ d · q = n`.

### Stainless Verification

```scala
def assertSmallestDivisorAtMostSqrt(n: BigInt): Boolean = {
  require(n > 1)
  require(!Prime.isPrime(n))
  val d = findSmallestDivisor(n, 2)
  d * d <= n
}.holds

private def assertCompositeHasDivisorStrictlyBelowN(n: BigInt): Boolean = {
  require(n > 1)
  require(!Prime.isPrime(n))
  val d = findSmallestDivisor(n, 2)
  d < n
}.holds
```

These properties are verified in the [
  PrimeProperties::assertSmallestDivisorAtMostSqrt
](
  ../../src/main/scala/v1/chapter5/prime/properties/PrimeProperties.scala
) and [
  PrimeProperties::assertCompositeHasDivisorStrictlyBelowN
](
  ../../src/main/scala/v1/chapter5/prime/properties/PrimeProperties.scala
).

## 4. The `.holds` Caching Insight

A key methodological discovery during this verification was the `.holds` caching mechanism. When a function is annotated with `.holds`, Stainless verifies it returns `true` and caches all internal assertions. These cached facts are then available at every call site without additional postcondition work.

For example, in `euclidTailLoop`:

```scala
assert(Calc.mod(n, p) != BigInt(0))
```

This assertion is verified and cached. When `euclidTheorem` calls `assert(euclidTailLoop(primes, d, n, BigInt(1)))`, the cached assertion that $\text{Calc.mod}(n, p) \neq 0$ for each $p$ is available, which is exactly what's needed to prove $p \neq d$.

This means we can write modular proofs using simple `assert` statements within `.holds` lemmas, without needing to enrich `ensuring` postconditions to expose every fact. The caching system does the work for us.

## 5. Verification Status

The properties described in this article are verified by Stainless through the source-linked `.holds` functions listed in Appendix A. The repository-wide verification-condition count is intentionally omitted because it changes as unrelated verified modules are added; the stable claim is that the Euclid theorem proof and its supporting lemmas are machine-checked in the current source.

## 6. Related Work

This formalization builds on a verified hierarchy of mathematical structures:

| Article | Topic | Reference |
|---------|-------|-----------|
| Modulo | Division and modulo properties | [[2]](#ref2) |
| Lists | Recursive list definitions | [[3]](#ref3) |
| Integral | Discrete integration | [[4]](#ref4) |
| Cycles | Unbounded periodic lists | [[5]](#ref5) |
| Cycle Integral | Integration over cycles | [[6]](#ref6) |

The present article adds Euclid's theorem as a formal capstone — a classical result of number theory, verified from first principles, with all arithmetic lemmas machine-checked.

## 7. Conclusion

We have presented a formally verified proof of Euclid's theorem using the Stainless verification system. The proof:

1. Builds on a zero-prior-knowledge foundation of modular arithmetic and list operations
2. Follows Euclid's classic primorial-plus-one construction
3. Proves that the resulting number has a prime divisor not in the original list
4. Achieves machine-checked verification through source-linked `.holds` functions

The key methodological insight — the `.holds` caching mechanism — simplifies the proof by making internal assertions available to callers without explicit postcondition enrichment.

## 8. Future Work

This formalization opens several directions for future work:

- **Fundamental Theorem of Arithmetic**: Formalize unique prime factorization
- **Dirichlet's Theorem**: Extend to arithmetic progressions
- **Prime Number Theorem**: Asymptotic distribution of primes

## References

<a name="ref1" id="ref1" href="#ref1">[1]</a>
Hamza, J., Voirol, N., & Kuncak, V. (2019). *System FR: Formalized foundations for the Stainless verifier*. Proceedings of the ACM on Programming Languages, OOPSLA Issue.

<a name="ref2" id="ref2" href="#ref2">[2]</a>
Mata, T. H. (2026). *Proving Properties of Division and Modulo using Formal Verification*. Available at: [https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter2/modulo.md](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter2/modulo.md)

<a name="ref3" id="ref3" href="#ref3">[3]</a>
Mata, T. H. (2026). *Using Formal Verification to Prove Properties of Lists Recursively Defined*. Available at: [https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter3/list.md](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter3/list.md)

<a name="ref4" id="ref4" href="#ref4">[4]</a>
Mata, T. H. (2026). *Formal Verification of Discrete Integration Properties from First Principles*. Available at: [https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter4/integral.md](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter4/integral.md)

<a name="ref5" id="ref5" href="#ref5">[5]</a>
Mata, T. H. (2026). *Using Formal Verification to Prove Properties of Unbound Lists*. Available at: [https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter4/cycle.md](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter4/cycle.md)

<a name="ref6" id="ref6" href="#ref6">[6]</a>
Mata, T. H. (2026). *Formal Verification of Cycle Integral Properties from First Principles*. Available at: [https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter4/integral-cycle.md](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter4/integral-cycle.md)

---

## Appendix A: Verification Source References

### A.1 `primorialPlusOneModAny`

**Source**: `src/main/scala/v1/chapter5/prime/properties/PrimeProperties.scala`

Full Scala verification code for Stage 1 (Section 3.1):

```scala
def primorialPlusOneModAny(primes: List[Prime]): Boolean = {
  require(primes.nonEmpty)
  decreases(primes.size)
  primorialPlusOneTailLoop(List.empty, primes)
}.holds
```

This lemma proves that $\text{primorial}(\text{primes}) + 1$ is not divisible by any prime in the list. The `.holds` annotation triggers Stainless verification of the recursive `primorialPlusOneTailLoop` helper, which iterates over the list and applies modular arithmetic lemmas.

### A.2 `newPrimeFromEuclid`

**Source**: `src/main/scala/v1/chapter5/prime/properties/PrimeProperties.scala`

Full Scala verification code for Stage 2 (Section 3.2):

```scala
def newPrimeFromEuclid(primes: List[Prime]): Prime = {
  require(primes.nonEmpty)
  require(primorialPlusOneModAny(primes))

  PrimeUtils.primorialPositive(primes)
  val n = PrimeUtils.primorial(primes) + 1
  val d = findSmallestDivisor(n, 2)

  if (d == n) {
    findSmallestDivisorIsNImpliesNoDivisorInRange(n, 2)
    Prime(n)
  } else {
    assertSmallestDivisorIsPrime(n, d)
    findSmallestDivisorResultModZero(n, d)
    Prime(d)
  }
}
```

This function constructs a new `Prime` value by finding the smallest divisor of $n = \text{primorial}(\text{primes}) + 1$. If $d = n$, then $n$ itself is prime; otherwise $d$ is a prime divisor. In either case, the result is a prime not in the original list.

### A.3 `euclidTheorem`

**Source**: `src/main/scala/v1/chapter5/prime/properties/PrimeProperties.scala`

Full Scala verification code for the main theorem (Section 3.4):

```scala
def euclidTheorem(primes: List[Prime]): Boolean = {
  require(primes.nonEmpty)

  primorialPlusOneModAny(primes)
  PrimeUtils.primorialPositive(primes)
  val n = PrimeUtils.primorial(primes) + 1
  val d = findSmallestDivisor(n, 2)

  if (d == n) {
    findSmallestDivisorIsNImpliesNoDivisorInRange(n, 2)
    assert(euclidTailLoop(primes, n, n, BigInt(1)))
    valueNotMatchesAny(primes, n)
  } else {
    assertSmallestDivisorIsPrime(n, d)
    findSmallestDivisorResultModZero(n, d)
    assert(euclidTailLoop(primes, d, n, BigInt(1)))
    valueNotMatchesAny(primes, d)
  }
}.holds
```

The `.holds` postcondition asserts: given any non-empty list of primes, there exists a prime not in that list.

---

## Appendix B: Stainless Verification Status and Log Output

The latest `just verify` run verifies all the described properties without errors. The full log output is available at: [logs/verify.log](../../logs/verify.log)