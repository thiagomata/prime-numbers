# Formal Verification of Euclid's Theorem on the Infinitude of Primes

**Author:** Thiago Henrique Ramos da Mata
Independent Researcher  
**Email:** [thiago.henrique.mata@gmail.com](mailto:thiago.henrique.mata@gmail.com)  
**GitHub:** [@thiagomata](https://github.com/thiagomata)  
**License:** [CC BY 4.0](../LICENSE)

---

## Abstract

We present a formally verified proof of Euclid's Theorem — that there are infinitely many primes — using the Stainless verification system. The proof uses the familiar primorial-plus-one specialization of Euclid's finite-list construction: given any finite list of primes, compute their product plus one, and show that this number has a prime divisor not in the original list. The formalization builds on a zero-prior-knowledge foundation of modular arithmetic and list operations, all previously verified from first principles. The described theorem and supporting lemmas are machine-checked using a minimal, self-contained framework.

---

## 1. Introduction

Euclid's theorem — proved in Euclid's *Elements*, Book IX, Proposition 20
[[7]](#ref7) — states that there are infinitely many prime numbers. Euclid's
original presentation uses a common multiple of the assigned primes plus one.
This article formalizes the product (primorial) specialization of that
construction:

> Given any finite list of primes $p_1, p_2, \dots, p_k$, let $N = p_1 \cdot p_2 \cdot \dots \cdot p_k + 1$.
> Then $N$ is either prime itself, or has a prime divisor $d$ that is not among $p_1, \dots, p_k$.
> In either case, a new prime is found, proving the list cannot contain all primes.

In this article, we formalize and verify this proof using [Scala Stainless](https://epfl-lara.github.io/stainless/intro.html) [[1]](#ref1), a verification framework for pure Scala programs. Our approach follows the zero-prior-knowledge methodology established in earlier articles: modular arithmetic [[2]](#ref2), lists [[3]](#ref3), and prime utilities are all defined from scratch and verified independently.

This article verifies:

- Primorial-plus-one coprime to all list primes — [§3.1](#31-stage-1-primorial-plus-one-modulo-all-primes)
- New prime found via the Euclid construction — [§3.2](#32-stage-2-finding-a-new-prime)
- The new prime is not in the original list — [§3.3](#33-stage-3-proving-the-new-prime-is-not-in-the-list)
- Euclid's theorem: primes are infinite — [§3.4](#34-the-main-theorem)
- Supporting verified prime lemmas — [§4](#4-supporting-verified-lemmas)

## 2. Preliminaries

We reuse several basic operations and their verified properties from companion articles:

- **Modular Arithmetic** [[2]](#ref2): Division, modulo, quotient invariance, mod idempotence
- **Lists** [[3]](#ref3): Size, append, sum, slicing, tail shift
- **Prime Utilities:** Primorial computation, primality testing, and finite divisor search, specified below

### 2.1 Key Definitions

Let $L = [p_1, p_2, \dots, p_k] \in \mathbb{N}^k$ be a non-empty list of primes, with $p_i > 1$ for all $i$.

We define the **primorial** of a list of primes as the product of all primes in the list:

```math
\begin{aligned}
\text{primorial}(L) = \prod_{i=1}^{k} p_i
\end{aligned}
```

A number $n$ is **prime** exactly when it is greater than $1$ and no integer
in $[2,n)$ divides it:

```math
\text{isPrime}(n) \;:\\Longleftrightarrow\; n>1\ \land\
\forall d\in[2,n),\ \text{mod}(n,d)\ne0.
```

### 2.2 Finite Prime Operations and Their Specifications

The article needs only finite search and the definitions below; it does not
assume an external enumeration of all primes.  Primorial is structural:

```math
\begin{aligned}
\text{primorial}([]) &:= 1, \\
\text{primorial}(p::P) &:= p\cdot\text{primorial}(P).
\end{aligned}
```

For $n>1$ and $2\leq s\leq n$, `findSmallestDivisor(n,s)` tests
$s,s+1,\ldots,n$ in order and returns the first divisor.  It terminates
because $n$ itself divides $n$.  Its specification is therefore

```math
\begin{aligned}
d &= \text{findSmallestDivisor}(n,s) \\
&\implies s\leq d\leq n\ \land\ \text{mod}(n,d)=0 \\
&\phantom{\implies}\land\ \forall e\in[s,d),\ \text{mod}(n,e)\ne0.
\end{aligned}
```

The recursive scan proves this by induction on $n-s$: either $s$ divides
$n$, or the same claim is inherited from the call beginning at $s+1$.
Thus, when $s=2$, `d=n` is equivalent to the prime definition in
[§2.1](#21-key-definitions); if $d<n$, $d$ is the least non-trivial divisor.
The divisor-range postcondition is encoded in
[`Prime::findSmallestDivisor`](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter5/prime/Prime.scala).
Its minimality and its equivalence with an empty divisor range are
machine-checked by `Prime::assertFindSmallestDivisorMinimality` and
`Prime::assertFindSmallestDivisorEquivNoDivisorInRange` in the same source.

For a list $P$ of positive integers, `isCoprime(n,P)` means that no member of
$P$ divides $n$; it is a direct recursion over the list.  This is the only
list-coprimality meaning used below.

## 3. The Proof Strategy

Euclid's theorem is formalized as the following lemma:

```math
\begin{aligned}
\forall\ \text{primes} \in \text{List[Prime]},\ \text{primes} \neq \emptyset \implies
\exists\ p \notin \text{primes} : \text{isPrime}(p)
\end{aligned}
```

In the source, this is expressed by `PrimeProperties::euclidTheorem`; the
verification reference is given in [§3.4](#34-the-main-theorem) and Appendix A.3.

- Stage 1: $\text{primorial}(L)+1$ is coprime to every prime in the list ([§3.1](#31-stage-1-primorial-plus-one-modulo-all-primes))
- Stage 2: find a prime divisor of $\text{primorial}(L)+1$ via `findSmallestDivisor` ([§3.2](#32-stage-2-finding-a-new-prime))
- Stage 3: the new prime is not in the original list ([§3.3](#33-stage-3-proving-the-new-prime-is-not-in-the-list))
- Main theorem: combine stages 1-3 into Euclid's theorem ([§3.4](#34-the-main-theorem))

The proof proceeds in three stages:

1. **Primorial-plus-one is not divisible by any prime in the list**: Show that $\text{primorial}(L) + 1 \bmod p_i = 1 \neq 0$ for every $p_i \in L$.
2. **Smallest divisor is a new prime**: Find the smallest divisor $d > 1$ of $\text{primorial}(L) + 1$. Prove $d$ is prime and is not in the original list.
3. **Construct the result**: Return either $d$ (if $d < \text{primorial}(L) + 1$) or $\text{primorial}(L) + 1$ itself (if it is prime).

### 3.1 Stage 1: Primorial-plus-one Modulo All Primes

The first stage is captured by the lemma `primorialPlusOneModAny`. Let
$L = [p_1,\dots,p_k]$ be the finite list of known primes and
$P=\text{primorial}(L)$. For each $p_i \in L$, the product $P$
contains $p_i$ as one factor, so $P$ is divisible by $p_i$. Adding one moves
the residue from $0$ to $1$, and because every prime is greater than $1$, that
residue is nonzero.

```math
\begin{aligned}
\text{primorial}(L)
  &= p_i \cdot \prod_{j\ne i} p_j
  &&\text{[By Definition]} \\
\text{mod}(\text{primorial}(L), p_i)
  &= 0
  &&\text{[Product Contains }p_i\text{]} \\
\text{mod}(\text{primorial}(L)+1, p_i)
  &= \text{mod}(1, p_i)
  &&\text{[Modulo Shift]} \\
  &= 1
  &&\text{[Since }1 < p_i\text{]} \\
  &\ne 0
  &&\blacksquare\ \text{[Q.E.D.]}
\end{aligned}
```

The verified source proves this by induction over the list. At each step, the
current prime is split out of the primorial product, the divisibility of the
remaining product is preserved by multiplication, and the induction hypothesis
continues over the tail. The loop step is built from three verified arithmetic
properties.

**Small Dividend Remainder.** A nonnegative dividend smaller than the divisor is
already its own remainder. In the Euclid step, this gives both
$\text{mod}(0,p)=0$ and $\text{mod}(1,p)=1$ because $p>1$.

```math
\begin{aligned}
0 \le a < b
&\Rightarrow \text{mod}(a,b)=a
&&\text{[Small Dividend]} \\
p>1
&\Rightarrow \text{mod}(0,p)=0
\land \text{mod}(1,p)=1
&&\text{[Substitution]}
\end{aligned}
```

This property is verified in [
  ModSmallDividend::modSmallDividend
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter2/div/properties/ModSmallDividend.scala).

**Zero Remainder Preserved by Multiplication.** If a number is divisible by
$b$, multiplying it by any nonnegative factor preserves divisibility by $b$.
This is the step that turns the explicit factor $p$ in the primorial into
$\text{mod}(p\cdot k,p)=0$.

```math
\begin{aligned}
\text{mod}(a,b)=0
&\Rightarrow \text{mod}(a\cdot m,b)=0
&&\text{[Multiplication Preserves Zero Remainder]} \\
\text{mod}(p,p)=0
&\Rightarrow \text{mod}(p\cdot k,p)=0
&&\text{[Substitution]}
\end{aligned}
```

This property is verified in [
  AdditionAndMultiplication::ATimesBSameMod
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter2/div/properties/AdditionAndMultiplication.scala).

**Adding One After a Multiple.** Once the primorial part is known to be
divisible by $p$, adding one gives the same remainder as one itself.
Together with the small-dividend property, this proves the Euclid number has
nonzero remainder modulo every original prime.

```math
\begin{aligned}
\text{mod}(m,b)=0
&\Rightarrow \text{mod}(m+c,b)=\text{mod}(c,b)
&&\text{[Modulo Shift]} \\
\text{mod}(p\cdot k,p)=0
&\Rightarrow \text{mod}(p\cdot k+1,p)=\text{mod}(1,p)=1
&&\text{[Substitution]} \\
&\Rightarrow \text{mod}(p\cdot k+1,p)\ne0
&&\blacksquare\ \text{[Q.E.D.]}
\end{aligned}
```

This property is verified in [
  ModOperations::modZeroPlusC
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter2/div/properties/ModOperations.scala).

This property is verified in [
  PrimeProperties::primorialPlusOneModAny
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter5/prime/properties/PrimeProperties.scala). A short public wrapper excerpt is included in Appendix A.1.

### 3.2 Stage 2: Finding a New Prime

Once we know $\text{primorial}(L)+1$ is not divisible by any prime in
$L$, let

```math
\begin{aligned}
N &= \text{primorial}(L)+1, \\
d &= \text{findSmallestDivisor}(N,2).
\end{aligned}
```

There are two cases. If $d=N$, the divisor search found no proper divisor in
$[2,N)$, so $N$ is prime. If $d < N$, then $d$ divides $N$ and no smaller integer
greater than $1$ divides $N$. If $d$ were composite, it would have a non-trivial
divisor $e$ with $1 < e < d$; since $e$ divides $d$ and $d$ divides $N$, $e$ would
divide $N$, contradicting the minimality of $d$. Hence $d$ is prime.

```math
\begin{aligned}
d=N
&\Rightarrow \forall e\in[2,N),\text{mod}(N,e)\ne0.         &&\text{[No Proper Divisor Found]} \\
&\Rightarrow \text{isPrime}(N)                              &&\text{[Prime Definition]} \\
&d < N \land \text{mod}(N,d)=0 \Rightarrow \text{isPrime}(d)  &&\text{[Minimal Divisor]} \\
\end{aligned}
```

The construction of the new prime is verified in [
  PrimeProperties::newPrimeFromEuclid
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter5/prime/properties/PrimeProperties.scala). A short public wrapper excerpt is included in Appendix A.2.

### 3.3 Stage 3: Proving the New Prime is Not in the List

The final and most subtle step is proving that the newly found prime $d$ (or
$N$ itself) is **not** in the original list.

Let $v$ be the divisor chosen in Stage 2: either $v=N$ when $N$ is prime, or
$v=d$ when $d$ is the smallest proper divisor of $N$. In both cases,
$\text{mod}(N,v)=0$. Now take any prime $p$ from the original list.
Because $N=\text{primorial}(L)+1$, the same argument from Stage 1 gives
$\text{mod}(N,p)=1$. If $p=v$, then $N$ would have two incompatible
remainders modulo the same positive divisor: $0$ and $1$. Therefore no element
of $L$ equals $v$.

```math
\begin{aligned}
N &= \text{primorial}(L) + 1
&&\text{[Euclid Construction]} \\
  &= p \cdot k + 1
&&\text{[Unfold Product at }p\text{]} \\
\text{mod}(N,p)
  &= \text{mod}(p\cdot k+1,p) \\
  &= \text{mod}(1,p)
&&\text{[Multiple of }p\text{ Drops Out]} \\
  &= 1
&&\text{[Since }p>1\text{]} \\
\text{mod}(N,v)
  &= 0
&&\text{[Chosen Divisor]} \\
p=v
  &\Rightarrow 1=0
&&\text{[Contradiction]} \\
\therefore\ p &\ne v
&&\blacksquare\ \text{[Q.E.D.]}
\end{aligned}
```

This non-membership argument is verified by the private helper
`euclidTailLoop`, which establishes `valueNotMatchesAny(primes, v)` for the
chosen divisor $v$ in [
  PrimeProperties
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter5/prime/properties/PrimeProperties.scala).

### 3.4 The Main Theorem

The main theorem combines the primorial-plus-one lemma, smallest-divisor
primality, and non-membership argument. If $N$ is prime, then $N$ itself is
the new prime. Otherwise, the smallest divisor $d$ of $N$ is prime and cannot
belong to the original list.

```math
\begin{aligned}
L &\ne [] \\
N &= \text{primorial}(L)+1 \\
d &= \text{findSmallestDivisor}(N,2) \\
d=N
&\Rightarrow \text{isPrime}(N)\land N\notin L
&&\text{[Stages 2 and 3]} \\
d < N
&\Rightarrow \text{isPrime}(d)\land d\notin L
&&\text{[Stages 2 and 3]} \\
\therefore\ \exists p:\text{isPrime}(p)\land p\notin L
&&\text{[Case Split]}\quad\blacksquare\ \text{[Q.E.D.]}
\end{aligned}
```

This property is verified in [
  PrimeProperties::euclidTheorem
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter5/prime/properties/PrimeProperties.scala). The public theorem wrapper is shown in Appendix A.3.

## 4. Supporting Verified Lemmas

The theorem above is the article's main result. We also record a few closely
related lemmas that reuse the same prime and divisibility foundations.
They are included here as supporting results, not as additional headline
claims.

- Finite-prefix consequence: a complete finite prime prefix has a larger prime — [§4.1](#41-corollary-greater-than-a-complete-finite-prefix)
- Divisor-search bounds: composite inputs have a proper smallest divisor below their square root — [§4.2](#42-smallest-divisor-bounds-for-composite-numbers)
- Finite-prefix primality: coprimality plus factor coverage excludes all proper divisors — [§4.3](#43-finite-prefix-primality-criterion)
- Bézout product lemmas: a prime divisor of a product is forced onto a factor — [§4.4](#44-bézout-and-prime-product-lemmas)

### 4.1 Corollary: Greater Than a Complete Finite Prefix

A direct corollary of Euclid's construction is that a complete finite prefix
of the primes is never closed. Let $P=[p_1,\dots,p_k]$ be a sorted finite list
that contains every prime up to its largest element $h=p_k$. Let $q$ be the
prime produced by the Euclid construction from $P$. Since [§3](#3-the-proof-strategy) proves
$q\notin P$, $q$ cannot be at or below $h$: every prime at or below $h$ is
already contained in the complete prefix. Therefore $q > h$.

```math
\begin{aligned}
P &= [p_1,\dots,p_k],\quad h=p_k
&&\text{[Finite Prime Prefix]} \\
\forall r,\ \text{isPrime}(r)\land r\le h
&\Rightarrow r\in P
&&\text{[Prefix Complete Through }h\text{]} \\
\text{isPrime}(q)\land q\notin P
&&\text{[Euclid Construction]} \\
q\le h
&\Rightarrow q\in P
&&\text{[Prefix Completeness]} \\
q\le h
&\Rightarrow q\in P\land q\notin P
&&\text{[Contradiction]} \\
\therefore\ q&>h
&&\blacksquare\ \text{[Q.E.D.]}
\end{aligned}
```

This is the ordered-prefix form of the Euclid theorem: from any complete finite
prefix of the primes, the construction produces a prime beyond that prefix.

This corollary is verified in [
  PrimeProperties::newPrimeNotInList
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter5/prime/properties/PrimeProperties.scala), [
  PrimeProperties::notContainsFromValueNotMatchesAny
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter5/prime/properties/PrimeProperties.scala), and [
  PrimeProperties::euclidPrimeGreaterThanHead
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter5/prime/properties/PrimeProperties.scala).

### 4.2 Smallest-Divisor Bounds for Composite Numbers

The primality test used in Euclid's proof relies on `findSmallestDivisor(n, 2)`,
which scans candidates from 2 upward until it finds the smallest divisor of $n$.
Two lemmas characterize why this scan is both correct and efficient.

**Composite has a divisor below n.** If $n$ is composite and $d$ is its smallest
non-trivial divisor, then $d < n$. This is immediate from the definition of
composite — there exists a proper divisor — but must be proved against the
`findSmallestDivisor` algorithm, which scans upward until a divisor is found
or $n$ itself is reached.

```math
\begin{aligned}
n > 1 \;\land\; \neg \text{isPrime}(n) &\Rightarrow \\
\exists\, d = \text{findSmallestDivisor}(n, 2) &: 2 \leq d < n \;\land\; \text{Calc.mod}(n, d) = 0
\end{aligned}
```

**Proof.** Since $n$ is composite, it has a proper divisor
$e\in[2,n)$. The minimality specification from [§2.2](#22-finite-prime-operations-and-their-specifications) gives
$2\leq d\leq e<n$ and $\text{mod}(n,d)=0$.

```math
\therefore\ 2\leq d<n\ \land\ \text{mod}(n,d)=0.
\quad \blacksquare\ \text{[Q.E.D.]}
```

**Smallest divisor is at most sqrt(n).** When $n$ is composite with smallest
divisor $d$, the factor $q = n / d$ satisfies $q \ge d$. Then $d \cdot d \le d \cdot q = n$,
so $d^2 \le n$. This means the scan only needs to check divisors up to $\sqrt{n}$
— any divisor beyond that would have a co-factor below $d$, violating
minimality.

```math
\begin{aligned}
n > 1 \;\land\; \neg \text{isPrime}(n) &\Rightarrow \\
d = \text{findSmallestDivisor}(n, 2) &: d \cdot d \leq n.
\end{aligned}
```

**Proof.** Put $q=n/d$. Since $d$ divides $n$, $dq=n$. Because $d<n$,
$q>1$; hence $q\ge2$. If $q<d$, then $q\in[2,d)$ is a divisor of $n$,
contradicting the minimality of $d$.
Hence $d\leq q$, and

```math
d^2\leq dq=n.\quad\blacksquare\ \text{[Q.E.D.]}
```

**Packaged composite divisor.** The wrapper `assertCompositeSmallestPrimeDivisor`
combines the previous results into a reusable form: every
composite number has a non-trivial prime divisor, the divisor really divides
the number, and it lies at or below the square root bound.

```math
\begin{aligned}
n > 1 \;\land\; \neg \text{isPrime}(n)
&\Rightarrow \exists d: \\
&2 \le d < n
\;\land\; \text{isPrime}(d)
\;\land\; d^2 \le n
\;\land\; \text{Calc.mod}(n,d)=0
  &&\text{[Composite Smallest Prime Divisor]}
\end{aligned}
```

**Proof.** From the composite assumption, `assertCompositeHasDivisorStrictlyBelowN(n)`
gives $d < n$ with $\text{mod}(n, d) = 0$. Let $q = n / d$, so $q \cdot d = n$.
If $q < d$, then $q$ is a divisor of $n$ smaller than $d$, contradicting $d$
being the smallest divisor. Therefore $q \ge d$, and $d \cdot d \le d \cdot q = n$.

These properties are verified in the [
  PrimeProperties::assertSmallestDivisorAtMostSqrt
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter5/prime/properties/PrimeProperties.scala), [
  PrimeProperties::assertCompositeHasDivisorStrictlyBelowN
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter5/prime/properties/PrimeProperties.scala), and [
  PrimeProperties::assertCompositeSmallestPrimeDivisor
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter5/prime/properties/PrimeProperties.scala).

### 4.3 Finite-Prefix Primality Criterion

The next supporting result is a local primality criterion. If a candidate
number is coprime to all primes in a finite filter list, and every integer in
the range $[2, head)$ has a prime factor among those filters, then the
candidate itself is prime.

This is not Euclid's infinitude theorem; it is a finite-prefix primality
criterion. It turns coverage of all smaller possible divisors into primality
of the candidate.

```math
\begin{aligned}
head > 1
\;\land\; \text{isCoprime}(head,\overline P)
\;\land\;
\forall d\in[2,head),\ \neg \text{isCoprime}(d,\overline P)
&\Rightarrow \text{isPrime}(head).
\end{aligned}
```

The proof is by contradiction over possible divisors. If a divisor $d$ of
$head$ existed in $[2, head)$, the range-coverage assumption would provide a
prime factor from the finite filter list dividing $d$. Divisibility would then
propagate from that factor through $d$ into $head$, contradicting that $head$
is coprime to every filter prime.

This property is verified in [
  PrimeProperties::assertHeadIsPrime
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter5/prime/properties/PrimeProperties.scala). Its main range helper is [
  PrimeProperties::assertNoDivisorInRangeFromHelper
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter5/prime/properties/PrimeProperties.scala).

### 4.4 Bézout and Prime-Product Lemmas

Several arguments about prime-filtered products use a product form of
primality: for a prime $p$, divisibility of a nonnegative product by $p$ can
be pushed onto a factor, and if neither nonnegative factor is divisible by
$p$, then the product is not divisible by $p$. The verified proof goes through
Bézout's identity.

First, if $0 < h < p$, $p$ is prime, and $h$ is not divisible by $p$, then
$h$ and $p$ have greatest common divisor $1$, and the extended Euclidean
algorithm exposes a linear combination:

```math
\begin{aligned}
\text{isPrime}(p)
\land 0 < h < p
\land \text{mod}(h,p)\ne0
&\Rightarrow
\exists x,y,\ h x + p y = 1.
\end{aligned}
```

For completeness, the subtractive extended Euclidean algorithm repeatedly
replaces the larger positive input by its difference with the smaller. Common
divisors are preserved and the positive sum decreases, so it reaches equal
values. Reversing either subtraction step preserves a linear-combination
witness:

```math
\begin{aligned}
(a-b)x+by=g &\implies ax+b(y-x)=g, \\
ax+(b-a)y=g &\implies a(x-y)+by=g.
\end{aligned}
```

Every common divisor of $h$ and the prime $p$ is either $1$ or $p$; it cannot
be $p$ because $0<h<p$. The terminal gcd is therefore $1$, which gives the
displayed Bézout identity. \(\blacksquare\ \text{[Q.E.D.]}\)

Multiplying that identity by $k$ gives $k h x + k p y = k$. If $p$ divides
$k h$, then $p$ divides both terms on the left and therefore divides $k$.

```math
\begin{aligned}
\text{isPrime}(p)
\land k\ge0
\land h\ge0
\land \text{mod}(h,p)\ne0
\land \text{mod}(kh,p)=0
&\Rightarrow \text{mod}(k,p)=0.
\end{aligned}
```

The contrapositive form used by product and density arguments is:

```math
\begin{aligned}
\text{isPrime}(p)
\land k\ge0
\land h\ge0
\land \text{mod}(k,p)\ne0
\land \text{mod}(h,p)\ne0
&\Rightarrow \text{mod}(kh,p)\ne0.
\end{aligned}
```

The full proof bodies are verified in [
  BezoutUtils::assertCoprimeLinearCombinationOne
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter5/prime/BezoutUtils.scala), [
  BezoutUtils::assertPrimeDivKhImpliesDivK
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter5/prime/BezoutUtils.scala), and [
  BezoutUtils::assertPrimeProductNotDivisible
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter5/prime/BezoutUtils.scala).

## 5. Verification Status

The properties described in this article are verified by Stainless through the
source-linked proof functions cited in the relevant sections and in Appendix A.
The repository-wide verification-condition count is intentionally omitted
because it changes as unrelated verified modules are added; the stable claim is
that the Euclid theorem proof and its supporting prime lemmas are
machine-checked in the current source.

## 6. Related Work

The modular-arithmetic and list foundations used here are cited in
[§2](#2-preliminaries). Euclid's classical construction supplies the
mathematical argument; this article contributes its recursive Scala/Stainless
formalization together with the explicitly specified finite divisor search.
For comparison, Mathlib also formalizes the infinitude of primes as
`Nat.exists_infinite_primes` [[8]](#ref8). That theorem has a different
library setting and statement form; it is related work, not a dependency of
this development.

## 7. Conclusion

This article formalizes Euclid's theorem from the same first-principles
foundation used throughout the preceding chapters. The proof follows the
classical primorial-plus-one construction: from a finite list of primes it
builds a number that is congruent to one modulo every prime in the list, then
uses the existence of a smallest divisor to extract a prime factor outside that
list. The contradiction is mathematical before it is computational: no member
of the original list can divide the constructed number, while the constructed
number must still have a prime divisor.

The Stainless development verifies each step that the article relies on:
small-remainder facts, zero-remainder preservation under multiplication,
divisibility of product members, smallest-divisor primality, and the final
non-membership theorem. The result is a source-backed formal proof of the
infinitude of primes, with the supporting finite-prefix corollaries separated
from the theorem spine rather than folded into the main claim.

The theorem spine can be read compactly as the following verified chain.  Let
$P=\text{primorial}(L)$ and $N=P+1$:

```math
\begin{aligned}
\forall p\in L,\quad \text{mod}(N,p)&=1\ne0
&&\text{[Stage 1]} \\
d=\text{findSmallestDivisor}(N,2),\quad d=N
&\Rightarrow \text{isPrime}(N) \\
d<N
&\Rightarrow \text{isPrime}(d)
&&\text{[Stage 2]} \\
v\mid N\ \land\ p\in L
&\Rightarrow p\ne v
&&\text{[Stage 3].}
\end{aligned}
```

Thus either $N$, or its least non-trivial divisor $d$, is a prime outside
$L$:

```math
L\ne[]\ \Rightarrow\ \exists p:\text{isPrime}(p)\land p\notin L.
\quad\blacksquare\ \text{[Q.E.D.]}
```

## 8. Future Work

The most natural continuation is the Fundamental Theorem of Arithmetic, since
Euclid's theorem already establishes the existence side of prime
decomposition. A verified uniqueness proof would require a stronger library of
divisibility and coprimality lemmas, but it would extend the present result in
a direct and structurally compatible way.

Further work could then move from existence to distribution. Dirichlet's
theorem would require arithmetic progressions and substantially richer modular
reasoning, while the Prime Number Theorem would require asymptotic analysis far
beyond the finite arithmetic developed here. Those directions are intentionally
outside the scope of this article, but this proof supplies a verified starting
point for them.

## References

<a name="ref1" id="ref1" href="#ref1">[1]</a>
Hamza, J., Voirol, N., & Kuncak, V. (2019). *System FR: Formalized foundations for the Stainless verifier*. Proceedings of the ACM on Programming Languages, OOPSLA Issue.

<a name="ref2" id="ref2" href="#ref2">[2]</a>
Mata, T. H. (2026). *Division and Modulo from Recursive Normalization*. Available at: [http://ai.viXra.org/abs/2609.0009](http://ai.viXra.org/abs/2609.0009)

<a name="ref3" id="ref3" href="#ref3">[3]</a>
Mata, T. H. (2026). *Using Formal Verification to Prove Properties of Lists Recursively Defined*. Available at: [https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter3/list.md](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter3/list.md)

<a name="ref4" id="ref4" href="#ref4">[4]</a>
Mata, T. H. (2026). *Formal Verification of Discrete Integration Properties from First Principles*. Available at: [https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter4/integral.md](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter4/integral.md)

<a name="ref5" id="ref5" href="#ref5">[5]</a>
Mata, T. H. (2026). *Formal Verification of Cyclic Lists*. Available at: [https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter4/cycle.md](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter4/cycle.md)

<a name="ref6" id="ref6" href="#ref6">[6]</a>
Mata, T. H. (2026). *Formal Verification of Cycle Integral Properties from First Principles*. Available at: [https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter4/integral-cycle.md](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter4/integral-cycle.md)

<a name="ref7" id="ref7" href="#ref7">[7]</a>
Euclid. *Elements*, Book IX, Proposition 20. Translation and notes by David E.
Joyce. Available at: [https://aleph0.clarku.edu/~djoyce/java/elements/bookIX/propIX20.html](https://aleph0.clarku.edu/~djoyce/java/elements/bookIX/propIX20.html)

<a name="ref8" id="ref8" href="#ref8">[8]</a>
The Mathlib Community. *Mathlib.Data.Nat.Prime.Infinite*: `Nat.exists_infinite_primes`.
Mathlib documentation. Available at: [https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Prime/Infinite.html](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Prime/Infinite.html)

---

## Appendix A: Verification Source References

### A.1 `primorialPlusOneModAny`

**Source**: [
  PrimeProperties.scala
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter5/prime/properties/PrimeProperties.scala)

Short source excerpt for Stage 1 (Section 3.1):

```scala
def primorialPlusOneModAny(primes: List[Prime]): Boolean = {
  require(primes.nonEmpty)
  decreases(primes.size)
  primorialPlusOneTailLoop(List.empty, primes)
}.holds
```

This lemma establishes that $\text{primorial}(\text{primes}) + 1$ is not divisible by any prime in the list, via the recursive `primorialPlusOneTailLoop` helper and the modular arithmetic lemmas cited in [§3.1](#31-stage-1-primorial-plus-one-modulo-all-primes).

### A.2 `newPrimeFromEuclid`

**Source**: [
  PrimeProperties.scala
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter5/prime/properties/PrimeProperties.scala)

Short source excerpt for Stage 2 (Section 3.2):

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

**Source**: [
  PrimeProperties.scala
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter5/prime/properties/PrimeProperties.scala)

Short source excerpt for the main theorem (Section 3.4):

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

This source proof is the machine-checked form of the main theorem: every
non-empty finite list of primes admits a prime outside the list.

## Appendix B: Verification Log

The latest `just verify` run verifies the described properties without errors.
The full log output is available at [logs/verify.log](https://github.com/thiagomata/prime-numbers/blob/master/logs/verify.log).
