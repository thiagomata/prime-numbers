# Structural Properties and Open Boundaries of 2-Gaps in Sieve Sequences

**Review status:** Draft v2 for mathematical and editorial review
**Author:** Mata, T. H.
Independent Researcher
**Email:** [thiago.mata@email.com](mailto:thiago.mata@email.com)
**GitHub:** [@thiagomata](https://github.com/thiagomata)

---

## Abstract

This article studies how 2-gaps evolve in the finite periodic states of a
Sieve Sequence. The verified sequence construction shows that filtering
preserves a gap when both endpoints survive and merges consecutive old gaps
when intermediate values are removed. Building on that foundation, this
article proves exact mathematical formulas for the global number of cyclic
2-gaps, their distribution across repeated copies, and their survival through
an arbitrary finite batch of new prime filters. It then separates those global
facts from the local square-safe window in which surviving endpoints are
certified prime.

For one transition from prime `p` to the next prime `q`, the article replaces a
coarse count of all multiples of `p` with the exact number of previously
accepted multiples in `[q,q^2)`. Together with the proved isolation of 2-gaps
after filters `2` and `3`, this gives a sharp sufficient local-survival
threshold. For several transitions, it gives an explicit finite
perfect-scenario certificate in terms of a safe-window copy-index interval and
two forbidden residue classes for each new prime.

None of these finite or complete-period results proves that successful
scenarios occur infinitely often. The remaining theorem is a short-window
positivity problem, equivalently a discrepancy or maximum-covered-run bound.
Recent prime-producing sieve research sharpens the analytic version of this
boundary: complete-period CRT information resembles Type I divisibility data,
but a prime-producing lower bound requires sufficiently strong Type II
bilinear cancellation. No such Type II estimate is proved here. The article
therefore presents a stronger structural reduction and a certifying finite
generator, not a proof of the Twin Prime Conjecture.

---

## 1. Scope And Verification Status

A Sieve Sequence stage with prime head `p` stores one period of the integers
accepted by every prime filter smaller than `p`. The gaps between consecutive
accepted values form a finite cyclic list. A gap of value `2` has endpoints
`(x,x+2)`; after the filter `2` is installed, the intermediate value `x+1` is
even and rejected, so accepted endpoints at distance `2` are consecutive.

This article distinguishes four statuses throughout:

- **Stainless verified:** an existing `.holds` function proves the stated
  program-level property under explicit preconditions.
- **Mathematically proved, Stainless pending:** a complete mathematical proof
  is given, but no packaged `.holds` theorem currently proves the same claim.
- **Conditional implication:** the conclusion is proved from an antecedent
  whose occurrence is not proved.
- **Open:** the required existence or distribution theorem is not proved.

The two local copy/merge branches are Stainless verified. The global CRT,
batch, local-capacity, finite-certificate, and scale results are mathematical
results whose Stainless packaging is pending. Infinite short-window positivity
and the required Type II estimate remain open.

The article is organized around properties of the sequence itself:

1. filtering copies or merges old gaps;
2. absence of 2-gaps is stable, while the complete cycle has an exact positive
   2-gap count;
3. repetition gives two exact forbidden copy-index classes per new prime;
4. finite batches have an exact complete-period survivor count;
5. rotation preserves global cyclic multiplicities but not local placement;
6. a square-safe survivor is a genuine twin-prime pair;
7. one transition has an exact accepted-strike threshold;
8. one perfect scenario has a finite certificate;
9. infinitude requires a new short-window distribution theorem.

---

## 2. Stage And Window Notation

Let `p>=5` be the head of a current stage. Every prime smaller than `p` is an
installed filter. Define the old modulus

```math
\begin{aligned}
M_p &= \prod_{r<p} r,
&& [\text{By Definition}]
\end{aligned}
```

where `r` ranges over primes. The accepted set is periodic modulo `M_p`.
Within one period, write the ordered accepted values as

```math
\begin{aligned}
e_0<e_1<\cdots<e_{T-1},
\end{aligned}
```

with cyclic gaps

```math
\begin{aligned}
g_i &= e_{i+1}-e_i,
&& [\text{By Definition}]
\end{aligned}
```

where the final index wraps to the next period.

Let `q` be the next prime after `p`. Before installing filter `p`, the window
relevant to the next stage is

```math
\begin{aligned}
W(p,q)
&=\{x:q\le x\text{ and }x+2<q^2\}.
&& [\text{By Definition}]
\end{aligned}
```

The strict upper endpoint is essential: `q^2` is composite but has no prime
factor smaller than `q`.

For a longer chain ending at a prime `Q`, write

```math
\begin{aligned}
P_Q &= \prod_{r<Q}r,\\
W_Q &= \{x:Q\le x\text{ and }x+2<Q^2\}.
\end{aligned}
```

---

## 3. Filtering Copies Or Merges Old Gaps

Filtering removes accepted values without changing the order of the values
that remain. Consequently, two consecutive survivors were either already
consecutive or had a consecutive block of old accepted values between them.
The first case copies one old gap. The second merges the old gaps spanning the
removed block.

### 3.1 Copied Gap

Suppose `e_i` and `e_{i+1}` both survive. Their new difference is unchanged:

```math
\begin{aligned}
g'_i
&=e_{i+1}-e_i
&& [\text{By Definition}]\\
&=g_i.
&& [\text{Substitution}]\\
&&& [\text{Q.E.D.}]
\end{aligned}
```

The immediate-survivor branch is Stainless verified. The implementation below
shows the exact verified theorem used by the sequence proof.

```scala
def assertFilterPreservesNextGap(
  seq: SpecSieveSequence,
  nextSeq: SpecSieveSequence,
  k: BigInt
): Boolean = {
  require(k >= BigInt(0))
  require(nextSeq.filterValues.nonEmpty)
  require(nextSeq.filterValues.tail == seq.filterValues)
  require(seq.head.value <= nextSeq.head.value)
  require(nextSeq.accepts(seq.apply(k)))
  require(Calc.mod(
    seq.apply(k + BigInt(1)),
    nextSeq.filterValues.head
  ) != BigInt(0))

  val v = seq.apply(k)
  val w = seq.apply(k + BigInt(1))
  val vIdx = nextSeq.indexOfAccepted(v)

  assert(nextSeq(vIdx) == v)
  assert(assertFilterPreservesNextPosition(seq, nextSeq, k))
  assert(nextSeq(vIdx + BigInt(1)) == w)

  nextSeq(vIdx + BigInt(1)) - nextSeq(vIdx) == w - v
}.holds
```

This property is verified in the [
  SpecSieveSeqNextProperties::assertFilterPreservesNextGap
](
  ../../src/main/scala/v1/chapter60/sieve/seq/spec/properties/SpecSieveSeqNextProperties.scala
).

### 3.2 Merged Gap

Suppose `e_i` and `e_j` survive while `e_{i+1},...,e_{j-1}` are removed. The
new gap telescopes across the old adjacent gaps:

```math
\begin{aligned}
g'_{i,j}
&=e_j-e_i
&& [\text{By Definition}]\\
&=\sum_{k=i}^{j-1}(e_{k+1}-e_k)
&& [\text{Telescoping}]\\
&=\sum_{k=i}^{j-1}g_k.
&& [\text{Substitution}]\\
&&& [\text{Q.E.D.}]
\end{aligned}
```

The skipped-successor branch and its telescoping sum are also Stainless
verified inside the next-stage property object.

```scala
private def assertMergeGapEqualsOldGapSum(
  seq: SpecSieveSequence,
  nextSeq: SpecSieveSequence,
  k: BigInt,
  period: BigInt
): Boolean = {
  require(k >= BigInt(0))
  require(period > BigInt(0))
  require(nextSeq.filterValues.nonEmpty)
  require(nextSeq.filterValues.tail == seq.filterValues)
  require(seq.head.value <= nextSeq.head.value)
  require(nextSeq.accepts(seq.apply(k)))
  require(Calc.mod(
    seq.apply(k + BigInt(1)),
    nextSeq.filterValues.head
  ) == BigInt(0))
  require(seq.apply(period) == seq.head.value + seq.tailPrimorial)
  require(Calc.mod(
    seq.head.value + seq.tailPrimorial,
    nextSeq.filterValues.head
  ) != BigInt(0))

  val p = nextSeq.filterValues.head
  val vIdx = nextSeq.indexOfAccepted(seq.apply(k))
  val bound = k + p * period

  assert(assertPeriodBoundIsNonMultiple(seq, nextSeq, k, period))
  val m = findFirstNonMultipleAfter(seq, k, p, bound)
  assert(m >= k)
  assert(assertMergeLandsOnFirstSurvivor(seq, nextSeq, k, period))
  assert(nextSeq(vIdx) == seq.apply(k))
  assert(nextSeq(vIdx + BigInt(1)) == seq.apply(m))
  assert(SpecSieveSeqPeriodProperties.assertSumGapTelescopes(seq, k, m))

  nextSeq(vIdx + BigInt(1)) - nextSeq(vIdx) ==
    SpecSieveSeqPeriodProperties.sumGap(seq, k, m)
}.holds
```

This supporting property is verified in the [
  SpecSieveSeqNextProperties::assertMergeGapEqualsOldGapSum
](
  ../../src/main/scala/v1/chapter60/sieve/seq/spec/properties/SpecSieveSeqNextProperties.scala
).

The copy-or-merge rule is structural. It constrains how gaps change but does
not, by itself, prove that any chosen gap value occurs locally.

---

## 4. Stable Absence And Exact Global Presence

Two complementary properties describe the complete cyclic population of
2-gaps. Copy-or-merge shows that global absence would be permanent. CRT shows
that the canonical complete period never reaches that absent state.

### 4.1 Absence Of 2-Gaps Is Stable

After filter `2` is installed, every accepted value is odd, so every old gap is
positive and even. If no old gap equals `2`, then every old gap is at least
`4`. A copied gap is at least `4`, while a merged gap is a sum of at least two
positive even gaps. Neither branch can produce `2`.

```math
\begin{aligned}
2\notin G_k
&\Longrightarrow
\forall g\in G_k,\ g\ge4
&& [\text{Positive Even Gaps}]\\
&\Longrightarrow
\forall g'\in G_{k+1},\ g'\ge4
&& [\text{Copy Or Merge}]\\
&\Longrightarrow
2\notin G_{k+1}.
&& [\text{Q.E.D.}]
\end{aligned}
```

**Stainless status:** mathematically proved; the complete packaged theorem is
pending. The existing verified copy and merge lemmas supply its main program
dependencies.

```scala
// DRAFT - specification sketch, not compiled or Stainless verified.
def assertTwoGapAbsenceStable(
  oldGaps: List[BigInt],
  nextGaps: List[BigInt]
): Boolean = {
  require(allPositiveEven(oldGaps))
  require(!oldGaps.contains(BigInt(2)))
  require(everyGapIsCopyOrMerge(oldGaps, nextGaps))
  !nextGaps.contains(BigInt(2))
}.holds
```

The complete mathematical proof is recorded in [Absence of 2-Gaps Is
Stable](../../properties/sieve-sequence/absence-of-two-gaps-is-stable.md).

### 4.2 Exact Non-Recursive Global Count

For one complete period modulo `M_p`, a cyclic 2-gap start `x` must make both
`x` and `x+2` coprime to every installed prime. Modulo `2`, exactly one class
is possible. For every odd prime `r<p`, exactly two classes are forbidden:
`0` and `-2`. The remaining choices combine independently by CRT.

```math
\begin{aligned}
G_2(p)
&=1\cdot
\prod_{\substack{3\le r<p\\r\text{ prime}}}
\left(r-2\right)
&& [\text{One Local Count Per Prime}]\\
&=\prod_{\substack{3\le r<p\\r\text{ prime}}}
\left(r-2\right).
&& [\text{By CRT}]\\
&&& [\text{Q.E.D.}]
\end{aligned}
```

Every factor is positive. Therefore every odd stage has at least one cyclic
2-gap in its complete period. This global positivity is exact and
non-recursive.

**Stainless status:** mathematically proved; CRT packaging for this theorem is
pending.

```scala
// DRAFT - specification sketch, not compiled or Stainless verified.
def assertExactGlobalTwoGapCount(p: BigInt): Boolean = {
  require(Prime.isPrime(p))
  require(p >= BigInt(3))
  cyclicTwoGapCount(p) ==
    product(primesInRange(BigInt(3), p).map(r => r - BigInt(2)))
}.holds
```

The full derivation appears in [Exact Global 2-Gap
Count](../../properties/sieve-sequence/exact-global-two-gap-count.md).

### 4.3 Boundary

Global presence does not imply safe-window presence. The complete period grows
primorially, while a square-safe window grows quadratically in its head. The
global theorem rules out complete-cycle extinction; it does not locate any
2-gap in `[p,p^2)`.

---

## 5. Repeated Copies And Exact Batch Survival

Repetition does provide exact distribution information. It does not place
copies arbitrarily. For one old cyclic 2-gap `(a,a+2)` modulo an old period
`M`, its absolute copies are

```math
\begin{aligned}
(x_j,x_j+2)=(a+jM,a+2+jM).
\end{aligned}
```

### 5.1 One New Prime Forbids Two Copy Classes

Let `r>2` be a new prime with `gcd(M,r)=1`. Filter `r` destroys copy `j`
exactly when one endpoint is `0 modulo r`. Since `M` is invertible modulo `r`,
the two conditions have unique copy-index solutions:

```math
\begin{aligned}
a+jM\equiv0\pmod r
&\Longleftrightarrow
j\equiv-aM^{-1}\pmod r,
&& [\text{Multiplicative Inverse}]\\
a+2+jM\equiv0\pmod r
&\Longleftrightarrow
j\equiv-(a+2)M^{-1}\pmod r.
&& [\text{Multiplicative Inverse}]
\end{aligned}
```

The classes are distinct because equality would imply `2=0 modulo r`.
Therefore every complete block of `r` copy indices has exactly two destroyed
copies and `r-2` survivors. In any `N` consecutive indices, each forbidden
class occurs at most `ceil(N/r)` times, giving

```math
\begin{aligned}
D_r(N)
&\le2\left\lceil\frac Nr\right\rceil.
&& [\text{Two Residue Classes}]\\
&&& [\text{Q.E.D.}]
\end{aligned}
```

**Stainless status:** mathematically proved; modular-inverse and finite-slice
packaging is pending.

```scala
// DRAFT - specification sketch, not compiled or Stainless verified.
def assertTwoForbiddenCopyClasses(
  a: BigInt,
  modulus: BigInt,
  filterPrime: BigInt,
  copies: BigInt
): Boolean = {
  require(Prime.isPrime(filterPrime))
  require(filterPrime > BigInt(2))
  require(Calc.mod(modulus, filterPrime) != BigInt(0))
  require(copies >= BigInt(0))
  destroyedCopies(a, modulus, filterPrime, copies) <=
    BigInt(2) * ceilDiv(copies, filterPrime)
}.holds
```

The full proof appears in [Exact Filter Frequency Across Repeated
Copies](../../properties/sieve-sequence/copy-index-filter-frequency.md).

### 5.2 An Arbitrary Finite Batch

Let `R` be a finite set of distinct new odd primes, none dividing `M`, and set

```math
\begin{aligned}
B=\prod_{r\in\mathcal R}r.
\end{aligned}
```

Each prime leaves `r-2` allowed copy-index classes. CRT combines one allowed
choice for each prime into one class modulo `B`. Thus the number of surviving
classes in one complete batch period is

```math
\begin{aligned}
S(\mathcal R)
&=\prod_{r\in\mathcal R}(r-2).
&& [\text{By CRT}]\\
&&& [\text{Q.E.D.}]
\end{aligned}
```

If the old complete period contains `G` cyclic 2-gaps, the complete batched
period contains exactly

```math
\begin{aligned}
G_{\mathrm{after}}
&=G\prod_{r\in\mathcal R}(r-2).
&& [\text{Sum Over Old 2-Gaps}]
\end{aligned}
```

This one-shot count automatically handles overlaps and is independent of the
order assigned to the filters.

**Stainless status:** mathematically proved; finite-set CRT product packaging
is pending.

```scala
// DRAFT - specification sketch, not compiled or Stainless verified.
def assertExactBatchedTwoGapSurvival(
  oldCount: BigInt,
  filters: List[BigInt]
): Boolean = {
  require(oldCount >= BigInt(0))
  require(distinctOddPrimes(filters))
  batchedSurvivorCount(oldCount, filters) ==
    oldCount * product(filters.map(r => r - BigInt(2)))
}.holds
```

The full proof appears in [Exact Batched 2-Gap
Survival](../../properties/sieve-sequence/exact-batched-two-gap-survival.md).

### 5.3 What The Batch Does Not Prove

The combined modulus `B` can be much longer than the eligible local run of
copy indices. Exact proportional survival over a complete `B`-block does not
force an allowed index in every shorter interval. Distinct primes can cover
different positions of one finite run even though every prime leaves most
indices untouched.

The unresolved local question is therefore not whether the copies have a
distribution. They do. It is how long a consecutive run can be covered by the
union of all known forbidden classes.

---

## 6. Rotation Preserves Global Multiplicity, Not Placement

Rotation chooses a different origin for the same finite cyclic gap list. For

```math
\begin{aligned}
G=(g_0,g_1,\ldots,g_{T-1}),
\end{aligned}
```

rotation by `j` is a permutation of the index set. Therefore, for every gap
value `d`, its cyclic multiplicity is unchanged:

```math
\begin{aligned}
\#\{i:g_i=d\}
&=\#\{i:\operatorname{rot}_j(G)_i=d\}
&& [\text{Rotation Is A Bijection}]\\
&&& [\text{Q.E.D.}]
\end{aligned}
```

Rotation can change which gap follows the displayed head and whether a cyclic
gap crosses the end of one linear rendering. It cannot destroy, merge, or
create a cyclic 2-gap.

**Stainless status:** the repository verifies several rotation/value and
rotation/positivity properties, but the packaged multiplicity theorem is
pending.

```scala
// DRAFT - specification sketch, not compiled or Stainless verified.
def assertRotationPreservesGapMultiplicity(
  gaps: List[BigInt],
  offset: BigInt,
  value: BigInt
): Boolean = {
  require(!gaps.isEmpty)
  countValue(SieveUtils.rotateAt(gaps, offset), value) ==
    countValue(gaps, value)
}.holds
```

The mathematical proof and local boundary are recorded in [Rotation Preserves
Cyclic Gap Counts](../../properties/sieve-sequence/rotation-preserves-cyclic-gap-counts.md).

An absolute window such as `[q,q^2)` is tied to numerical coordinates, not
only cyclic indices. Rotation is therefore not a random reshuffle and does not
imply that every short absolute window receives its proportional share.

---

## 7. Square-Safe 2-Gaps Are Twin Primes

Let `q` be prime and suppose `n` satisfies

```math
\begin{aligned}
q\le n<q^2,
\qquad
\gcd(n,P_q)=1.
\end{aligned}
```

If `n` were composite, it would have a prime divisor `r<=sqrt(n)<q`. That
prime would divide `P_q`, contradicting the coprimality condition. Hence `n`
is prime.

```math
\begin{aligned}
n\text{ composite}
&\Longrightarrow
\exists r\text{ prime}:r\mid n\land r\le\sqrt n
&& [\text{Small Prime Divisor}]\\
&\Longrightarrow
r<q
&& [n<q^2]\\
&\Longrightarrow
r\mid P_q
&& [\text{By Definition}]\\
&\Longrightarrow
\gcd(n,P_q)>1,
&& [\text{Contradiction}]\\
\therefore\quad n&\text{ is prime}.
&& [\text{Q.E.D.}]
\end{aligned}
```

Applying the argument to both endpoints proves

```math
\begin{aligned}
q\le x,quad x+2<q^2,quad
\gcd(x(x+2),P_q)=1
\Longrightarrow
x\text{ and }x+2\text{ are prime}.
\end{aligned}
```

**Stainless status:** the sequence development verifies the analogous
first-successor primality theorem under a square-bound precondition. The
generic two-endpoint theorem is mathematically proved here and its packaged
Stainless verification is pending.

```scala
// DRAFT - generic two-endpoint theorem, not yet Stainless verified.
def assertSafeTwoGapIsTwinPrime(
  q: BigInt,
  x: BigInt,
  smallerPrimes: List[BigInt]
): Boolean = {
  require(Prime.isPrime(q))
  require(q <= x)
  require(x + BigInt(2) < q * q)
  require(allPrimesBelow(q, smallerPrimes))
  require(CoprimeUtils.isCoprime(x, smallerPrimes))
  require(CoprimeUtils.isCoprime(x + BigInt(2), smallerPrimes))
  Prime.isPrime(x) && Prime.isPrime(x + BigInt(2))
}.holds
```

The verified one-successor analogue is in [
  SpecSieveSeqHeadIsPrime::assertApplyOneIsPrimeIfBelowHeadSq
](
  ../../src/main/scala/v1/chapter60/sieve/seq/spec/properties/SpecSieveSeqHeadIsPrime.scala
). The generic mathematical proof appears in [Safe-Window 2-Gaps Certify Twin
Primes](../../properties/sieve-sequence/safe-window-two-gaps-certify-twin-primes.md).

This theorem certifies a survivor. It does not prove that the safe window
contains one.

---

## 8. The Sharp One-Transition Capacity Theorem

The old article-level capacity argument counted all multiples of the new
filter prime. Most of those multiples were already removed by smaller filters.
The exact transition theorem counts only previously accepted multiples and
uses the next stage's actual safe window.

Let `p>=5` be the new filter and `q` the next prime after `p`. Define

```math
\begin{aligned}
K&=\left\lfloor\frac{q^2-1}{p}\right\rfloor,\\
A(p,q)&=\pi(K)-\pi(p-1).
\end{aligned}
```

### 8.1 Exact Accepted Strikes

A multiple of `p` in `[q,q^2)` has the form `pk`. It was accepted by every old
filter exactly when `k` has no prime divisor below `p`. Bertrand's postulate
gives `q<2p`, so

```math
\begin{aligned}
K
&<\frac{q^2}{p}
<4p
\le p^2.
\end{aligned}
```

If such a `k<p^2` were composite, it would have a prime divisor below `p`.
Therefore the accepted multipliers are exactly the primes `k` with `p<=k<=K`,
and their number is `A(p,q)`.

```math
\begin{aligned}
\#\{\text{accepted multiples of }p\text{ in }[q,q^2)\}
&=\#\{k:p\le k\le K,\ k\text{ prime}\}
&& [\text{Accepted Multiplier Characterization}]\\
&=\pi(K)-\pi(p-1)
&& [\text{By Definition Of }\pi]\\
&=A(p,q).
&& [\text{Q.E.D.}]
\end{aligned}
```

### 8.2 One Strike Destroys At Most One 2-Gap

After filters `2` and `3` are installed, every 2-gap start is `5 modulo 6`.
Two 2-gaps cannot share an endpoint: among `x,x+2,x+4`, one value is divisible
by `3`. Thus one removed accepted value is an endpoint of at most one 2-gap.

```math
\begin{aligned}
(x,x+2)\text{ and }(x+2,x+4)\text{ both accepted}
&\Longrightarrow
x,x+2,x+4\not\equiv0\pmod3
&& [\text{Acceptance}]\\
&\Longrightarrow
\bot,
&& [\text{One Of Three Is }0\pmod3]\\
\therefore\quad
\text{one removed value destroys at most one 2-gap}.
&& [\text{Q.E.D.}]
\end{aligned}
```

### 8.3 Sharp Sufficient Threshold

Let `G_local(p,q)` be the number of pre-filter 2-gaps with both endpoints in
`[q,q^2)`. Since filter `p` removes exactly `A(p,q)` accepted values and each
removal destroys at most one 2-gap,

```math
\begin{aligned}
G_{\mathrm{surviving}}(p,q)
&\ge G_{\mathrm{local}}(p,q)-A(p,q)
&& [\text{Destruction Capacity}]\\
G_{\mathrm{local}}(p,q)>A(p,q)
&\Longrightarrow
G_{\mathrm{surviving}}(p,q)>0.
&& [\text{Integer Positivity}]\\
&&& [\text{Q.E.D.}]
\end{aligned}
```

This is stronger and more accurately staged than the raw `p-1` bullet bound.
It is still conditional: it does not prove the required local abundance.

**Stainless status:** all three mathematical claims in this section are proved;
their packaged `.holds` theorems are pending.

```scala
// DRAFT - specification sketch, not compiled or Stainless verified.
def assertSharpLocalTwoGapSurvival(
  p: BigInt,
  q: BigInt,
  localTwoGaps: BigInt
): Boolean = {
  require(p >= BigInt(5))
  require(Prime.isPrime(p))
  require(nextPrime(p) == q)
  require(localTwoGaps > acceptedStrikeCount(p, q))
  survivingLocalTwoGaps(p, q) > BigInt(0)
}.holds
```

Detailed proofs appear in [Isolation of 2-Gaps After Filtering by
3](../../properties/sieve-sequence/two-gap-isolation-after-filter-three.md),
[Exact Accepted Filter Strikes](../../properties/sieve-sequence/exact-accepted-local-filter-strikes.md),
and [Sharp Local 2-Gap Survival
Threshold](../../properties/sieve-sequence/sharp-local-two-gap-survival-threshold.md).

---

## 9. Finite Perfect Scenarios

An infinite proof does not need every stage to satisfy the sharp threshold. It
is enough that rare finite scenarios occur at unbounded coordinates. One old
2-gap need only survive the finite set of filters required to reach one
square-safe certification stage.

Choose an initial prime `p`, its modulus `M_p`, and a cyclic seed `(a,a+2)`.
For a later prime `q>p`, the copy indices whose endpoints lie in the safe
window are

```math
\begin{aligned}
I(a,M_p,q)=
\left[
\left\lceil\frac{q-a}{M_p}\right\rceil,
\left\lfloor\frac{q^2-3-a}{M_p}\right\rfloor
\right]\cap\mathbb Z.
\end{aligned}
```

Let the transition batch be

```math
\begin{aligned}
\mathcal R(p,q)=\{r:r\text{ prime and }p\le r<q\}.
\end{aligned}
```

For each `r` in the batch, copy index `j` must avoid

```math
\begin{aligned}
j&\equiv-aM_p^{-1}\pmod r,\\
j&\equiv-(a+2)M_p^{-1}\pmod r.
\end{aligned}
```

Define the batch-allowed set `A(a,M_p,p,q)` by those avoidance conditions.
The complete finite certificate is

```math
\begin{aligned}
I(a,M_p,q)\cap\mathcal A(a,M_p,p,q)
&\ne\varnothing.
&& [\text{Perfect-Scenario Certificate}]
\end{aligned}
```

If `j` lies in this intersection, `x=a+jM_p` and `x+2` survive every prime
filter below `q` and lie strictly below `q^2`. Section 7 certifies both as
prime. When the sieve sequence later reaches head `x`, the next accepted value
is `x+2`, since `x+1` is even. Thus the head gap is `2`.

```math
\begin{aligned}
j\in I\cap\mathcal A
&\Longrightarrow
\gcd(x(x+2),P_q)=1
&& [\text{Batch Compatibility}]\\
&\Longrightarrow
x,x+2\text{ are prime}
&& [\text{Safe-Window Certification}]\\
&\Longrightarrow
\text{the stage with head }x\text{ begins with gap }2.
&& [\text{Consecutive Prime Heads}]\\
&&& [\text{Q.E.D.}]
\end{aligned}
```

**Stainless status:** mathematically proved conditional certificate; packaged
verification is pending.

```scala
// DRAFT - specification sketch, not compiled or Stainless verified.
def assertPerfectScenarioReachesHeadTwoGap(
  p: BigInt,
  q: BigInt,
  modulus: BigInt,
  seed: BigInt,
  copyIndex: BigInt
): Boolean = {
  require(validSeedTwoGap(p, modulus, seed))
  require(copyLiesInSafeWindow(q, modulus, seed, copyIndex))
  require(copyAvoidsBatch(p, q, modulus, seed, copyIndex))
  eventualHeadGap(modulus, seed, copyIndex) == BigInt(2)
}.holds
```

The complete certificate and worked example appear in [Reverse-Engineered
Initial Scenario](../../properties/sieve-sequence/reverse-engineered-eventual-head-scenario.md).

One certificate proves one twin-prime pair. Infinitely many pairs require an
unbounded family of certificates. Success at every head, positive density, and
survival of one immortal seed are all stronger than necessary.

---

## 10. The Fixed-Seed Scale Conflict

One proposed restriction keeps the whole consecutive prime chain below the
initial square horizon:

```math
\begin{aligned}
q<p^2.
\end{aligned}
```

This limits the numerical length of the chain, but it conflicts with using
many repeated copies of one fixed seed inside the final safe window. By the
prime number theorem in Chebyshev-theta form,

```math
\begin{aligned}
\log M_p
&=\sum_{r<p}\log r
\sim p.
\end{aligned}
```

Hence `M_p=exp((1+o(1))p)`. Meanwhile `q<p^2` implies `q^2<p^4`. Therefore

```math
\begin{aligned}
\frac{M_p}{q^2}
&>\frac{\exp((1+o(1))p)}{p^4}
\longrightarrow\infty,
&& [p\longrightarrow\infty]\\
\therefore\quad M_p&>q^2
&& [\text{For All Sufficiently Large }p].
\end{aligned}
```

For all sufficiently large scenarios satisfying `q<p^2`, one fixed residue
class modulo `M_p` occurs at most once in `[q,q^2)`. Its exact global
repetition frequency therefore cannot force local placement.

This is not a disproof of finite perfect scenarios. It says that a proof cannot
simultaneously rely on a short chain under `p^2` and on many local copies of
one fixed seed. A viable average must instead range over seed residues, use a
much earlier seed and a longer filter chain, average over final heads, or find
another bilinear variable.

**Stainless status:** asymptotic mathematical consequence of the prime number
theorem; no Stainless theorem is claimed.

```scala
// RESEARCH SPECIFICATION ONLY.
// A finite Stainless theorem would need an explicit effective threshold for p.
def fixedSeedEventuallyHasAtMostOneSafeCopy(
  p: BigInt,
  q: BigInt
): Boolean = {
  require(Prime.isPrime(p))
  require(Prime.isPrime(q))
  require(q < p * p)
  require(p >= explicitEffectiveThreshold)
  safeWindowLength(q) < primorialBefore(p)
}.holds
```

The derivation and its implications are discussed in [Recent Prime-Producing
Sieves: A Deep-Dive](../../properties/sieve-sequence/research/recent-prime-producing-sieves-deep-dive.md).

---

## 11. The Exact Open Boundary

The proved complete-period density does not become a local lower bound without
an error estimate. Define the fully filtered starts in a finite window `W` by

```math
\begin{aligned}
\mathcal S_Q(W)
=\{x\in W:\gcd(x(x+2),P_Q)=1\}.
\end{aligned}
```

CRT gives the complete-period density

```math
\begin{aligned}
\delta_Q
=\frac12
\prod_{\substack{3\le r<Q\\r\text{ prime}}}
\left(1-\frac2r\right).
\end{aligned}
```

For the safe window `W_Q`, write the exact identity

```math
\begin{aligned}
|\mathcal S_Q(W_Q)|
=|W_Q|\delta_Q+E_Q,
\end{aligned}
```

where `E_Q` is the short-window discrepancy. Positivity would follow from

```math
\begin{aligned}
E_Q>-|W_Q|\delta_Q.
\end{aligned}
```

No such general bound is proved here. The main term is not itself a lower
bound.

### 11.1 Equivalent Covered-Run Form

For one seed `(a,a+2)`, every future prime supplies two known forbidden
copy-index classes. Let `C` be the union of those classes over the batch. The
local question is equivalent to asking how long a consecutive interval can be
contained in `C`.

```math
\begin{aligned}
\operatorname{coverRun}(C)
=\max\{|J|:J\text{ is consecutive and }J\subseteq C\}.
\end{aligned}
```

If an eligible copy-index interval is longer than this maximum covered run, it
contains a survivor. The missing theorem is a bound strong enough for an
unbounded family of eligible scenarios.

### 11.2 What Does Not Follow

The following implications are invalid without additional hypotheses:

```math
\begin{aligned}
\text{positive complete-period density}
&\not\Longrightarrow
\text{positive safe-window count},\\
\text{rotation}
&\not\Longrightarrow
\text{random local placement},\\
\text{two forbidden classes per prime}
&\not\Longrightarrow
\text{no finite run is fully covered},\\
\text{many global 2-gaps}
&\not\Longrightarrow
\text{one fixed seed has many local copies}.
\end{aligned}
```

These are theorem boundaries, not a history of failed experiments.

The full discrepancy formulation appears in [Batched Short-Window Discrepancy
Boundary](../../properties/sieve-sequence/batched-short-window-discrepancy-boundary.md).

### 11.3 The Extremal Global-Count Threshold

A global count can force a local survivor, but only when it is so large that
all 2-gaps cannot fit outside the safe window. After filters `2` and `3`, every
2-gap start is `5 modulo 6`. One complete old period therefore has `M_p/6`
possible start slots.

Let

```math
\begin{aligned}
C(q)
=\left\lfloor\frac{q^2-8}{6}\right\rfloor
-\left\lfloor\frac{q-6}{6}\right\rfloor,
\end{aligned}
```

the number of eligible `5 modulo 6` starts in the next safe window. Assuming
the window maps injectively modulo `M_p`, its complement has only
`M_p/6-C(q)` possible 2-gap slots. Therefore

```math
\begin{aligned}
G_{\mathrm{local}}(p,q)
&\ge
G_{\mathrm{global}}(p)-\left(\frac{M_p}{6}-C(q)\right)
&& [\text{Outside-Slot Capacity}]\\
G_{\mathrm{global}}(p)
&>\frac{M_p}{6}-C(q)+A(p,q)
&& [\text{Sufficient Global Threshold}]\\
&\Longrightarrow
G_{\mathrm{local}}(p,q)>A(p,q)
&& [\text{Substitution}]\\
&\Longrightarrow
G_{\mathrm{surviving}}(p,q)>0.
&& [\text{Sharp Local Threshold}]\\
&&& [\text{Q.E.D.}]
\end{aligned}
```

This is a rigorous count-only bridge, but it is generally impractical. The
known exact global count has order roughly `M_p/log^2(p)`, while the outside
capacity is close to `M_p/6` once the primorial dominates the window. The
theorem therefore explains quantitatively why global abundance needs
additional positional information.

**Stainless status:** mathematically proved sufficient condition; packaged
verification is pending.

```scala
// DRAFT - specification sketch, not compiled or Stainless verified.
def assertGlobalCountForcesLocalSurvival(
  p: BigInt,
  q: BigInt,
  globalTwoGaps: BigInt
): Boolean = {
  require(nextPrime(p) == q)
  require(safeWindowInjectsModuloOldPeriod(p, q))
  require(globalTwoGaps >
    outsideTwoGapSlotCapacity(p, q) + acceptedStrikeCount(p, q))
  survivingLocalTwoGaps(p, q) > BigInt(0)
}.holds
```

The exact theorem appears in [Global Count Threshold That Forces Local
Survival](../../properties/sieve-sequence/global-count-forcing-local-survival.md).

---

## 12. Recent Prime-Producing Sieve Research

Ford and Maynard study nonnegative sequences whose difference from a comparison
model satisfies Type I and Type II estimates. Type I controls divisibility
averages over many factor scales. Type II controls bilinear sums against
arbitrary bounded coefficient sequences. Their framework proves that a
substantial Type II range is genuinely necessary to guarantee a nontrivial
prime lower bound; very strong Type I information alone can still be
consistent with a sequence containing no primes.

The Sieve Sequence's exact residue and CRT formulas are algebraic input for a
possible Type I analysis. They are not yet a Ford-Maynard Type I theorem over
the required short intervals, because the accumulated discrepancy norm has
not been bounded. No arbitrary-coefficient Type II estimate is currently
proved for the perfect-scenario weights.

A natural endpoint weight at scale `X=q^2` is

```math
\begin{aligned}
A_q(n)
=\mathbf1_{\gcd(n(n+2),P_q)=1}.
\end{aligned}
```

On primes `n` strictly below `q^2-2`, positivity of the weighted prime sum

```math
\begin{aligned}
\sum_{\substack{n\text{ prime}\\q^2/2<n\le q^2-3}}A_q(n)>0
\end{aligned}
```

would produce a twin-prime pair. Establishing the necessary Type I/II
hypotheses for this or a non-circular comparison weight is itself the hard
problem.

Green and Sawhney's accepted work on prime values of `p^2+nq^2` demonstrates a
modern successful Type II strategy using extra algebraic variables, number-
field factorization, and Gowers-norm machinery. Those structural inputs do not
automatically exist for the affine pair `(x,x+2)`. Their result is therefore a
methodological guide, not a theorem that transfers to the present problem.

The actionable analytic target is:

```text
Define a non-circular averaged perfect-scenario weight, prove a genuine
short-window Type I estimate and a sufficiently long arbitrary-coefficient
Type II estimate, then test those proved ranges against the Ford-Maynard
lower-bound criteria.
```

The detailed research mapping appears in [Recent Prime-Producing Sieves: A
Deep-Dive](../../properties/sieve-sequence/research/recent-prime-producing-sieves-deep-dive.md).

---

## 13. Suggested Experiment: A Certifying Finite Generator

The open infinitude theorem does not prevent finite generation. For a chosen
prime `q`, initialize all starts

```math
\begin{aligned}
J_q=\{q,q+1,\ldots,q^2-3\}.
\end{aligned}
```

For every prime `r<q`, remove starts in the two classes

```math
\begin{aligned}
n\equiv0\pmod r,
\qquad
n\equiv-2\pmod r.
\end{aligned}
```

Every returned `n` satisfies the square-safe certificate and is therefore a
genuine twin-prime start. For any chosen earlier stage `p`, its ancestry can be
reconstructed using

```math
\begin{aligned}
a&=n\bmod M_p,\\
j&=\frac{n-a}{M_p}.
\end{aligned}
```

The generator has a precise contract:

- every fixed finite-window run terminates;
- every returned result has a complete modular certificate;
- exhaustive filtering returns all scenarios in that chosen window;
- one run may return no scenario;
- searching forever for the next scenario is not proved to terminate;
- continued empirical success does not prove infinitude.

The generator should compare direct endpoint filtering with sieve-sequence
ancestry filtering and record local discrepancy, longest covered runs, seed
residue distribution, and candidate Type II correlation statistics.

**Stainless status:** proposed implementation and soundness theorem; not yet
implemented or verified.

```scala
// DRAFT - proposed generator contract, not implemented or verified.
def generateCertifiedScenarios(q: BigInt): List[BigInt] = {
  require(Prime.isPrime(q))
  val starts = intervalInclusive(q, q * q - BigInt(3))
  filterTwoGapStarts(starts, primesBelow(q))
}.ensuring(result => result.forall(n =>
  q <= n &&
  n + BigInt(2) < q * q &&
  Prime.isPrime(n) &&
  Prime.isPrime(n + BigInt(2))
))
```

The complete experimental contract is specified in [A Finite Perfect-Scenario
Generator](../../properties/sieve-sequence/suggested-next-step-finite-perfect-scenario-generator.md).

---

## 14. Claim Boundary

This article establishes or records the following results:

1. The local copied-gap and merged-gap branches are Stainless verified under
   their explicit next-sequence preconditions.
2. Absence of 2-gaps is mathematically stable under later post-2 filtering.
3. The complete cyclic 2-gap count is the exact non-recursive product
   `product(r-2)` over installed odd primes.
4. One new odd prime forbids exactly two copy-index classes; an arbitrary
   finite batch has an exact complete-period CRT survivor product.
5. Rotation preserves global cyclic gap multiplicity but supplies no local
   equidistribution theorem.
6. A surviving 2-gap strictly inside `[q,q^2)` after all filters below `q` is a
   genuine twin-prime pair.
7. One transition has the sharp sufficient threshold
   `G_local(p,q)>A(p,q)`, where `A(p,q)` is the exact accepted strike count.
8. One finite perfect scenario is certified by a nonempty intersection between
   an eligible copy-index interval and a batch-allowed residue set.
9. Under the optional restriction `q<p^2`, one fixed seed eventually has at
   most one local copy, so any averaging proof must range over another
   variable.

This article does **not** prove:

- that every safe window contains a 2-gap;
- that the sharp local threshold holds eventually;
- that finite perfect scenarios occur beyond every bound;
- that a complete-period density controls the short-window discrepancy;
- that the candidate weights satisfy Ford-Maynard Type I or Type II estimates;
- that infinitely many twin primes exist.

---

## 15. Conclusion

The Sieve Sequence gives more than an informal statement that 2-gaps are
"distributed." It gives an exact finite structure. Every new prime forbids two
known copy-index classes. Every complete finite batch has an exact CRT survivor
count. Rotation preserves the global cyclic population. The square-safe window
turns one surviving pair into a genuine twin-prime certificate. For one
transition, the exact accepted-strike count gives a sharp sufficient survival
threshold.

The remaining problem is local and positional. A complete batch period may be
far larger than the safe window, and a fixed old seed may have at most one
local copy. The exact missing theorem is therefore not another global count.
It is a lower bound for the sifted pair count in a specified short window, a
bound on the longest run covered by the batch-forbidden copy classes, or an
analytic Type I/Type II theorem strong enough to force prime positivity.

Rare finite perfect scenarios are sufficient. A certifying generator can find
and study them now, but proving that it succeeds at unbounded coordinates
remains equivalent to the unresolved infinitude problem. This is the honest
boundary of the current results and the point from which further mathematical
or computational research should begin.

---

## References

1. Mata, T. H. (2026). [Formal Verification of the Sieve
   Sequence](sieve-sequence.md).
2. Mata, T. H. (2026). [Sieve-Sequence Mathematical Property
   Catalog](../../properties/sieve-sequence/README.md).
3. Kevin Ford and James Maynard (2024). [On the theory of prime producing
   sieves](https://arxiv.org/abs/2407.14368).
4. Ben Green and Mehtaab Sawhney (2024, revised 2026). [Primes of the form
   p^2+nq^2](https://arxiv.org/abs/2410.04189). Accepted for publication in
   *Acta Mathematica*.
5. Hardy, G. H. and Wright, E. M. (1979). *An Introduction to the Theory of
   Numbers*, 5th edition. Oxford University Press.

---

## Appendix A. Verification Map

The following existing Stainless surfaces support this article:

- [SpecSieveSeqNextProperties::assertFilterPreservesNextGap](../../src/main/scala/v1/chapter60/sieve/seq/spec/properties/SpecSieveSeqNextProperties.scala)
  verifies the copied-gap branch.
- [SpecSieveSeqNextProperties::assertConsecutiveAcceptedByNextPreservesGap](../../src/main/scala/v1/chapter60/sieve/seq/spec/properties/SpecSieveSeqNextProperties.scala)
  verifies copying between current and actual next-stage heads.
- [SpecSieveSeqNextProperties::assertMergeGapEqualsOldGapSum](../../src/main/scala/v1/chapter60/sieve/seq/spec/properties/SpecSieveSeqNextProperties.scala)
  verifies the skipped-successor merge telescope as a private supporting
  theorem.
- [SpecSieveSeqHeadIsPrime::assertApplyOneIsPrimeIfBelowHeadSq](../../src/main/scala/v1/chapter60/sieve/seq/spec/properties/SpecSieveSeqHeadIsPrime.scala)
  verifies the first-successor square-bound primality analogue.
- [SpecSieveSeqHeadIsPrime::assertApplyOneEqualsNextPrime](../../src/main/scala/v1/chapter60/sieve/seq/spec/properties/SpecSieveSeqHeadIsPrime.scala)
  verifies next-head equality under the stated square-bound precondition.

All other Scala blocks in this article are explicitly marked draft
specification sketches. They have not been compiled or run through Stainless.
