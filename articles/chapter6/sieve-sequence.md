# Formal Verification of Sieve Sequence Stages and Their Transitions

**Author:** Mata, T. H.
Independent Researcher
**Email:** [thiago.henrique.mata@gmail.com](mailto:thiago.henrique.mata@gmail.com)
**GitHub:** [@thiagomata](https://github.com/thiagomata)  
**License:** [CC BY 4.0](../LICENSE)

## Abstract

<div align="justify">
<p style="text-align: justify">

This article defines a sieve sequence stage as the increasing sequence of
integers accepted by a finite prefix of the prime filters. The accepted pattern
is periodic modulo the product of those filters, so one finite list of positive
gaps reconstructs the entire infinite stage. We formally verify the stage's
strict increase, completeness, block-period shift, gap-cycle reconstruction,
and exact transition count. If the current head is $h$, the current period has
$T$ accepted values, and the current modulus is $M$, then the expanded
window of length $hM$ contains $hT$ old survivors; exactly $T$ are
multiples of $h$, leaving $T(h-1)$ survivors. We also verify the local
copy-or-merge rule for the next gaps. For each real linear 2-gap, the two
endpoint strikes occur at distinct lift offsets, so exactly two of its $h$
lifts are destroyed and exactly $h-2$ keep both endpoints. Under explicit
structural and period preconditions, the resulting gap prefix agrees with the
next linear specification.

The formal result has two explicit boundaries. First, next-head primality is
conditional on the square bound supplied mathematically by Bertrand's postulate.
Second, the article proves the semantic transition between stages, while the
direct construction of the next cycle from a repeated and filtered current cycle
is a separate open composition problem. Accordingly, the article establishes a
formally verified finite-stage sieve specification and transition semantics, not
a new prime-sieving algorithm or a theorem about the persistence of any
particular prime gap in a prescribed short window.

</p>
</div>

## 1. Introduction

The sieve of Eratosthenes repeatedly removes multiples of known primes
[[5]](#ref5). A standard implementation stores a bounded array and crosses out
composites. The Sieve Sequence studied here exposes a different mathematical
view: after a finite set of prime filters has been installed, the survivors
form an infinite periodic sequence. A finite cycle of adjacent gaps therefore
represents the whole stage.

This representation belongs to the broad family of cyclic or wheel-based sieve
descriptions. Pritchard's survey places wheel sieves among systematic families
of prime-number sieves [[6]](#ref6). The present contribution is not the wheel
idea itself. It is the explicit decomposition of the stage and transition into
contracts that can be checked by Stainless, a verifier for Scala programs
[[7]](#ref7), against a first-principles arithmetic and list library.

The proof is organized into these property groups:

- stage semantics and complete increasing enumeration - Section 3;
- canonical period and finite gap-cycle reconstruction - Section 4;
- repeated-cycle invariance, exact filtering, and copy-or-merge dynamics - Section 5;
- next-head primality and next-stage agreement - Section 6;
- conditional assumptions and open composition problems - Section 7.

The mathematical object is separate from its proof namespaces. `SpecSieveSequence`
is the data model and linear semantic specification. Independent property
objects establish the period, survivor count, transition, next-stage assembly,
and head-primality theorems.

## 2. Preliminaries

This section fixes the notation, relates the linear and cyclic views, and states
how to interpret a Stainless-verified contract.

- Section 2.1 defines one stage and its acceptance predicate.
- Section 2.2 defines the finite period and gap cycle.
- Section 2.3 maps the proof architecture.
- Section 2.4 explains the verification boundary.

### 2.1 Stage Definition

Let a stage $S$ be determined by a current head prime $h$ and the complete
list $\overline{P}$ of primes smaller than $h$. The list is stored in
descending order, but its order does not affect divisibility. Define

```math
\begin{aligned}
M &= \prod_{q \in \overline{P}} q,
  &&\text{[Tail primorial]} \\
A_S(v) &\Longleftrightarrow
  v \ge h \land
  \forall q \in \overline{P},\ v \not\equiv 0 \pmod q.
  &&\text{[Acceptance]}
\end{aligned}
```

The linear sequence $L=(\ell_k)_{k\ge 0}$ starts at $h$ and repeatedly
selects the least later accepted value:

```math
\begin{aligned}
\ell_0 &= h, \\
\ell_{k+1}
  &= \min\{v\gt\ell_k : A_S(v)\}.
\end{aligned}
```

A stage does **not** claim that every $\ell_k$ is prime. For example, the
stage with $h=5$ and filters $3,2$ emits
$5,7,11,13,17,19,23,25,\ldots$. The value $25$ survives because the
current head $5$ has not yet been added to the filter list. Prime generation
comes from the chain of stage heads, not from treating all values in one stage
as prime.

The figure below makes this concrete for six early stages: each panel is a
survivor's own leading $100$ values reshaped into a $10\times10$ grid, colored
green where the survivor is actually prime and red where the current filter
set accepted it anyway even though it is composite (stage $0$, with no filter
installed yet, marks every composite integer this way). Every red cell is
exactly the phenomenon named above — a value $A_S$ currently accepts that a
later stage head will remove.

![Six small hit/miss matrices, one per early stage: green cells are survivors that are actually prime, red cells are survivors the current filter set accepts despite being composite](https://raw.githubusercontent.com/thiagomata/prime-numbers/master/presentations/sieve-sequence-visualization/figures/out/hit-miss-matrices.svg)

### 2.2 Period and Gap Cycle

Because every $q\in\overline{P}$ divides $M$, acceptance is unchanged by
adding $M$:

```math
\begin{aligned}
A_S(v+M)
&\Longleftrightarrow
\forall q\in\overline{P},\
(v+M)\not\equiv0\pmod q \\
&\Longleftrightarrow
\forall q\in\overline{P},\
v\not\equiv0\pmod q \\
&\Longleftrightarrow A_S(v).
\end{aligned}
```

Let $T\gt0$ be the unique index satisfying
$\ell_T=h+M$. Define one complete gap list

```math
\begin{aligned}
G &= (g_0,\ldots,g_{T-1}), \\
g_i &= \ell_{i+1}-\ell_i.
\end{aligned}
```

Every gap is positive and the gaps telescope across the period:

```math
\begin{aligned}
g_i &\gt 0, \\
\sum_{i=0}^{T-1} g_i
  &= \ell_T-\ell_0 \\
  &= (h+M)-h \\
  &= M.
\end{aligned}
```

The cycle integral repeatedly adds the entries of $G$. With the indexing used
by the Scala implementation, its position $k-1$ reconstructs $\ell_k$ for
every $k\gt0$.

### 2.3 Source Evidence Map

The proofs below use `SpecSieveSequence` as the linear mathematical model of a
stage. Separate property objects verify the period, gap-cycle reconstruction,
survivor count, copy-or-merge transition, next-stage agreement, and head
primality facts. The model does not depend on those property objects; they are
source-backed evidence for the mathematical properties stated in the article.

The construction builds on the verified modulo [[1]](#ref1), list [[2]](#ref2),
cycle [[3]](#ref3), and cycle-integral [[4]](#ref4) foundations.

### 2.4 Verification Evidence

Each verified property cited below is tied to a concrete Scala contract in the
repository. The preconditions in those contracts are part of the theorem
statement, and the article states them in mathematical form before linking to
the source. This keeps the mathematical result and the Stainless evidence
aligned without relying on repository-wide verification-condition totals, which
change when unrelated functions are added.

## 3. Linear Stage Semantics

The linear specification is an ordered enumeration of exactly the integers that
pass the installed filters at or after the head.

- `apply` returns accepted values and never moves backwards.
- `indexOfAccepted` proves completeness of the enumeration.
- strict increase makes indexes and adjacent gaps unambiguous.

### 3.1 Accepted Values and Completeness

The generator's `apply` contract proves soundness:
$A_S(\ell_k)$ for every $k\ge0$. Conversely, `indexOfAccepted` proves that
every accepted $v\ge h$ occurs at some index. Together they establish exact
enumeration rather than merely generation of a subset.

```math
\begin{aligned}
\forall k\ge0,\quad
A_S(\ell_k)
&\quad\text{[Soundness]} \\
\forall v\ge h,\quad
A_S(v)
&\Longrightarrow
\exists i\ge0,\ \ell_i=v
\quad\text{[Completeness]}.
\end{aligned}
```

For completeness, start at $\ell_0=h\le v$. If the current generated value
is smaller than $v$, the next generated accepted value cannot pass over $v$,
because $v$ itself is accepted. Repeating this finite descent on
$v-\ell_k$ reaches an index $i$ with $\ell_i=v$.

This verified contract is implemented in [
  SpecSieveSequence::indexOfAccepted
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter6/sieve/seq/spec/SpecSieveSequence.scala).

### 3.2 Strict Increase

Each recursive step searches strictly after the previous result. Consequently,
the sequence is strictly increasing, indexes are injective, and every adjacent
gap is positive.

```math
\begin{aligned}
\ell_{k+1}
&\ge \ell_k+1
  &&\text{[Search starts after previous value]} \\
&\gt \ell_k
  &&\text{[Integer order]} \\
g_k
&=\ell_{k+1}-\ell_k\gt0
  &&\text{[Q.E.D.]}.
\end{aligned}
```

This property is verified in [
  SpecSieveSequence::applyStrictlyIncreases
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter6/sieve/seq/spec/SpecSieveSequence.scala).

## 4. Period and Cycle Reconstruction

The finite representation works because the filter predicate is periodic and
the scan preserves the order of the repeated accepted residues.

- one period shifts every generated value by $M$;
- every later block is a translated copy of the first block;
- integrating one finite positive gap cycle reconstructs the infinite scan.

### 4.1 Canonical Block Shift

The boundary $h+M$ passes exactly the same filters as $h$, so completeness
gives a positive index $T$ with $\ell_T=h+M$. Periodicity of acceptance and
strict order then identify the $k$-th accepted value in the following block:

```math
\begin{aligned}
A_S(v+M) &= A_S(v)
  &&\text{[Modulo-period invariance]} \\
\ell_T &= h+M
  &&\text{[Canonical boundary]} \\
\ell_{k+T} &= \ell_k+M
  &&\text{[Same ordered survivor]} \\
\ell_{k+nT} &= \ell_k+nM
  &&\text{[Block induction; Q.E.D.]}.
\end{aligned}
```

This property is verified in [
  SpecSieveSeqPeriodProperties::assertBlockShiftMultiple
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter6/sieve/seq/spec/properties/SpecSieveSeqPeriodProperties.scala).

### 4.2 Gap-Cycle Reconstruction

Let `GapCycle(G)` store the first $T$ adjacent differences. The block-shift
theorem makes those differences periodic:

```math
\begin{aligned}
g_{k+T}
&=\ell_{k+T+1}-\ell_{k+T} \\
&=(\ell_{k+1}+M)-(\ell_k+M)
  &&\text{[Block shift]} \\
&=g_k.
\end{aligned}
```

The cycle integral starts at $h$ and adds these gaps. Induction on $k$
then reconstructs every scan value:

```math
\begin{aligned}
I_G(0)
&=h+g_0=\ell_1
  &&\text{[Base]} \\
I_G(k)
&=I_G(k-1)+g_k \\
&=\ell_k+(\ell_{k+1}-\ell_k)
  &&\text{[Induction hypothesis]} \\
&=\ell_{k+1}
  &&\text{[Q.E.D.]}.
\end{aligned}
```

This property is verified in [
  SpecSieveSeqPeriodProperties::assertSpecGapCycleIntegralMatchesApply
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter6/sieve/seq/spec/properties/SpecSieveSeqPeriodProperties.scala).

### 4.3 Repetition Does Not Change the Infinite Sequence

The transition prepares $h$ copies of the current period before installing
the head $h$ as a new filter. Repeating the stored gap list multiplies the
finite representation's period from $T$ to $hT$, but it does not change
the infinite periodic sequence represented by the cycle integral.

```math
\begin{aligned}
G^{\langle h\rangle}
  &=\underbrace{G\mathbin{\texttt{++}}\cdots\mathbin{\texttt{++}}G}_{h\text{ copies}}, \\
|G^{\langle h\rangle}|&=hT, \\
G^{\langle h\rangle}_{k\bmod hT}
  &=G_{k\bmod T}, \\
I_{G^{\langle h\rangle}}(k)
  &=I_G(k)
  \quad\text{[Equal increments and initial value; Q.E.D.]}.
\end{aligned}
```

This property is verified in [
  SpecDerivedRepeatedCycleProperties::assertSpecRepeatedCycleIntegralMatchesBase
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter6/sieve/seq/spec/properties/SpecDerivedRepeatedCycleProperties.scala).

## 5. Installing the Current Head as a Filter

The next stage adds $h$ to the active filter list. Over one complete expanded
window, this operation has an exact count and a deterministic effect on gaps.

- the expanded old stage contains exactly $hT$ accepted values;
- exactly $T$ of those values are divisible by $h$;
- a real linear 2-gap has exactly two destroyed lifts and $h-2$ lifts whose
  endpoints survive;
- every next gap is either copied or is a sum of consecutive old gaps;
- filtering the base and repeated cycle views yields equal survivor-gap lists.

### 5.1 Exact Survivor Count

Consider the accepted values with indexes $r+iT$, where
$0\le r\lt T$ and $0\le i\lt h$. The block-shift theorem gives

```math
\begin{aligned}
\ell_{r+iT}=\ell_r+iM.
\end{aligned}
```

The head $h$ is a prime not present among the smaller-prime factors of $M$,
so $\gcd(M,h)=1$. Multiplication by $M$ permutes the residues modulo $h$.
For each fixed $r$, exactly one offset $i\in\{0,\ldots,h-1\}$ therefore
satisfies $\ell_r+iM\equiv0\pmod h$. There are $T$ choices of $r$, so
exactly $T$ old survivors are removed:

```math
\begin{aligned}
N_{\mathrm{old}} &= hT
  &&\text{[Repeated blocks]} \\
N_{\mathrm{removed}} &= T
  &&\text{[One zero residue per row]} \\
N_{\mathrm{survive}}
  &=hT-T \\
  &=T(h-1)
  &&\text{[Q.E.D.]}.
\end{aligned}
```

This is an exact full-period theorem, not a probabilistic density estimate.

This property is verified in [
  SpecSieveSeqSurvivorCountProperties::assertSameHeadExtendedFilterCount
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter6/sieve/seq/spec/properties/SpecSieveSeqSurvivorCountProperties.scala).

### 5.2 Exact Lifted-Copy Law for a Real 2-Gap

This subsection concerns the actual deterministic sieve sequence, not a
random model. Suppose two consecutive values in the real sequence satisfy
$\ell_{k+1}-\ell_k=2$. Write $p=h$ for the incoming odd prime and $M$ for the
current tail primorial. The complete lift block contains the $p$ endpoint
pairs

```math
(\ell_k+jM,\ \ell_{k+1}+jM),
\qquad 0\le j\lt p.
```

The verified result is deliberately local to one real sequence pair. It does
not yet aggregate over the cyclic wrap gap or establish a recurrence for the
total next-stage 2-gap population.

#### 5.2.1 The Two Forbidden Lift Offsets Are Distinct

Each endpoint has one unique lift offset at which the incoming prime divides
it. Those offsets cannot coincide: if the same prime divided both lifted
endpoints, it would divide their difference $2$, which is impossible for an
odd prime. This is the structural fact that prevents the two endpoint strikes
from collapsing into one destroyed copy.

```math
\begin{aligned}
j_L,j_R&\in\{0,\ldots,p-1\},
&&[\text{By Unique Lift Offset}]\\
\ell_k+j_LM&\equiv0\pmod p,\\
\ell_{k+1}+j_RM&\equiv0\pmod p.\\[2pt]
j_L=j_R=j
&\Longrightarrow
(\ell_{k+1}+jM)-(\ell_k+jM)\equiv0\pmod p
&&[\text{Substitution}]\\
&\Longrightarrow 2\equiv0\pmod p
&&[\ell_{k+1}-\ell_k=2]\\
&\Longrightarrow 2=0
&&[\text{By Modulo Property},\ 2\lt p],
\end{aligned}
```

which is a contradiction. Therefore

```math
j_L\ne j_R.
\qquad[\text{Q.E.D.}]
```

```scala
def assertForbiddenLiftOffsetsDistinct(
  seq: SpecSieveSequence,
  k: BigInt
): Boolean = {
  require(k >= BigInt(0))
  require(seq.head.value > BigInt(2))
  require(Calc.mod(seq.tailPrimorial, seq.head.value) != BigInt(0))
  require(seq.apply(k + BigInt(1)) - seq.apply(k) == BigInt(2))

  val p = seq.head.value
  val step = seq.tailPrimorial
  val left = seq.apply(k)
  val right = seq.apply(k + BigInt(1))
  val leftOffset = BezoutUtils.coprimeStepZeroOffset(left, step, p)
  val rightOffset = BezoutUtils.coprimeStepZeroOffset(right, step, p)

  assert(right == left + BigInt(2))
  assert(Calc.mod(left + leftOffset * step, p) == BigInt(0))
  assert(Calc.mod(right + rightOffset * step, p) == BigInt(0))

  if (leftOffset == rightOffset) {
    val leftCopy = left + leftOffset * step
    val rightCopy = right + rightOffset * step
    assert(rightCopy == leftCopy + BigInt(2))
    assert(Calc.mod(leftCopy, p) == BigInt(0))
    assert(Calc.mod(rightCopy, p) == BigInt(0))
    assert(ModOperations.modZeroPlusC(leftCopy, p, BigInt(2)))
    assert(Calc.mod(rightCopy, p) == Calc.mod(BigInt(2), p))
    assert(ModSmallDividend.modSmallDividend(BigInt(2), p))
    assert(Calc.mod(BigInt(2), p) == BigInt(2))
    assert(Calc.mod(rightCopy, p) != BigInt(0))
    leftOffset != rightOffset
  } else {
    leftOffset != rightOffset
  }
}.holds
```

This property is verified in [
  SpecSieveSeqTwoGapProperties::assertForbiddenLiftOffsetsDistinct
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter6/sieve/seq/spec/properties/SpecSieveSeqTwoGapProperties.scala).

#### 5.2.2 Exactly Two Lifted Copies Are Destroyed

A copied pair is destroyed when at least one endpoint is divisible by $p$.
The left endpoint is struck once, the right endpoint is struck once, and the
distinct-offset theorem makes these two singleton strike sets disjoint.
Consequently their union contains exactly two copy indices.

```math
\begin{aligned}
D_L&=\{j:0\le j\lt p,\ p\mid(\ell_k+jM)\},\\
D_R&=\{j:0\le j\lt p,\ p\mid(\ell_{k+1}+jM)\},
&&[\text{By Definition}]\\
|D_L|&=1,
\qquad |D_R|=1,
&&[\text{By Unique Lift Offset}]\\
D_L\cap D_R&=\varnothing
&&[\text{By Lemma }j_L\ne j_R]\\
D&=D_L\cup D_R,
&&[\text{By Definition}]\\
|D|&=|D_L|+|D_R|=2.
&&[\text{Q.E.D.}]
\end{aligned}
```

```scala
def assertExactlyTwoDestroyedCopies(
  seq: SpecSieveSequence,
  k: BigInt
): Boolean = {
  require(k >= BigInt(0))
  require(seq.head.value > BigInt(2))
  require(Calc.mod(seq.tailPrimorial, seq.head.value) != BigInt(0))
  require(seq.apply(k + BigInt(1)) - seq.apply(k) == BigInt(2))

  val p = seq.head.value
  val step = seq.tailPrimorial
  val left = seq.apply(k)
  val right = seq.apply(k + BigInt(1))
  val leftWitness = BezoutUtils.coprimeStepZeroOffset(left, step, p)
  val rightWitness = BezoutUtils.coprimeStepZeroOffset(right, step, p)

  assert(right == left + BigInt(2))
  assert(assertForbiddenLiftOffsetsDistinct(seq, k))
  assert(leftWitness != rightWitness)
  assert(assertDestroyedCountEqualsEndpointCounts(
    left,
    step,
    p,
    BigInt(0),
    leftWitness,
    rightWitness
  ))
  assert(SieveUtils.assertCountZeroOffsetsOne(left, step, p))
  assert(SieveUtils.countZeroOffsets(left, step, p, BigInt(0)) == BigInt(1))
  assert(SieveUtils.assertCountZeroOffsetsOne(right, step, p))
  assert(SieveUtils.countZeroOffsets(right, step, p, BigInt(0)) == BigInt(1))

  countDestroyedTwoGapCopies(left, step, p, BigInt(0)) == BigInt(2)
}.holds
```

This property is verified in [
  SpecSieveSeqTwoGapProperties::assertExactlyTwoDestroyedCopies
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter6/sieve/seq/spec/properties/SpecSieveSeqTwoGapProperties.scala).

#### 5.2.3 Exactly \(p-2\) Lifted Copies Keep Both Endpoints

There are $p$ candidate lifts in the complete block. Removing the two and
only two destroyed indices leaves exactly $p-2$ copies whose two endpoints
survive the incoming filter. This is an exact deterministic count, not an
expected value or an independence heuristic.

```math
\begin{aligned}
|\{0,\ldots,p-1\}|&=p,
&&[\text{By Definition}]\\
|D|&=2,
&&[\text{By Lemma: Exactly Two Destroyed Copies}]\\
N_{\mathrm{endpoint\text{-}surviving}}
&=p-|D|\\
&=p-2.
&&[\text{Substitution; Q.E.D.}]
\end{aligned}
```

```scala
def assertExactlyHeadMinusTwoCopiesSurvive(
  seq: SpecSieveSequence,
  k: BigInt
): Boolean = {
  require(k >= BigInt(0))
  require(seq.head.value > BigInt(2))
  require(Calc.mod(seq.tailPrimorial, seq.head.value) != BigInt(0))
  require(seq.apply(k + BigInt(1)) - seq.apply(k) == BigInt(2))

  val p = seq.head.value
  val step = seq.tailPrimorial
  val left = seq.apply(k)

  assert(assertExactlyTwoDestroyedCopies(seq, k))
  p - countDestroyedTwoGapCopies(left, step, p, BigInt(0)) == p - BigInt(2)
}.holds
```

This property is verified in [
  SpecSieveSeqTwoGapProperties::assertExactlyHeadMinusTwoCopiesSurvive
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter6/sieve/seq/spec/properties/SpecSieveSeqTwoGapProperties.scala).

### 5.3 Copy-or-Merge Gap Dynamics

Let old consecutive values be $\ell_k\lt\ell_{k+1}$. If both survive the new
filter, no new accepted value can appear between them, so their difference is
copied unchanged. If one or more old values are removed, the next surviving
endpoints are $\ell_k$ and $\ell_j$ for some $j\gt k+1$; telescoping merges the
intermediate gaps:

```math
\begin{aligned}
\ell_{k+1}\text{ survives}
&\Longrightarrow
g'_m=\ell_{k+1}-\ell_k=g_k,
  &&\text{[Copy]} \\
\ell_{k+1},\ldots,\ell_{j-1}\text{ removed}
&\Longrightarrow
g'_m=\ell_j-\ell_k \\
&=\sum_{i=k}^{j-1}(\ell_{i+1}-\ell_i) \\
&=\sum_{i=k}^{j-1}g_i.
  &&\text{[Merge; Q.E.D.]}
\end{aligned}
```

The immediate-survivor branch is verified in [
  SpecSieveSeqNextProperties::assertFilterPreservesNextGap
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter6/sieve/seq/spec/properties/SpecSieveSeqNextProperties.scala).

The skipped-successor branch is verified as a supporting theorem. When the
immediate old successor is removed, the next gap is the sum of the old gaps up
to the first later survivor. This supporting property is verified in [
  SpecSieveSeqNextProperties::assertMergeGapEqualsOldGapSum
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter6/sieve/seq/spec/properties/SpecSieveSeqNextProperties.scala).

The general merged prefix is then verified against the next specification's
gap list. This property is verified in [
  SpecSieveSeqNextProperties::assertMergedGapPrefixMatchesNext
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter6/sieve/seq/spec/properties/SpecSieveSeqNextProperties.scala).

### 5.4 Filtering the Repeated Cycle Preserves the Semantic Result

Section 4.3 proved pointwise equality between the base and repeated cycle
integrals. Applying the same divisibility predicate at the same positions must
therefore select identical survivor values. Equal survivor lists have equal
adjacent-gap lists:

```math
\begin{aligned}
I_{G^{\langle h\rangle}}(k)&=I_G(k)
  &&\text{[Repeated-cycle equality]} \\
I_{G^{\langle h\rangle}}(k)\not\equiv0\pmod h
&\Longleftrightarrow I_G(k)\not\equiv0\pmod h
  &&\text{[Substitution]} \\
\text{survivors}(I_{G^{\langle h\rangle}},h)
&=\text{survivors}(I_G,h) \\
\text{gaps}(\text{survivors}(I_{G^{\langle h\rangle}},h))
&=\text{gaps}(\text{survivors}(I_G,h))
  &&\text{[Q.E.D.]}.
\end{aligned}
```

This property is verified in [
  SpecDerivedRepeatedCycleProperties::assertSpecBaseAndRepeatedGapListMatch
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter6/sieve/seq/spec/properties/SpecDerivedRepeatedCycleProperties.scala).

## 6. The Next Stage

The next stage installs the current head as a filter, starts at the following
prime, and represents its own accepted sequence by a new finite gap cycle.
Throughout this section, a prime marks the next stage's own version of each
object defined in Section 2: $S'$ is the next stage, $h'=\ell_1$ its head,
$M'$ its tail primorial, $\ell'$ its linear enumeration, and $G'$ its gap
cycle.

- the first old-stage successor is the next prime under the square bound;
- the semantic merged-gap prefix equals the next specification's gap prefix;
- a valid next-period boundary lets the next gap cycle reconstruct the next scan.

### 6.1 Square-Bound Successor Primality

The first old-stage successor is accepted by all filters smaller than $h$.
If that successor lies below $h^2$, then a composite successor would have a
prime divisor below $h$, contradicting acceptance. Therefore the successor is
prime under the square-bound precondition:

```math
\begin{aligned}
\ell_1&\lt h^2, \\
\ell_1\text{ composite}
&\Longrightarrow
\exists d\lt h,\ d\text{ prime and }d\mid \ell_1
  &&\text{[Smallest prime divisor]} \\
d\lt h
&\Longrightarrow d\in\overline{P}
  &&\text{[All smaller primes are filters]} \\
d\mid\ell_1
&\Longrightarrow \neg A_S(\ell_1)
  &&\text{[Filter contradiction]} \\
&\Longrightarrow \ell_1\text{ is prime}.
  &&\text{[Q.E.D.]}
\end{aligned}
```

This property is verified in [
  SpecSieveSeqHeadIsPrime::assertApplyOneIsPrimeIfBelowHeadSq
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter6/sieve/seq/spec/properties/SpecSieveSeqHeadIsPrime.scala).

### 6.2 The First Successor Is the Next Prime

Suppose the next prime after $h$ is $p^+$ and $p^+\lt h^2$. The next prime
passes every smaller-prime filter, so $\ell_1\le p^+$. Conversely, if
$\ell_1\lt h^2$ were composite, it would have a prime divisor at most
$\sqrt{\ell_1}\lt h$. That divisor belongs to $\overline{P}$, contradicting
acceptance. Thus $\ell_1$ is prime. No prime lies strictly between $h$ and
$p^+$, so $\ell_1=p^+$.

```math
\begin{aligned}
A_S(p^+) &\quad\text{[Distinct larger prime passes old filters]} \\
\ell_1 &\le p^+
  &&\text{[Least accepted successor]} \\
\ell_1 \lt h^2
  &\Longrightarrow \ell_1\text{ is prime}
  &&\text{[Small composite divisor]} \\
h\lt\ell_1\le p^+,
\quad \ell_1\text{ prime}
  &\Longrightarrow \ell_1=p^+
  &&\text{[No intervening prime; Q.E.D.]}.
\end{aligned}
```

This property is verified in [
  SpecSieveSeqHeadIsPrime::assertApplyOneEqualsNextPrime
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter6/sieve/seq/spec/properties/SpecSieveSeqHeadIsPrime.scala).

### 6.3 Semantic Pipeline Agreement

Let $T'=T(h-1)$. Under the stated stage-relationship invariants, the semantic
merge process starts at the first surviving old value and emits $T'$ merged
gaps. Section 5.2 proves recursively that this list equals the first $T'$
gaps of the next linear specification:

```math
\begin{aligned}
T'&=T(h-1), \\
\text{mergedGaps}(S,S',1,T')
&=\text{gapList}(S',0,T')
  \quad\text{[By copy-or-merge induction; Q.E.D.]}.
\end{aligned}
```

This property is verified in [
  SpecSieveSeqNextStageProperties::assertPipelineOutputMatchesNextGapList
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter6/sieve/seq/spec/properties/SpecSieveSeqNextStageProperties.scala).

### 6.4 Conditional Next-Cycle Reconstruction

If $T'$ is known to be the canonical period of the next stage, the generic
cycle-reconstruction theorem from Section 4.2 applies directly to that stage:

```math
\begin{aligned}
\ell'_{T'} &= h'+M'
  &&\text{[Next-period boundary]} \\
G'&=\text{gapList}(S',0,T') \\
I_{G'}(k-1)&=\ell'_k
  &&\text{[Cycle reconstruction; Q.E.D.]}.
\end{aligned}
```

This property is verified in [
  SpecSieveSeqNextStageProperties::assertNextCycleReconstructsNextSpec
](https://github.com/thiagomata/prime-numbers/blob/master/src/main/scala/v1/chapter6/sieve/seq/spec/properties/SpecSieveSeqNextStageProperties.scala).

## 7. Exact Proof Boundary

The verified results above do not form an unconditional operational theorem.
This section states the boundary as part of the theorem.

- **Square bound.** `SpecSieveSequence.next` and the next-head theorem require
  $p^+\lt h^2$. Bertrand's postulate supplies a prime between $h$ and $2h$;
  for prime $h\ge2$, this implies the required square bound (with $h=2$
  checked directly). Ramanujan gives a direct proof of the required postulate
  [[9]](#ref9), but
  Bertrand's postulate is an external mathematical dependency here, not a
  Stainless theorem in this development.

- **Count-to-period bridge.** Section 5.1 verifies that filtering the complete
  expanded current-stage window leaves exactly $T(h-1)$ values. Section 6.3
  separately reconstructs the next stage when
  $\ell'_{T'}=h'+M'$ is supplied. The derivation of that next canonical-period
  equation from the same-head count is a distinct open composition theorem.

- **Direct cycle-to-cycle construction.** Repetition preserves the represented
  values; filtering the base and repeated views gives equal survivor lists and
  gaps; the first survivor is the next head; and the semantic merged-gap prefix
  agrees with the next specification. The open composition theorem is the
  equality between the repeated cycle's filtered survivor-gap list and that
  semantic merged-gap prefix, followed by packaging those gaps into a new
  integral cycle.

- **No short-window gap-persistence theorem.** Section 5.2 proves that exactly
  $h-2$ lifts of one real linear 2-gap keep both endpoints over a complete
  lift block. It does not imply that one of those lifts lies in a shorter
  interval such as $[h,h^2)$, nor does it yet aggregate the cyclic wrap gap
  into a total next-stage recurrence. This article makes no claim about
  infinitely many twin primes or the survival of 2-gaps in every local window.

- **No efficiency theorem.** The period grows from $T$ to $T(h-1)$. The finite
  cycle is analytically useful, but materializing it need not outperform a
  conventional segmented sieve. No time or space complexity advantage is claimed.

These qualifications are part of the result: they separate the verified
finite-stage theorem from adjacent mathematical questions.

## 8. Open Proof Work

The main open proof obligation is to connect the filtered repeated-cycle survivor
gaps with the semantic merged-gap prefix. That equality is the missing bridge
between the local delete-and-merge description and the concrete gap list of
the next sieve level. Once that bridge is verified, the next `CycleIntegral`
can be constructed directly from the current repeated and filtered cycle
rather than being related through a separate semantic transition.

A second open obligation is to derive the next canonical-period boundary from the
exact survivor count. The article already proves the complete-period counting
law, but the canonical boundary requires turning that count into the precise
finite prefix used by the next stage. The square-bound dependency currently
supplied by Bertrand's postulate is another natural verification target:
either a Stainless proof of the needed bound or a clearly stated formal
substitute would make the dependency explicit inside the project.

Local gap-distribution theorems remain separate from
the full-period construction results proven here. The full-period facts explain
how the sieve stage is represented and transformed; they do not by themselves
settle which gaps appear in a particular finite window.

## 9. Conclusion

The Sieve Sequence is a finite representation of an infinite accepted-value
stream. The formalization verifies the following core facts:

```math
\begin{aligned}
A_S(v)
&\Longrightarrow \exists i\ge0,\ \ell_i=v,
  &&\text{[Complete enumeration]} \\
\ell_{k+1}&\gt\ell_k,
  &&\text{[Strict increase]} \\
\ell_{k+nT}&=\ell_k+nM,
  &&\text{[Block shift]}.
\end{aligned}
```

The finite gap cycle reconstructs the same stream and remains semantically
unchanged when the cycle is repeated:

```math
\begin{aligned}
I_G(k-1)&=\ell_k,
  &&\text{[Cycle reconstruction]} \\
I_{G^{\langle h\rangle}}(k)&=I_G(k),
  &&\text{[Repetition invariance]}.
\end{aligned}
```

Installing the current head as a new filter has an exact complete-period count,
an exact lifted-copy law for each real linear 2-gap, and a copy-or-merge local
gap update:

```math
\begin{aligned}
N_{\mathrm{survive}}&=T(h-1),
  &&\text{[Exact expanded filtering]} \\
N_{\mathrm{destroyed\ lifts}}(\ell_k,\ell_{k+1})&=2,
  &&\text{[Real 2-gap endpoint strikes]} \\
N_{\mathrm{endpoint\text{-}surviving\ lifts}}(\ell_k,\ell_{k+1})&=h-2,
  &&\text{[Exact lifted-copy survival]} \\
g'_m&=g_k
  \quad\text{or}\quad
  g'_m=\sum_{i=k}^{j-1}g_i,
  &&\text{[Copy or merge]}.
\end{aligned}
```

Under the explicit square-bound and period-boundary assumptions, the next head
and next-stage reconstruction properties are also verified:

```math
\begin{aligned}
p^+\lt h^2&\Longrightarrow \ell_1=p^+,
  &&\text{[Next head]} \\
\text{mergedGaps}(S,S',1,T')
&=\text{gapList}(S',0,T'),
  &&\text{[Semantic transition]} \\
\ell'_{T'}=h'+M'
&\Longrightarrow I_{G'}(k-1)=\ell'_k.
  &&\text{[Conditional next reconstruction]}
\end{aligned}
```

The formalization therefore gives a precise finite-stage account of the sieve:
the old filter pattern repeats, the new head removes exactly one lift per old
residue over a complete expanded period, the two endpoint strikes of a real
linear 2-gap occur at distinct lift offsets, and deletion changes gaps only by
copying or merging them. The theorem does not infer short-window prime-gap
persistence, a cyclic population recurrence, or algorithmic efficiency from
the full-period facts alone.

## References

<a name="ref1" id="ref1" href="#ref1">[1]</a>
Mata, T. H. (2026). *Division and Modulo from Recursive
Normalization*. [Local article](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter2/modulo.md).

<a name="ref2" id="ref2" href="#ref2">[2]</a>
Mata, T. H. (2026). *Using Formal Verification to Prove Properties of Lists
Recursively Defined*. [Local article](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter3/list.md).

<a name="ref3" id="ref3" href="#ref3">[3]</a>
Mata, T. H. (2026). *Formal Verification of Cyclic Lists*.
[Local article](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter4/cycle.md).

<a name="ref4" id="ref4" href="#ref4">[4]</a>
Mata, T. H. (2026). *Formal Verification of Cycle Integral Properties from
First Principles*. [Local article](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter4/integral-cycle.md).

<a name="ref5" id="ref5" href="#ref5">[5]</a>
Hardy, G. H. and Wright, E. M. (1979). *An Introduction to the Theory of
Numbers* (5th ed.). Clarendon Press, Oxford. See Section 5.4 for the Chinese
Remainder Theorem and Section 15.1 for the sieve of Eratosthenes.
[Bibliographic record](https://books.google.com/books?id=FlUj0Rk_rF4C).

<a name="ref6" id="ref6" href="#ref6">[6]</a>
Pritchard, P. (1987). "Linear prime-number sieves: a family tree."
*Science of Computer Programming*, 9(1), 17-35.
[doi:10.1016/0167-6423(87)90024-4](https://doi.org/10.1016/0167-6423(87)90024-4).

<a name="ref7" id="ref7" href="#ref7">[7]</a>
EPFL-LARA. *Stainless documentation: Verification Conditions*.
[Official documentation](https://epfl-lara.github.io/stainless/verification.html).

<a name="ref8" id="ref8" href="#ref8">[8]</a>
Hamza, J., Voirol, N., and Kuncak, V. (2019). "System FR: Formalized
Foundations for the Stainless Verifier." *Proceedings of the ACM on Programming
Languages*, 3(OOPSLA), Article 166.
[doi:10.1145/3360592](https://doi.org/10.1145/3360592).

<a name="ref9" id="ref9" href="#ref9">[9]</a>
Ramanujan, S. (1919). "A proof of Bertrand's postulate." *Journal of the
Indian Mathematical Society*, 11, 181-182.
[Original paper](https://ramanujan.sirinudi.org/Volumes/published/ram24.pdf).
