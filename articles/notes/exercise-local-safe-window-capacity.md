# Exercise: Local Strike Capacity for 2-Gaps in a Sieve Sequence

**Status:** Worked exercise, not a promotion candidate — see
[`README.md`](README.md). Its background material links to the published
articles instead of restating them, and its main pigeonhole bound is the
elementary warm-up to the exact result in [Gap Dynamics
§4.3–4.4](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter6/gap-dynamics.md#43-exact-accepted-local-filter-strikes),
not an independent discovery.

**Author:** Mata, T. H., Independent Researcher
**Date:** 2026-08-15
**License:** [CC BY 4.0](../LICENSE)

This exercise is meant to be read after:

- [Formal Verification of the Sieve Sequence](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter6/sieve-sequence.md)
- [Gap Dynamics in Sieve Sequences](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter6/gap-dynamics.md)

The goal is to prove a local capacity bound. The exercise does not ask you to
prove that many 2-gaps exist in the local window. Instead, it asks you to prove
that once enough local 2-gaps exist, the next filter does not have enough local
strikes to destroy all of them.

## 1. Background

A sieve sequence stage has a current head prime, a list of previous prime
filters, and a finite period — see [Sieve Sequence
§2.1](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter6/sieve-sequence.md#21-stage-definition).
Let the current stage be $S$.

Use the following notation:

```math
\begin{aligned}
p &= \text{current head prime of } S, \\
q &= \text{next prime after } p, \\
M &= \text{product of all primes smaller than } p.
\end{aligned}
```

The next stage adds $p$ as a new filter and removes exactly the values
divisible by $p$ from the values accepted by the previous filters ([Sieve
Sequence
§5](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter6/sieve-sequence.md#5-installing-the-current-head-as-a-filter)).

The distinction between a global argument and a local argument is not the
rule. The distinction is the interval being counted. Over a complete global
expanded block, every old accepted value has exactly one of its $p$ lifted
copies removed, and a real 2-gap has exactly two of its $p$ lifted copies
destroyed — both proved exactly in [Sieve Sequence
§5.1](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter6/sieve-sequence.md#51-exact-survivor-count)
and
[§5.2](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter6/sieve-sequence.md#52-exact-lifted-copy-law-for-a-real-2-gap).

This exercise studies the local next safe window

```math
[q, q^2)
```

the part of the next stage where accepted values are certified prime by the
usual square-bound argument ([Sieve Sequence
§6.1](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter6/sieve-sequence.md#61-square-bound-successor-primality);
the same window as Gap Dynamics' square-safe certificate, [§2.1](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter6/gap-dynamics.md#21-roles-populations-and-scopes)).
Unlike the complete global expanded block, this local window is usually only a
partial interval. It need not contain complete lifted orbits. So instead of
using full-orbit uniformity, we will use a capacity bound: count how many
local strikes the $p$-filter can possibly make.

## 2. Definitions

A local 2-gap before the $p$-filter is a pair

```math
(x, x+2)
```

such that:

```math
\begin{aligned}
q &\le x, \\
x+2 &< q^2,
\end{aligned}
```

and both endpoints are consecutive accepted values before applying the
$p$-filter.

The $p$-filter destroys this 2-gap if it removes at least one endpoint:

```math
p \mid x
```

or

```math
p \mid (x+2).
```

Let:

```math
W = [q, q^2)
```

and let:

```math
R(p,q) = \text{number of multiples of } p \text{ inside } W.
```

## 3. Main Claim

Prove that:

```math
R(p,q) = \left\lfloor\frac{q^2-1}{p}\right\rfloor - \left\lfloor\frac{q-1}{p}\right\rfloor.
```

Then prove that the number of local 2-gaps destroyed by the $p$-filter is at
most:

```math
2R(p,q).
```

Therefore, if the number of local 2-gaps before filtering is $G_{\text{local}}$, and

```math
G_{\text{local}} > 2R(p,q),
```

then at least one local 2-gap survives the $p$-filter.

## 4. Tasks

### Task 1: Count Multiples in a Half-Open Interval

Prove the following elementary counting lemma.

For positive integers $a$, $A$, and $B$, with $A < B$, the number of multiples
of $a$ in the half-open interval $[A, B)$ is:

```math
\left\lfloor\frac{B-1}{a}\right\rfloor - \left\lfloor\frac{A-1}{a}\right\rfloor.
```

Apply this lemma with:

```math
\begin{aligned}
a &= p, \\
A &= q, \\
B &= q^2,
\end{aligned}
```

to obtain:

```math
R(p,q) = \left\lfloor\frac{q^2-1}{p}\right\rfloor - \left\lfloor\frac{q-1}{p}\right\rfloor.
```

### Task 2: Relate Filter Strikes to Removed Values

Show that the $p$-filter removes a value $v$ from the local window only if $v$
is one of the $R(p,q)$ multiples counted above.

Conclude that the number of removed local values is at most:

```math
R(p,q).
```

This is an upper bound. Some multiples of $p$ might not be present among the
accepted values before filtering, so the actual number removed can be smaller.

### Task 3: Bound How Many 2-Gaps One Removed Value Can Destroy

Let $v$ be a value removed by the $p$-filter.

A local 2-gap destroyed by removing $v$ must have $v$ as one of its endpoints.
There are only two possible local 2-gaps with endpoint $v$:

```math
(v-2, v)
```

and

```math
(v, v+2).
```

Therefore one removed value can destroy at most two local 2-gaps.

Conclude that the total number of destroyed local 2-gaps is at most:

```math
2R(p,q).
```

### Task 4: Prove the Survival Condition

Let $G_{\text{local}}$ be the number of local 2-gaps before applying the
$p$-filter.

Using Task 3, prove:

```math
G_{\text{local}} > 2R(p,q)
\implies
\text{at least one local 2-gap survives the } p\text{-filter.}
```

This is a pigeonhole argument. If there are more local 2-gaps than the maximum
number that can be destroyed, at least one local 2-gap remains.

## 5. Optional Stronger Variant

Suppose the local 2-gaps are endpoint-disjoint: no accepted value is the
endpoint of two different local 2-gaps.

Under this additional assumption, one removed value can destroy at most one
local 2-gap. Prove the sharper bound:

```math
\text{destroyed local 2-gaps} \le R(p,q).
```

Then prove the sharper survival condition:

```math
G_{\text{local}} > R(p,q)
\implies
\text{at least one local 2-gap survives the } p\text{-filter.}
```

This stronger statement requires the endpoint-disjointness assumption. Without
that assumption, the safe general bound is $2R(p,q)$.

## 6. What This Exercise Proves

This exercise proves a local capacity theorem: local survival follows if
local 2-gaps outnumber local filter capacity.

It does not prove that the local window always contains that many 2-gaps.
That is a separate abundance question.

The exact result established here is:

```math
G_{\text{local}} > 2\left(\left\lfloor\frac{q^2-1}{p}\right\rfloor - \left\lfloor\frac{q-1}{p}\right\rfloor\right)
```

implies that at least one local 2-gap survives the transition from the
current stage to the next stage.

The exercise is deliberately local. It uses the same filtering rule as the
global sieve-sequence construction, but it avoids assuming that the local
safe window contains complete lifted residue orbits.

A sharper version of this same theorem — using the exact count of accepted
values struck, rather than every multiple of $p$ — is proved in [Gap Dynamics
§4.3](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter6/gap-dynamics.md#43-exact-accepted-local-filter-strikes)
and
[§4.4](https://github.com/thiagomata/prime-numbers/blob/master/articles/chapter6/gap-dynamics.md#44-sharp-local-2-gap-survival-threshold).
This exercise's `2R(p,q)` pigeonhole bound is the elementary warm-up to that
exact `A(r,Q)` result, not an independent discovery.

## 7. Suggested Final Write-Up

A complete student solution should contain:

1. A proof of the half-open interval multiple-counting formula.
2. A clear explanation that every removed local value must be a multiple of
   $p$.
3. A proof that one removed value can destroy at most two local 2-gaps.
4. The final pigeonhole argument proving survival.
5. A short note explaining why this is a capacity theorem, not a proof of
   local 2-gap abundance.
6. A pointer to the sharper accepted-strikes bound in Gap Dynamics §4.3–4.4
   (§6 above), so the pigeonhole bound is not mistaken for the state of the
   art.

## Appendix: Solution Sketches

**Task 1.** The multiples of $a$ in $[A, B)$ are exactly the numbers $ak$
with $\lceil A/a \rceil \le k < \lceil B/a \rceil$. The count of such integers
$k$ is $\lceil B/a \rceil - \lceil A/a \rceil$, and the identity
$\lceil n/a \rceil - 1 = \lfloor (n-1)/a \rfloor$ converts this to
$\lfloor (B-1)/a \rfloor - \lfloor (A-1)/a \rfloor$.

**Task 2.** The $p$-filter removes $v$ only when $p$ divides $v$; inside the
window $W = [q, q^2)$, every such $v$ is one of the $R(p,q)$ multiples
counted in Task 1. Since some multiples of $p$ may not be accepted values,
the number actually removed is at most $R(p,q)$.

**Task 3.** A destroyed local 2-gap must have a removed endpoint $v$, and the
only possible 2-gaps with endpoint $v$ are $(v-2, v)$ and $(v, v+2)$. So one
removed value is credited with at most two destroyed 2-gaps. If both
endpoints of one gap are removed, that gap is counted twice in this
bookkeeping, which only keeps the total an upper bound. Hence at most
$2R(p,q)$ local 2-gaps are destroyed.

**Task 4.** If $G_{\text{local}} > 2R(p,q)$, more local 2-gaps exist than the
maximum number the filter can destroy, so at least one survives.

**Variant (endpoint-disjoint 2-gaps).** Endpoint-disjointness means no two
local 2-gaps share an endpoint, so a removed value $v$ can be the endpoint of
at most one local 2-gap. The same counting then gives at most $R(p,q)$
destroyed 2-gaps, and survival follows whenever $G_{\text{local}} > R(p,q)$.
