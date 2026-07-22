# Reverse-Engineered Initial Scenario for an Eventual Head 2-Gap

**Status:** Mathematically proved conditional certificate. The existence of an
unbounded family of certificates is not proved here. Stainless verification is
not claimed here.

## Purpose

This property works backward from the desired final event:

```text
some future sieve stage has a 2-gap immediately after its head.
```

It identifies every condition that must already be true of a suitable repeated
copy of an earlier cyclic 2-gap. The pair does not need to survive forever. It
only needs to survive a finite batch of filters until a square-safe stage
certifies both endpoints as prime.

## Setup

Let an initial stage have prime head `p` and modulus

```math
M=\prod_{r<p}r.
```

Let `(a,a+2)` represent a cyclic 2-gap modulo `M`. Its absolute repeated copies
are

```math
(x,x+2)=(a+jM,\ a+2+jM).
```

For a chosen copy `x`, define its certification head

```math
q(x)=
\min\{q:q\text{ is prime},\ q\ge p,\ x+2<q^2\}.
```

The filters installed between the initial and certification stages are

```math
\mathcal R(p,q)=\{r:r\text{ is prime and }p\le r<q\}.
```

Their number is exactly

```math
k(x,p)=\pi(q(x))-\pi(p).
```

## The Four Initial-Scenario Properties

### 1. Seed 2-Gap

The initial residue must already be a valid cyclic 2-gap:

```math
\gcd(a,M)=1
\qquad\text{and}\qquad
\gcd(a+2,M)=1.
```

This guarantees that every copy is accepted by all filters smaller than `p`.

### 2. Reachable Certification Window

The chosen copy must lie inside the safe window of its certification head:

```math
q(x)\le x
\qquad\text{and}\qquad
x+2<q(x)^2.
```

The second inequality holds by the definition of `q(x)`. The first prevents
the pair from lying below the future stage head.

For a proposed future head `q`, the copy indices with this geometry form the
explicit interval

```math
I(a,M,q)=
\left[
\left\lceil\frac{q-a}{M}\right\rceil,
\left\lfloor\frac{q^2-3-a}{M}\right\rfloor
\right].
```

### 3. Finite-Batch Compatibility

For every prime `r` in `R(p,q(x))`, neither endpoint may be divisible by `r`:

```math
r\nmid x
\qquad\text{and}\qquad
r\nmid x+2.
```

Because `gcd(M,r)=1`, this is equivalently the copy-index condition

```math
j\not\equiv-aM^{-1}\pmod r
```

and

```math
j\not\equiv-(a+2)M^{-1}\pmod r
```

for every prime in the finite batch.

### 4. Unboundedness For An Infinite Result

One successful scenario proves one eventual head 2-gap. Infinitely many twin
prime pairs require an unbounded family of successful coordinates:

```math
x_1<x_2<x_3<\cdots
\qquad\text{and}\qquad
x_n\longrightarrow\infty.
```

No positive density and no success at every future head is required.

## Eventual-Head Certificate Theorem

If Properties 1 through 3 hold for one tuple `(p,M,a,j)`, then the pair
`(x,x+2)` eventually appears as a 2-gap at head `x`.

## Proof

Property 1 says the pair survives every filter below `p`. Property 3 says it
also survives every filter from `p` through the last prime below `q(x)`.
Therefore both endpoints are accepted at the stage with head `q(x)`.

Property 2 places both accepted endpoints inside `[q(x),q(x)^2)`. The
safe-window square argument proves that `x` and `x+2` are prime.

The sieve sequence advances through consecutive prime heads. It therefore
eventually reaches the stage whose head is `x`. At that stage `x+2` remains
accepted because it is prime, and `x+1` is even and rejected. Hence the first
gap after head `x` has value `2`.

Property 4 applied to successful certificates gives infinitely many distinct
head 2-gaps and therefore infinitely many twin-prime pairs.

## Worked Example

Start with `p=5`, `M=6`, and the cyclic 2-gap residue `(a,a+2)=(5,7)`.
Choose copy index `j=4`, giving

```math
x=a+jM=5+4\cdot6=29
```

and the pair `(29,31)`. The first certification head is `q=7`, because

```math
7\le29
\qquad\text{and}\qquad
31<7^2.
```

The finite batch contains only filter `5`. Neither endpoint is divisible by
`5`, so `j=4` avoids both forbidden classes for this batch. At stage `7`, the
square bound certifies both endpoints as prime. The sieve later reaches head
`29`, where the first gap is therefore `2`.

The example uses only one filter, but the certificate has exactly the same
form for a batch containing many primes.

## Compact Scenario Condition

For a proposed head `q`, define the batch-allowed copy indices

```math
\mathcal A(a,M,p,q)=
\left\{j:
\begin{array}{l}
j\text{ avoids both forbidden classes modulo every prime }r,\\
p\le r<q
\end{array}
\right\}.
```

The entire initial-scenario requirement is then

```math
\boxed{
I(a,M,q)\cap\mathcal A(a,M,p,q)\ne\varnothing.
}
```

The infinite target is not that this intersection is nonempty for every `q`.
It is enough to find an unbounded sequence of `q` values, seed gaps, and copy
indices for which the intersection is nonempty.

## Dependency Diagram

```mermaid
flowchart LR
    A["Seed 2-gap a modulo M"]
    B["Choose copy x = a + jM"]
    C["Avoid batch-forbidden copy-index classes"]
    D["Survive into q <= x and x + 2 < q^2"]
    E["Square bound certifies both endpoints prime"]
    F["Later stage reaches head x with gap 2"]

    A --> B --> C --> D --> E --> F
```

## Exact Remaining Research Problem

The deterministic construction, certification, and eventual-head implication
are all explicit. The missing theorem is an infinitude statement:

```math
\text{prove that }
I(a,M,q)\cap\mathcal A(a,M,p,q)
\text{ is nonempty for an unbounded family of scenarios.}
```

The seed stage, seed gap, and future certification head may all vary between
successful scenarios. This permits rare favorable cases and avoids the much
stronger requirement that every local safe window succeed.
