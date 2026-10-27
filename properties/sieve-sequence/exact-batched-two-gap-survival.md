# Exact Batched 2-Gap Survival

**Status:** Mathematically proved. Stainless verification is not claimed here.

## Meaning

Several future prime filters can be applied as one mathematical batch. This
avoids recursive rounding and counts overlaps exactly over a complete expanded
period.

## Exact Jump to a Later Sieve Sequence

We can construct a later sieve sequence in one finite jump: perform all the
expansions first, apply the union of the new prime filters once, and reconstruct
the final cyclic gaps. Intermediate filtering and rotations are unnecessary for
determining the final sequence. This is an equality of complete sieve sequences,
not only an equality of their numbers of 2-gaps.

Let `p >= 3` and `q > p` be primes. The sequence with head `p` has already
installed exactly the prime filters smaller than `p`. Define

```math
\begin{aligned}
M_p&=\prod_{\substack{r<p\\r\ \mathrm{prime}}}r,\\
\mathcal B_{p,q}&=\{r:r\ \mathrm{prime},\ p\le r<q\},\\
K_{p,q}&=\prod_{r\in\mathcal B_{p,q}}r,\\
M_q&=M_pK_{p,q}.
\end{aligned}
```

Represent the old cycle by its canonical residues

```math
R_p=\{a\in\mathbb Z:0\le a<M_p,\ \gcd(a,M_p)=1\}.
```

Repeating the gap cycle by each successive prime in the batch is equivalent to
repeating it `K_{p,q}` times. In terms of values, these are translated copies,
not repeated identical integers. The complete expanded residue set is

```math
E_{p,q}=\{a+jM_p:a\in R_p,\ 0\le j<K_{p,q},\ j\in\mathbb Z\}.
```

Filter this set once by all primes in the batch. The resulting identity is

```math
\begin{aligned}
\{n\in E_{p,q}:\forall r\in\mathcal B_{p,q},\ r\nmid n\}
&=\{n\in\mathbb Z:0\le n<M_q,\ \gcd(n,M_q)=1\}\\
&=R_q.
\end{aligned}
```

To prove it, each integer in `[0,M_q)` has a unique decomposition
`n = a + j M_p`, where `0 <= a < M_p` and `0 <= j < K_{p,q}`. Membership in
`E_{p,q}` is therefore exactly avoidance of every old prime filter. The final
filter adds exactly the missing primes below `q`:

```math
\begin{aligned}
n\in E_{p,q}\ \land\ \forall r\in\mathcal B_{p,q},\ r\nmid n
&\iff 0\le n<M_q\ \land\ \gcd(n,M_p)=1
       \ \land\ \gcd(n,K_{p,q})=1
&&[\text{By Definition}]\\
&\iff 0\le n<M_q\ \land\ \gcd(n,M_q)=1
&&[\text{By Prime Factorization}]\\
&\iff n\in R_q.
&&[\text{Q.E.D.}]
\end{aligned}
```

Sort `R_q`, take consecutive differences, and include the wrap-around difference
from the last residue to the first residue plus `M_q`. Rotate that gap cycle to
start at the residue of `q` and anchor its integral at the actual value `q`.
This recovers precisely the later stream

```math
S_q=\{n\in\mathbb Z:n\ge q,\ \gcd(n,M_q)=1\}
```

in increasing order. The lower bound matters: canonical residues describe the
periodic pattern, whereas the sieve stream begins at its head. The new filters
include `p` and exclude `q` itself. Filter order is irrelevant because retaining
a value means satisfying every divisibility condition simultaneously.

In particular, choose `q` to be the first prime greater than `p^2`. Expanding by
every prime from `p` through the last prime before `q`, then filtering once,
produces exactly the same `q` sequence as all the individual transitions. The
identity does not require this special choice; it holds for any later prime head.

The acceptance convention is implemented by
[`SpecSieveSequence::passesFilter` and `accepts`](../../src/main/scala/v1/chapter6/sieve/seq/spec/SpecSieveSequence.scala).
The multi-stage identity above is a mathematical derivation; no dedicated
Stainless verification of this identity is claimed. This records a consequence
of the usual residue sieve construction, without a claim of historical novelty.
As with the count below, equality over the expanded period does not establish
where surviving 2-gaps occur inside a shorter safe window.

## Setup

Let `M` be the current modulus and let `(x,x+2)` be one current cyclic 2-gap.
Choose a finite set of distinct odd primes

```math
\mathcal R=\{r_1,r_2,\ldots,r_k\}
```

such that no `r_i` divides `M`. Define

```math
B=\prod_{r\in\mathcal R}r.
```

In the combined period modulo `MB`, the old 2-gap has `B` lifted copies.

## Property

Exactly

```math
\prod_{r\in\mathcal R}(r-2)
```

of those `B` copies survive every filter in the batch. Consequently, if the
old complete period contains `G` cyclic 2-gaps, the batched period contains

```math
G_{\mathrm{after}}
=G\prod_{r\in\mathcal R}(r-2).
```

## Proof

Fix one new prime `r`. A lifted pair is destroyed by its filter exactly when
its left endpoint is `0 modulo r` or its right endpoint is `0 modulo r`:

```math
x\equiv0\pmod r
\qquad\text{or}\qquad
x\equiv-2\pmod r.
```

The two forbidden classes are distinct, leaving exactly `r-2` allowed classes
modulo `r`.

The primes in the batch are pairwise coprime and are also coprime to `M`.
The Chinese remainder theorem makes the allowed choices independent across
the whole batch. Their product is therefore the exact number of surviving
lifts. Summing the same count over all old 2-gaps proves the aggregate formula.

## Why Batching Is Stronger Bookkeeping

- No floor is applied after an intermediate prime.
- A value hit by several new filters is still removed only once.
- The result is independent of the order in which the batch filters are
  conceptually applied.
- Prime-by-prime multiplication and one-shot CRT counting give the same exact
  complete-period answer.

## Limitation

The theorem needs the complete combined period of length `MB`. In a shorter
window, the allowed CRT classes need not occur in their full proportions.
Batching therefore proves global survival but does not, by itself, prove a
surviving 2-gap inside a safe window shorter than `MB`.

The [current batched-window research summary](research/batched-survival-progress.md)
records subsequent analytical transition-loss bounds. They do not close the
short-window positivity problem: sustaining an actual positive margin remains open.
