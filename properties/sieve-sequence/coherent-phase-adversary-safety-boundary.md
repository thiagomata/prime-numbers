# Coherent-Phase Adversary Safety Boundary

**Status:** Mathematically proved boundary theorem. The measurement section is
finite empirical evidence. The cross-layer rigidity result uses Dirichlet's
theorem as an external mathematical dependency. Stainless verification is not
claimed.

## Meaning

Requiring an adversarial filter to respect the real distance between the two
harmful classes changes the companion game, but fixed distance has two
different strengths.

Inside one layer, a single shared phase turns independent target choices into
one two-class residue-histogram maximum. This is substantially less freedom,
but it is not universally safe: a population concentrated in the two harmful
classes can still be extinguished. The existing two-class capacity threshold
is sharp for this coherent model.

Across every layer, the restriction becomes rigid if the removed residue of
each prime is fixed forever in absolute integer coordinates and every
canonical prime head must survive. Under those requirements, every shifted
residue is forced back to zero. Thus the infinite canonical model is no longer
an adversarial companion; at the filter-family level it is the real sieve.

## One-Layer Setup

Let `r>=5` be an incoming prime and let `S` be a finite population of `N>0`
post-filter-3 2-gap starts. For `a` in `Z/rZ`, define the residue histogram

```math
n_a=\#\{x\in S:x\equiv a\pmod r\},
\qquad
\sum_{a\bmod r}n_a=N.
```

A shared absolute phase `s` removes the values congruent to `s modulo r`.
The 2-gap `(x,x+2)` is destroyed exactly when one of its endpoints has that
residue, equivalently

```math
x\equiv s\pmod r
\qquad\text{or}\qquad
x\equiv s-2\pmod r.
```

Therefore the exact destruction count is

```math
\boxed{D_r(s)=n_s+n_{s-2}.}
```

Changing from absolute residues to copy indices multiplies every class by the
same invertible old-period factor, so it only relabels the phases. The maximum
and all conclusions below are unchanged.

## Random Average and Coherent Maximum

Summing over every shared phase gives

```math
\begin{aligned}
\sum_{s\bmod r}D_r(s)
&=\sum_s n_s+\sum_s n_{s-2}\\
&=2N.
\end{aligned}
```

Hence the balanced-random benchmark is the exact phase average

```math
\boxed{\frac1r\sum_sD_r(s)=\frac{2N}{r}.}
```

The coherent adversary does not receive independent choices for different
parents. Its exact worst damage and relative-to-random factor are

```math
\boxed{
D_r^*=\max_{s\bmod r}(n_s+n_{s-2}),
\qquad
w_r^*=\frac{rD_r^*}{2N}.
}
```

In particular `w_r^*>=1`: maximizing over phases can never be less damaging
than the phase average. This explains why adding coherence does not make the
worst phase identical to a random phase.

## Exact Extinction Criterion

Because the histogram entries are nonnegative and sum to `N`,

```math
D_r(s)=N
```

holds exactly when every occupied residue is one of the two harmful residues:

```math
\boxed{
D_r^*=N
\quad\Longleftrightarrow\quad
\operatorname{supp}(n)
\subseteq\{s,s-2\}
\text{ for some }s.
}
```

Thus fixed within-pair distance plus one shared phase does not alone prevent
local extinction. It replaces arbitrary parent-wise targeting with a precise
two-class concentration question.

## Sharp Capacity-Only Safety Line

After filter `3`, the [Harmful Residue Capacity] property proves that each
residue class contains at most

```math
B=
\left\lfloor\frac{L}{6r}\right\rfloor+1
```

starts in a target interval of available diameter `L`. Consequently

```math
D_r^*\le\min(N,2B),
```

and

```math
\boxed{N>2B\quad\Longrightarrow\quad D_r^*<N.}
```

This threshold is sharp using only population size, fixed harmful distance,
shared phase, and per-class capacity. If `0<N<=2B`, choose a phase `s` and set

```math
n_s=\min(N,B),
\qquad
n_{s-2}=N-n_s,
```

with every other entry zero. Both occupied entries are at most `B`, but
`D_r(s)=N`. Additional spacing can realize each occupied class as a `6r`-spaced
train whenever the interval supplies the stated class capacity. Therefore no
universal below-extinction bound stronger than `N>2B` follows from these
constraints alone.

## Finite Measurement

A read-only pass over
`data/sieve-sequence/first_gaps_per_seq.csv` reconstructed each stored
pre-filter square window, counted its 2-gap starts by residue modulo the
incoming prime, and evaluated every shared phase through `D_r(s)`.

Across the 187 complete stored windows (`r=3` through `r=1123`):

- no coherent phase extinguished a target population;
- `1<=w_r^*<=2.506667`;
- every measured stage `r>=67` satisfied
  `w_r^*<(1/2)log(r)`, the companion article's head-frontier scale; and
- at the final measured transition, `r=1123`, `N=10056`, `D_r^*=28`, and
  `w_r^*=1.563445`.

These observations suggest a constant-scale two-class discrepancy target.
They do not prove a uniform bound, do not validate the article's mixing
premises, and do not imply deterministic head recurrence.

## Cross-Layer Prime-Head Rigidity

Now assign every prime `r` one residue `c_r modulo r`, chosen once and fixed
forever in the absolute integer coordinate. Filter `r` removes precisely the
integers

```math
x\equiv c_r\pmod r.
```

Every finite family of these assignments is CRT-compatible: it specifies one
residue modulo the product of its primes. Require additionally that **every**
canonical prime `q`, not merely a finite prefix, survives all filters `r<q`
before becoming the head.

Suppose `c_r` is nonzero for some prime `r`. Then

```math
\gcd(c_r,r)=1.
```

Dirichlet's theorem on primes in arithmetic progressions supplies a prime
`q>r` satisfying

```math
q\equiv c_r\pmod r.
```

Filter `r` removes this prime before its canonical head stage, contradicting
prime-head preservation. For `r=2`, the only nonzero shift is `1`, which
removes every later odd prime directly. Therefore

```math
\boxed{
\text{fixed absolute shifts + all canonical prime heads}
\quad\Longrightarrow\quad
c_r=0\text{ for every prime }r.
}
```

Conversely, `c_r=0` recovers the real sieve's per-filter absolute
residue-removal family. This converse is stated only at the filter-family
level; it does not claim to reconstruct every implementation detail of the
sieve sequence.

## Consequence For The Adversarial Program

There is no unresolved safety theorem hiding solely between the free
companion and the real filter:

1. Fixed harmful-pair distance without a shared phase still lets each parent
   target its chosen child independently.
2. One shared layer phase reduces damage to the exact maximum
   `max_s(n_s+n_(s-2))`, but this can still equal `N` up to the sharp capacity
   boundary.
3. Fixed cross-layer absolute phases that preserve every canonical prime head
   are forced to be the real zero-residue filter family.

The measured constant-scale coherent maximum is a legitimate conjectural
direction, but proving it requires a new local two-class discrepancy theorem.
At full canonical fidelity, the remaining noncoverage question is the actual
twin-prime/backward-recurrence problem described by the [Coherent Head
Suppression] property. It remains open.

## Related

- [Harmful Residue Capacity After Filter Three](
  harmful-residue-capacity-after-filter-three.md)
- [Two-Gap Placement Saturation And The Cross-Fiber Coupling Boundary](
  two-gap-placement-saturation.md)
- [Coherent Head Suppression Is Shifted Prime-Shot Coverage](
  coherent-head-suppression-is-shifted-prime-shot-coverage.md)
- [Local Pattern-Residue Balance](
  ../../candidates/local-pattern-residue-balance.md)
- [Survival Frontiers in Balanced 2-Gap Companion Processes](
  ../../articles/draft/draft-adversariality-phase-transition-2-gap-companions.md)
