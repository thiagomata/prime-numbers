# Seven-Layer Capacity Floor

**Candidate hypothesis:** Partially proved. The early inequality
`rho(Q,7)>1` is proved for every integer `Q>=17`; the later-layer lower
envelope remains unproved and potentially false.

**Conditional implication:** Mathematically proved from the local-count
threshold and candidate #14's one-layer capacity theorem.

**Algebraic status:** The exact modulo-30 proof establishes the proposed base
floor without an asymptotic or distribution assumption.

**Empirical status:** REINFORCED AT FINITE SCALE — across 53 future heads and
1,837 conditioned layers, every capacity ratio is above `1` and every chain
minimum occurs at `r=7`. No universal later-layer claim is proved.

## Purpose

The proved local-count theorem converts candidate #14's qualitative close-pair
obligation into an exact population threshold. This candidate asks whether the
weakest normalized capacity in a conditioned future-window chain is controlled
by the early `r=7` layer, whose population is exactly periodic modulo `30`.

If true, the difficult all-layer density obligation would reduce to an early
finite-period calculation plus one chain-wide lower-envelope theorem.

## Capacity Ratio

Fix a future prime head `Q`. At a conditioned layer with incoming prime `r`,
let

```math
W_Q=[Q,Q^2)
```

and let `G_r(W_Q)` count the complete 2-gaps present before filter `r`, after
every smaller filter in the chain has been installed. Define

```math
L_Q=Q^2-Q-3
```

and

```math
\rho(Q,r)
=
\frac{(G_r(W_Q)-1)(2r-2)}{L_Q}.
```

The strict inequality `rho(Q,r)>1` is equivalent to

```math
(G_r(W_Q)-1)(2r-2)>Q^2-Q-3.
```

By the proved local-count theorem, this forces two complete 2-gaps whose
enclosing interval is shorter than `2r`.

## Candidate Hypothesis

The minimally sufficient form is that for infinitely many future prime heads
`Q`, every prime layer `5<=r<Q` satisfies

```math
\rho(Q,r)\ge\rho(Q,7)>1.
```

The stronger empirical target is eventual uniformity:

```math
\boxed{
\text{For every sufficiently large prime }Q
\text{ and every prime }5\le r<Q,\quad
\rho(Q,r)\ge\rho(Q,7)>1.
}
```

The hypothesis is a lower-envelope statement, not stepwise monotonicity.
Individual transitions may decrease `rho` as long as the chain never falls
below its `r=7` floor.

## Equivalent Unnormalized Form

For one fixed `Q`, the denominator `L_Q` is constant across the chain.
Therefore

```math
\rho(Q,r)\ge\rho(Q,7)
```

is equivalent to

```math
\boxed{
(r-1)(G_r(W_Q)-1)
\ge
6(G_7(W_Q)-1).
}
```

This form isolates the proposed invariant without division.

## Why It Is Sufficient

Suppose one future head `Q` satisfies the candidate. Then every layer has

```math
\rho(Q,r)>1.
```

The local-count theorem gives

```math
G_r(W_Q)
\ge
\left\lfloor
\frac{Q^2-Q-3}{2r-2}
\right\rfloor+2,
```

so candidate #14's `k=2` interval premise holds at every layer. At least one
2-gap survives each filter in the conditioned chain. After the last prime
below `Q` is installed, a surviving complete 2-gap in `[Q,Q^2)` is square-safe
and certifies a twin-prime pair.

Consequently, infinitely many heads satisfying the candidate produce
infinitely many twin-prime certificates.

## The Proved r=7 Floor

Immediately before filter `7`, only filters `2`, `3`, and `5` are installed.
The complete 2-gap starts are exactly the residue classes

```math
11,17,29\pmod{30}.
```

Writing the number of eligible integer starts as

```math
Q^2-Q-2=30k+t,
\qquad 0\le t<30,
```

gives `G_7(W_Q)>=3k`. For `Q>=17`, `k>=9`, and therefore

```math
\begin{aligned}
12(G_7(W_Q)-1)-(Q^2-Q-3)
&\ge 6k-t-11\\
&\ge14\\
&>0.
\end{aligned}
```

Hence

```math
\boxed{\rho(Q,7)>1}
```

for every integer `Q>=17`. The exact derivation is recorded in
[Exact Seven-Layer Capacity Floor](
../properties/sieve-sequence/exact-seven-layer-capacity-floor.md
).

The same periodic count also gives the limiting scale

```math
\rho(Q,7)\longrightarrow\frac65.
```

The limit is descriptive only; the finite quotient/remainder inequality above
is the proof. Neither result controls later conditioned layers.

## Empirical Falsifiers

For each measured future head, compute

```math
m(Q)=\min_{5\le r<Q}\rho(Q,r)
```

and an attaining layer

```math
r_{\min}(Q)\in
\operatorname*{arg\,min}_{5\le r<Q}\rho(Q,r).
```

The measurements have three immediate interpretations:

1. `m(Q)<=1` means the count theorem cannot certify that chain at its weakest
   layer.
2. `m(Q)>1` but `r_min(Q)!=7` refutes the `r=7` lower-envelope statement for
   that head while leaving candidate #14 itself possible.
3. A downward trend of `m(Q)` toward `1` weakens the proposed eventual uniform
   form; a stable margin above `1` strengthens it empirically but does not prove
   it.

A finite exceptional head does not refute the minimally sufficient
"infinitely many `Q`" form. It does refute any claim that the floor holds for
every measured head or from a stated finite threshold onward.

## Empirical Results

The expanded in-memory lineage sweep covers every prime head `17<=Q<=251`
together with

```text
307, 401, 503, 701, 997.
```

Its 53 heads and 1,837 applicable layers give:

```text
0 layers with rho(Q,r) <= 1
0 heads with rho(Q,r) < rho(Q,7) at any layer
53/53 chain minima attained at r=7
```

The observed floor ranges from approximately `1.132743` to `1.199989`, and
the exact period-30 calculation shows `rho(Q,7)` converging to `6/5`.

This is unusually coherent finite evidence for the proposed lower envelope,
but it does not prove its preservation under arbitrarily many conditioned
filters. Definitions, validation gates, selected-head values, and falsifiers
are recorded in
[Empirical Evidence for Capacity-Density Candidates](
../empirical/sieve-sequence/capacity-density-candidates.md
).

## Algebraic Bridge To Candidate #24

Property #75 proves that this candidate's one-layer threshold has a second
consequence beyond close-pair survival. For

```math
B_r
=
\left\lfloor
\frac{Q^2-Q-3}{6r}
\right\rfloor+1,
```

the threshold and the already-installed filter `5` imply

```math
2B_r\le G_r(W_Q)\le(r-2)B_r.
```

Therefore property #74's population slack is maximal:

```math
\sigma_r=2B_r,
\qquad
X_r\ge B_r^2.
```

At the proved base layer `r=7`, property #76 inserts this floor into the
native-period Bessel normalization. It proves

```math
e_2
\ge
\left(
\frac{7B_7^2}{30}
-((Q^2-Q-2)\bmod210)
\right)_+
\ge1
```

for every integer `Q>=36`. Thus the established base case already gives a
strict improvement of candidate #24's all-capacity energy envelope for every
future prime head `Q>=37`.

This does not prove the later-layer lower envelope stated by this candidate,
and strict energy-envelope improvement does not by itself prove survival. The
remaining #24 comparison is whether the quantified gain clears its extinction
deficit.

## Limitation

The candidate is a conditioned short-window density theorem. Exact
complete-period counts do not imply it, and the period-30 calculation at
`r=7` does not propagate through later filters.

Proving the lower envelope may require a cumulative discrepancy estimate,
residue-balance theorem, or another invariant controlling how quickly
`G_r(W_Q)` can fall relative to the growth of `r`. Such a theorem would supply
the missing localization input rather than follow from the global cluster
recurrence alone.

## Related

- [A local count forces the k=2 shot-capacity premise](
  ../properties/sieve-sequence/local-count-forces-k2-shot-capacity.md
  ) — proves that `rho(Q,r)>1` is sufficient at one layer.
- [Exact seven-layer capacity floor](
  ../properties/sieve-sequence/exact-seven-layer-capacity-floor.md
  ) — proves the base inequality `rho(Q,7)>1` for every integer `Q>=17`.
- [Seven-layer density floor maximizes capacity width](
  ../properties/sieve-sequence/seven-layer-density-floor-maximizes-capacity-width.md
  ) — converts this candidate's count threshold into maximal population
  slack for candidate #24.
- [Seven-layer floor forces native overflow](
  ../properties/sieve-sequence/seven-layer-floor-forces-native-overflow.md
  ) — proves unconditional positive overflow at the native cut after filter
  `7` for every future prime head `Q>=37`.
- [Hereditary shot-spacing capacity](
  hereditary-shot-spacing-capacity.md
  ) — candidate #14, whose full chain premise follows from this candidate.
- [Local pattern-residue balance](
  local-pattern-residue-balance.md
  ) — a possible mechanism for controlling conditioned population loss.
