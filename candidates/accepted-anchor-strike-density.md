# Accepted-Anchor Strike Density

**Candidate hypothesis:** Unproved and potentially false.

**Algebraic role:** Exact.

**Empirical status:** NOT EVALUATED AS STATED — this candidate isolates the
accepted-anchor density error required by candidates #13 and #21. Candidate
#10 measures a different, post-filter safe-window discrepancy.

## Purpose

Endpoint sampling compares the 2-gap neighborhoods selected by a filter with
all eligible neighborhoods. That comparison controls which struck anchors are
2-gap endpoints, but it does not control how many accepted anchors the filter
strikes.

This candidate supplies that missing scalar input. It asks whether the
accepted anchors in the local window meet the incoming residue class with
density close enough to `1/r` in the exact weighted sense required by the
collision budget.

## Setup

At layer `i` of a conditioned chain, let `r_i` be the incoming prime. Let
`P_i` be the accepted anchors eligible for the complete local neighborhoods
used by candidate #13, and let

```math
A_i=|P_i|.
```

Let `D_i` be the anchors struck by the actual filter and write

```math
H_i=|D_i|.
```

Let `S_i` be the complete 2-gap starts in the same boundary convention and
write

```math
N_i=|S_i|.
```

When `A_i>0`, define the accepted-strike density error

```math
\boxed{
\varepsilon_i
=
\frac{H_i}{A_i}
-
\frac1{r_i}.
}
```

The exact uncentered discrepancy is equivalently

```math
H_i-\frac{A_i}{r_i}=A_i\varepsilon_i.
```

## Candidate Hypothesis

For infinitely many future heads `Q`, the conditioned chain admits
nonnegative bounds `xi_i` such that

```math
\boxed{
|\varepsilon_i|\le\xi_i
}
```

and the resulting weighted strike-error contribution fits inside candidate
#21 after the independently obtained harmless-dispersion and endpoint-sampling
budgets are inserted.

The preferred theorem is an aggregate bound on the actual errors, rather than
a pointwise discrepancy requirement:

```math
\boxed{
\sum_i
w_i
\frac{r_i}{2(r_i-2)}
\left(2N_i\varepsilon_i\right)^2
\le
\mathcal E_{\mathrm{strike}}(Q).
}
```

Here `mathcal E_strike(Q)` must be small enough that the complete allowance in
the section below remains positive. This weighted statement permits an
exceptional layer when its later-survival weight or its current 2-gap
population is small.

## Exact Composition With Candidate #13

Define candidate #13's unsigned endpoint-sampling bias

```math
\beta_i
=
\frac{K_i}{H_i}
-
\frac{2N_i}{A_i}
```

when `H_i>0`, where `K_i` is the number of destroyed complete 2-gaps. Define
the harmful excess

```math
b_i
=
K_i-\frac{2N_i}{r_i}.
```

Direct substitution gives the proved exact bridge

```math
\boxed{
b_i
=
H_i\beta_i
+
2N_i\varepsilon_i.
}
```

If candidate #13 supplies

```math
|\beta_i|\le\eta_i,
\qquad
|\Delta_i|\le H_i\eta_i,
```

then candidate #23 supplies

```math
\boxed{
|b_i|
\le
H_i\eta_i+2N_i\xi_i.
}
```

The case `H_i=0` needs no division by `H_i`: then `K_i=Delta_i=0`, while the
identity for `b_i` follows directly from
`epsilon_i=-1/r_i`.

## Exact Allowance Consumed By Candidate #21

Let

```math
W=\sum_iw_i,
\qquad
T=N_0A_{0,m}.
```

The orthogonal energy identity is

```math
V_i
=
U_i
+
\frac{r_i}{2(r_i-2)}b_i^2
+
\frac12\Delta_i^2.
```

Let

```math
D_i
=
H_i-\frac{A_i}{r_i}.
```

Using property #36's contraction and property #37's weighted composition,
define

```math
\mathcal E_\beta
=
\sum_iw_i
\frac{r_i}{2(r_i-2)}
H_i^2\eta_i^2,
\qquad
\mathcal E_D
=
\sum_iw_i
\frac{r_i}{2(r_i-2)}
D_i^2,
```

```math
\mathcal E_\Delta
=
\frac12\sum_iw_iH_i^2\eta_i^2.
```

Then candidate #21 is implied by

```math
\boxed{
\sum_iw_iU_i
+
\left(
\sqrt{\mathcal E_\beta}
+
\sqrt{\mathcal E_D}
\right)^2
+
\mathcal E_\Delta
<
\frac{T^2}{2W}.
}
```

Equivalently, candidate #22 receives the exact remaining allowance

```math
\boxed{
\mathcal U_*(Q)
=
\frac{T^2}{2W}
-
\left(
\sqrt{\mathcal E_\beta}
+
\sqrt{\mathcal E_D}
\right)^2
-
\mathcal E_\Delta.
}
```

This is the precise interface between candidates #13, #22, #23, and #21.

## Why This Is Not Candidate #10

Candidate #10 compares a post-filter count in a safe window with a scaled
count from an earlier stage. The present quantity compares the number of
accepted anchors struck at one layer with `A_i/r_i`.

The two statements use different populations and different denominators.
Deriving one from the other would require a new lemma; similarity of
discrepancy notation is not such a derivation.

## Noncircularity Audit

The density error is defined even if no 2-gap survives the complete chain. It
does not assume `N_m>0`, and the aggregate statement can be normalized by the
initial main term `T`, not by the unknown final population.

This makes the candidate noncircular as a component. It may nevertheless be
parity-hard. In particular, a proof that first divides by a positive lower
bound for a late conditioned 2-gap population would reintroduce the same wall
that blocked the hereditary forms of candidates #14 and #19.

## Exact Reduction To Boundary Cancellation

For all accepted anchors in an integer interval `[L,U)`, let `P` be the
squarefree product of the old filters and let `r` be the incoming prime. The
proved boundary decomposition gives

```math
\boxed{
H-\frac Ar
=
\left(\ell_r-\frac\ell r\right)\frac{\varphi(P)}P
+
E_P(L_r,U_r)
-
\frac1rE_P(L,U),
}
```

where

```math
L_r=\left\lceil\frac Lr\right\rceil,
\qquad
U_r=\left\lceil\frac Ur\right\rceil,
\qquad
\ell_r=U_r-L_r,
```

and `E_P` is the centered signed inclusion--exclusion boundary sum.

Thus the expected bulk density `1/r` is already exact. Candidate #23 reduces
to controlling the difference of two Möbius boundary sums, preferably after
the chain weights are inserted.

Bounding the divisor summands independently gives only

```math
|E_P(L,U)|<2^{\omega(P)}-1,
```

which is exponentially too large. Any successful proof must use signed
cancellation, correlation between the original and scaled boundary sums, or
cross-layer averaging. The identity applies directly to all accepted anchors;
candidate #13's complete-neighborhood convention additionally requires an
explicit endpoint correction.

For a fixed window along the conditioned chain, define

```math
E_i
=
A_i
-
\ell\frac{\varphi(P_i)}{P_i}.
```

The proved chain recurrence is

```math
\boxed{
H_i-\frac{A_i}{r_i}
=
\left(1-\frac1{r_i}\right)E_i-E_{i+1},
}
```

so

```math
\boxed{
\varepsilon_i
=
\frac{
\left(1-\frac1{r_i}\right)E_i-E_{i+1}
}{A_i}.
}
```

The signed discrepancies telescope under the natural one-anchor survival
weights. Candidate #21 instead requires a weighted sum of their squares with
two-endpoint survival weights.

Property #36 proves `2N_i<=A_i`, and hence

```math
\left|2N_i\varepsilon_i\right|
\le
\left|H_i-\frac{A_i}{r_i}\right|.
```

Thus a denominator-free sufficient #23 target is

```math
\boxed{
\sum_i
w_i
\frac{r_i}{2(r_i-2)}
\left(
\left(1-\frac1{r_i}\right)E_i-E_{i+1}
\right)^2,
}
```

with a bound small enough to fit candidate #21.

More precisely, for arbitrary `lambda_i>0`, candidate #13's
`|beta_i|\le eta_i` and Young's inequality give

```math
\boxed{
b_i^2
\le
(1+\lambda_i)H_i^2\eta_i^2
+
\left(1+\frac1{\lambda_i}\right)
\left(
\left(1-\frac1{r_i}\right)E_i-E_{i+1}
\right)^2.
}
```

This removes both the endpoint-to-anchor denominator and the cross term
between #13 and #23. Proving the remaining square sum requires a
quadratic-variation or adjacent-correlation estimate for `E_i`; the linear
telescope alone is insufficient.

Property #38 expands that quadratic variation exactly. Under candidate #21's
weights,

```math
\mathcal E_D
+
c_0q_0(1-q_0)E_0^2
```

is a sum of nonnegative adjacent-variation and terminal terms plus strictly
positive interior multiples of `E_i^2`. Consequently, summation by parts does
not furnish the needed upper bound. A successful #23 proof now requires new
arithmetic control of the square-window boundary errors themselves.

Property #39 performs the square-window endpoint test. It proves

```math
E_P(Q,Q^2)
=
\sum_{\substack{d\mid P\\d>1}}
\mu(d)
\frac{[Q]_d-[Q^2]_d}{d}.
```

Every divisor `d|(Q-1)` contributes zero, but the remaining terms have no
universal sign. In the fixed window `[19,19^2)`, the exact boundary error is
negative for `P=2310` and positive after adjoining filter `13`, when
`P=30030`. Thus primality of `Q`, universal sign, and sign preservation do not
prove #23.

## Divisor Activation-Shell Reduction

Property #48 assigns every divisor of the final modulus an activation time

```math
\tau(d)
=
\min\{t:d\mid P_t\}.
```

If

```math
Z_t
=
\sum_{\substack{d\mid P_m\\d>1\\\tau(d)=t}}
\mu(d)
\frac{[Q]_d-[Q^2]_d}{d},
```

then the accepted-strike discrepancy is exactly

```math
\boxed{
D_i
=
-\frac1{r_i}\sum_{t=0}^{i}Z_t
-Z_{i+1}.
}
```

Consequently,

```math
\boxed{
\mathcal E_D
=
\sum_{t,u=0}^{m}
\mathcal K(t,u)Z_tZ_u,
}
```

where `mathcal K` is an explicit `(m+1) by (m+1)` positive-semidefinite
kernel with nonnegative entries.

This collapses the apparent exponential divisor-pair problem to a weighted
norm of `m+1` signed activation-shell sums. The chain weights do not create
kernel sign cancellation; the remaining arithmetic is cancellation inside
the `Z_t`, or a direct bound for their vector in the `mathcal K` norm.

## What Would Prove It

Any of the following could supply the required input:

1. a quadratic-variation bound for the exact adjacent boundary-error
   recurrence;
2. a discrepancy estimate for accepted anchors against the single incoming
   residue class, normalized by `A_i` rather than by a final survivor count;
3. a weighted covariance bound between earlier acceptance and the incoming
   divisibility indicator;
4. a direct aggregate estimate for
   `sum_i w_i N_i^2 epsilon_i^2` that fits the displayed allowance, even when
   no useful pointwise bound holds.

The first option must add information beyond the exact recurrence. Algebraic
rearrangement of its weighted square has already been exhausted by property
#38. The second and third options must add cancellation beyond property #39's
exact residue representation; favorable sign is refuted.

## Limitation

No universal bound of the required strength is currently proved. The exact
accepted-strike formula for the immediate next safe window gives useful
arithmetic structure, but it does not automatically extend to every later
layer of a conditioned chain. Complete-period uniformity also does not imply
local-window strike density.

The candidate isolates the missing scalar theorem; it does not establish that
the theorem is easier than harmless-class dispersion.
The general recurrence, its squared summation by parts, and the simplest
prime-square endpoint sign mechanisms have now been exhausted. Continuing
requires a new mean-square or Möbius-residue cancellation theorem.

## Established Inputs

- [Endpoint density contracts accepted-strike discrepancy](
  ../properties/sieve-sequence/endpoint-density-contracts-strike-discrepancy.md
  )
- [Weighted composition of endpoint and strike-density errors](
  ../properties/sieve-sequence/weighted-scalar-error-composition.md
  )
- [Accepted-strike error is a positive quadratic variation](
  ../properties/sieve-sequence/accepted-strike-quadratic-variation.md
  )
- [Prime-square window boundary residue formula](
  ../properties/sieve-sequence/prime-square-window-boundary-residue-formula.md
  )
- [Accepted-strike divisor activation kernel](
  ../properties/sieve-sequence/accepted-strike-divisor-activation-kernel.md
  )
- [Accepted-strike density as a Möbius boundary sum](
  ../properties/sieve-sequence/accepted-strike-density-boundary-decomposition.md
  )
- [Exact accepted local filter strikes](
  ../properties/sieve-sequence/exact-accepted-local-filter-strikes.md
  )
- [Two endpoint observables separate harmful excess and imbalance](
  ../properties/sieve-sequence/two-endpoint-observables-separate-harmful-excess-and-imbalance.md
  )
- [Orthogonal residue-energy decomposition after a two-class filter](
  ../properties/sieve-sequence/orthogonal-residue-energy-decomposition-after-two-class-filter.md
  )
- [Uniform local observable sampling](
  uniform-local-observable-sampling.md
  )
- [Conditioned harmless-class collision energy](
  conditioned-harmless-class-collision-energy.md
  )
- [Cumulative weighted collision budget](
  cumulative-weighted-collision-budget.md
  )
