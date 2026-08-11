# Accepted-Anchor Strike Density

**Candidate hypothesis:** Unproved and potentially false.

**Algebraic role:** Exact.

**Empirical status:** NOT EVALUATED AS STATED — this candidate isolates the
accepted-anchor density error used by the fallback #13+#23 decomposition for
#21. Candidate #10 measures a different, post-filter safe-window discrepancy.

## Purpose

Endpoint sampling compares the 2-gap neighborhoods selected by a filter with
all eligible neighborhoods. That comparison controls which struck anchors are
2-gap endpoints, but it does not control how many accepted anchors the filter
strikes.

This candidate supplies one exact scalar component for the separate #13+#23
route. It asks whether the accepted anchors in the local window meet the
incoming residue class with density close enough to `1/r` in the exact
weighted sense required by the collision budget.

The Sampling-Density Recombination property shows that restricted candidate #12's direct weighted
two-harmful-residue norm can bypass this decomposition and is the preferred
scalar interface. Candidate #23 remains a valid fallback if its boundary
arithmetic admits estimates unavailable for the direct route. The Terminal Harmful-Excess Energy property
shows that either assembled aggregate scalar route is terminal at candidate
#21's global allowance.

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

and the resulting weighted strike-error contribution combines with candidate
#13's endpoint-sampling budget to place the actual harmful scalar energy below
candidate #21's global allowance. The Terminal Harmful-Excess Energy property then forces final survival;
candidate #22's harmless-dispersion budget is not an additional premise for
that implication.

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

Using the Endpoint Discrepancy Contraction and Weighted Error Composition properties,
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
The Terminal Harmful-Excess Energy property sharpens its role: once the scalar expression

```math
\left(
\sqrt{\mathcal E_\beta}
+
\sqrt{\mathcal E_D}
\right)^2
+
\mathcal E_\Delta
```

is strictly below `T^2/(2W)`, its bound on the actual harmful-excess energy
already forces `N_m>0`. Thus `mathcal U_*(Q)>0` is itself terminal when backed
by valid #13 and #23 estimates; the additional #22 inequality is unnecessary
for survival in this separated composition.

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

This makes the strike-density estimate noncircular as a component. The
assembled scalar theorem is different: the Terminal Harmful-Excess Energy property proves that it is
terminal at the required global scale. The component may nevertheless be
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

The Endpoint Discrepancy Contraction property proves `2N_i<=A_i`, and hence

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

The Strike-Error Quadratic Variation property expands that quadratic variation exactly. Under candidate #21's
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

The Prime-Square Boundary Formula property performs the square-window endpoint test. It proves

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

The Strike Divisor-Activation Kernel property assigns every divisor of the final modulus an activation time

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

The Strike CRT Lift-Index property splits every newly activated residue by a bounded CRT lift index
and cancels the complete old boundary error. Define

```math
\mathcal M_i(Q)
=
\sum_{e\mid P_i}\mu(e)
\left(
t_{Q,r_i}(e)-t_{Q^2,r_i}(e)
\right),
```

where

```math
t_{x,r_i}(e)
=
\left[
\left\lfloor\frac{x-1}{e}\right\rfloor
\right]_{r_i}^{(0)}.
```

Then

```math
\boxed{
D_i=\frac{\mathcal M_i(Q)}{r_i},
\qquad
\mathcal E_D
=
\sum_i
\frac{w_i}{2r_i(r_i-2)}
\mathcal M_i(Q)^2.
}
```

This is the sharpest current statement of candidate #23's missing theorem.
It requires a weighted mean-square estimate for explicit bounded-index
Möbius transforms; neither bulk density nor the old boundary error remains.

The Strike Summatory Remainder property identifies that transform exactly with a finite-sieve summatory
remainder. If

```math
F_P(X)
=
\#\{1\le n\le X:\gcd(n,P)=1\}
```

and

```math
T_{P,r}(x)
=
F_P(x-1)
-
rF_P\left(\left\lfloor\frac{x-1}{r}\right\rfloor\right),
```

then

```math
\boxed{
\mathcal M_i(Q)
=
T_{P_i,r_i}(Q)-T_{P_i,r_i}(Q^2).
}
```

Therefore the exact denominator-free budget is

```math
\boxed{
\mathcal E_D
=
\sum_i
\frac{w_i}{2r_i(r_i-2)}
\left(
T_{P_i,r_i}(Q)-T_{P_i,r_i}(Q^2)
\right)^2.
}
```

This classification is important: the lift-index formula does not reveal an
additional elementary cancellation. It is an exact coordinate rewrite of
the original dilation discrepancy. The remaining theorem is a weighted
mean-square bound for these dilation remainders at the two prime-square
endpoints, with both the modulus and the dilation prime changing by layer.

The Cross-Layer CRT Orthogonality property proves that the centered layer strike observables are pairwise
orthogonal on the complete final CRT period `R=P_m`. In particular,

```math
\boxed{
\sum_i
\frac{r_i^2}{
\frac{\varphi(P_i)}{P_i}(r_i-1)
}
D_i^2
\le
|I|R
}
```

when the interval `I` has length at most `R`. This is a genuine cross-layer
mean-square theorem, but it has the wrong normalization for the safe-window
problem: the right side contains the full final primorial. Thus ordinary
Bessel composition of the complete-period CRT orthogonality does not prove
candidate #23. A useful theorem must localize this orthogonality or add a new
averaging variable.

The Localized-Layer Gram Matrix property performs that localization exactly. On the actual interval, the
layer Gram matrix is

```math
\boxed{
G_{ii}
=
A_i\frac{r_i-1}{r_i^2}
+
\left(1-\frac2{r_i}\right)D_i,
}
```

```math
\boxed{
G_{ij}
=
-\frac{D_{\max(i,j)}}{r_{\min(i,j)}}
\qquad(i\ne j).
}
```

If `C=diag(c_i)` with
`c_i=w_i r_i/(2(r_i-2))`, then

```math
\boxed{
\mathcal E_D
\le
|I|\lambda_{\max}\left(C^{1/2}GC^{1/2}\right).
}
```

This removes the final-primorial normalization and turns the remaining
problem into a local finite spectral estimate. However, bounding the largest
eigenvalue by the trace is exactly the sum of the separate per-layer Cauchy
bounds. Progress now requires signed spectral cancellation in the explicit
off-diagonal discrepancies, not generic positive-semidefinite matrix algebra.

The First-Deletion Variance Identity property partitions the initial accepted anchors by their first deleting
layer. If `n_k` is the size of class `k`, including `n_m=A_m` for final
survivors, and `v_k` is its centered strike vector, then

```math
\boxed{
D=\sum_kn_kv_k,
\qquad
G=\sum_kn_kv_kv_k^T.
}
```

For the candidate weights `C=diag(c_i)`, this yields the exact variance
identity

```math
\boxed{
\mathcal E_D
=
A_0\operatorname{tr}(CG)
-
\sum_{k<\ell}
n_kn_\ell
\left\lVert C^{1/2}(v_k-v_\ell)\right\rVert^2.
}
```

Thus deletion-time dispersion is an exact negative correction to generic
Cauchy. But if only `n_k>=0` and `sum n_k=A_0` are known, the sharp abstract
envelope is

```math
\boxed{
\mathcal E_D
\le
A_0^2\max_k\left\lVert C^{1/2}v_k\right\rVert^2,
}
```

attained in the abstract model by concentrating all mass in one deletion
class. First-deletion geometry therefore helps only if new arithmetic proves
that the actual local class counts are dispersed.

The Active Two-Class Variance property strength-tests the compulsory part of that dispersion. At every
layer,

```math
\boxed{
D_i^2
=
A_iG_{ii}
-
H_iA_{i+1}.
}
```

Thus the guaranteed separation between class `i` and all later deletion
classes contributes `H_iA_(i+1)`, but retaining only this term exactly
rearranges the unknown `D_i^2`. It is not an independent estimate. A useful
first-deletion argument must retain the additional intermediate-coordinate
distances from the First-Deletion Variance Identity property or establish arithmetic bounds for the actual
class masses.

The First-Deletion Reindexing property reindexes all of those additional distances and closes the pure
first-deletion algebra. The complete deletion-vector variance is

```math
\boxed{
\sum_i c_i
\left[
H_iA_{i+1}
+
(A_0-A_i)G_{ii}
\right].
}
```

Substitution into the First-Deletion Variance Identity property, followed by the Active Two-Class Variance property, returns exactly
`sum_i c_iD_i^2`. Therefore neither the compulsory distance nor the full
triangular distance matrix supplies an independent upper bound. The
first-deletion representation becomes useful only after adding arithmetic
constraints on the actual class counts or an external averaging theorem.

The Sampling-Density Recombination property supplies an alternative to proving #23 separately. If
`delta_0` and `delta_(-2)` are the two harmful 2-gap-start residue deviations,
then

```math
b=\delta_0+\delta_{-2},
\qquad
\Delta=\delta_0-\delta_{-2}.
```

The decomposition `b=H beta+2N epsilon` is exactly a split of this same
two-class residue error into candidate #13 sampling and candidate #23 strike
density. A direct joint bound for `delta_0,delta_(-2)` can therefore bypass
the separate #23 budget and retain correlation lost by Minkowski. This is the
preferred restricted form of candidate #12. The Terminal Harmful-Excess Energy property proves that success
for either representation at candidate #21's global allowance already forces
final survival.

## What Would Prove It

Any of the following could supply the required input:

1. a sharp upper bound for the largest eigenvalue of the Localized-Layer Gram Matrix property's localized
   Gram matrix that improves substantially on its trace;
2. a quadratic-variation bound for the exact adjacent boundary-error
   recurrence;
3. a discrepancy estimate for accepted anchors against the single incoming
   residue class, normalized by `A_i` rather than by a final survivor count;
4. a weighted covariance bound between earlier acceptance and the incoming
   divisibility indicator;
5. a direct aggregate estimate for
   `sum_i w_i N_i^2 epsilon_i^2` that fits the displayed allowance, even when
   no useful pointwise bound holds.

The first option must add information beyond the exact recurrence. Algebraic
rearrangement of its weighted square has already been exhausted by property
#38. The second and third options must add cancellation beyond the Prime-Square Boundary Formula property's
exact residue representation; favorable sign is refuted.

## Limitation

No universal bound of the required strength is currently proved. The exact
accepted-strike formula for the immediate next safe window gives useful
arithmetic structure, but it does not automatically extend to every later
layer of a conditioned chain. Complete-period uniformity also does not imply
local-window strike density.

The candidate isolates a noncircular fallback component of a terminal scalar
theorem; it does not establish that the component is easier to bound than the
direct restricted #12 norm. Candidate #22's harmless-class dispersion is a
separate distribution question, but it is not required for survival after the
assembled scalar allowance is positive.
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
- [Weighted harmful-excess energy is already terminal](
  ../properties/sieve-sequence/weighted-harmful-excess-energy-is-terminal.md
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
- [Accepted-strike CRT lift-index transform](
  ../properties/sieve-sequence/accepted-strike-crt-lift-index-transform.md
  )
- [Accepted-strike summatory coprime remainder](
  ../properties/sieve-sequence/accepted-strike-summatory-coprime-remainder.md
  )
- [Accepted-strike cross-layer CRT orthogonality](
  ../properties/sieve-sequence/accepted-strike-cross-layer-crt-orthogonality.md
  )
- [Accepted-strike localized layer Gram matrix](
  ../properties/sieve-sequence/accepted-strike-localized-layer-gram-matrix.md
  )
- [Accepted-strike first-deletion variance identity](
  ../properties/sieve-sequence/accepted-strike-first-deletion-variance-identity.md
  )
- [Accepted-strike active two-class variance identity](
  ../properties/sieve-sequence/accepted-strike-active-two-class-variance-identity.md
  )
- [Accepted-strike first-deletion coordinate reindexing](
  ../properties/sieve-sequence/accepted-strike-first-deletion-coordinate-reindexing.md
  )
- [Endpoint sampling and strike density recombine into harmful residues](
  ../properties/sieve-sequence/endpoint-sampling-strike-density-harmful-residue-bridge.md
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
