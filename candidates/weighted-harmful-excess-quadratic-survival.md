# Weighted Harmful-Excess Quadratic Survival

**Candidate hypothesis:** Unproved and potentially false.

**Conditional implication:** Mathematically proved.

**Scope:** Complete conditioned chain in one fixed future-head window.

**Quantifier:** Proposed for infinitely many future heads.

**Role:** Terminal survival theorem.

**Empirical status:** NOT EVALUATED — this candidate is an algebraic
consequence of property #66 and is not a request for additional data.

## Purpose

Candidate #21 controls the full residue collision energy. Its orthogonal
decomposition pays for three nonnegative quantities:

1. total harmful excess;
2. left/right harmful-class imbalance;
3. harmless-class dispersion.

Only the total number of destroyed 2-gaps appears in the exact population
recurrence. Candidate #24 therefore keeps only the total harmful-excess
square and uses its natural dual weight sum. It is strictly weaker than
candidate #21 and is the leanest current quadratic certificate for final
survival.

The candidate remains terminal: proving its hypothesis for infinitely many
future heads would already prove a positive final 2-gap-start population for
those heads.

## Setup

Fix a future prime head `Q` and a nonempty conditioned chain

```math
5\le r_0<r_1<\cdots<r_{m-1}<Q.
```

Let `S_i` be the complete 2-gap starts in the stated square window immediately
before filter `r_i`, and write

```math
N_i=|S_i|.
```

Let `N_m` be the actual final survivor count. Define

```math
a_i=1-\frac2{r_i},
\qquad
A_{u,v}=\prod_{j=u}^{v-1}a_j,
```

```math
w_i=A_{i+1,m},
\qquad
w_{-1}=A_{0,m}.
```

The final multiplicative main term is

```math
T=N_0A_{0,m}.
```

If

```math
K_i=N_i-N_{i+1}
```

is the number of 2-gaps destroyed by filter `r_i`, define the signed total
harmful excess

```math
b_i
=
K_i-\frac{2N_i}{r_i}
=
a_iN_i-N_{i+1}.
```

The weighted harmful-excess energy is

```math
\boxed{
E_b
=
\sum_{i=0}^{m-1}
w_i
\frac{r_i}{2(r_i-2)}
b_i^2.
}
```

Its natural dual weight sum is

```math
\boxed{
W_-
=
\sum_{i=0}^{m-1}w_{i-1}.
}
```

Because the chain is nonempty and every weight is positive, `W_->0`.

## Candidate Hypothesis

For infinitely many future heads `Q`, suppose the complete conditioned chain
satisfies

```math
\boxed{
E_b
<
\frac{T^2}{2W_-}.
}
```

This statement names one fixed population and one complete conditioned chain.
It is not a one-layer ellipse, a complete-period average, or an empirical
claim.

## Why The Candidate Is Sufficient

Property #25 proves the exact signed conservation law

```math
\sum_iw_ib_i=T-N_m.
```

Property #66 applies weighted Cauchy--Schwarz and proves

```math
\boxed{
E_b
\ge
\frac{(T-N_m)^2}{2W_-}.
}
```

If `N_m=0`, then

```math
E_b
\ge
\frac{T^2}{2W_-},
```

contradicting the candidate hypothesis. Therefore

```math
\boxed{N_m>0.}
```

After the conditioned chain has installed every missing prime below `Q`, a
2-gap start in the eligible square-safe window certifies a twin-prime pair.
Thus the candidate holding for infinitely many future heads would yield
infinitely many square-safe certificates.

The implication is mathematically proved. The open theorem is that the strict
energy inequality holds for infinitely many heads.

## Sharpness Of The Quadratic Threshold

Let

```math
c_i=\frac{r_i}{2(r_i-2)}.
```

The dual sum in weighted Cauchy is

```math
\sum_i\frac{w_i}{c_i}
=
2\sum_iw_{i-1}
=
2W_-.
```

Equality in Cauchy is possible over real layer errors when `c_ib_i` is
constant. Therefore

```math
\frac{T^2}{2W_-}
```

is the sharp threshold obtainable from only:

1. the signed conservation law;
2. the quadratic energy `E_b`;
3. no additional arithmetic restriction on the layer errors.

A larger allowance cannot force survival from those inputs alone. Improving
the candidate further requires new information about which harmful excess
profiles an actual sieve chain can realize.

## Normalized-Population Form

Put

```math
P_i=A_{0,i},
\qquad
z_i=\frac{N_i}{P_i}.
```

Property #66 proves the exact identity

```math
E_b
=
\frac{P_m}{2}
\sum_{i=0}^{m-1}
P_i(z_i-z_{i+1})^2.
```

Since `T=N_0P_m`, the candidate hypothesis is equivalently

```math
\boxed{
\sum_{i=0}^{m-1}
P_i(z_i-z_{i+1})^2
<
\frac{N_0^2P_m}{W_-}.
}
```

The missing theorem is therefore a bound on the weighted quadratic variation
of the realized local 2-gap population relative to its multiplicative
survival profile.

This form uses the vocabulary distinction between the actual population
`N_i` and the multiplicative profile `P_i`. It does not assume that the actual
population follows that profile.

Property #67 proves that the scalar constraints visible in this form are not
enough. For every fixed prime chain, the Cauchy-equality extinction profile
can be scaled so that all `N_i` and `K_i=N_i-N_{i+1}` are nonnegative
integers and the populations decrease strictly to zero. Therefore
integrality, monotonicity, and the exact population recurrence do not improve
the threshold. The missing theorem must distinguish actual CRT deletion
profiles from those abstract integral schedules.

## Strict Weakening Of Candidate #21

Candidate #21 asks for the full weighted residue energy

```math
\sum_iw_iV_i
<
\frac{T^2}{2W},
\qquad
W=\sum_iw_i.
```

The orthogonal decomposition gives

```math
E_b
\le
\sum_iw_iV_i.
```

Also,

```math
w_{i-1}=a_iw_i<w_i,
```

so

```math
W_-<W
```

and hence

```math
\frac{T^2}{2W}
<
\frac{T^2}{2W_-}
```

when `T>0`.

Therefore candidate #21 implies candidate #24. Candidate #24 ignores both

```math
\frac12\sum_iw_i\Delta_i^2
```

and

```math
\sum_iw_iU_i,
```

and permits more harmful-excess energy. The converse does not follow even at
the inequality level: imbalance or harmless dispersion may be arbitrarily
large while `E_b` stays small.

Candidate #24 is therefore strictly weaker as an algebraic sufficient
condition. It replaces #21 as the top quadratic survival target.

## Relation To Other Candidates

- **#12 Local pattern-residue balance:** its restricted weighted two-harmful
  norm contains `E_b` but also pays for harmful-class imbalance. Candidate #24
  asks only for the total harmful-excess direction used by population
  survival.
- **#13 plus #23:** these candidates decompose `b_i` into endpoint sampling
  and accepted-strike density. They remain a fallback way to estimate `E_b`,
  but generic Minkowski composition can lose correlation.
- **#19 Sixfold harmful capacity:** supplies one-layer absolute bounds on the
  two harmful counts. Those bounds do not compose automatically into the
  candidate #24 quadratic variation.
- **#21 Cumulative weighted collision budget:** strictly stronger because it
  controls full residue energy with the smaller `W` allowance.
- **#22 Harmless-class energy:** independent of candidate #24 and unnecessary
  for its survival implication.

## What Would Prove It

A proof must establish the strict conditioned-chain inequality for an
unbounded family of future heads. Viable theorem shapes include:

1. an arithmetic restriction on the joint harmful counts
   `c_{i,0}+c_{i,-2}` across incoming primes;
2. a cross-layer estimate showing that large harmful excess cannot occur at
   too many heavily weighted layers;
3. a coefficient-sensitive estimate for the two harmful residue classes that
   avoids paying for harmless dispersion and left/right imbalance;
4. a localized interval-correlation inequality for the centered paired
   observables that replaces the complete-period CRT scale by a short-window
   scale.

The proof must not:

- normalize by an unproved positive final population;
- sum one-layer ellipse allowances;
- replace the actual conditioned populations by the multiplicative profile;
- rely only on integrality or monotonicity of the population sequence;
- present another exact rearrangement as an upper bound;
- apply black-box Bessel to complete-period CRT orthogonality;
- use additional finite data as proof evidence.

## Stability-Gap Extension

Property #68 proves the exact extinction identity

```math
E_b
=
\frac{T^2}{2W_-}
+
\sum_iw_i\frac1{2a_i}
\left(
b_i-b_i^\star
\right)^2.
```

This exposes a second, optional arithmetic interface. If first-hit CRT
geometry proves that every realizable extinct chain has stability remainder
at least `Gamma(Q)>0`, then

```math
E_b
<
\frac{T^2}{2W_-}
+\Gamma(Q)
```

would also certify survival.

Property #69 supplies the first proved instance of this interface from the
post-filter-3 harmful-class capacities. It defines

```math
\Gamma_{\mathrm{cap}}
=
\max_i
\frac{
\left(
K_i^\star-C_i
\right)_+^2
}{
D_i
},
```

where `K_i^star` is the Cauchy minimizer's deletion mass, `C_i` is the proved
total capacity of the two harmful classes, and `D_i` is the exact dual norm of
the layer-`i` deletion functional. Every extinct chain satisfies

```math
E_b
\ge
\frac{T^2}{2W_-}
+\Gamma_{\mathrm{cap}}.
```

Consequently,

```math
\boxed{
E_b
<
\frac{T^2}{2W_-}
+\Gamma_{\mathrm{cap}}
}
```

is a proved relaxed survival certificate. It is stronger than the original
certificate whenever at least one minimizing deletion mass exceeds its
arithmetic capacity.

The stability gap does not prove the original candidate and does not upper
bound `E_b`. It enlarges the usable threshold only when paired with a separate
upper bound for the actual energy. Thus the two proof obligations are:

1. control actual harmful-excess energy from above; and
2. optionally control extinct CRT distance from the Cauchy minimizer from
   below.

## Capacity-Only Upper Interface

Property #70 projects the proved common residue-class capacities onto the
single harmful-excess coordinate. For each layer, put

```math
\ell_i=\max(0,N_i-(r_i-2)B_i),
\qquad
u_i=\min(N_i,2B_i),
```

```math
M_i
=
\max
\left\{
\left(\ell_i-\frac{2N_i}{r_i}\right)^2,
\left(u_i-\frac{2N_i}{r_i}\right)^2
\right\}.
```

This is the sharp one-layer maximum for `b_i^2` given only the actual
population and common capacity. Therefore

```math
\boxed{
E_b
\le
\mathcal U_{\mathrm{cap}}
:=
\sum_i
w_i\frac{r_i}{2(r_i-2)}M_i.
}
```

Combining properties #69 and #70 proves the explicit sufficient theorem

```math
\boxed{
\mathcal U_{\mathrm{cap}}
<
\frac{T^2}{2W_-}
+\Gamma_{\mathrm{cap}}
\quad\Longrightarrow\quad
N_m>0.
}
```

This is now the cleanest capacity-only form of candidate #24. The remaining
problem is to prove the displayed aggregate inequality for an unbounded
family of actual conditioned population profiles. The per-layer envelope
cannot be improved from `N_i`, `r_i`, and `B_i` alone; any improvement must
use cross-layer CRT compatibility.

There is no new one-layer regime hidden in this projection. Property #70
proves that the sharp b-only envelope fits its one-layer allowance exactly
when

```math
\frac{N_i}{B_i}
>
\rho_*(r_i)
>
2.
```

This is strictly stronger than candidate #19's ordinary capacity-survival
condition `N_i>2B_i`. For a one-layer chain, `Gamma_cap` is zero below that
ordinary survival threshold and redundant above it. Properties #69--#70 are
therefore useful only if cross-layer CRT compatibility improves on the sum of
separate endpoint maxima.

## Cross-Layer CRT Orthogonality Boundary

Property #71 gives the exact first cross-layer theorem for the harmful-excess
coordinates themselves. With

```math
g_i(n)
=
F_i(n)
\left(
\mathbf 1_{r_i\mid n(n+2)}-\frac2{r_i}
\right),
\qquad
b_i=\sum_{n\in I}g_i(n),
```

the observables have zero mean and are pairwise orthogonal over the final CRT
period `R`:

```math
\sum_{n\bmod R}g_i(n)=0,
\qquad
\sum_{n\bmod R}g_i(n)g_j(n)=0
\quad(i\ne j).
```

If `d_i` is the complete-period paired-survivor density before layer `i`,
their exact norms are

```math
\lVert g_i\rVert_2^2
=
Rd_i\frac2{r_i}
\left(
1-\frac2{r_i}
\right).
```

For a window of length `L<=R`, black-box Bessel consequently gives

```math
E_b
\le
\frac{LRd_m}{r_0-2}.
```

This retains `Rd_m`, the number of final paired-survivor classes in a complete
primorial period. The cross-layer orthogonality is exact, but this bound is
far above the required safe-window scale.

The remaining CRT target is therefore narrower than generic orthogonality:
prove cancellation in the localized interval Gram matrix, exploit the actual
coefficient vector rather than its norm, or introduce an averaging variable
that removes the complete-period factor.

## Native-Period Capacity Hybrid

Property #72 extracts a rigorous intermediate-period gain before requiring
any new correlation theorem. For a cut `k`, complete `M_k` blocks cancel from
the observables `g_i` with `i<k`. If

```math
s_k=L\bmod M_k,
\qquad
q_{i,k}=M_kd_ip_ia_i,
```

native-period Bessel gives the joint prefix constraint

```math
\sum_{i<k}\frac{b_i^2}{q_{i,k}}\le s_k.
```

Intersect this with property #70's individual bounds `b_i^2<=X_i`. After the
normalization

```math
t_i=\frac{b_i^2}{q_{i,k}},
\qquad
c_{i,k}=\frac{X_i}{q_{i,k}},
```

the prefix energy has decreasing objective coefficients

```math
\beta_{i,k}
=
\frac{M_kd_m}{r_i-2}.
```

The sharp upper envelope therefore fills the Bessel budget greedily from the
smallest incoming prime:

```math
t_{i,k}^{\star}
=
\min
\left\{
c_{i,k},
\left(
s_k-\sum_{j<i}c_{j,k}
\right)_+
\right\}.
```

With

```math
\mathcal H_k
=
\sum_{i<k}\beta_{i,k}t_{i,k}^{\star},
```

property #72 proves

```math
\boxed{
E_b
\le
\mathcal U_{\mathrm{hyb}}
:=
\min_{0\le k\le m}
\left[
\mathcal H_k
+
\sum_{i=k}^{m-1}\frac{w_i}{2a_i}X_i
\right]
\le
\mathcal U_{\mathrm{cap}}.
}
```

The gain at a fixed positive cut is strict exactly when

```math
\sum_{i<k}
\frac{X_i}{M_kd_ip_ia_i}
>
s_k.
```

Combining the hybrid upper bound with property #69 gives the currently
sharpest proved capacity/orthogonality certificate:

```math
\boxed{
\mathcal U_{\mathrm{hyb}}
<
\frac{T^2}{2W_-}
+
\Gamma_{\mathrm{cap}}
\quad\Longrightarrow\quad
N_m>0.
}
```

This theorem couples the early layers and can strictly improve the
all-capacity envelope. The open obligation is now to prove that its left side
clears the extinction threshold for an unbounded family of actual chains.

## Scalar Capacity-Overflow Checkpoint

Property #73 compresses the exact greedy gain to one scalar per cut:

```math
e_k
=
\left(
\sum_{i<k}\frac{X_i}{M_kd_ip_ia_i}
-
s_k
\right)_+.
```

If

```math
\Delta_k
=
\mathcal U_{\mathrm{cap}}
-
\mathcal U_k^{\mathrm{hyb}},
```

then

```math
\boxed{
\frac{M_kd_m}{r_{k-1}-2}e_k
\le
\Delta_k
\le
\frac{M_kd_m}{r_0-2}e_k.
}
```

Thus `e_k>0` is exactly strict gain, and the lower estimate gives the simpler
proved certificate

```math
\boxed{
\mathcal U_{\mathrm{cap}}
-
\max_{1\le k\le m}
\left[
\frac{M_kd_m}{r_{k-1}-2}e_k
\right]
<
\frac{T^2}{2W_-}
+
\Gamma_{\mathrm{cap}}
\quad\Longrightarrow\quad
N_m>0.
}
```

This scalar form is weaker than evaluating the exact greedy envelope, but it
isolates the next possible algebraic input: a lower bound for one normalized
capacity overflow at the scale of the remaining extinction deficit.

## Limitation

This candidate does not escape the terminal positivity wall. Property #66
proves that its strict inequality cannot hold when `N_m=0`. Its advantage is
economy, not noncircularity: it removes every quadratic term that the exact
population recurrence does not need and uses the sharp conservation-only
allowance.

A universal hybrid upper envelope for `E_b` is now proved and is never weaker
than the capacity-only envelope, but it is not proved to fit below the relaxed
survival threshold. The candidate is not refuted; the explicit aggregate
inequality for actual chains remains open. Separate-layer capacity
optimization and complete-period black-box orthogonality are exhausted;
property #72 is the remaining native-period algebraic interface.
Property #73 makes its simplest missing input explicit, but supplies no
independent lower bound for the overflow.

## Established Inputs

- [Weighted deletion conservation law](
  ../properties/sieve-sequence/weighted-deletion-conservation-law.md
  )
- [Weighted harmful-excess energy is already terminal](
  ../properties/sieve-sequence/weighted-harmful-excess-energy-is-terminal.md
  )
- [Integral population profiles attain the harmful-energy threshold](
  ../properties/sieve-sequence/integral-population-profiles-attain-harmful-energy-threshold.md
  )
- [Harmful-excess energy has an exact stability decomposition](
  ../properties/sieve-sequence/harmful-excess-energy-exact-stability-decomposition.md
  )
- [Harmful capacity separates the energy minimizer](
  ../properties/sieve-sequence/harmful-capacity-separates-energy-minimizer.md
  )
- [Sharp harmful-capacity excess envelope](
  ../properties/sieve-sequence/sharp-harmful-capacity-excess-envelope.md
  )
- [Paired harmful-excess CRT orthogonality has primorial scale](
  ../properties/sieve-sequence/paired-harmful-excess-crt-orthogonality-has-primorial-scale.md
  )
- [Native-period Bessel and capacity give a sharp hybrid envelope](
  ../properties/sieve-sequence/native-period-bessel-capacity-hybrid-envelope.md
  )
- [Native-period capacity overflow quantifies the hybrid gain](
  ../properties/sieve-sequence/native-period-capacity-overflow-quantifies-hybrid-gain.md
  )
- [Endpoint sampling and strike density recombine into harmful residues](
  ../properties/sieve-sequence/endpoint-sampling-strike-density-harmful-residue-bridge.md
  )
- [One-layer harmful ellipses do not compose](
  ../properties/sieve-sequence/one-layer-harmful-ellipses-do-not-compose.md
  )
- [Cumulative weighted collision budget](
  cumulative-weighted-collision-budget.md
  )
