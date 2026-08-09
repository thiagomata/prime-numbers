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

## Population-Slack Overflow Floor

Property #74 supplies the first unconditional algebraic lower bound for that
overflow from the actual populations. Define

```math
\sigma_i
:=
\min(N_i,2B_i,r_iB_i-N_i).
```

This is exactly the width of property #70's feasible total-harmful-count
interval. Its sharp endpoint envelope satisfies

```math
X_i\ge\frac{\sigma_i^2}{4},
```

so

```math
\boxed{
e_k
\ge
\underline e_k
:=
\left(
\sum_{i<k}
\frac{\sigma_i^2}{4M_kd_ip_ia_i}
-
s_k
\right)_+.
}
```

Substituting `underline e_k` for `e_k` in property #73's lower gain estimate
gives another fully proved survival certificate.

The same theorem identifies the exact boundary:

```math
X_i=0
\quad\Longleftrightarrow\quad
N_i\in\{0,r_iB_i\}
```

when `B_i>0`. Thus no positive lower bound depending only on `r_i,B_i` can
advance candidate #24. The remaining input must quantitatively keep enough
actual populations away from both empty and full capacity, or use localized
residue information outside the capacity model.

## Seven-Layer Overflow Is Unconditionally Positive

Property #75 connects candidate #17's local-count threshold to the preceding
population-slack floor. For every applicable layer `r>=7`, that threshold and
the already-installed filter `5` imply

```math
2B_r\le N_r\le(r-2)B_r.
```

Hence the slack is maximal:

```math
\sigma_r=2B_r,
\qquad
X_r\ge B_r^2.
```

At the first such layer, `r=7`, the local-count threshold is already proved
for every integer `Q>=17`. Property #76 evaluates the native cut after filter
`7` exactly. With `r_0=5`, `r_1=7`, `k=2`, and `M_2=210`, the filter-`7`
coordinate has

```math
q_{1,2}=\frac{30}{7}.
```

Writing

```math
B_7
=
\left\lfloor
\frac{Q^2-Q-3}{42}
\right\rfloor+1,
```

the normalized overflow satisfies

```math
\boxed{
e_2
\ge
\left(
\frac{7B_7^2}{30}
-((Q^2-Q-2)\bmod210)
\right)_+
\ge1
}
```

for every integer `Q>=36`. Therefore the hybrid envelope is strictly smaller
than the all-capacity envelope for every future prime head `Q>=37`, with

```math
\boxed{\Delta_2\ge42d_m e_2.}
```

This settles positivity of one native overflow unconditionally. It does not
settle the candidate: the quantified gain must still exceed the difference
between the all-capacity envelope and the extinction threshold.

## No Fixed Native Cut Is Enough

Property #77 performs that comparison against the original threshold. Assume
candidate #17's count threshold at the first untouched layer, filter `11`.
For every chain with `Q>=17` and at least `37` filter layers, the filter-`11`
suffix term alone satisfies

```math
\mathcal U_2^{\mathrm{hyb}}
\ge
\alpha_2X_2
>
\frac{T^2}{2W_-}.
```

Thus the positive filter-`7` overflow cannot make the fixed `k=2` envelope
certify this candidate's original conservation-only threshold on long chains.
The result concerns the capacity-based upper envelope, not the actual energy:
it does not prove `E_b` is above the threshold.

This classifies the fixed early cut. Further progress must bring additional
layers into the joint Bessel budget through a moving cut, use the larger
capacity-relaxed threshold quantitatively, or reduce the suffix with localized
residue information.

Property #78 proves the arbitrary-cut form. If candidate #17 holds at the
first suffix layer `r_k`, then

```math
m
>
P_k(r_k-2)^2
\left(1+\frac6D\right)^2
\quad\Longrightarrow\quad
\mathcal U_k^{\mathrm{hyb}}
>
\frac{T^2}{2W_-}.
```

Every fixed `k` therefore fails eventually along unbounded chains. A cut that
could clear the original threshold must move with the future head and satisfy
the exact necessary condition

```math
m
\le
P_k(r_k-2)^2
\left(1+\frac6D\right)^2.
```

Since `P_k<=3/7` for `k>=2`, this forces

```math
\boxed{
r_k
\ge
2+
\frac{\sqrt{7m/3}}{1+6/D}.
}
```

This lower bound is necessary, not sufficient. A moving cut must also retain
a useful native-period remainder budget.

## Moving Cuts Lose Complete Native Blocks

Property #79 proves the complementary obstruction. Suppose a moving cut both
clears the original threshold and retains `M_k<=H`, so that the square-window
start interval contains at least one complete native block. Under a finite
Chebyshev-theta lower bound

```math
\vartheta(r_{k-1})\ge c r_{k-1}
```

and Bertrand's inequality, it must satisfy

```math
\boxed{
m
<
\frac37
\left(1+\frac6D\right)^2
\left(
\frac{2\log H}{c}-2
\right)^2.
}
```

For the complete chain, `m=pi(Q)-3`. Using the prime number theorem explicitly
as an external mathematical dependency, `m` grows like `Q/log(Q)`, whereas
the right side grows only like `log^2(Q)`. Thus every sufficiently large cut
that could avoid the suffix obstruction necessarily has

```math
M_k>H,
\qquad
s_k=H.
```

There are no complete native blocks to cancel. Property #80, in the next
section, proves that the single-incomplete-block capacity box eventually fits
inside the Bessel budget, so this remaining native-period step gives no gain.

## Incomplete-Block Bessel Gives No Gain

Property #80 closes that final native-period step. For `M_k>H`, it proves

```math
\sum_{i<k}
\frac{X_i}{q_{i,k}}
\le
\frac{3kD^2r_k^2}{25M_kP_k(r_k-2)}.
```

Consequently, the finite product condition

```math
M_kP_k
\ge
\frac{3kD^2r_k^2}{25H(r_k-2)}
```

forces

```math
e_k=0,
\qquad
\mathcal U_k^{\mathrm{hyb}}
=
\mathcal U_{\mathrm{cap}}.
```

Using PNT explicitly outside Stainless, `M_kP_k` grows exponentially in the
moving-cut prime while the required right side is only polynomial. The
condition therefore holds at every sufficiently large moving cut forced by
property #78.

Together, properties #77--#80 prove that the current
capacity-plus-native-Bessel envelope cannot clear this candidate's original
threshold under the full candidate #17 hypothesis on an unbounded family.
This is a method obstruction, not a refutation of either candidate.

## Capacity Stability Gap Does Not Rescue the Envelope

Property #81 closes the remaining capacity-relaxed comparison. For every
post-`5` layer it proves

```math
K_i^\star-C_i
\le
\frac{N_0}{S}
-
\frac{2D-18}{15r_i}.
```

Once `S>=15QN_0/(2D-18)`, all those minimizing deletion masses fit their
capacities, and the only possible stability contribution satisfies

```math
\Gamma_{\mathrm{cap}}
\le
\frac{25P_m}{18}
\left(
\frac25+\frac{3N_0}{5S}
\right)^2.
```

Candidate #17 at filter `7` simultaneously forces

```math
\mathcal U_{\mathrm{cap}}
\ge
\frac{P_mD^2}{1080}.
```

Prime Mertens and PNT, used explicitly outside Stainless, give
`S` of order `Q log Q` and `m` of order `Q/log Q`. The stability gap is
eventually positive, but both it and the original threshold are negligible
relative to the filter-`7` envelope floor. Hence

```math
\mathcal U_{\mathrm{cap}}
>
\frac{T^2}{2W_-}
+
\Gamma_{\mathrm{cap}}
```

for every sufficiently large head under full candidate #17. Thus
`Gamma_cap` cannot rescue the separate capacity envelope. The result does not
exclude a smaller upper bound for the actual `E_b`.

## Exact Localized Saving at Filter Seven

Property #82 supplies the first such smaller actual-energy bound. The
filter-`7` observable is mean-zero and periodic modulo `210`. Its 21
admissible centered integer weights have cumulative sums between `-8` and
`10`, so every interval satisfies

```math
\boxed{|b_7|\le\frac{18}{7}}.
```

Consequently, the actual filter-`7` energy contribution obeys

```math
\boxed{
\alpha_1b_7^2
\le
\frac{54}{5}P_m.
}
```

This replaces the separate capacity charge

```math
\alpha_1M_1
\ge
\frac{P_mD^2}{1080}
```

by a boundary constant times `P_m`. Their ratio is at most `11664/D^2`.
Thus the filter-`7` obstruction used to diagnose properties #77--#81 is not
an obstruction for the actual coefficient. The remaining problem is to make
this localized saving scale across the growing set of later filters. Property
#58 identifies the general coefficient as
`b_i=delta_(0,i)+delta_(-2,i)`, so direct native-period enumeration returns
to candidate #23's accepted-boundary discrepancy. Its generic exponential
inclusion--exclusion and total-variation bounds do not scale; a successful
extension needs new signed mean-square or cross-layer cancellation.

## Copy-Block Localization Through Residue Energy

Property #83 supplies a second exact localized bridge. For one incoming prime,
partition the numerical interval into old-period copy blocks. If `V_i` is the
full residue-histogram energy before filter `r_i` and `B_(i,j)` is the centered
harmful excess in copy block `j`, then

```math
\boxed{
\sum_{j=0}^{r_i-1}B_{i,j}^2\le4V_i.
}
```

After complete `r_i`-block cycles cancel, any remaining `k_i<r_i` consecutive
complete blocks contribute at most

```math
\boxed{
\left|\sum_jB_{i,j}\right|^2\le4k_iV_i.
}
```

This turns candidate #20's relative collision-energy theorem into a proved
input for the complete old-period interior of candidate #24's coefficient.
It is different from the capacity/native-period envelopes: it uses the actual
residue energy rather than maximizing each harmful class separately.

An arbitrary interval still has two partial old-period boundary fragments.
When the old period exceeds the square window, the entire coefficient is such
a fragment. Thus property #83 narrows the signed-cancellation frontier but
does not remove it: a viable continuation needs candidate #20-type energy plus
a separate partial-boundary theorem, or one joint estimate controlling both.

## Limitation

This candidate does not escape the terminal positivity wall. Property #66
proves that its strict inequality cannot hold when `N_m=0`. Its advantage is
economy, not noncircularity: it removes every quadratic term that the exact
population recurrence does not need and uses the sharp conservation-only
allowance.

A universal hybrid upper envelope for `E_b` is proved and is never weaker than
the capacity-only envelope. The candidate is not refuted; the explicit
aggregate inequality for actual chains remains open. Separate-layer capacity,
complete-period black-box orthogonality, and the native-period capacity hybrid
are now exhausted for the original threshold under full candidate #17.
Property #73 makes its simplest missing input explicit, and property #74
lower-bounds it by actual population slack. Properties #75--#76 now prove
that the first native cut has positive overflow for every sufficiently large
head. Property #77 proves that the first fixed cut cannot clear the original
threshold on long chains; property #78 proves the same eventual obstruction
for every fixed cut and gives the necessary moving-prime scale. Property #79
then proves, using Bertrand/PNT explicitly outside Stainless, that such a
moving cut eventually has no complete native blocks. Property #80 proves that
the remaining incomplete-block constraint eventually excludes no capacity
mass. Property #81 proves that the capacity-relaxed `Gamma_cap` threshold
cannot absorb the remaining separate-envelope excess. Property #82 proves
that exact localized residue structure does remove that excess at filter `7`.
Property #83 proves that candidate #20's residue energy controls complete
old-period block runs, but leaves partial boundary fragments. The live #24
route is now a scalable localized bound for the growing collection of actual
`b_i^2`, potentially split into collision-controlled block interiors and
signed boundaries. This is the same new-arithmetic obligation as candidate
#23's boundary-cancellation frontier unless a genuinely different cross-layer
inequality is found.

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
- [Capacity stability gap cannot rescue the capacity envelope](
  ../properties/sieve-sequence/capacity-stability-gap-cannot-rescue-capacity-envelope.md
  )
- [Filter-seven harmful excess is boundary-sized](
  ../properties/sieve-sequence/filter-seven-harmful-excess-is-boundary-sized.md
  )
- [Copy-block harmful excess is controlled by residue energy](
  ../properties/sieve-sequence/copy-block-harmful-excess-controlled-by-residue-energy.md
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
- [Capacity-envelope width floor needs population slack](
  ../properties/sieve-sequence/capacity-envelope-width-floor-needs-population-slack.md
  )
- [Seven-layer density floor maximizes capacity width](
  ../properties/sieve-sequence/seven-layer-density-floor-maximizes-capacity-width.md
  )
- [Seven-layer floor forces native overflow](
  ../properties/sieve-sequence/seven-layer-floor-forces-native-overflow.md
  )
- [Fixed seven cut cannot clear the original threshold](
  ../properties/sieve-sequence/fixed-seven-cut-cannot-clear-original-threshold.md
  )
- [Every fixed native cut fails the original threshold](
  ../properties/sieve-sequence/every-fixed-native-cut-fails-original-threshold.md
  )
- [Moving cut loses complete native blocks](
  ../properties/sieve-sequence/moving-cut-loses-complete-native-blocks.md
  )
- [Incomplete-block Bessel excludes no capacity](
  ../properties/sieve-sequence/incomplete-block-bessel-excludes-no-capacity.md
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
