# Conditioned Harmless-Class Collision Energy

**Candidate hypothesis:** Unproved and potentially false.

**Algebraic reduction:** Mathematically proved.

**Empirical status:** BOUNDED FALSIFIER INCONCLUSIVE — the exact pointwise
inequality `U_i<=M_i` has no violation in the 1,035 layers with prime heads
`5<=Q<224`. This finite agreement is not evidence for the theorem and says
nothing decisive about infinitely many heads. The weakest standalone
distribution target remains a weighted aggregate bound for
`sum_i w_i U_i`; pointwise `U_i<=M_i` is only a convenient stronger
benchmark. Property #66 shows that this harmless target is no longer the
primary missing survival theorem.

## Purpose

The full residue energy before a filter mixes three effects: total excess in
the two harmful classes, imbalance between those classes, and nonuniformity
among the classes that survive.

The first two effects have exact endpoint-observable interpretations. This
candidate isolates the third effect and asks only for relative collision
control among the `r-2` harmless classes.

This remains a well-defined noncircular distribution problem: `U_i=0` when
the actual harmless survivor population is zero. Its role in the survival
program is now diagnostic rather than decisive. Property #66 proves that the
separate harmful-excess square is already terminal at candidate #21's global
allowance.

## Setup

At layer `i`, let `S_i` be the 2-gap starts before filtering by prime `r_i`,
with residue counts

```math
c_{i,a}
=
\#\{x\in S_i:x\equiv a\pmod{r_i}\}.
```

The two harmful classes are `0` and `-2`. Let

```math
M_i
=
\sum_{a\notin\{0,-2\}}c_{i,a}
=
N_{i+1}
```

be the survivor population after the filter.

This note uses `M_i` only for the actual post-filter survivor population
`N_{i+1}`. It must not be confused with notes that use `M_i=a_iN_i` for a
one-step multiplicative main term.

Define the harmless-class energy

```math
U_i
=
\sum_{a\notin\{0,-2\}}
\left(
c_{i,a}-\frac{M_i}{r_i-2}
\right)^2.
```

## Candidate Hypothesis

The weakest current target is weighted and aggregate. Let

```math
W=\sum_iw_i,
\qquad
T=N_0A_{0,m}.
```

Suppose candidate #13 gives endpoint-sampling bounds `eta_i`. Let candidate
#23's unnormalized accepted-strike discrepancy be

```math
D_i
=
H_i-\frac{A_i}{r_i}
```

and define

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

Properties #36 and #37 give the denominator-free scalar bound

```math
\sum_iw_i
\left[
\frac{r_i}{2(r_i-2)}b_i^2
+
\frac12\Delta_i^2
\right]
\le
\left(
\sqrt{\mathcal E_\beta}
+
\sqrt{\mathcal E_D}
\right)^2
+
\mathcal E_\Delta.
```

Define the remaining harmless-energy allowance

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

The original combined candidate hypothesis is that, for infinitely many
future heads `Q`,

```math
\boxed{
\mathcal U_*(Q)>0
\qquad\text{and}\qquad
\sum_iw_iU_i<\mathcal U_*(Q).
}
```

This is exactly the harmless allowance left by the orthogonal candidate #21
decomposition. It permits individual layers to violate the natural linear
benchmark.

Property #66 changes its survival interpretation. The first condition
`mathcal U_*(Q)>0` says that the proved scalar upper bound is already strictly
below `T^2/(2W)`. Since that upper bound contains the actual harmful-excess
energy `E_b`, property #66 already gives

```math
N_m>0.
```

Therefore the second condition

```math
\sum_iw_iU_i<\mathcal U_*(Q)
```

is redundant for final survival in this separated composition. It remains a
legitimate standalone theorem about conditioned harmless-class distribution,
but it is not the missing step after the scalar feasibility condition has
been proved.

A convenient stronger pointwise hypothesis is that every layer in the
conditioned chain satisfies

```math
\boxed{
U_i\le M_i.
}
```

Equivalently,

```math
\boxed{
\sum_{a\notin\{0,-2\}}c_{i,a}^2
\le
M_i+\frac{M_i^2}{r_i-2}.
}
```

This is a relative same-residue collision bound on the post-filter survivor
alphabet.

## Exact Off-Diagonal Target

Let

```math
R_i
=
\#\{
(x,y)\in S_{i+1}^2:
x\ne y,\ r_i\mid x-y
\}.
```

Property #40 gives

```math
\boxed{
U_i
=
M_i+R_i-\frac{M_i^2}{r_i-2}.
}
```

Therefore the displayed standalone aggregate hypothesis is exactly equivalent
to

```math
\boxed{
\sum_iw_iR_i
<
\mathcal U_*(Q)
-
\sum_iw_iM_i
+
\sum_iw_i\frac{M_i^2}{r_i-2}.
}
```

This is the weakest currently identified correlation theorem for #22.
It asks only for a weighted bound on off-diagonal same-residue pairs among
starts that already survived the relevant filter.

The same property lifts the left-hand side to `S_0` with post-deletion
indicators `f_{i+1}`. Its pair kernel stops before the first deleting filter
and retains an additional negative centering term relative to the full
candidate #21 kernel.

## Complete-Period Boundary

Property #41 proves that every harmless class has exactly the same number of
2-gap starts over one complete CRT period. Therefore

```math
\boxed{
U_i^{\mathrm{complete\ period}}=0.
}
```

Complete periods also cancel from a longer interval: its harmless energy is
exactly the energy of the incomplete remainder prefix.

Thus candidate #22 is purely a localization theorem. It does not require
better complete-period counting; it requires control of how `[Q,Q^2)` samples
an exactly balanced cyclic harmless-class sequence.

## Spectral Boundary

Extend the harmless counts by setting the two harmful class counts to zero,
and let `hat(d_i)(k)` be their additive Fourier transform modulo `r_i`.
Property #42 proves

```math
\boxed{
U_i
=
\frac1{r_i}
\sum_{k\ne0}
|\widehat d_i(k)|^2
-
\frac{2M_i^2}{r_i(r_i-2)}.
}
```

The subtracted term is the sharp nontrivial spectral floor forced by the two
empty classes. Therefore #22 asks for the weighted spectral excess above that
floor.

Generic localized Fourier bounds retain the complete-period population rather
than `M_i`. Subtracting the local floor does not repair that normalization
mismatch. A successful spectral proof needs a new localized inequality
normalized directly by the conditioned population or cancellation involving
the post-deletion difference kernel.

## CRT Translated-Fiber Boundary

Property #43 gives a physical-space normal form for the same problem. If `P`
is the prior-filter modulus, `s=r_i^{-1} modulo P`, and a surviving start is
written as `x=a+r_i t`, then every harmless-class count has the form

```math
d_{i,a}
=
\rho_i\ell_{i,a}
+
E_{\ell_{i,a}}(v_{i,a}),
\qquad
v_{i,a}
=
\left\lceil\frac{Q-a}{r_i}\right\rceil
+s a
\pmod P.
```

Here all classes sample one common periodic prior-filter word, the lengths
`ell_{i,a}` differ by at most one, and the phases are spaced on the order of
`P/r_i`.

Uncentered Parseval or generic large-sieve sampling still retains the
complete-period population. The sharper remaining question is whether
subtracting the harmless-class mean gives a **centered inverse-phase
sampling inequality** at local scale:

```math
\sum_{a\notin\{0,-2\}}
\left(
\rho_i\ell_{i,a}
+E_{\ell_{i,a}}(v_{i,a})
-\overline d_i
\right)^2
\le M_i.
```

This is exactly the pointwise benchmark, now expressed as a theorem about one
explicit CRT word and one explicit family of inverse phases. It is not proved
by property #43.

Property #44 inserts the harmless-class mean projection exactly. For
`phi_m(a)=exp(2 pi i m v_{i,a}/P)` and `h=r_i-2`, its single-frequency cost is

```math
\|C\phi_m\|_2^2
=
h-\frac{|K_m|^2}{h},
\qquad
K_m=\sum_{a\notin\{0,-2\}}\phi_m(a).
```

It also evaluates `K_m` as two collapsed geometric progressions and proves
the exact cross-frequency entry

```math
\langle C\phi_m,C\phi_n\rangle
=
K_{m-n}-\frac{K_mK_{-n}}h.
```

Thus centering can make some frequencies much cheaper than an uncentered
large-sieve estimate predicts. The open step is to control the full
cross-frequency quadratic form on the particular factored CRT spectrum;
property #44 does not prove that form is diagonal.

Property #45 computes the generic centered operator norm exactly. The inverse
phases have orthogonal full-Fourier rows, so

```math
\mathsf A\mathsf A^*=P I,
\qquad
C\mathsf A\mathsf A^*C=PC.
```

The norm `sqrt(P)` is sharp. Applied without further arithmetic information,
it returns exactly to the full-shift Parseval bound, including after the
one-unit fiber-length correction is split off.

Therefore neither uncentered nor centered black-box operator estimates can
prove #22. A remaining spectral proof must couple the explicit CRT factors of
`hat(g_0)(m)` to the centered kernel from property #44, or obtain cancellation
only after candidate #21's chain weights are inserted.

Property #46 makes the first coupling conductor-sensitive. For exact
conductor `q`, let `mu_q` be the largest multiplicity of one inverse phase
modulo `q`. The two affine phase runs give

```math
\mu_q
\le
\left\lceil\frac bq\right\rceil
+
\left\lceil\frac{r_i-b}{q}\right\rceil,
\qquad
q\mu_q<r_i+2q.
```

Hence the squared centered block norm is at most `q mu_q`, replacing the full
period `P` by conductor scale `O(r_i+q)`. This is a real improvement.

The exact-conductor blocks are not orthogonal after inverse-phase sampling.
Adding their norms by triangle inequality produces the oversized divisor sum

```math
\sum_{\substack{q\mid P\\q>1}}
\min(\ell,q)\sqrt{q\mu_q}
\prod_{p\mid q}\sqrt{\frac2{p-2}},
```

which does not close the local-population bound. The remaining spectral
question is cross-conductor cancellation or an almost-orthogonal square-sum
theorem that keeps the interval multipliers.

Property #47 calculates the cross-conductor geometry exactly:

```math
\|\mathsf A_q^*C\mathsf A_{q'}\|_{\mathrm{HS}}^2
=
\operatorname{tr}
\left(
C\mathsf R_qC\mathsf R_{q'}C
\right),
\qquad
(\mathsf R_q)_{a,c}=c_q(v_a-v_c).
```

Distinct blocks are not generically orthogonal. At
`P=30`, `r=7`, `q=2`, `q'=3`, the squared cross-block Hilbert--Schmidt norm is
exactly `168/25`. A second exact pair has squared normalized coherence
`2793/3203`, so uniformly small unweighted coherence is also unavailable.

This exhausts conductor distinctness, conductor coprimality, and unweighted
block geometry as automatic sources of cancellation. A remaining #22 theorem
must be genuinely coefficient-weighted: it must use the signs and phases of
`hat(g_0)(m)D_ell(m)`, or combine layers before absolute values are taken.

## Exact Composition With Endpoint Errors

Let

```math
b_i
=
K_i-\frac{2N_i}{r_i}
```

be total harmful excess, and let

```math
\Delta_i
=
c_{i,0}-c_{i,-2}
```

be left/right harmful-class imbalance.

The proved orthogonal decomposition is

```math
\boxed{
V_i
=
U_i
+
\frac{r_i}{2(r_i-2)}b_i^2
+
\frac12\Delta_i^2.
}
```

Therefore this candidate implies

```math
V_i
\le
M_i
+
\frac{r_i}{2(r_i-2)}b_i^2
+
\frac12\Delta_i^2.
```

If candidate #13 and candidate #23 give

```math
|b_i|\le\mathcal B_i,
\qquad
|\Delta_i|\le\mathcal D_i,
```

then

```math
V_i
\le
M_i
+
\frac{r_i}{2(r_i-2)}\mathcal B_i^2
+
\frac12\mathcal D_i^2.
```

Inserting these bounds into candidate #21 gives the explicit sufficient
condition

```math
\boxed{
2
\left(\sum_iw_i\right)
\sum_iw_i
\left(
M_i
+
\frac{r_i}{2(r_i-2)}\mathcal B_i^2
+
\frac12\mathcal D_i^2
\right)
<
\left(N_0A_{0,m}\right)^2.
}
```

When this inequality holds, candidate #21's proved implication gives a final
2-gap survivor. Property #66 gives a sharper interpretation: if the scalar
terms alone are already bounded strictly below the complete allowance, they
force a final survivor without requiring the additional `M_i` contribution.

## Relation To Candidate #20

Candidate #20 asks for a relative collision bound on all `r_i` residue
classes before filtering. This candidate asks for the same natural
linear-error scale only after removing the two harmful classes and recentering
on the remaining `r_i-2` classes.

The new statement is narrower and composes orthogonally with endpoint errors,
but it is not known to be easier to prove. It may retain the same short-window
and parity obstruction as #20.

## What Would Prove It

Any of the following would suffice:

1. a direct harmless-class collision estimate
   `sum c_{i,a}^2<=M_i+M_i^2/(r_i-2)`;
2. a deterministic discrepancy theorem on the `r_i-2` survivor classes with
   squared error sum at most `M_i`;
3. a four-point correlation bound restricted to differences divisible by
   `r_i`, normalized by the actual survivor population;
4. a stronger weighted aggregate bound for `sum_iw_iU_i`, even if some
   individual layers violate `U_i<=M_i`. This would prove the standalone
   distribution statement, but property #66 shows it is not needed for
   survival once the scalar allowance is positive.

## Limitation

The hypothesis is unproved and strong. It controls the distribution of an
already conditioned short-window set among particular residue classes. A
complete-period CRT average does not imply it, and a black-box large sieve is
quantitatively too weak for candidate #21. Candidate #10's post-filter count
discrepancy is not the accepted-strike density estimate needed to control
`b_i`; that separate theorem is candidate #23.

This candidate is useful because it is the smallest independently noncircular
distributional component left by the exact algebra, not because the parity
barrier has been removed. It is no longer a top survival target in the current
separated framework. The aggregate form has a scalar feasibility precondition
`mathcal U_*(Q)>0`, and property #66 proves that satisfying that precondition
with valid scalar bounds already forces survival. If the scalar errors exhaust
the allowance, no harmless-dispersion estimate can rescue this particular #21
budget.

## Established Inputs

- [Orthogonal residue-energy decomposition after a two-class filter](
  ../properties/sieve-sequence/orthogonal-residue-energy-decomposition-after-two-class-filter.md
  )
- [Two endpoint observables separate harmful excess and imbalance](
  ../properties/sieve-sequence/two-endpoint-observables-separate-harmful-excess-and-imbalance.md
  )
- [Accepted-anchor strike density](
  accepted-anchor-strike-density.md
  )
- [Endpoint density contracts accepted-strike discrepancy](
  ../properties/sieve-sequence/endpoint-density-contracts-strike-discrepancy.md
  )
- [Weighted composition of endpoint and strike-density errors](
  ../properties/sieve-sequence/weighted-scalar-error-composition.md
  )
- [Weighted harmful-excess energy is already terminal](
  ../properties/sieve-sequence/weighted-harmful-excess-energy-is-terminal.md
  )
- [Harmless energy as a fixed-set pair correlation](
  ../properties/sieve-sequence/harmless-energy-fixed-set-pair-form.md
  )
- [Complete-period uniformity of harmless 2-gap classes](
  ../properties/sieve-sequence/complete-period-harmless-class-uniformity.md
  )
- [Harmless energy as spectral excess above the two-class floor](
  ../properties/sieve-sequence/harmless-energy-spectral-excess.md
  )
- [Harmless-class counts as translated CRT fibers](
  ../properties/sieve-sequence/harmless-class-crt-translated-fibers.md
  )
- [Centered inverse-phase Gram matrix](
  ../properties/sieve-sequence/centered-inverse-phase-gram-matrix.md
  )
- [Centered phase operator norm boundary](
  ../properties/sieve-sequence/centered-phase-operator-norm-boundary.md
  )
- [Exact-conductor phase-block operator bound](
  ../properties/sieve-sequence/exact-conductor-phase-block-operator-bound.md
  )
- [Centered Ramanujan cross-conductor geometry](
  ../properties/sieve-sequence/centered-ramanujan-cross-conductor-geometry.md
  )
- [Refuted centered conductor-block orthogonality](
  refuted/centered-conductor-block-orthogonality.md
  )
- [Cumulative weighted collision budget](
  cumulative-weighted-collision-budget.md
  )
