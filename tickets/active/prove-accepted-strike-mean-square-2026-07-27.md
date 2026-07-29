# Prove The Accepted-Strike Boundary Mean-Square Estimate

**Created:** 2026-07-27
**Status:** Complete — algebraically classified; analytic estimate remains open
**Candidate:** #23 accepted-anchor strike density
**Depends on:**
`verify-19-21-escape-wall-2026-07-27.md`,
`algebraic-conditioned-survival-2026-07-27.md`

> Persistent-memory ticket. Update continuously per `TICKET_DISCIPLINE.md`.

## START HERE

Candidate #23 is the active top-candidate path after candidate #22's generic
finite-Fourier routes were exhausted. Do not collect more data.

The activated shell factors exactly through bounded CRT lift indices, the
complete old boundary error cancels, and property #50 identifies the
remaining transform exactly as a summatory coprime-count dilation remainder.
The immediate micro-goal is to classify whether an existing mean-square
theorem applies to the changing pairs `(P_i,r_i)`, or whether #23 requires new
analytic input.

Do not retry unsigned inclusion--exclusion, the linear telescope after
squaring, summation by parts without new arithmetic input, or universal sign
laws.

## Goal

Prove, refute, or classify the weakest noncircular weighted estimate for
candidate #23's accepted-strike discrepancy that composes with candidates
#13, #22, and #21 without normalizing by an unknown late or final 2-gap
population.

This ticket is complete when either:

1. a sound algebraic mean-square theorem is proved and promoted to
   `properties/`; or
2. the exact theorem is reduced to a clearly identified analytic/parity
   boundary, with all generic algebraic routes audited and the surviving
   external ingredient stated precisely.

## Strategy

Work from the exact signed boundary formula, not from empirical strike
densities.

1. Restate candidate #21's required #23 budget using only initial or
   independently controlled quantities.
2. Insert property #35's Möbius boundary formula and property #38's exact
   positive quadratic variation.
3. Keep the divisor coefficients signed until the final quadratic form.
4. Derive the coefficient kernel produced by the layer weights and adjacent
   boundary differences.
5. Test whether this kernel has positivity, orthogonality, low rank, or
   factorization that yields a nontrivial upper bound.
6. If absolute values recreate `2^omega(P)`, stop that route immediately.

This strategy was selected because bulk density already cancels exactly. The
only open arithmetic is cancellation among boundary residues and across
conditioned layers.

## Current State

- Candidate #23 defines

  ```math
  D_i
  =
  H_i-\frac{A_i}{r_i}.
  ```

- Property #35 rewrites each centered accepted-strike discrepancy as a signed
  Möbius boundary sum. The main density term cancels exactly.
- Property #36 removes the dangerous population ratio by proving
  `2N_i<=A_i`.
- Property #37 gives the sharp aggregate scalar composition

  ```math
  \left(
  \sqrt{\mathcal E_\beta}
  +
  \sqrt{\mathcal E_D}
  \right)^2
  +
  \mathcal E_\Delta.
  ```

- Property #38 proves that the weighted square of adjacent boundary errors is
  a positive quadratic variation; the linear telescope does not upper-bound
  it.
- Property #39 gives the exact prime-square endpoint residue formula and
  refutes universal sign and sign-preservation laws.
- Property #48 collapses the exponential divisor-pair quadratic form to
  `m+1` signed activation-shell sums:

  ```math
  D_i
  =
  -\frac1{r_i}\sum_{t=0}^{i}Z_t-Z_{i+1},
  \qquad
  \mathcal E_D
  =
  \sum_{t,u}\mathcal K(t,u)Z_tZ_u.
  ```

  The explicit kernel `mathcal K` is positive semidefinite and has
  nonnegative entries.
- Property #49 proves

  ```math
  D_i
  =
  \frac{\mathcal M_i(Q)}{r_i},
  \qquad
  \mathcal E_D
  =
  \sum_i
  \frac{w_i}{2r_i(r_i-2)}
  \mathcal M_i(Q)^2,
  ```

  where `mathcal M_i(Q)` is the signed Möbius transform of the difference
  between the two bounded CRT lift indices at `Q` and `Q^2`.
- Property #50 proves

  ```math
  \mathcal M_i(Q)
  =
  T_{P_i,r_i}(Q)-T_{P_i,r_i}(Q^2),
  ```

  where

  ```math
  T_{P,r}(x)
  =
  F_P(x-1)
  -
  rF_P\left(\left\lfloor\frac{x-1}{r}\right\rfloor\right).
  ```

  Thus the lift-index transform is exactly the dilation remainder of the
  finite-sieve summatory coprime count.
- Property #51 proves that the complete-period centered strike functions
  `g_i` are pairwise orthogonal and

  ```math
  \lVert g_i\rVert_2^2
  =
  R\frac{\varphi(P_i)}{P_i}\frac{r_i-1}{r_i^2}.
  ```

  Bessel therefore gives an exact cross-layer mean square, but its right side
  is proportional to the full final period `R=P_m`.
- Property #52 localizes those functions to the actual interval and proves

  ```math
  G_{ii}
  =
  A_i\frac{r_i-1}{r_i^2}
  +
  \left(1-\frac2{r_i}\right)D_i,
  ```

  ```math
  G_{ij}
  =
  -\frac{D_{\max(i,j)}}{r_{\min(i,j)}}
  \qquad(i\ne j).
  ```

  It reduces the energy to

  ```math
  \mathcal E_D
  \le
  |I|\lambda_{\max}(C^{1/2}GC^{1/2}).
  ```
- Property #53 factors the local Gram matrix by first-deletion class and
  proves

  ```math
  \mathcal E_D
  =
  A_0\operatorname{tr}(CG)
  -
  \sum_{k<\ell}
  n_kn_\ell
  \lVert C^{1/2}(v_k-v_\ell)\rVert^2.
  ```

  It also proves that if only `n_k>=0` and `sum n_k=A_0` are retained, the
  sharp abstract envelope is

  ```math
  \mathcal E_D
  \le
  A_0^2\max_k\lVert C^{1/2}v_k\rVert^2.
  ```
- Property #54 proves the exact active two-class identity

  ```math
  D_i^2=A_iG_{ii}-H_iA_{i+1}.
  ```

  Therefore retaining only the compulsory distance `c_i` between deletion
  class `i` and all later classes rearranges the unknown strike energy rather
  than upper-bounding it.
- Property #55 reindexes the complete first-deletion variance and proves that
  property #53 collapses exactly to `sum_i c_iD_i^2`. No residual spectral
  gain remains without new arithmetic constraints on the deletion counts.
- No weighted mean-square upper bound for `mathcal E_D` is proved.

## Expected Theorem Shape

Let `E_i` denote the accepted-anchor boundary error before adjoining filter
`r_i`, with the exact adjacent recurrence

```math
D_i
=
\left(1-\frac1{r_i}\right)E_i-E_{i+1}.
```

Candidate #21 consumes

```math
\mathcal E_D
=
\sum_i
w_i
\frac{r_i}{2(r_i-2)}
D_i^2.
```

The weakest useful theorem has the form

```math
\boxed{
\mathcal E_D
\le
\mathcal B_D(Q),
}
```

where `mathcal B_D(Q)`:

1. is explicit in the initial window, installed primes, and layer weights;
2. does not contain a denominator involving a late or final survivor count;
3. leaves positive allowance in candidate #22's
   `mathcal U_*(Q)` for infinitely many heads;
4. is obtained from signed coefficient cancellation, not an unsigned divisor
   count.

The first algebraic task is to derive the exact divisor-by-divisor quadratic
kernel whose upper bound would imply this statement.

## Assumptions And Validation

- **Assumption:** property #35's boundary sum applies to the untrimmed accepted
  anchor interval.
  **Validation:** derive the endpoint correction needed by candidate #13
  before composing the final theorem.
- **Hypothesis:** the chain weights create cancellation in the divisor
  quadratic kernel.
  **Validation:** compute the exact kernel before applying inequalities; a
  positive-entry kernel defeats this hypothesis.
- **Hypothesis:** the theorem is weaker than final twin-prime positivity.
  **Validation:** evaluate its statement at zero final population and check
  that no late-population lower bound appears.
- **Risk:** coefficientwise absolute values recreate exponential divisor
  mass.
  **Validation:** factor the unsigned coefficient sum; stop if it contains
  `2^omega(P)` or a comparable product without compensating decay.

## What is Learned

- The bulk accepted-strike density is exact; only boundary cancellation is
  open.
- Candidate #23 is noncircular as stated because `D_i` exists even when the
  final 2-gap population is zero.
- Linear cancellation is insufficient after squaring.
- The endpoint-density contraction removes `N_i/A_i` as a separate obstacle.
- Prime-square endpoints do not impose a stable sign.
- The exponential divisor-pair kernel depends only on activation times and
  compresses to dimension `m+1`.
- The chain weights do not create kernel sign cancellation; useful
  cancellation must occur inside the signed shell sums `Z_t` or after
  averaging over heads.
- CRT cancels the complete old boundary term from every `D_i`. The only
  remaining coefficient is the bounded lift-index difference
  `t_{Q,r_i}(e)-t_{Q^2,r_i}(e)`.
- The lift-index Möbius transform is not a new cancellation mechanism. It is
  exactly the summatory coprime-count dilation discrepancy, evaluated at `Q`
  and `Q^2`.
- The missing theorem must control a weighted mean square while both the
  finite-sieve modulus `P_i` and dilation prime `r_i` vary with the layer.
- Standard fixed-sequence large-sieve theorems do not match the target
  directly: the coefficient sequence
  `1_{gcd(n,P_i)=1}` changes with `i`. The exact common-space substitute is
  property #51's CRT orthogonality, whose norm retains the final primorial.
- Complete-period layer orthogonality is exact, but restriction to the local
  window is precisely where its useful normalization is lost.
- Localizing restores the correct window scale and leaves a highly structured
  Gram matrix: every cross entry is a later discrepancy divided by an earlier
  prime.
- The generic trace bound ignores all of that structure and is exactly the
  sum of the separate per-layer Cauchy inequalities.
- First-deletion dispersion is the exact negative term lost by generic
  population bounds.
- Triangular support of the deletion vectors alone cannot force a gain:
  abstract class counts can concentrate in one vector. Useful improvement
  requires arithmetic information about the actual class masses.
- The minimum forced deletion-class separation is already the ordinary
  two-value variance of the active population at one layer.
- The full first-deletion variance is the sum of those layer-coordinate
  variances, including the zero mass from anchors deleted earlier. It contains
  no independent cross-layer upper bound.

## Failed Paths

- **Unsigned inclusion--exclusion:** gives
  `2^omega(P)-1`, exponentially too large. Retry only with signed
  cancellation or a decaying coefficient norm.
- **Linear boundary telescope used for squares:** squaring introduces
  uncontrolled adjacent products and differently weighted terms. Retry only
  with a quadratic-variation theorem.
- **Summation by parts of the squared recurrence:** all interior mass
  coefficients are positive. Retry only with new arithmetic control of the
  boundary errors themselves.
- **Universal sign or sign preservation:** exactly refuted at `Q=19` when
  filter `13` is adjoined. Retry only with averaged cancellation that permits
  sign changes.
- **Expecting the layer kernel to alternate:** property #48 proves every
  kernel entry is nonnegative. Retry only with cancellation inside the signed
  activation shells or with external averaging.
- **Repeated floor, residue, shell, or CRT coordinate rewrites:** properties
  #48--#50 show these are exact representations of the same dilation
  discrepancy and provide no upper bound by themselves. Retry only if a new
  inequality or analytic mean-square theorem is introduced.
- **Complete-period CRT orthogonality plus Bessel:** property #51 gives a
  right side proportional to `|I|P_m`, which retains the enormous ambient
  period. Retry only with localized Gram control or another averaging
  variable.
- **Localized Gram trace/self-bound:** property #52's trace inequality
  discards every off-diagonal entry and reproduces per-layer Cauchy; bounding
  its remaining signed linear term by Cauchy introduces a generic
  `|I|sqrt(C_0)` term. Retry only with a sharper spectral estimate using the
  nested off-diagonal structure.
- **First-deletion triangular geometry without class-mass information:**
  property #53's population-only envelope is sharp under abstract
  concentration in one deletion class. Retry only with a forced-dispersion
  lower bound for the actual `H_k` and `A_m`.
- **Only the compulsory `c_i H_i A_(i+1)` deletion variance:** property #54
  proves it contains `D_i^2` through an exact two-class identity. Retry only
  if the additional intermediate-coordinate distances are retained.
- **Full first-deletion distance reindexing:** property #55 proves that all
  remaining intermediate-coordinate terms complete the exact coordinatewise
  variance identity and return to `mathcal E_D`. Retry only with genuinely
  new arithmetic restrictions on `H_i`, averaging over heads, or an external
  mean-square theorem.

## Open Concerns

- The candidate #13 endpoint trimming correction is not yet inserted into the
  Möbius boundary formula.
- A useful mean-square theorem may be a genuinely new analytic-number-theory
  input rather than a consequence of finite copy/filter algebra.
- The exact allowance remaining after #13 and #22 must be positive; a valid
  but oversized #23 bound is not useful.
- A coefficient kernel that is merely positive semidefinite gives a lower
  bound or norm interpretation, not the required upper estimate.

## Next Action

The generic algebraic audit of candidate #23 is complete. The surviving
external theorem is a bound of the form

```math
\sum_i
\frac{w_i}{2r_i(r_i-2)}
\left(
T_{P_i,r_i}(Q)-T_{P_i,r_i}(Q^2)
\right)^2
\le
\mathcal B_D(Q),
```

where `mathcal B_D(Q)` fits candidate #21's remaining allowance. Proving this
requires new arithmetic distribution input, not another exact
representation.

Return top-candidate algebra work to candidate #13's independent
endpoint-sampling error `beta_i` and signed imbalance `Delta_i`. First audit
its existing properties and ticket state; do not assume #23 is proved, and do
not combine the components until both receive valid bounds.

## Validation

- Check every algebraic identity using exact rational arithmetic on a small
  chain only as a validation of the derivation.
- Passing finite examples is not evidence for the universal theorem.
- Markdown-only work requires `git diff --check`; no Stainless run is needed.
- Any future Scala change must begin from a green verification baseline and
  follow the one-change verification cycle.

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-07-27 | Dedicated #23 ticket created after #22's generic finite-Fourier program reached a coefficient-weighted bilinear boundary. | Derive the exact divisor-by-divisor quadratic kernel for `mathcal E_D` without collecting more data. |
| 2026-07-27 | The divisor-pair kernel factors exactly through activation times: `mathcal E_D=Z^T mathcal K Z` with only `m+1` signed shell sums. The kernel is positive semidefinite and entrywise nonnegative. | Promoted property #48, synchronized candidate #23, and selected the newly activated shell's CRT factorization as the next algebraic test. |
| 2026-07-28 | CRT lift indices split every new `r_i e` boundary summand into the old `e` summand plus a bounded index difference; the old boundary error cancels completely from `D_i`. | Promoted property #49, synchronized candidate #23, and selected the exact summatory-coprime interpretation to classify the remaining mean-square theorem. |
| 2026-07-28 | The lift-index transform is exactly `T_{P,r}(x)=F_P(x-1)-rF_P(floor((x-1)/r))`; it is a coordinate rewrite of the original dilation discrepancy, not an additional elementary cancellation. | Promoted property #50, synchronized candidate #23, ruled out further representation-only rewrites, and selected an applicability audit of existing mean-square results. |
| 2026-07-28 | The centered strike functions are exactly orthogonal across layers on the final CRT period, but their norms contain `P_m`; Bessel gives a genuine theorem at the unusable complete-period scale. Standard fixed-sequence large-sieve input also mismatches the changing nested sieve weights. | Promoted property #51, synchronized candidate #23, recorded complete-period Bessel as exhausted, and selected the exact localized Gram matrix as the next self-bounding test. |
| 2026-07-28 | On the actual window, `G_ij=-D_max(i,j)/r_min(i,j)` off diagonal and the diagonal is explicit in `A_i,D_i`; this removes the primorial but trace composition is exactly per-layer Cauchy. | Promoted property #52, synchronized candidate #23, recorded trace/self-bounding as exhausted, and selected the first-deletion rank-one factorization for the next spectral audit. |
| 2026-07-28 | The local Gram matrix is a sum of first-deletion rank-one blocks, and `mathcal E_D` is exactly population-times-trace minus weighted deletion-class variance. Without constraints on class masses, concentration makes the population envelope sharp. | Promoted property #53, synchronized candidate #23, recorded triangular geometry alone as exhausted, and selected the forced variance `sum c_k H_k A_(k+1)` as the next deterministic gain. |
| 2026-07-28 | The compulsory distance between deletion class `i` and all later classes gives `H_i A_(i+1)`, but `D_i^2=A_iG_(ii)-H_iA_(i+1)` exactly. The apparent forced gain is the active two-class variance itself. | Promoted property #54, synchronized candidate #23, recorded minimum-distance truncation as a loop, and selected reindexing of every remaining deletion-distance term. |
| 2026-07-28 | Reindexing every first-deletion distance by coordinate gives `sum_i c_i[H_iA_(i+1)+(A_0-A_i)G_(ii)]`; substitution collapses exactly to the original weighted strike energy. | Promoted property #55, synchronized candidate #23, completed the generic algebraic classification, and handed the next top-candidate audit to #13. |
