# Prove The Accepted-Strike Boundary Mean-Square Estimate

**Created:** 2026-07-27
**Status:** In progress
**Candidate:** #23 accepted-anchor strike density
**Depends on:**
`verify-19-21-escape-wall-2026-07-27.md`,
`algebraic-conditioned-survival-2026-07-27.md`

> Persistent-memory ticket. Update continuously per `TICKET_DISCIPLINE.md`.

## START HERE

Candidate #23 is the active top-candidate path after candidate #22's generic
finite-Fourier routes were exhausted. Do not collect more data.

The exact mean-square theorem and its activation-shell kernel are now stated.
The immediate micro-goal is to determine whether each newly activated divisor
shell factors through the old modulus with useful cancellation, or remains an
irreducible Möbius-residue sum.

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

For the shell activated when `r_i` is installed, derive

```math
Z_{i+1}
=
-\sum_{e\mid P_i}
\mu(e)
\frac{[Q]_{r_i e}-[Q^2]_{r_i e}}{r_i e}.
```

Use CRT to test whether the residue term modulo `r_i e` splits into an
old-modulus boundary term plus a bounded coefficient depending on `r_i`.
Keep the `mu(e)` signs intact.

If no such factorization exists, state the weakest shell mean-square theorem
directly in terms of the `Z_t` and classify which new analytic input would be
needed. Do not return to coefficientwise absolute values.

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
