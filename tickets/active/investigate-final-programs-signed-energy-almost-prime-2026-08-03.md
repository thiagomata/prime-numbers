# Investigate the Two Final Algebraic Programs

**Created:** 2026-08-03
**Updated:** 2026-08-03
**Status:** Complete — both programs have stable algebraic reductions; their
remaining estimates require new arithmetic information
**Depends on:** `quantifier-screen-refutation-targets-2026-08-03.md`
(complete, 30 valid / 0 invalid / 0 unknown baseline)

## START HERE

Work on two deliberately separate final programs:

1. **Twin-prime track:** obtain genuinely new signed arithmetic control of
   candidate #23's accepted-boundary discrepancies strong enough to reduce
   candidate #24's weighted harmful-excess energy.
2. **Almost-prime track:** specialize candidate #25's relaxed weight to the
   exact sieve-sequence algebra and identify the first honest Type-I or
   bilinear theorem that can be proved without importing the desired
   positivity.

Do not restart representation-only #23 algebra, capacity-only #24 envelopes,
undirected empirical sweeps, or the claim that complete-period CRT is already
a short-interval Type-I theorem.

## Related Tickets

- `quantifier-screen-refutation-targets-2026-08-03.md` — completed the
  25-candidate closure audit and selected these two final programs.
- `verify-19-21-escape-wall-2026-07-27.md` — contains the properties from Terminal Harmful-Excess Energy through Filter-Seven Excess Bound and
  exhausts the separate/native capacity route for #24.
- `prove-accepted-strike-mean-square-2026-07-27.md` — completes candidate #23's
  generic activation/CRT/Gram/first-deletion audit; further progress requires
  new arithmetic rather than another coordinate rewrite.
- `algebraic-conditioned-survival-2026-07-27.md` — proves that the harmful
  scalar energy is terminal and records the direct restricted-#12 bridge.
- `prove-hereditary-shot-spacing-2026-07-23.md` — checks the Type-II/parity
  boundary and identifies the almost-prime pivot as a genuinely different
  goal.

## Goal

For each final program, derive one precise new intermediate theorem candidate
whose truth would materially advance the program and whose falsity can be
tested algebraically. Complete the ticket when both tracks have an
evidence-backed verdict: a proved new lemma/property, an exact obstruction, or
a sharply stated remaining estimate with all representation-only work removed.

## Strategy

### Track A — Signed boundary energy (#23 -> #24)

Start from the Filter-Seven Excess Bound property's exact filter-`7` interval-order saving and candidate
#23's identity for the general coefficient `b_i`. Search existing properties
and lemma bodies before writing anything. Derive the exact prefix-recursive
relation when a native accepted set is enlarged by one filter, retaining signs
and actual interval endpoints. The first target is not a final mean-square
bound; it is a sub-native recursion that separates a bounded boundary increment
from the inherited prefix discrepancy.

Test whether the recursion yields one of:

- a martingale-difference or orthogonality relation under an explicit average;
- a deterministic square-function inequality with a non-primorial norm; or
- an exact obstruction showing that the inherited term can align with every
  boundary increment.

### Track B — Relaxed almost-prime weight (#25)

Fix `X=Q^2`, one dyadic subinterval below `Q^2`, and
`z=X^alpha` for a fixed `alpha>1/3`. Use the project-specific survivor weight,
not bare Chen-pair existence. Derive the exact divisor-dependent local factor
for

```text
n survives primes below Q,
n+2 avoids primes below z,
m divides n.
```

The first target is an exact Type-I main-term formula plus a named boundary
remainder for one divisor `m`, including the cases where `m` shares primes with
the installed wheel or `P(z)`. Only after that formula is correct should the
ticket ask whether the remainders sum over `m` in a nontrivial range.

Then identify the smallest genuine bilinear family exposed by a factor split
of `n`, `n+2`, seed residue, or final-head averaging. If no extra variable
appears, record that as a no-go result rather than relabeling unsigned density
as Type II cancellation.

## Current State

- Candidate #23's bulk term cancels exactly and its discrepancy is a signed
  adjacent boundary difference. Activation-shell, CRT-lift, summatory,
  complete-period orthogonality, localized Gram, and first-deletion rewrites
  are already classified.
- Candidate #24's terminal threshold is proved. The properties from Integral Profile Attainment through Capacity Stability Gap exhaust
  the current conservation/capacity/native-period envelopes. The Filter-Seven Excess Bound property
  proves a real localized saving at filter `7`, but its general coefficient is
  exactly candidate #23's accepted-boundary discrepancy.
- Candidate #25 now states a project-specific relaxed-weight positivity target
  for some fixed `alpha>1/3`. The analytic deep-dive specifies Ford--Maynard
  Type-I/Type-II requirements but does not derive the divisor-local comparison
  sequence from the sieve-sequence definitions.
- Track A's proposed accepted-anchor prefix recursion is pre-empted: property
  #49 already cancels the inherited old boundary term by CRT lift indices, and
  The Strike Summatory Remainder property proves that the remainder is exactly the original summatory
  coprime dilation discrepancy.
- A distinct one-filter block identity survives the search. If `c_t` is the
  old-period start histogram modulo incoming prime `r`, `d_t=c_t-N/r`, and
  `t=-jM modulo r`, then the centered harmful excess in copy block `j` is
  exactly `B_j=d_t+d_(t-2)`. Hence
  `sum_j B_j^2=2V+2sum_t d_t d_(t-2)<=4V`, where
  `V=sum_t d_t^2`. A run of `k` complete old-period blocks therefore has
  squared discrepancy at most `4kV`.
- That identity is now promoted as the Copy-Block Excess Control property, **Copy-Block Harmful Excess
  Is Controlled By Residue Energy**, cataloged in the sieve-sequence property
  index, and linked from candidates #20 and #24. Track A's exact algebraic
  bridge is complete; its remaining obstacle is arithmetic control of residue
  energy together with the two partial old-period boundary fragments.
- For Track B, put `W=P(Q)`, `Z=P(z)`, assume `2|W`, and count `n=mk` in an
  interval subject to `gcd(n,W)=1` and `gcd(n+2,Z)=1`. If `gcd(m,W)>1`, the
  count is exactly zero. If `gcd(m,W)=1`, the allowed `k` residues at a prime
  `p|WZ` number `p-1` for `p|W, p\nmid Z`, one for `p=2|W,Z`, `p-2` for odd
  `p|W,Z`, `p` for odd `p|Z, p\nmid W, p|m`, and `p-1` for odd
  `p|Z, p\nmid W, p\nmid m`. CRT therefore gives an exact divisor-dependent
  complete-period factor and an arbitrary-interval boundary remainder.
- That formula is now promoted and cataloged as the Divisor Local Factor property, **Relaxed
  Almost-Prime Weight Has An Exact Divisor Local Factor**, and candidate #25
  now states the exact comparison density and accumulated signed Type-I
  remainder rather than an unspecified Type-I analogy.
- In the nested range `Z|W`, the centered bilinear relaxed condition has the
  exact expansion
  `sum_(d|Z/2) mu(d)[1_(n=-2m^(-1) mod d)-1/phi(d)]` after both factors are
  restricted to be wheel-coprime. Character orthogonality converts every
  bracket into nonprincipal modes proportional to `chi(m)chi(n)`.
- the Bilinear Character Obstruction property now proves and catalogs that exact inverse-residue/character
  decomposition. Its complete-wheel modulo-`3` example refutes scalar-density
  Type-II orthogonality at full survivor scale; the auxiliary route is saved
  in `candidates/refuted/` without refuting candidate #25.
- the Cofactor Progression Discrepancy property now proves the natural pre-sieved shifted-divisor identity.
  For odd `d|P(z)` in the square-safe window,
  `A_d(I)-A_1(I)/phi(d)=pi(I;d,-2)-pi(I)/phi(d)`. The missing accumulated
  Type-I input is therefore exactly an averaged prime-progression theorem.
- No numbered candidate is currently refuted. Candidate #4's constant `R<=2`
  auxiliary route is separately refuted and irrelevant to these tracks.
- Stainless baseline is 30 valid, 0 invalid, 0 unknown. Initial work is
  mathematical/Markdown; any Scala change requires green-to-green chapter
  verification and one lemma per cycle.

## What is Learned

- The next #23 result must add arithmetic cancellation. Algebraically exact
  reindexing alone has repeatedly returned the original energy.
- The first #25 obligation is not positivity. It is the correct
  divisor-dependent comparison model and its boundary remainder; without it,
  “Type I” is only an analogy.
- The tracks share a short-window boundary problem but have different terminal
  strength: #23/#24 seeks twin-prime positivity, while #25 permits a two-factor
  cofactor and may admit a different bilinear range.
- The copy-block identity gives a nontrivial bridge from candidate #20's
  one-layer residue energy to candidate #24's localized harmful excess. It
  controls complete old-period blocks but leaves the two partial boundary
  fragments of an arbitrary interval untreated.
- In the useful range `1/3<alpha<1/2`, one has `Z|W`. For every
  `gcd(m,W)=1`, Track B's local density becomes independent of `m` and equals
  `(1/2) prod_(2<p<z)(1-2/p) prod_(z<=p<Q)(1-1/p)`; non-coprime divisors have
  density zero. This is dimension two below `z` and dimension one from `z`
  to `Q`.
- The exact CRT formula supplies the correct one-divisor comparison sequence,
  but its trivial boundary error is at most one complete modulus. Since that
  modulus is primorial-sized, the formula alone is not an accumulated Type-I
  theorem. The next honest obligation is cancellation after summing these
  boundary remainders over divisors.
- The first genuine Type-II family is therefore an inverse-residue, or
  equivalently nonprincipal-character, bilinear family over squarefree
  divisors of `Z/2`. It is not representation-only: arbitrary coefficients
  can correlate perfectly with an individual character mode. Consequently a
  theorem centered only by the scalar density cannot follow from formal
  orthogonality; it needs locally adapted comparison/removal or additional
  restrictions on the coefficient family.

## Expected State

- Track A has an exact sub-native signed recursion or a proved reason that the
  proposed recursion supplies no new norm reduction.
- Track B has an exact one-divisor local-factor formula with all shared-prime
  cases and a precise accumulated Type-I remainder target.
- Each track names its first arbitrary-sign/bilinear obligation and explains
  whether existing properties contribute to it.
- Durable results are promoted into `properties/` or the corresponding
  candidate file; failed universal statements go to `candidates/refuted/`.

## Approaches Considered

### A1. Sub-Native Prefix Recursion

**Status:** REFINED

The accepted-anchor version duplicates the properties from Strike CRT Lift-Index through Strike Summatory Remainder. The surviving
version groups the paired harmful observable into complete old-period copy
blocks and relates its block sequence to the old-period residue histogram.

**Strengths:** Directly generalizes the mechanism behind the Filter-Seven Excess Bound property and does
not introduce the final primorial norm.
**Risks:** Candidate #20's residue energy is itself open, and arbitrary
intervals leave two uncontrolled partial old-period blocks.
**Fallback:** Preserve the exact identity as a composition bridge and classify
the boundary fragments as the remaining obstruction.

### A2. Repeat Generic Gram/Bessel Algebra

**Status:** BLOCKED

The properties from Strike Divisor-Activation Kernel through First-Deletion Reindexing and #71 already classify this route. Complete-period norms
retain the primorial, while localized trace bounds reproduce per-layer Cauchy.

**Retry condition:** A new arithmetic restriction on boundary/deletion-class
masses, not another factorization identity.

### B1. Exact One-Divisor Type-I Model

**Status:** EXACT LOCAL FACTOR DERIVED; ACCUMULATED REMAINDER OPEN

Compute the local density and boundary remainder after imposing `m|n`, with
all gcd interactions explicit.

**Strengths:** Necessary, finite, exact, and independent of the final positive
lower bound.
**Risks:** The remainder may remain of full boundary size once the modulus
exceeds the interval.
**Fallback:** Prove the exact obstruction and identify what averaging variable
would be required.

### B3. Scalar-Centered Final-Weight Type II

**Status:** REFUTED AS A COMPLETE-WHEEL UNIVERSAL LAW

The Bilinear Character Obstruction property proves that the final relaxed weight retains nonprincipal local
character modes after scalar centering. Modulo-`3` product coefficients attain
the full relaxed survivor count on the complete reduced wheel.

**Retry condition:** Use a locally adapted comparison, a justified restricted
coefficient family, or the pre-sieved shifted-divisor sequence. Do not retry
formal scalar-density orthogonality.

### B4. Pre-Sieved Shifted-Divisor Program

**Status:** EXACT REDUCTION PROVED; PRIME-PROGRESSION AVERAGE OPEN

The Cofactor Progression Discrepancy property identifies the divisor remainder exactly with the progression
discrepancy for certified primes. This is now the recommended formulation.

### B2. Import Chen's Theorem as the Project Proof

**Status:** BLOCKED BY SCOPE

Chen establishes existence but does not prove positivity from these weights.

**Retry condition:** None; external existence remains background, not the
project-specific candidate.

## Assumptions

- Candidate and property definitions at HEAD are authoritative; tickets are
  descriptive and must be checked against them.
- `P(z)` means the product of primes strictly below `z`.
- Square-safe survivors in `[Q,Q^2)` are prime after all required filters below
  `Q` are installed.
- `alpha>1/3` is fixed independently of `Q` in candidate #25.
- Exact complete-period identities may supply local factors but not
  short-interval error bounds without a separate argument.

## Risks

- Accidentally rebuilding an exhausted #23 representation under new notation.
- Squaring a signed recursion before locating its cancellation source.
- Choosing a constant-density comparison sequence for #25 and ignoring local
  factors when divisors share wheel primes.
- Calling an unsigned bilinear count a Type-II theorem; arbitrary coefficient
  control is essential.
- Treating a failed method as a refutation of either infinitely-many
  candidate.

## Validation

- Deep-search existing `.holds` lemmas, mathematical properties, and ticket
  failure logs before proposing any new lemma.
- Check every exact identity on small finite wheels as a falsifier, but do not
  treat finite agreement as proof.
- State population, interval, filter scope, quantifier, and proof status using
  `VOCABULARY.md`.
- Markdown-only changes require `git diff --check` and link checks.
- Any non-Markdown change requires the chapter-by-chapter regression path,
  starting from the current 30/0/0 baseline.

## Failed Paths

- **Generic #23 activation/CRT/Gram/first-deletion rewrites:** exact but return
  the original weighted energy or unusable primorial norm. Retry only with new
  arithmetic constraints or averaging.
- **Accepted-anchor sub-native recursion:** pre-empted by the properties from Strike CRT Lift-Index through Strike Summatory Remainder;
  the inherited boundary cancels and the remaining lift-index transform is
  exactly the original dilation remainder. Retry only with a new averaged
  estimate, not another recursion formula.
- **#24 capacity/native-period envelope optimization:** the properties from Integral Profile Attainment through Capacity Stability Gap
  exhaust the current route, including its stability-gap repair. Retry only
  with signed information not present in separate capacities.
- **#25 constant-density comparison model:** invalid when the divisor shares
  primes with the wheel or relaxed cofactor sieve. Retry only with
  divisor-dependent local factors.
- **#25 bare Chen existence:** externally known and not the project-specific
  proof obligation.
- **Candidate #24 synchronization patch, first attempt:** the patch context did
  not match the current Markdown and made no change. Reading the exact section
  and retrying once with current context succeeded; this was a mechanical
  patch failure, not a failed mathematical route.
- **the Divisor Local Factor property Related link, first validation:** the initial property used
  the nonexistent filename `exact-batch-survival.md`. Validation caught it;
  the sole red-state action corrected the link to the existing
  `exact-batched-two-gap-survival.md`, after which all checks passed. This was
  a documentation-link failure, not a mathematical failure.
- **the Cofactor Progression Discrepancy property deep search, first command:** a combined ripgrep expression
  used an unsupported escape and failed before searching. A read-only retry
  with fixed-string patterns succeeded and found no existing shifted-divisor
  property. This was a search-syntax failure and made no repository change.

## Open Concerns

- the Filter-Seven Excess Bound property may rely on the exceptional fixed modulo-`210` order and fail
  to expose a scalable recursion.
- The correct #25 weight uses a survivor condition for `n` and a separate
  relaxed condition for `n+2`; symmetric pair-survivor formulas may over-sieve
  the prime side or hide shared local factors.
- A genuine #25 Type-II family may require averaging over heads or seed
  residues, expanding the theorem beyond one fixed window. Such an expansion
  must still imply the candidate's stated positivity.
- the Bilinear Character Obstruction property proves that a scalar comparison cannot remove fixed local
  character modes. The unresolved formulation question is how much local
  structure must be absorbed while retaining a nonvacuous theorem that still
  feeds the lower-bound almost-prime sieve.
- the Cofactor Progression Discrepancy property moves the first arithmetic obligation into prime distribution
  in progressions. Proving it purely from current sieve-sequence properties is
  not expected; importing an analytic theorem would require matching its
  modulus range and interval uniformity to the candidate exactly.

## Next Action

Stable handoff:

1. For Track A, attempt candidate #20's relative residue-energy theorem only
   if a new arithmetic estimate controls `V_r` in late short windows; property
   #83 already supplies the composition into #24.
2. For Track B, select an explicit prime-progression theorem and check whether
   its divisor range and interval uniformity prove the Cofactor Progression Discrepancy property's accumulated
   target. Only then formulate the corresponding pre-sieved bilinear
   remainder, with all local character modes accounted for.
3. Do not collect more undirected empirical data or restart the refuted
   scalar-density Type-II route.

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-08-03 | Ticket created after the 25-candidate closure audit selected #23->#24 signed cancellation and #25 relaxed-weight Type-I/Type-II as the two final programs. Prior searches show #23's generic algebra and #24's capacity envelopes are exhausted, while #25 lacks a project-specific divisor-local model. | Start with Track A's sub-native prefix recursion; do not write a new lemma until existing property bodies are read. |
| 2026-08-03 | The accepted-anchor recursion is exactly the properties from Strike CRT Lift-Index through Strike Summatory Remainder and is pre-empted. A distinct copy-block identity survives: block harmful excess is a paired residue-histogram deviation, with total block energy at most four times candidate #20's residue energy. | Promote the exact one-filter bridge and its partial-boundary limitation, then advance to #25. |
| 2026-08-03 | the Copy-Block Excess Control property now records and catalogs the exact copy-block bridge; candidates #20 and #24 are synchronized. Track A has reached a stable reduction: complete blocks are controlled by residue energy, while partial fragments and the residue-energy estimate remain open. | Treat Track A's representation work as complete and do not restart accepted-anchor or generic Bessel rewrites. |
| 2026-08-03 | Track B's exact local factor is divisor-dependent in general. When `1/3<alpha<1/2`, `P(z)|P(Q)`, coprime divisors share one explicit density and non-coprime divisors contribute zero. The remaining one-divisor error is a periodic boundary discrepancy, not yet a Type-I average. | Promote the exact formula, then expose the inverse-residue bilinear family created by expanding the relaxed cofactor sieve. |
| 2026-08-03 | the Divisor Local Factor property now proves and catalogs the exact one-divisor local factor; candidate #25 names the accumulated signed remainder. Its initial Related link was stale and was corrected under red-cascade discipline before further work. | Treat scalar local density as solved bookkeeping, not as Type-I cancellation. |
| 2026-08-03 | Möbius expansion of the centered relaxed condition gives exact inverse-residue brackets, and character orthogonality diagonalizes them into nonprincipal `chi(m)chi(n)` modes. Arbitrary coefficients can select an individual mode, so scalar-density centering alone cannot yield formal Type-II cancellation. | Promote the decomposition and classify the naive scalar-density Type-II route as blocked, not the candidate itself. |
| 2026-08-03 | the Bilinear Character Obstruction property proves the exact bilinear character family. The modulo-`3` character has full-survivor correlation on the complete reduced wheel, so scalar-density Type-II orthogonality and every strict uniform contraction are refuted auxiliary laws. | Save the refutation; move the viable program one level earlier than the final sifted indicator. |
| 2026-08-03 | the Cofactor Progression Discrepancy property proves that the pre-sieved shifted-divisor remainder is exactly `pi(I;d,-2)-pi(I)/phi(d)` in the square-safe window. The first Type-I input is therefore a prime arithmetic-progression average, not further CRT bookkeeping. | Close this investigation with a stable handoff to theorem matching; retain candidate #25 as open. |
