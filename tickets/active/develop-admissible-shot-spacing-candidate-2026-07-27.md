# Develop #15 Admissible-Tuple Shot-Spacing Theory

**Created:** 2026-07-27
**Updated:** 2026-07-27
**Status:** Complete — candidate created, proved results promoted, empirical
falsifier sweep recorded
**Related tickets:**
`prove-hereditary-shot-spacing-2026-07-23.md`;
`lineage-experiment-2026-07-23.md`

## START HERE

This ticket is complete. It produced:

1. the theorem that fixed-`k` wheel spacing stabilizes at the minimum
   admissible diameter `D(k)`;
2. exact values
   `D(2..10)=(2,6,8,12,16,20,26,30,32)`;
3. a complete-period theorem forcing two 2-gaps inside a cyclic arc of length
   `8`;
4. candidate #15 with proposed
   `D(11..14)=(36,42,48,50)`;
5. an exact `k=2` sweep over 53 heads and 1,837 layers with no interval
   failure.

Resume only through a focused follow-on ticket for the `D(11)..D(14)` lower
certificates, general recurrence/extremal bounds, or square-window placement.
Candidate #14 remains a downstream application.

## Goal

Create a new candidate centered on the intrinsic theory of fixed-`k`
shot-spacing in primorial wheels. Promote every deductively proved theorem to
`properties/`, retain only genuinely unproved sharp-value, recurrence,
extremal, or clustering statements in the candidate, and relate the result
honestly to candidate #14.

## Strategy

Work from the wheel minimum span

```math
s_P(k)
=
\min_i\sum_{t=0}^{k-2}g_{i+t},
\qquad
\sigma_r(k)=r\,s_P(k).
```

The first route is constructive. For fixed `k`, use

```math
B_k=\prod_{p\le k}p,
\qquad
H_k=\{0,B_k,\ldots,(k-1)B_k\}.
```

For every prime `p`, the forbidden translations of `H_k` occupy fewer than
all residues modulo `p`. CRT should therefore place a translate of `H_k`
inside every finite primorial wheel. Combined with the already proved
monotonicity of `s_P(k)`, this may give a uniform upper bound and eventual
stabilization.

The second route is extremal. Define `D(k)` as the minimum diameter of an
admissible `k`-point integer set. Prove both inequalities between the eventual
wheel span and `D(k)` if possible. Exact values and recurrence laws are then a
finite-pattern problem rather than an extrapolation from wheel prefixes.

This route is preferred over beginning with another `Q` sweep because it can
produce universal sieve-sequence facts independent of candidate #14.

## Current State

- The repository already proves that filtering cannot decrease minimum
  `k`-span and that `s_P(2)=2`.
- The previous claim that monotonicity alone proves stabilization was invalid
  and has been withdrawn.
- Define `D(k)` as the minimum diameter of a globally admissible `k`-point
  integer set. The construction `H_k={0,B_k,...,(k-1)B_k}` proves that `D(k)`
  exists and `D(k)<=(k-1)B_k`.
- **Audited theorem:** if a primorial wheel contains every prime `p<=k` and its
  period satisfies `M>(k-1)B_k`, then

  ```math
  s_P(k)=D(k).
  ```

  The upper inequality translates a diameter-`D(k)` admissible tuple into the
  wheel by CRT. For the lower inequality, a minimizing cyclic `k`-block has
  span `<M` and normalizes to `k` integer offsets. It misses a residue modulo
  every installed prime `p<=k`; every prime `p>k` is automatically missed
  because only `k<p` offsets exist. Hence the normalized block is globally
  admissible and cannot have diameter below `D(k)`.
- Eventual fixed-`k` stabilization follows immediately from this equality.
  Monotonicity remains a separate inherited lower-bound theorem.
- The supplied 200-stage prefixes provide empirical target values but do not
  prove full-period minima or eventual equality.
- Q101 has exact finite `k=2` interval certificates at all 23 defined layers;
  this is evidence for candidate #14, not a universal clustering theorem.
- The characterization theorem is now promoted into
  `properties/sieve-sequence/stable-small-k-shot-spacing.md`, alongside the
  independent monotonicity proof. It is math-only; Stainless verification is
  not claimed.
- Candidate #15 now exists at
  `candidates/sharp-admissible-shot-spacing-profile.md`. Its main concrete
  conjecture is the exact table `D(2)..D(10)`; recurrence and local-clustering
  transfer are explicitly open extensions.
- The properties and candidates catalogs now index the theorem and candidate
  separately. Related #14 and empirical notes have been corrected to say that
  stabilization is proved while exact `D(k)` values remain open.
- All nine listed diameter witnesses were checked prime-by-prime and are
  admissible, so the proposed values are proved upper bounds.
- Exhausting normalized even `k`-sets below each proposed diameter found no
  smaller admissible set. The largest search has 5,005 cases. This supports
  the matching lower bounds.
- A transparent residue-cover certificate is now available. After
  normalization, admissibility modulo `2` forces all offsets even. For proposed
  diameter `d_k`, choose the remaining `k-1` points from
  `{2,4,...,d_k-2}`. If `n_j` counts these offsets in residue class `j`
  modulo `3`, the number not already rejected by covering all three classes is

  ```math
  {n_0+n_1\choose k-1}
  +
  {n_0+n_2\choose k-1}
  -
  {n_0\choose k-1}.
  ```

  For `k=3..10` this leaves respectively
  `0,0,0,1,2,16,18,20` cases. Every remaining case covers all residues modulo
  `5`, except two `k=8` patterns; those two cover all residues modulo `7`.
  Hence every shorter pattern is inadmissible, proving the proposed lower
  bounds.
- The exact `k=2` application sweep covered 53 prime heads (every prime
  `17<=Q<=251`, plus `307,401,503,701,997`) and 1,837 defined filter layers.
  No interval-premise failure occurred. The nearest-pair enclosure was at most
  `8` throughout; the worst ratio to exact capacity `2r` was `0.8` at `r=5`.
- The admissible pattern `{0,2,6,8}` gives a complete-period clustering
  theorem: every sufficiently deep complete wheel contains two 2-gaps in a
  cyclic arc of length `8`. This does not place the cluster inside an absolute
  square window.
- The exact admissible-diameter profile
  `D(2..10)=(2,6,8,12,16,20,26,30,32)` is proved by explicit upper witnesses
  and a finite residue-cover lower certificate.
- Candidate #15 has been advanced to the next open profile
  `D(11..14)=(36,42,48,50)`. Explicit upper witnesses are proved; exhaustive
  searches found no smaller patterns, but compact lower certificates remain
  open.

## What is Learned

- A monotone integer sequence stabilizes only after a uniform upper bound is
  proved.
- An admissible `k`-tuple is a natural source of such an upper bound: CRT can
  translate it away from every prime dividing a finite wheel.
- Having at least `k` accepted points in an arc of length `L` is sufficient
  for `s_P(k)\le L`; the selected points need not already be consecutive,
  because some consecutive `k`-block inside the arc has no larger span.
- A `k`-point pattern is globally admissible once it is known to miss a residue
  modulo every prime `p<=k`; primes `p>k` cannot be fully covered by only `k`
  offsets.
- The stable wheel value is not merely bounded by admissible tuples: it equals
  their minimum possible diameter `D(k)` after an explicit finite threshold.
- Determining exact stable values is therefore the extremal finite-pattern
  problem of determining `D(k)`, rather than an extrapolation problem over
  ever-larger primorials.
- For the proposed `k<=10` values, every shorter normalized even pattern in the
  finite search covers all residues modulo `3`, `5`, or `7`. No counterexample
  to the table was found.
- Combined with the explicit admissible witnesses, the residue-cover
  certificate proves the exact values `D(2)..D(10)`. These values are ready
  for promotion to `properties/`.
- The repeated empirical nearest-pair length `8` has a structural explanation
  over complete wheels: `{0,2,6,8}` is admissible. The remaining difficulty is
  translate location in a partial period, not existence somewhere in the
  cycle.
- Exact finite observations and universal wheel theorems must remain in
  `empirical/` and `properties/`, respectively. The new candidate should
  contain only the remaining unproved sharpening.

## Failed Paths

- **Monotonicity alone implies stabilization.** Invalid because a monotone
  non-decreasing integer sequence may be unbounded. Retry only with a proved
  uniform upper bound; the admissible-pattern construction is precisely such
  a new ingredient.
- **Treat the finite `k=2..10` table as exact at arbitrary stages.** Invalid
  because finite wheel or prefix agreement does not prove persistence. Retry
  an exact value only with a persistent admissible witness plus a matching
  lower bound or exhaustive counterexample argument below that diameter.
- **Make hereditary interval survival the central theorem.** This entangles
  intrinsic wheel geometry with conditioned short-window clustering. Retry
  only as an application after the capacity theory is established.
- **Infer square-window clustering directly from complete-period CRT.** CRT
  places an admissible translate somewhere modulo the full primorial; it does
  not control whether a translate lies in `[Q,Q^2)`, which is a partial-period
  window. Retry only with an additional location or discrepancy theorem.

## Open Concerns

- The CRT construction must be stated in cyclic coordinates carefully,
  including the requirement that the wheel period eventually exceeds the
  pattern diameter.
- The theorem currently has a mathematical proof but no Stainless
  implementation. Any article must label that distinction explicitly.
- Exact recurrence under installing a prime may be a word-level transformation
  rather than a closed scalar recurrence for `s_P(k)`.
- The analysis table through `k=10` is now mathematically justified. Any
  future table entry beyond `k=10` must remain gated or explicitly heuristic.
- Two tracked Chapter 6 test files were already missing from the shared
  worktree before this ticket began. Do not restore or alter them as part of
  this Markdown-only task.
- One ticket-transition edit in this pass was applied after an informal
  announcement but without the formal Worker/Critic/Monitor pre-execution
  blocks. Content passed review; count it as process attempt 1.

## Next Action

This ticket is complete. Follow-on work should open a new focused ticket for
exactly one of:

1. compact residue-cover lower certificates for `D(11)..D(14)`;
2. recurrence or extremal bounds for general `D(k)`;
3. a copy-index/location theorem placing the complete-period length-8 cluster
   inside relevant square windows.

Do not combine these into one proof attempt; they are distinct mathematical
obligations.

## Validation

- Search existing `.holds` lemmas and mathematical notes before asserting a
  new result.
- Check every implication against the cyclic definition of `s_P(k)`.
- Use the trusted 200-stage CSV only as empirical evidence or a finite
  counterexample source.
- Markdown-only changes require `git diff --check` and consistency review, not
  Stainless verification.

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-07-27 | User reframed the research: develop `sigma_r(k)` theory first, sweep `Q` for falsifiers, seek copy-index clustering, and treat hereditary survival as an application. | Opened this related ticket and prioritized the admissible-pattern stabilization argument before empirical expansion. |
| 2026-07-27 | Audited the CRT construction against cyclic wheel coordinates and the source model. A minimizing block below the explicit period bound normalizes to a globally admissible pattern, giving the converse inequality as well as the CRT upper bound. | Established the math-only theorem `s_P(k)=D(k)` once the wheel contains all primes `<=k` and `M>(k-1)B_k`; selected property promotion as the next action. |
| 2026-07-27 | Promoted the fixed-`k` theorem into the spacing property note. The proof now separates monotonic inheritance from admissible-pattern stabilization and leaves exact `D(k)` values open. | Set candidate #15 drafting as the next action, centered on the sharp profile, recurrence, and local realization rather than hereditary survival. |
| 2026-07-27 | Created candidate #15 with exact `D(2)..D(10)` as its first falsifiable target. Checked every proposed witness for admissibility and exhaustively searched all normalized even patterns below each proposed diameter; no smaller admissible pattern exists in the finite search. | Kept equality conjectural pending a transparent residue-cover certificate; selected catalog and stale-claim alignment as the next action. |
| 2026-07-27 | Indexed candidate #15 and the fixed-`k` theorem, then corrected related #14/empirical descriptions. No stale claim that fixed-`k` stabilization is unproved remains in current documentation. | Selected the user-prioritized exact `k=2` Q-sweep as the next action. |
| 2026-07-27 | Swept 53 prime heads and 1,837 exact `k=2` layers with no failure; every nearest-pair enclosure was at most 8. Recognized `{0,2,6,8}` as the complete-period structural source of that cluster shape. | Selected promotion of the complete-period cluster theorem and empirical recording of the sweep; retained absolute square-window placement as the open boundary. |
| 2026-07-27 | One ticket-transition edit omitted the formal pre-execution pipeline blocks after an informal announcement. | Recorded process attempt 1 and restored the full gate for subsequent modifications. |
| 2026-07-27 | Converted the no-smaller-pattern search into a finite residue-cover certificate: parity normalizes to even offsets, a binomial modulo-3 count leaves at most 20 cases, modulo 5 rejects all but two `k=8` cases, and modulo 7 rejects those two. | Marked exact `D(2)..D(10)` ready for property promotion and narrowed the future candidate scope accordingly. |
| 2026-07-27 | Promoted exact `D(2)..D(10)`, proved complete-period length-8 two-gap clustering, restored the analysis table through `k=10` as exact, and moved candidate #15 to proposed `D(11)..D(14)`. Final consistency search and `git diff --check` passed. | Marked this scoped ticket complete. Follow-on work is split into exact-profile certificates, general recurrence/extremal theory, or square-window location. |
