# Prove Algebraic Capacity Foundations for Candidates #17 and #18

**Created:** 2026-07-27
**Updated:** 2026-07-27
**Status:** Complete

**Depends on:**

- `tickets/done/prove-local-count-forces-shot-capacity-2026-07-27.md`
- `tickets/done/analyze-capacity-density-candidates-2026-07-27.md`
- `properties/sieve-sequence/two-gap-isolation-after-filter-three.md`
- `properties/sieve-sequence/local-count-forces-k2-shot-capacity.md`

## START HERE

Prove two separate algebraic foundations, one property per change:

1. the exact period-30 `r=7` capacity floor `rho(Q,7)>1` for every integer
   `Q>=17`;
2. a quantitative theorem converting local capacity surplus into a lower bound
   on raw and disjoint close-pair certificates.

Do not attempt the later-layer lower envelope until both foundations are proved
and validated. Do not update Chapter 6 articles during this ticket.

## Goal

Promote two sound mathematical properties supporting candidates #17 and #18,
align their candidate notes and catalogs, and leave the exact remaining
later-layer proof obligation explicit.

## Strategy

### Property A: exact seven-layer floor

Before filter `7`, installed filters are `{2,3,5}`. Complete 2-gap starts are
exactly residues

```text
11, 17, 29 modulo 30.
```

The eligible integer start interval has

```text
n = Q^2-Q-2
```

positions. Writing `n=30k+t`, with `0<=t<30`, every complete 30-block contains
exactly three starts, so

```text
G_7(W_Q) >= 3k.
```

For `Q>=17`, `n>=270`, hence `k>=9`. The target inequality reduces to

```text
12(3k-1) > 30k+t-1,
```

or

```text
6k > t+11,
```

which follows from `k>=9` and `t<=29`.

### Property B: surplus forces redundancy

Let `N` ordered post-filter-3 starts lie in range length `L`. Let

```text
d = 2r-2
```

and call an adjacent pair qualifying when its start difference is `<d`.
Post-filter-3 start differences are positive multiples of `6`.

Let

```text
Delta_r = 6 ceil(d/6),
```

the least multiple of `6` not smaller than `d`. If `P` adjacent differences
are qualifying, then the other `N-1-P` differences are at least `Delta_r`,
while qualifying differences are at least `6`. Telescoping gives

```text
L >= 6P + Delta_r(N-1-P).
```

Rearrangement yields a lower bound on `P`. Qualifying edges form a subgraph of
a path, whose maximum matching `D` satisfies

```text
D >= ceil(P/2).
```

This gives an algebraic disjoint-certificate lower bound from capacity surplus.

## Current State

- Candidate #17 is reinforced across 53 heads and 1,837 layers; every measured
  minimum occurs at `r=7`.
- Direct finite computation confirms the modulo-30 formula at all 53 measured
  heads, but the general `Q>=17` inequality is not yet promoted as a property.
- The full property and Chapter 6 `.holds` search found no existing theorem
  counting these starts in an arbitrary finite interval. The closest results
  are the complete-period CRT product and general periodicity/counting lemmas.
- Property A now exists as
  `properties/sieve-sequence/exact-seven-layer-capacity-floor.md`; independent
  validation passed, and it is cataloged as established property 18.
- Candidate #17 now marks `rho(Q,7)>1` as universally proved for `Q>=17`
  while retaining its later-layer lower envelope as the open hypothesis.
- Candidate #18 is reinforced by positive disjoint counts at all measured
  layers. Its note now distinguishes the proved density-to-matching conversion
  from the open uniform/unbounded conditioned-density hypothesis.
- The candidate catalog audit found stale #17 and #18 summaries: neither
  named the newly proved algebraic component. Both summaries and proof-target
  bullets are now aligned.
- The required Property B search is complete. Existing `.holds` telescoping
  lemmas prove sequence-value difference identities and positivity, but no
  existing property bounds the number of short adjacent differences or a
  matching from total span and point count.
- Property B's proposed inequalities passed 21,834,930 exhaustive finite
  cases over five prime-layer thresholds, point counts `2..8`, multiple-of-6
  gaps on both sides of each strict threshold, and several admissible span
  bounds.
- Property B now exists as
  `properties/sieve-sequence/local-density-forces-close-pair-matching.md`.
  Its Markdown integrity and link-target checks pass, and it is cataloged as
  established property 19.
- Applying its formulas to the unchanged 53-head, 1,837-layer sweep produced
  zero violations. The minimum raw and disjoint validity margins are both
  zero: raw equality occurs on 35 layers and disjoint equality on 39 layers.
- The established formulas and all theorem-bound measurements are now
  integrated into
  `empirical/sieve-sequence/capacity-density-candidates.md`.
- The unchanged repository-local lineage regression suite passes completely
  after the documentation work.
- Final static validation passes across all eight touched Markdown artifacts:
  no trailing whitespace, every local link resolves, no stale candidate status
  remains, and no Chapter 6 article or Scala source was changed.
- Strict stepwise monotonicity of the later-layer capacity ratio is false.
- No property file has yet been added in this ticket.

## What is Learned

- The exact `r=7` floor needs only periodic counting and integer inequalities;
  it does not rely on a fitted limit.
- Modulo `30`, the accepted residues are
  `1,7,11,13,17,19,23,29`. Their cyclic successor differences are
  `6,4,2,4,2,4,6,2`, so the 2-gap starts are exactly
  `11,17,29 modulo 30`.
- `exact-global-two-gap-count.md` cannot replace the local calculation: it
  gives three starts per complete period but explicitly does not locate them
  in a short interval. General `.holds` period lemmas likewise do not provide
  the finite-window quotient/remainder lower bound.
- The common `5 mod 6` residue class provides more than isolation: every start
  difference is a positive multiple of `6`, strengthening the generic
  ordered-point bound.
- Disjoint redundancy is a path-matching problem after qualifying adjacent
  differences are identified.
- The closest existing bounded-pair property starts from one already-close
  pair; it cannot establish how many close pairs the population forces.
- The exact integer lower bound is
  `P >= max(0, ceil((Delta(N-1)-L)/(Delta-6)))`. The zero floor is necessary
  when total density does not force any qualifying edge.
- Greedy matching on the qualifying-edge path achieved the expected universal
  bound `D>=ceil(P/2)` in every enumerated case.
- Candidate #18's remaining algebraic target can be stated exactly: control
  the conditioned-chain lower envelope of
  `(Delta_r(G_r(W_Q)-1)-L_Q)/(Delta_r-6)`. The new theorem converts that
  quantity into raw and disjoint certificate counts.
- Across the sweep, the algebraic raw bound captures at least `44.8276%` of
  actual `P`; the derived disjoint bound captures at least `36.3636%` of
  actual `D`.
- Median capture is `75.5162%` for raw edges and `74.3869%` for the actual
  maximum matching. The proved disjoint bound is positive on all 1,837 layers.
- The headwise minimum proved disjoint bound grows from `4` at `Q=17` to
  `3799` at `Q=997`, close to the measured actual endpoint `4043`.
- The sampled headwise minimum has exactly one decrease, from `4` at `Q=17`
  to `3` at `Q=19`; this is a finite observation, not an eventual theorem.
- Property A has a uniform positive algebraic margin:
  `12(G_7(W_Q)-1)-L_Q >= 6k-t-11 >= 14`. Thus strict positivity does not
  depend on the phase of `Q modulo 30`.
- An independent quotient/remainder checker recovered the accepted and start
  residue sets, passed all 30 worst remainder cases, and found no failure for
  any integer `17<=Q<=1,000,000`. This corroborates the derivation but is not
  used as its proof.

## Failed Paths

- **Strict layerwise monotonicity.** Already falsified empirically. Do not use
  it as an induction hypothesis. Retry only with a cumulative or lower-envelope
  invariant.
- **Treating `rho(Q,7)->6/5` as proof of `rho(Q,7)>1`.** A limit does not
  discharge finite endpoint cases. The exact `n=30k+t` inequality is required.
- **Using raw qualifying-edge count as independent redundancy.** Adjacent
  qualifying edges may share a 2-gap. Only a matching supplies distinct
  survivor certificates.
- **Repeated brute-force square-window scan.** The first independent checker
  counted every integer in `[Q,Q^2)` separately for every `Q<=10000`, giving
  an unnecessarily cubic-style cumulative workload. It was interrupted
  without changing files. Do not retry this shape; count complete periods and
  the at-most-29-position remainder directly.
- **Stale universal-status sentence.** The first candidate #17 update retained
  “No universal claim is proved,” contradicting the new universal base-floor
  theorem. The post-execution monitor caught it and the sentence was narrowed
  to “No universal later-layer claim is proved.” Do not reuse the broader
  wording.
- **Monotone headwise proved redundancy.** The 53 sampled headwise minimum
  disjoint bounds are not nondecreasing, despite growing strongly from first
  to last. Do not propose stepwise monotonicity; use an unbounded/eventual
  lower-envelope target.
- **Empirical-note notation patch context.** The first attempt to define
  `P_alg,min` expected an aligned `&=` line, while the source used a plain
  `=`. The patch did not apply and changed nothing. Retry only against the
  exact block read from lines 303-308.
- **Per-layer versus headwise equality wording.** The first candidate #18
  update said “It equals the actual bound on 39 layers” immediately after a
  headwise-minimum sentence. Review caught the ambiguous antecedent. It now
  states explicitly that `D_alg(Q,r)=D(Q,r)` on 39 individual layers.
- **Nonexistent top-level property catalog.** The catalog audit included
  `properties/README.md`, which does not exist. `rg` still returned useful
  matches from the other paths but exited with code 2. Use
  `properties/sieve-sequence/README.md` as the property catalog.
- **Wrong final-test interpreter path.** From `candidates/analysis`, the first
  invocation used `../.venv/bin/python`; that path does not exist and zero
  tests ran. Use `./.venv/bin/python test_lineage.py` from that directory.

## Open Concerns

- The period-30 residue statement must be re-derived from the actual accepted
  residues, not accepted solely from empirical code.
- The redundancy inequality direction and all ceiling/floor boundaries need
  independent finite checks.
- Property B's lower bound may be positive but weak; report its exact strength
  against data without changing the theorem to fit observations.
- The later-layer capacity floor remains the load-bearing unproved part of
  candidate #17.
- The worktree contains unrelated code/test changes. Do not alter or restore
  them.
- Per user direction, do not update Chapter 6 articles until the broader
  candidate program is complete.

## Next Action

None. This ticket is complete. The remaining later-layer lower-envelope and
conditioned surplus-growth statements are the explicitly open parts of
candidates #17 and #18, not unfinished work in these two algebraic
foundations.

## Validation

1. Search existing mathematical and Stainless lemmas before each new property.
2. Prove exactly one property per change.
3. Check strict inequalities at `Q=17` and at all residue cases `0<=t<30`.
4. Cross-check Property A against all 53 measured heads.
5. Check Property B by exhaustive finite ordered sequences before promotion.
6. Run Markdown and link checks after every documentation change.
7. If any non-Markdown file changes, run the required verification sequence.

## Learning Log

| Date | Learning | Action |
|---|---|---|
| 2026-07-27 | The empirical floor suggests two algebraic extractions: exact period-30 positivity at `r=7`, and a telescoping/matching redundancy bound from surplus. | Opened this focused ticket; search existing lemmas before drafting the exact seven-layer property. |
| 2026-07-27 | Existing proofs establish the global CRT count, post-3 isolation, and general sequence periodicity, but no local modulo-30 interval floor. Direct residue inspection gives accepted residues `1,7,11,13,17,19,23,29` and starts `11,17,29`. | Treat the finite-window quotient/remainder bound as a new property rather than misusing the global count. |
| 2026-07-27 | Added the exact seven-layer floor property. The first independent checker was computationally mis-shaped because it rescanned each entire square window for every head and was interrupted. | Keep the proof; replace only the checker with complete-period plus remainder counting, which is constant time per head. |
| 2026-07-27 | Property A passed independent checks: exact accepted/start residues, all 30 worst remainder boundaries, every integer head through one million, Markdown whitespace, and link targets. The general proof has margin at least `14`. | Catalog the established property and narrow candidate #17's unproved status to later-layer propagation. |
| 2026-07-27 | Cataloged the exact seven-layer floor as established property 18. | Update candidate #17 so its status reports the proved base floor separately from the unproved conditioned lower envelope. |
| 2026-07-27 | Candidate #17 now separates the proved base floor from open propagation. A post-edit review caught and corrected one stale sentence that denied all universal claims. | Property A is aligned. Begin the required existing-lemma search for the surplus-to-redundancy theorem. |
| 2026-07-27 | Existing sequence and cycle-integral `.holds` lemmas provide generic telescoping identities, but no theorem converts span surplus into a count of short adjacent differences or disjoint path edges. | Validate the proposed new inequality exhaustively before drafting it. |
| 2026-07-27 | The proposed raw-edge and matching bounds passed 21,834,930 exhaustive finite cases, including equality at the nonqualifying threshold. | Draft the algebraic theorem with the zero floor and strict-threshold conventions explicit. |
| 2026-07-27 | Added and integrity-checked the local-density-to-matching theorem. It proves explicit raw and disjoint lower bounds and reduces unbounded redundancy to a conditioned surplus lower envelope. | Measure the theorem's strength on the existing full empirical sweep before cataloging and aligning candidate #18. |
| 2026-07-27 | The theorem passed all 1,837 real layers and is attained with equality on some layers. It captures at least `44.8276%` of raw edges and `36.3636%` of actual disjoint certificates; headwise proved minimum grows `4 -> 3799`, but is not monotone. | Locate equality/capture quantiles, then promote the result through the property catalog, empirical note, and candidate #18 without claiming monotonicity. |
| 2026-07-27 | Detailed measurement found 35 raw-equality layers, 39 disjoint-equality layers, positive proved `D` on every layer, and median capture near 75% for both counts. The only sampled head-minimum decrease is `Q17:4 -> Q19:3`. | Catalog the theorem and add these finite results to durable empirical and candidate notes. |
| 2026-07-27 | Cataloged the local-density-to-matching theorem as established property 19. | Add the exact theorem-bound measurements to the existing empirical note before aligning candidate #18. |
| 2026-07-27 | The empirical-note integration passed content checks except that `P_alg,min` lacked a definition. The first correction patch used mismatched alignment context and did not apply. | Replace the exact unaligned block with paired aligned definitions, then re-run the note checks. |
| 2026-07-27 | Integrated the two proved properties and theorem-derived redundancy measurements into the empirical note. Final notation, whitespace, framing, and link checks pass. | Align candidate #18 with the proved algebraic conversion while preserving its open chain-wide growth claim. |
| 2026-07-27 | Candidate #18 now identifies its exact proved conversion and remaining conditioned surplus theorem. Review corrected one ambiguous sentence so 39 equality cases are explicitly layer-level, not headwise-minimum equalities. | Audit the candidate catalog and finish validation without updating Chapter 6 articles. |
| 2026-07-27 | Catalog audit found stale #17/#18 summaries. The audit also named nonexistent `properties/README.md`, causing a nonzero search exit despite useful results from the real files. | Update the two adjacent candidate catalog summaries and use only the sieve-sequence property catalog in final checks. |
| 2026-07-27 | Updated the candidate catalog: #17 reports universal base-floor positivity plus open propagation; #18 reports the proved matching conversion plus open conditioned surplus growth. | Run final read-only validation and close the ticket if green. |
| 2026-07-27 | The first final lineage-test invocation used the wrong relative virtual-environment path and ran zero tests. | Retry the unchanged suite once with `./.venv/bin/python test_lineage.py` from `candidates/analysis`. |
| 2026-07-27 | The corrected repository-local lineage regression suite passed every check (`RESULT: PASS`). | Complete static Markdown/link/status validation, then close the ticket. |
| 2026-07-27 | Final validation passed: eight touched Markdown files have no trailing whitespace, every local link resolves, candidate statuses are aligned, and scoped Git status shows no article or Scala source edits. | Marked the ticket complete and moved it to `tickets/done/`. |
