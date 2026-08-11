# Analyze Capacity-Density Candidates for #14

**Created:** 2026-07-27
**Updated:** 2026-07-27
**Status:** Complete

**Depends on:**

- `tickets/done/prove-local-count-forces-shot-capacity-2026-07-27.md`
- `tickets/active/prove-hereditary-shot-spacing-2026-07-23.md`
- `tickets/active/lineage-experiment-2026-07-23.md`

## START HERE

This ticket is complete. It created two non-redundant candidate conditions
suggested by the proved count-to-`k=2` lemma and tested their exact stated
metrics across the established 53-head lineage sweep.

The two candidates are:

The durable outputs are:

1. `candidates/seven-layer-capacity-floor.md`;
2. `candidates/redundant-close-pair-capacity.md`;
3. `empirical/sieve-sequence/capacity-density-candidates.md`;
4. aligned candidate and empirical catalogs.

Resume only through a focused proof ticket for the later-layer capacity floor,
a fixed-fraction disjoint-certificate bound, or a larger sparse falsifier
sweep. Do not rerun the same dense small-Q analysis without a new falsifier.

## Goal

Add two candidate notes, index them, run a finite falsification-oriented
analysis across every prime head `17<=Q<=251` plus
`307,401,503,701,997`, and publish one empirical note containing definitions,
results, limitations, and the next mathematical target.

## Strategy

For each future head `Q` and conditioned layer `r>=5`, let

```text
L_Q = Q^2-Q-3
G = G_r(W_Q)
rho(Q,r) = (G-1)(2r-2)/L_Q.
```

The proved local-count theorem gives

```text
rho(Q,r)>1  ==>  candidate #14's k=2 premise at layer r.
```

Candidate A tests the stronger lower-envelope hypothesis

```text
rho(Q,r) >= rho(Q,7) > 1
```

throughout a chain. Candidate B counts consecutive start pairs satisfying

```text
x_{i+1}+2-x_i < 2r
```

and counts half-open blocks of length `2r-2` containing at least two starts.

This approach is preferred over another nearest-pair-only sweep because it
measures margin and redundancy. The empirical goal is falsification and
scaling, not promotion to `properties/`.

## Current State

- The count-to-`k=2` property is proved, cataloged, and linked from candidate
  #14.
- Stored Q17 and Q101 lineages have `rho>1` at every applicable layer.
- Their minimum capacity ratios occur at `r=7`:
  - Q17: approximately `1.159851`;
  - Q101: approximately `1.199168`.
- Strict layerwise monotonicity is already false: Q17 has one decrease and
  Q101 has five. Only a chain-wide lower-envelope hypothesis remains viable.
- `candidates/seven-layer-capacity-floor.md` now states the first candidate,
  its equivalent division-free form, conditional implication, and empirical
  falsifiers.
- `candidates/redundant-close-pair-capacity.md` now states the second
  candidate, proves the one-layer disjoint-certificate lower bound, and defines
  raw, disjoint, and canonical-block metrics.
- Neither candidate is indexed yet because its empirical status is still
  pending.
- The expanded density sweep has not yet run. No source modification has been
  needed.
- The first lineage-test invocation failed before test execution because the
  system `python3` cannot import NumPy. The repository-local analysis virtual
  environment exists.
- The unchanged lineage suite passes completely under
  `candidates/analysis/.venv/bin/python`.
- The established 53-head sweep completed in memory with no source or data
  writes:
  - 53 heads and 1,837 applicable layers;
  - zero `destroyed+surviving==G` failures;
  - zero `B_2<=D` failures;
  - zero layers with `rho<=1`;
  - every head has its minimum `rho` at `r=7`;
  - `rho(Q,7)` ranges from approximately `1.132743` to `1.199989`;
  - zero layers have `D=0` or `B_2=0`;
  - `D_min(Q)` ranges from `8` at Q17 to `4043` at Q997;
  - fitted `D_min` log-log slope is approximately `1.572157`, with
    correlation `0.998923`.
- Independent validation also passes:
  - the direct period-30 formula for `G_7(W_Q)` matches the lineage population
    at all 53 heads;
  - fresh recomputation matches all 4 applicable stored Q17 rows and all 23
    applicable stored Q101 rows;
  - selected `rho(Q,7)` values converge from `1.159851` at Q17 to
    `1.199989` at Q997, consistent with the exact period-30 limit `6/5`.
- `empirical/sieve-sequence/capacity-density-candidates.md` now documents both
  metrics, all green gates, selected-head results, fitted redundancy scale,
  falsifiers, next measurements, and the universal-proof boundary.
- The empirical note passes Markdown, link, and numerical consistency checks.
- The seven-layer candidate now reports the validated 53-head finite result
  and links the empirical note while remaining mathematically unproved.
- The redundancy candidate now reports positive disjoint and canonical-block
  counts at every measured layer, growth of `D_min` from 8 to 4043, and the
  finite fitted scale while remaining mathematically unproved.
- Both candidate notes are aligned with the empirical artifact. The candidate
  catalog remains pending.
- Catalog inspection found three required alignment points:
  - add #17 and #18 to the REINFORCED status row;
  - add numbered index entries with their exact 53-head results;
  - add proof-oriented next steps and clarify that their Q-sweep is complete
    even though the broader #12/#13 sweep remains open.
- `candidates/README.md` now includes #17 and #18 in the REINFORCED taxonomy,
  indexes both notes, distinguishes their completed 53-head sweep from
  remaining cross-candidate measurements, and names proof-oriented next steps.
- `empirical/README.md` currently indexes only the earlier hereditary
  shot-spacing note, so one capacity-density evidence entry was required and
  has now been added.
- Final scoped link, status, numbering, and `git diff --check` validation pass.
- Only Markdown artifacts changed in this task.

## What is Learned

- The capacity ratio is exactly aligned with the proved theorem:
  `rho>1` is equivalent to `(G-1)(2r-2)>L_Q`.
- The `r=7` layer is structurally attractive because only filters `2,3,5`
  have been installed, giving period `30` and an asymptotic ratio near `6/5`.
- Close-pair multiplicity can distinguish a fragile one-certificate chain from
  a chain with large local redundancy.
- A finite failure of the `r=7` floor at one head refutes that per-head
  instance but not the minimally sufficient "infinitely many heads" form.
  Empirical summaries must distinguish those scopes.
- Raw qualifying pairs can overlap heavily. The maximum matching on the path
  of consecutive starts is the correct independent-certificate count, and one
  pair per multiply occupied canonical block supplies a computable sub-count.
- Reading A can be reproduced efficiently without a source change: initialize
  the `[Q,Q^2)` survivor population with filters `2,3`, measure layer `r`, then
  remove multiples of `r` to obtain the next layer. Independent checks will
  enforce `destroyed+surviving==G` and `B_2<=D`.
- The `r=7` bottleneck is exact across every measured head, not merely Q17 and
  Q101. Strict transition monotonicity remains false, so the lower envelope is
  the empirically correct formulation.
- Redundancy grows strongly over the measured range. The minimum disjoint
  certificate density is approximately `0.296296`; the minimum raw qualifying
  edge fraction is approximately `0.307692`.
- The canonical block sub-count is positive at every measured layer, despite
  its fixed origin at `Q`.
- The early bottleneck is not a numerical artifact of the lineage engine:
  `G_7(W_Q)` is exactly the count of starts congruent to `11`, `17`, or `29`
  modulo `30` in the eligible start interval.
- The empirical artifact is sufficient to change both candidates from
  pending/unmeasured to reinforced-at-finite-scale, but not to change either
  mathematical hypothesis status.
- The redundancy data is not merely a restatement of candidate #14's Boolean
  success: it measures thousands of disjoint certificates at the largest head
  and exposes a stable positive fraction as a sharper proof target.

## Failed Paths

- **Irrelevant agent-status check.** A read-only collaboration status command
  was issued while transitioning from ticket creation to the first candidate.
  It returned only the current root agent, changed nothing, and was unrelated
  to the next action. Do not repeat; this task neither requests nor permits
  delegation.
- **System Python for lineage tests.** `python3 test_lineage.py` failed at
  import time with `ModuleNotFoundError: No module named 'numpy'`; zero tests
  ran. Do not install or modify dependencies. Retry only with the existing
  `candidates/analysis/.venv/bin/python` interpreter.
- **Strict layerwise monotonicity of `rho`.** Already falsified by stored
  lineages: Q17 has one decrease and Q101 has five. Retry only with a
  smoothed, cumulative, or lower-envelope formulation.
- **Prime-head phase as a standalone candidate.** Without a quantitative count
  or capacity lower bound, “the phase is not exceptional” merely renames the
  desired local-density conclusion. Retain phase percentiles as a diagnostic,
  not a third candidate, unless data suggests a precise non-circular bound.

## Open Concerns

- The established 53-head sweep was previously executed in memory but only
  Q17 and Q101 were stored. Recomputing every layer through Q997 may be
  expensive; use the existing pure lineage functions and yield progress rather
  than modifying source prematurely.
- Half-open block occupancy depends on block origin. Use the canonical origin
  `Q` and report this convention explicitly.
- Consecutive close-pair counts overlap. They measure certificate redundancy,
  not the number of endpoint-disjoint certificates, unless a disjoint
  sub-count is computed separately.
- The worktree contains unrelated code/test changes. Do not alter or restore
  them.

## Next Action

Done. The highest-value mathematical follow-up is a proof or falsifier for

```text
(r-1)(G_r(W_Q)-1) >= 6(G_7(W_Q)-1),
```

not another repetition of the completed 53-head sweep.

## Validation

1. Use the existing `lib_lineage.py` population definitions without changing
   their window or conditioning conventions.
2. Test the existing lineage suite before trusting a recomputation if any
   source execution is needed.
3. For every row, independently check `destroyed+surviving==G`.
4. Report failures before trends; finite agreement never proves a candidate.
5. Run `git diff --check` and link checks after every Markdown change.
6. If any non-Markdown file changes, run the required verification sequence.

All applicable checks passed. No non-Markdown file changed, so Stainless
verification was not required. The existing lineage suite passed under the
repository-local analysis virtual environment.

## Learning Log

| Date | Learning | Action |
|---|---|---|
| 2026-07-27 | The proved threshold yields an exact normalized capacity ratio. Q17 and Q101 both have their chain minimum at `r=7`, while strict monotonicity is already false. | Opened this focused ticket; selected a lower-envelope candidate and a redundancy candidate for the empirical sweep. |
| 2026-07-27 | An irrelevant read-only agent-status check returned only the root agent and contributed nothing to the task. | Recorded the off-track diagnostic; return directly to the capacity-floor candidate with no delegation. |
| 2026-07-27 | Added the seven-layer capacity-floor candidate with both the infinitely-many-heads form and the stronger eventual-uniform empirical target. | Define the redundancy candidate with raw, disjoint, and block-occupancy metrics before running the sweep. |
| 2026-07-27 | Added the redundant close-pair candidate. A maximum matching of qualifying consecutive-pair edges gives distinct one-layer survivors; canonical multiply occupied blocks give a sufficient sub-count. | Run the existing lineage tests before recomputing the 53-head metrics in memory. |
| 2026-07-27 | The system Python lineage gate failed before tests because NumPy is unavailable. The repository-local analysis virtual environment already exists. | Record the interpreter failure and retry the unchanged suite with `.venv/bin/python`; do not install dependencies. |
| 2026-07-27 | The unchanged lineage suite passes completely under the repository-local interpreter. An incremental NumPy filter reproduces Reading A while avoiding repeated full-window reconstruction. | Run the 53-head capacity and redundancy sweep in memory with structural identity checks. |
| 2026-07-27 | The in-memory sweep completed over 53 heads and 1,837 layers. All heads have `r=7` as the capacity minimum; no `rho`, disjoint-pair, or canonical-block condition failed. `D_min` grows from 8 to 4043 with fitted exponent 1.572 and correlation 0.9989. | Independently cross-check stored lineages and compute grouped summaries before writing the empirical artifact. |
| 2026-07-27 | Direct modulo-30 counts match all 53 `r=7` populations, and recomputation matches every applicable stored Q17/Q101 row. `rho(Q,7)` approaches the exact `6/5` limit. | Write one empirical note before changing candidate statuses or catalogs. |
| 2026-07-27 | Published and validated the capacity-density empirical note. It records zero failures for both candidates while preserving the finite-only boundary. | Propagate the result to the seven-layer candidate first, then update the ticket before touching the redundancy candidate. |
| 2026-07-27 | Updated the seven-layer candidate to reinforced-at-finite-scale: 53/53 minima at `r=7`, no ratio at or below the capacity boundary. | Propagate the validated disjoint and block redundancy results to the second candidate. |
| 2026-07-27 | Updated the redundancy candidate: no disjoint or block count vanishes, `D_min` grows from 8 to 4043, and the fitted scale is retained as empirical only. | Inspect the candidate catalog and align both new entries in one reviewed documentation pass. |
| 2026-07-27 | Catalog inspection located the status row, numbered index, and proof-next-step section; the cross-cutting Q-sweep text also needs to distinguish completed #17/#18 capacity work from open #12/#13 measurements. | Apply one coherent catalog-alignment edit, then run final link and consistency checks. |
| 2026-07-27 | Candidate catalog alignment is complete: statuses, entries #17/#18, completed-sweep scope, and proof next steps are current. | Check whether the empirical catalog needs one discoverability link before final validation. |
| 2026-07-27 | The empirical catalog indexes only the prior #14 evidence note; the new validated note is otherwise undiscoverable from that entry point. | Add one finite-scope evidence link, then perform final validation. |
| 2026-07-27 | Final validation passed: both candidates and the empirical note are linked and status-aligned; all changes are Markdown-only; the ticket retains both failed diagnostics and their causes. | Marked the work complete and moved the ticket to `tickets/done/`. |
