# Empirical Stress-Test of the 2-Gap Survival Candidates

**Created:** 2026-07-23
**Updated:** 2026-07-23
**Status:** In progress (plan complete, implementation starting)
**Depends on:** none (decoupled from Stainless verification)

## Related Tickets

- `document-2-gap-merge-survival-candidates-2026-07-23.md` — created the `candidates/` catalog this effort measures (Complete). The candidates are unproved hypotheses; this ticket tests their actual antecedents against data.
- `deep-study-sieve-sequence-gap-dynamics-2026-07-23.md` — read-only source study (Complete). Established the article/proof boundaries this work aims to break through.
- `local-safe-window-capacity-exercise.md` — earlier capacity framing (Active). Related local-window framing.
- `m-interval-density-and-sieve-sequence-v2.md` — long density argument (Active). Adjacent analytic direction.

## Goal

Decide, from **measured data** rather than from the `learnings-capacity-argument.md`
verdicts, which of the fourteen candidate conditions for square-safe 2-gap
survival are alive (their antecedents actually hold at scale) versus dead. The
immediate scope is the **window-measurable** candidates, sieved per transition
over `W = [q, q^2)`. Survivors of this fast pass earn a deeper (whole-period)
pass later.

The decisive measurement the existing `data/empirical/results.csv` does not
capture: the **actual number of 2-gaps the real modular filter destroys, versus
the worst-case bound `A(p,q)`**. Candidate #14 (hereditary shot-spacing)
predicts the filter wastes most of its shots missing 2-gap endpoints; candidate
#2 (local surplus) assumes the worst case. That ratio is the single
highest-signal number this effort produces.

## Current State

- `candidates/` holds 14 self-contained candidate notes, each separating an
  unproved hypothesis from a proved conditional implication.
- `data/empirical/results.csv` (from the `@extern` Scala `EmpiricalRunner`)
  records `G_local` and `delta = G_local - p` for transitions up to p=997, using
  the window `[p, p^2)`. It does not measure actual destruction vs. worst case.
- `presentations/.../figures/out/gaps.csv` (a separate, standalone
  `generate_gaps.py`) records a **fixed 4000-gap prefix per stage** (its README
  is stale, says 2000). It does not cover full `[q, q^2)` at higher stages, so
  it is a cross-check only.

### Critical finding (corrects the learnings doc)

`articles/learnings/learnings-capacity-argument.md` presents several candidate
inputs as bedrock that this effort's source-grounded investigation found to be
unreliable:

- **None of the six "established inputs" the candidates cite as "Established
  Inputs" is Stainless-verified.** Every file in
  `properties/sieve-sequence/` explicitly disclaims verification
  ("Status: Mathematically proved. Stainless verification is not claimed
  here."). The candidates' links point at unverified mathematical notes.
- **The isolation lemma ("after filter 3, one removed value destroys at most one
  2-gap") does not exist in code.** The learnings doc labels it "[Proven]" /
  "[Verified]" and cites `verifyGeneralizedGrowth`; that symbol appears
  **nowhere** in any `.scala` file. The verified code proves only generic
  gap-positivity, generic gap-sum telescoping, the survivor count
  `T' = T*(head-1)`, and single-value `apply(1) < head^2 => prime`.

Conclusion: the candidate antecedents, and several of their "established"
inputs, have never been measured or verified — only asserted. An empirical run
is the right tool to cut through that. This effort is **empirical only**; the
verification gap is recorded here as a finding and is not addressed by this
ticket.

## Expected State

- `candidates/analysis/measure_candidates.py` + `lib.py` + `test_measure.py` +
  `requirements.txt` (NumPy, SymPy): a standalone, stdlib-plus-numpy/sympy
  Python package, run by hand, **zero Stainless / sbt / Scala involvement**.
- `data/candidates/window-measurements.csv`: per-transition measurements for the
  10 window-measurable candidates, to ~p=1000 by default.
- `candidates/analysis/README.md`: run instructions, **explicit limits of every
  input file**, per-column measurement power, and the window-vs-whole-period
  scope boundary.
- `candidates/analysis/FINDINGS.md`: data-grounded verdict per candidate
  (killed / survived / inconclusive), written after the run. This is a NEW
  evidence-based note; it does NOT overwrite the suspect
  `learnings-capacity-argument.md`.
- `test_measure.py` green is the gate for every column added and every claim
  cited.

## Approaches Considered

### A. Standalone Python (NumPy + SymPy) — RECOMMENDED

A pure Python package in the style of the presentation repo's `generate_gaps.py`:
stdlib + NumPy/SymPy, run by hand, decoupled from the build. NumPy vectorizes the
window sieve (window up to ~10^6); SymPy supplies tested `primepi` for the exact
worst-case `A(p,q)`.

**Strengths:** instant iteration (no Stainless compile tax); uses tested
number-theory primitives; matches an established precedent in this project
ecosystem; the sieve is a boolean-array slice-assignment, fast and low-bug.
**Risks:** none load-bearing; dependency install only.
**Fallback:** none needed.

### B. Extend the `@extern` Scala `EmpiricalRunner` — REJECTED

**Why rejected:** Even though the existing empirical files are `@extern`, they
still compile through the Stainless-augmented compiler on every `just compile`,
which is exactly the slow/heavy iteration loop analysis work must avoid. User
decision: do not run analysis execution mixed with the Stainless code.

### C. New Spark pipeline — REJECTED

**Why rejected:** Spark's granularity is wrong: it persists every gap to disk
(the project's prior Spark full-period pipeline "reached 3GB by stage 10"). We
need per-stage *summaries*, not every gap. User decision.

### D. Measure candidate #14 only — REJECTED

**Why rejected:** #14 is the only candidate with genuinely new mechanistic
content, but betting on one candidate before the data justifies it repeats the
premature-narrowing error the learnings doc is full of. Measure broadly first.

### E. Measure all 14 including whole-period — REJECTED

**Why rejected:** Whole-period candidates (#5, #6, #7, #9) require sieving up to
`M_p` (primorial), which blows up; mixing sampling regimes risks slow,
memory-heavy runs — the thing we are avoiding. User decision: start fast.

## Scope Boundary (window-measurable vs. whole-period)

Window-measurable this pass (sieve `W = [q, q^2)` + one linear scan):
#1 Protected-endpoints, #2 Local-surplus, #3 Protected-cluster, #4
Bounded-consecutive-destruction, #8 Distinguished-head-spacer, #10
Short-window-discrepancy, #11 Random-like-merge-survival, #12
Local-pattern-residue-balance (LOW POWER: small sample), #13
Uniform-local-observable-sampling, #14 Hereditary-shot-spacing (BUILDING BLOCK
ONLY: one transition, not the hereditary chain).

Deferred to a deeper pass for survivors (whole-period / `M_p`-scale):
#5 Bounded-post-merge-spacer, #6 Controlled-merge-run, #7 Balanced-spacers,
#9 Forbidden-copy-covered-run (true copy-index view).

## Per-Column Validity Review (being critical, applied up front)

- **#14** is a *multi-layer hereditary* claim; a single transition tests only
  one ingredient, not the chain. The `destroyed` / `waste_ratio` columns are
  labeled "per-layer building block, hereditary composition deferred" — they do
  NOT validate #14.
- **#12** is a whole-residue-distribution claim; one window is a small sample,
  so `residue_max_dev` is measured but flagged low-power, not decisive.
- Every other column is a direct test of its candidate's antecedent.

## Assumptions

- Convention (article-authoritative, `gap-dynamics.md` S9): transition `(p, q)`,
  q = next prime after p; `W = [q, q^2)`; a value `< q^2` coprime to all primes
  `< q` is certified prime.
- Pre-filter survivors = integers in `W` coprime to all primes `< p`. Installing
  filter `p` removes those `= 0 (mod p)`; the remainder is the certified-prime
  pool. A 2-gap among post-filter survivors in `W` is a genuine twin-prime
  certificate.
- A 2-gap `(x, x+2)` of pre-filter survivors is destroyed by installing `p` iff
  `x = 0 (mod p)` or `x+2 = 0 (mod p)`. Counted directly from the survivor list
  — no model, no assumption.

## Risks

- **Wrong window convention.** results.csv uses `[p, p^2)`, not `[q, q^2)`.
  Mitigation: use the article-authoritative `[q, q^2)` and cross-check the
  overlap with results.csv after adjusting the convention.
- **Measurement mis-sold as candidate validation.** Mitigation: the per-column
  validity review above; FINDINGS.md states power explicitly per candidate.
- **Stale learnings doc treated as ground truth.** Mitigation: this effort
  measures antecedents directly and reports what the data shows, even where it
  contradicts the learnings doc.
- **gaps.csv / results.csv limits ignored.** Mitigation: README documents every
  input file's limits; they are cross-checks only, not primary sources.

## Validation (the green gate)

`test_measure.py` (stdlib `assert`, exit 0/1, `verify.py` style) is run before
AND after every one-column change (the empirical analog of green-to-green). It
enforces:

- **Hand check** (q=5, p=3): `W=[5,25)`; pre-filter (coprime to {2}); install 3
  -> survivors 5,7,11,13,17,19,23; 2-gaps (5,7),(11,13),(17,19) -> `surviving=3`
  (real twin primes). Must reproduce.
- **Identities:** `destroyed + surviving == G_local`; `surviving >= 0`;
  `surviving > 0` iff a twin pair exists in `W` (cross-check vs known twin
  primes via SymPy `isprime`).
- **Cross-check** `G_local` vs `results.csv` on the overlap, after the
  `[p,p^2)` vs `[q,q^2)` adjustment.

Small-changes rule: add ONE measurement column -> run tests -> green -> next.
Never compute all columns then check. Red-cascade rule: if a test goes red,
revert that single change; do not pile fixes onto other columns.

## Implementation Plan

1. `candidates/analysis/requirements.txt` (numpy, sympy).
2. `candidates/analysis/lib.py`: `sieve_window` (NumPy boolean array),
   `survivors_list`, `count_two_gaps`, `actual_destroyed`, `worst_case_A`
   (SymPy `primepi`). No I/O.
3. `candidates/analysis/test_measure.py`: hand check + identities + cross-check.
   Get green on the hand check BEFORE adding any candidate columns.
4. Add columns one at a time, tests green before/after each:
   - `surviving` (#1), `G_local`/`A_worst`/`surplus` (#2),
     `destroyed`/`waste_ratio` (#11 / #14 building block),
     then #3, #4, #8, #10, #12, #13.
5. `candidates/analysis/measure_candidates.py`: thin runner (args, loop, write
   `data/candidates/window-measurements.csv`).
6. `candidates/analysis/README.md`: run instructions, input-file limits, per-column
   power notes, scope boundary.
7. Run at default scale (~1000); write `candidates/analysis/FINDINGS.md`.

## Out of Scope (per decisions)

- No Scala / Stainless / Spark changes (decoupled Python).
- No formal `.holds` work (verification gap recorded as a finding, not
  addressed).
- No whole-period candidates this pass.
- No phase-2 deep pass yet — earned only by survivors.

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-07-23 | Ticket created. Found the candidates catalog and the unreliable learnings doc; verified that the isolation lemma + 5 "established inputs" are NOT code-verified and that `verifyGeneralizedGrowth` is nonexistent. User chose standalone Python (NumPy+SymPy), window-measurable scope, decoupled from Stainless. | Start implementation: requirements + lib + tests. |
| 2026-07-23 | Built `lib.py` core + `test_measure.py`. First green run FAILED on my own hand-check expectations at p=3 — and the failure was correct: the code was right, my hand math was wrong. **Real finding:** the bound `destroyed <= A_worst` holds only for transitions with p >= 5 (filter 3 already installed). At p=3 the pre-filter still has endpoint-sharing 2-gaps, so destruction can reach `2*A_worst` (observed: destroyed=6 = 2*A_worst=3). Candidates #2/#11/#14 implicitly assume this bound and must scope themselves to post-filter-3 stages. | Fixed the test expectations; added a p=5 hand check as the first clean transition; scoped identity (d) to p>=5. |
| 2026-07-23 | Added all candidate columns (#3,#4,#8,#10,#11,#12,#13 + #14 building block) with hand-verified q=7/p=5 expectations. Gate green after each. | Build thin runner. |
| 2026-07-23 | Ran `measure_candidates.py 1000` (166 transitions). **Decisive window-scale result:** `surplus > 0` in 165/165 clean transitions (worst-case bound alone guarantees survival); `waste_ratio` mean 0.778, 85/165 transitions destroyed nothing; total destroyed 103 vs total `A_worst` budget 449. Contradicts the learnings doc's "Fatal (unproven)" local-density verdict at window scale. Scope kept honest: this is window-scale survival, NOT the infinitude theorem (that is the whole-period / hereditary question). | Wrote `FINDINGS.md` with per-candidate verdicts and the scope line stated up front. |
| 2026-07-23 | **Self-correction:** I had claimed in README that `gaps.csv` "does NOT cover full [q,q^2) at higher stages" — that was FALSE, asserted without checking. The 4000-gap prefix reaches q^2 for stages up to head ~1123 (187/200). Conflated "period M_p exceeds p^2" (true) with "prefix doesn't reach the window" (false). | Verified exact survivor-list match between my NumPy sieve and gaps.csv's independent pure-Python walk-forward over 8 stages (head 7..887). Wired it in as `test_cross_check_gaps_csv` (PASS). Fixed the README limits table. Lesson: assert a file's limits only after checking them. |
| 2026-07-23 | User: two sieves agreeing cannot rule out a shared conceptual error; unit tests against independently hand-derived ground truth are the real defense (and even those can be wrong). Recognized the candidate columns (#3,#4,#8) were pinned to only ONE hand example (q=7/p=5), and #12/#13 only to "finite and >= 0" -- thin. | Hand-derived a SECOND example (q=11/p=7) independently of lib.py (G_local=11, destroyed=3, surviving=8, A_worst=4, cluster=2, run=2, d_head=0) and pinned #3/#4/#8 to it. Hand-derived EXACT values for #12 (0.8) and #13 (1/7) at q=7/p=5. Gate green. README now documents test strength honestly, including the one remaining thin pin (#10 discrepancy, formula-trusted not hand-pinned). |
| 2026-07-23 | Per-transition pass/fail analysis: NOT a clean sweep. #2,#1,#8,#10,#11 pass 165/165. #3 protected-cluster FAILS at (5,7) only (smallest window, 2-gaps evenly spaced 6 apart so no cluster fits width<5). #14 building block FAILS at 5 transitions: (5,7),(19,23),(239,241),(313,317),(569,571) -- filter hit full worst-case capacity. Notable: 3 of 5 #14 failures are twin-prime transitions. Corrected FINDINGS.md which had over-labeled #3/#14 as "Alive". | Saved the counterexamples IN THE CANDIDATE NOTES themselves (protected-cluster.md, hereditary-shot-spacing-capacity.md), with precise transitions, measured values, and honest scoping (#14 counterexample defeats only the per-layer building block, NOT the full hereditary candidate). This is where someone evaluating those candidates will look for them. |
| 2026-07-23 | User: some candidates are VAGUE about the number ("if we have enough survivals", "clusters bigger than some limit"). How are those tested? Realized the candidates split into two kinds. EXPLICIT-threshold (#2,#3,#8,#10): note states a concrete inequality -> real pass/fail, reported N/165. #3's ">=2" is explicit (not vague) -- tested correctly. EXISTENTIAL-threshold (#4 "exists R_p", #7 "exists C(q)", #11/#13 "exists epsilon_p/eta_p small enough"): note asserts existence of a bound/tolerance with no value. Picking an arbitrary constant to test against would be dishonest. | Reclassified in FINDINGS.md: existential candidates marked "trajectory reported," not "pass". Reported trajectories: #4 run is 0/1/2 (flat, 85/79/1, max 1 in last 30 transitions); #11 destruction_rate/(2/p) median 0.000 max 0.955 (last-30 max 0.265). No finite run can confirm an existential claim -- only falsify via unbounded growth / closed margin. Added the explicit-vs-existential distinction as a header note in FINDINGS so the reader doesn't mistake "trajectory reported" for "pass". |
| 2026-07-23 | User: for existential candidates, the best data can do is report the full distribution (min/median/mean/max) of the quantity, so any future lemma has real numbers to fight against: if the proof needs the quantity bigger than observed-max or smaller than observed-min, the data refutes it. This reframes the whole exercise: the data imposes CONSTRAINTS on what a proof is allowed to assume. | Added a "Data-imposed constraints on the unknown thresholds" table to FINDINGS with min/median/mean/max plus early-max vs late-max (reveals flat vs growing). Key reads: #4 run never exceeds 2 and is flat (a proof needing R_p=2 is data-supported; needing R_p unbounded is not). #11 destruction_rate max 0.333, shrinking with p (margin near 0 is available at large p). #13 endpoint_bias in [0, 0.77], roughly flat. #14 building block waste_ratio hits exactly 0 in 5/165 (a hereditary proof assuming waste>0 always is refuted). #12 residue_max_dev GROWS 0.8->10.3 -- unfavorable flag for #12 (low power). None prove the existential claim; all bound the space of viable proofs. |
| 2026-07-23 | User: some properties change at big numbers; check against big primes. Calibrated cost: window grows QUADRATICALLY, so dense run to large p is infeasible (one transition at q~20000 = ~400M ints, 13s). Built a SPARSE sampler (every 100th prime, p to ~19000, 21 new transitions; each window still sieved in full, peak mem one transition). Added `--sparse` mode to measure_candidates.py; gate green. | Ran sparse to p~19000. Result: headline signals STRENGTHEN, not weaken. #2 surplus>0 in 21/21 with min surplus 11768 (grows with p). #11 destruction_rate max collapsed 0.333->0.00008. #4 run max 1. #14 building block still hits worst-case occasionally (1/21). #12 RESOLVED: its apparent growth was a small-sample artifact -- normalized by sqrt(G_local) the median shrinks 0.14->0.067 and max 0.43->0.096; the residue distribution gets CLOSER to uniform at scale, not further. Withdrew the unfavorable flag on #12. Wrote a "Large-p check" section in FINDINGS and added the sparse file to the README limits table. Honest scope: p~19000 is still small analytically; this refutes "only works for tiny p" but does not prove the existential claims for all p. |
| 2026-07-23 | User: is there any kind of TREND? Computed log-log fits (value ~ p^k) over all 186 transitions (dense+sparse). Strong clean trends (|r|>0.97): #2 surplus grows like p^1.6 (r=0.998); #11 destruction_rate shrinks like p^-1.6 (r=-0.991); #12 normalized shrinks p^-0.09 (r=-0.87). Flat/no-trend (|r|<0.1): #4 run (r=-0.09), #13 endpoint_bias (r=-0.05) -- treat as bounded/stationary. Noisy/low-r: #14 waste_ratio (r=0.14), #8 d_head (r=0.44 but bound is quadratic so irrelevant). | Added a "Trends vs p" table to FINDINGS converting distributions into scaling exponents a lemma developer can use (e.g. "a proof of #2 may assume surplus >= p^1.6 at this scale"). Key read: no trend turns unfavorable with p; the load-bearing ones (#2,#11) improve markedly. Stated honestly these are empirical exponents over p<=19000, not proven asymptotics. |
| 2026-07-23 | User: some candidates are now better positioned than others. Synthesized a RANKING but forced a critical distinction: (A) empirical strength (what this run measured) vs (B) relevance to the infinitude theorem (what actually matters). These are DIFFERENT and conflating them misleads. | Added a Ranking section to FINDINGS. (A) Empirical ranking: #2 > #11 > #12-normalized > #4=#13 > #1/#8/#10 > #3 > #14-building-block. (B) The crucial caveat: EVERY measured candidate is window-scale and was already known sufficient conditionally; none alone advances the open problem. The candidates that bear on infinitude (#5,#6,#7,#9, full #14 hereditary chain) are precisely the UNMEASURED ones. So #2 being empirically strongest does NOT make it the priority for proof work on the actual theorem. Justified conclusions: prioritize #2/#11 for window-scale lemma work; treat #4/#13 as bounded assumptions; don't over-trust #14 from its building block; don't rank unmeasured candidates as "worse". The deeper whole-period pass is where infinitude-relevant signal would come from. |
| 2026-07-23 | User: are you keeping the candidate files updated with the latest data? Honest answer: NO -- only #3 and #14 had empirical sections (from the early counterexample pass); the large-p check, trends, #12 normalization correction, and ranking had NOT propagated back into the individual notes. User chose: FULL writeup per candidate (self-contained, prioritizing each note being readable standalone). | Wrote an "Empirical status" section into all 14 candidate files, computed from the full 186-transition dataset (dense+sparse): #1 (pass 186/186, surviving~p^1.6), #2 (pass 186/186, surplus~p^1.6, strongest), #4 (flat, max 2), #8 (pass 186/186), #10 (pass 186/186, E_q convention caveat), #11 (pass 186/186, dest_rate~p^-1.6), #12 (low-power; RECORDED THE CORRECTION -- relative dev shrinks p^-0.09, unfavorable flag withdrawn), #13 (flat, [0,0.85]). Refreshed #3 (185/186, cluster grows to 248 at scale) and #14 (180/186, 6 failures incl new one at p=11681 confirming worst-case persists at scale). Added "not measured this pass" notes to the 4 deferred candidates (#5,#6,#7,#9) explaining why each needs whole-period data. Updated candidates/README.md index with per-candidate [measured]/[deferred] status and headline result. Gate green. Audit confirms all 14 files now carry empirical content. |

## Conclusion

Window-scale candidate stress-test complete and green. Deliverables:
`candidates/analysis/{lib,test_measure,measure_candidates,requirements}.txt`,
`candidates/analysis/{README,FINDINGS}.md`,
`data/candidates/window-measurements.csv` (166 transitions, p to 991).

**Headline:** at the window scale to p=997, the survival question is not close
to failing — `surplus > 0` in every clean transition and the filter wastes ~78%
of its shot budget. This overturns the learnings doc's "Fatal (unproven)"
local-density verdict at window scale.

**Honest scope:** this does NOT prove the infinitude theorem (the
whole-period / hereditary candidates #5, #6, #7, #9, and the full #14 chain
bear on that). The deeper pass for those candidates is the natural next step.
Two scope corrections are recorded above (p>=5 bound; gaps.csv coverage).

**Verification-gap finding still open (out of scope here):** the isolation
lemma and five "established inputs" cited by the candidates are NOT
Stainless-verified; `verifyGeneralizedGrowth` does not exist in code. A
separate formal-verification ticket would be needed if anyone wants to close
that gap; this effort is empirical only by decision.
