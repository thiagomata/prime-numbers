# Open Problems — Sieve Sequence 2-Gap Survival

**Status:** Open problems under active investigation, drawn from
`properties/sieve-sequence/`, `candidates/`, `articles/learnings/`,
and active tickets. The primary twin-prime frontier converges to the signed
mean-square cancellation and residue-energy path (candidates #23/#24); a
separate almost-prime fallback exists at candidate #25. A formal Stainless
verification gap (the isolation lemma and foundational inputs) underpins
many candidates independently.

Contributions in the form of partial results, counter-examples, or proof
sketches are welcome. Each entry states the goal, what's known, what's
open, and points to source files.

---

## Primary Frontier

### 1. Weighted Harmful-Excess Quadratic Survival (#24)

- **Goal:** Prove twin-prime survival via a weighted harmful-excess bound
  `E_b < T²/(2W_-)`, then compose across the filter chain.
- **Known:** Terminal threshold proved. Exact filter-7 saving proved.
  Capacity envelopes exhausted (#66–#81). Complete-old-period blocks reduce
  exactly to residue energy `V_r`.
- **Open:** Three remaining needs: (1) relative bound for residue energy
  `V_r` via four-point correlation (#20), (2) signed control of two partial
  old-period fragments, (3) composition across the weighted filter chain.
- **Source:** `candidates/weighted-harmful-excess-quadratic-survival.md`

### 2. Accepted-Anchor Strike Density / Signed Arithmetic (#23)

- **Goal:** Prove a weighted mean-square or Möbius-residue cancellation
  estimate for `epsilon_i = H_i/A_i - 1/r_i`.
- **Known:** Exact boundary decomposition, divisor activation kernel, CRT
  lift-index transform, and five other representation identities proved.
  Representation recursion exhausted.
- **Open:** Bound the localized layer Gram matrix's largest eigenvalue
  below its trace, or a quadratic-variation bound for adjacent boundary
  errors. New signed mean-square or cross-layer cancellation needed.
- **Source:** `candidates/accepted-anchor-strike-density.md`

### 3. Residue-Collision Energy / Four-Point Correlation (#20)

- **Goal:** A relative four-point correlation bound normalized by actual
  local population `N_r`.
- **Known:** Exact autocorrelation reduction proved. Minimal violating
  histograms established. Finite exact witness search found no failure
  through `Q <= 251`.
- **Open:** Prove `C_r <= N_r + N_r²/r`.
- **Source:** `candidates/conditioned-residue-collision-energy.md`

### 4. Capacity-Frontier Proof Bridge

- **Goal:** Prove the real sieve's per-sequence 2-gap count `G_local(h)`
  stays above the c=1 phase-transition frontier for all `h ≥ h₀`.
- **Known:** Per-layer lower bound `G_surviving ≥ G_local − A(p,q)` proved.
  `rho(Q,7) > 1` for all `Q ≥ 17`. Exact global `G₂(p) = ∏(r−2)` proved.
  Empirically `G_local` tracks the random expectation within ~5% and stays
  ~10⁵ above the frontier (188 heads measured).
- **Open:** (a) Tight bound on `A(p,q)` — Bertrand gives `≤ 4p/ln p`,
  only ~2× the frontier's expected destruction, not a guarantee; needs
  stronger prime-gap theorem or unconditional bound. (b) Monotonicity
  `rho(Q,r) ≥ rho(Q,7)` for all `r > 7`. (c) The unresolved bridge:
  intersection of the allowed copy-index set with the safe-window interval.
- **Sources:** `properties/sieve-sequence/sharp-local-two-gap-survival-threshold.md`,
  `properties/sieve-sequence/README.md`, `candidates/local-surplus.md`

---

## Per-Layer Local Guarantees

### 5. Local Surplus — Terminal Sufficient Target (#2)

- **Goal:** A lower bound on the local surplus `L(p,q) − A(p,q)` that
  forces 2-gap survival.
- **Known:** Conditional implication proved: `L(p,q) > A(p,q)` →
  survival. Empirically `surplus > 0` in 186/186 transitions, growing like
  `p^1.6`. Danger-Annulus Decomposition refines to annular form
  `L_D(p,q) > A(p,q) − 1`.
- **Open:** No mechanism for a lower bound on `L(p,q)` or annular
  population `L_D`. Needs an independent local lower bound or paired
  population/destruction estimates.
- **Source:** `candidates/local-surplus.md`

### 6. Short-Window Discrepancy — Random Behavior Bridge (#10)

- **Goal:** Prove `|E_q| < main_term` (a two-sided bound on the deviation
  from the complete-period expected 2-gap count).
- **Known:** Conditional implication proved: `|E_q| < |W_q|·delta_q` →
  positive 2-gap count. Complete-period CRT formula determines `main_term`.
  Post-filter `E_q` now computed by the lineage experiment.
- **Open:** The two-sided bound is unmeasured at scale and requires
  distributional input beyond total counts and per-prime residue
  frequencies. One-sided form is equivalent to survival (circular).
- **Source:** `candidates/short-window-discrepancy.md`

### 7. Local Pattern-Residue Balance (#12)

- **Goal:** Fix a concrete error family and prove its conditioned weighted
  bound `nu·E < N·(1 − nu/r)`.
- **Known:** Reduced from arbitrary patterns to two harmful classes.
  Margins positive in 1,890/1,890 exact lineage layers.
- **Open:** The unspecified `E_p(J,w)` term is not falsifiable; needs
  concrete specification and a provable bound.
- **Source:** `candidates/local-pattern-residue-balance.md`

### 8. Uniform Local Observable Sampling (#13)

- **Goal:** Prove a signed endpoint imbalance bound for a concrete
  observable class `eta_p`.
- **Known:** One-sided margin `H·(2L/N + b₊) < L` positive in
  1,890/1,890 layers. Exact bridge with #23 and #24 recorded.
- **Open:** Fix a concrete `eta_p` and prove the two required
  observables, not an arbitrary class.
- **Source:** `candidates/uniform-local-observable-sampling.md`

### 9. Random-Like Deterministic Transference (#11)

- **Goal:** Derive `destruction_rate ≤ 2/p` from modular arithmetic
  (deterministic, not probabilistic).
- **Known:** Random benchmark proved. `destruction_rate < 2/p` in
  186/186 transitions, gap widens with p.
- **Open:** A deterministic transference bound through restricted
  candidates #12/#13.
- **Source:** `candidates/random-like-merge-survival.md`

### 10. Bounded Consecutive Destruction (#4)

- **Goal:** A quantitative bound on the maximum number of consecutive
  2-gaps a filter can destroy (the cyclic run length).
- **Known:** Constant `R=2` shortcut refuted (counterexample: cyclic run
  of 3 at `Q=101, r=23`). Window-linear run maximum is 2.
- **Open:** A useful quantitative cyclic-run bound surviving the
  run-3 counterexample, paired with an independent local-block lower
  bound. Cyclic full-period run is unmeasurable at later primorial-scale
  layers.
- **Source:** `candidates/bounded-consecutive-destruction.md`

---

## Multi-Layer / Hereditary

### 11. Hereditary Shot-Spacing Capacity (#14)

- **Goal:** Prove the interval premise (close-pair existence with
  separation `< 2r`) holds for *some* layer in *every* sufficiently long
  chain.
- **Known:** Exact `k=2` certificates at 1,837 layers across 53 heads.
  `sigma_r(2) = 2r` proved. Admissible-diameter profile `D(2..14)` proved.
- **Open:** Hereditary composition across unboundedly many layers.
  Close-pair existence and hereditary residue balance remain unproved.
- **Source:** `candidates/hereditary-shot-spacing-capacity.md`

### 12. Seven-Layer Capacity Floor — Later Envelope (#17)

- **Goal:** A cumulative conditioned-count lower envelope for later layers:
  `(r−1)(G_r(W_Q)−1) ≥ 6(G_7(W_Q)−1)`.
- **Known:** `rho(Q,7) > 1` for all `Q ≥ 17`. All 53 measured heads and
  1,837 layers satisfy `rho(Q,r) ≥ rho(Q,7)`. Population-slack consequences
  inside #24 established.
- **Open:** The cumulative envelope needs arithmetic information beyond
  the exhausted native-capacity envelope. Reopenable for #24 only.
- **Source:** `candidates/seven-layer-capacity-floor.md`

### 13. Reundant Close-Pair Capacity — Uniform Lower Envelope (#18)

- **Goal:** A uniform/unbounded conditioned-density lower envelope with
  a nontrivial recovery term:
  `(Delta_r(G_r(W_Q)−1) − L_Q) / (Delta_r − 6)`.
- **Known:** Density-to-matching conversion and sharp attrition bounds
  proved. Monotone reconstruction laws refuted.
- **Open:** The uniform lower envelope itself.
- **Source:** `candidates/redundant-close-pair-capacity.md`

### 14. Expanded-Zone Exterior Capacity (#16)

- **Goal:** A favorable exactly-countable annular expansion for the
  Danger-Annulus decomposition `L_D ≥ B_D − U_D` with target
  `B_D − U_D > A − 1`.
- **Known:** Exact cluster growth proved. Naive complete-lift
  pigeonhole refuted. Post-filter full-window route preserved.
- **Open:** No favorable exactly-countable annular expansion with
  proved `B_D, U_D` is known. Unmeasured entirely.
- **Source:** `candidates/expanded-zone-exterior-capacity.md`

---

## Structural and Formal

### 15. Companion Models — CRT-Coupled Transfer

- **Goal:** Prove that "random choice of which two copies die" in the
  balanced companion models produces uniformly random positions (i.e.,
  the companions faithfully model the real filter's stochastics), or
  characterize the correlations introduced by the copy-index structure.
- **Known:** Twelve theorems proved about four companion models. The
  adversarial companion proves global divergence and head-extinction are
  simultaneously achievable, bracketing the real filter.
- **Open:** The CRT-coupled transfer to the real sieve remains open.
- **Sources:** `articles/draft/draft-adversariality-phase-transition-2-gap-companions.md`,
  `companions/`

### 16. Stainless Verification — Foundational Lemmas

- **Goal:** Close the formal verification gap for the isolation lemma
  ("one removed value destroys at most one 2-gap") and five other
  foundational inputs cited across candidate notes.
- **Known:** Mathematically proved in
  `properties/sieve-sequence/two-gap-isolation-after-filter-three.md`
  but not Stainless-verified. `verifyGeneralizedGrowth` does not exist
  in any `.scala` file.
- **Open:** Stainless verification of the isolation lemma and the other
  five established inputs. Underpins candidates #2, #3, #4, #11, #13, #14
  and others.
- **Source:** `candidates/README.md`, `properties/sieve-sequence/`

### 17. Safe-Zone Exhaustion Curve — Tight Bound

- **Goal:** Prove the tight estimated lower bound for the number of
  survivors in the window `[p, p²)` (the "safe zone").
- **Known:** A loose but universal bound using Schroeder 2017 exists
  (`Phi(n,p) ≥ floor(2n/p) + 1`). A tight but unproven estimate
  exists. Two dead-end attempts documented.
- **Open:** Proving the tight bound for the full period.
- **Source:** `properties/sieve-sequence/safe-zone-exhaustion-curve.md`

---

## Almost-Prime Fallback

### 18. Chen-Type Almost-Prime Survivor (#25)

- **Goal:** A project-specific almost-prime result (weight positivity).
- **Known:** Externally established (Chen's theorem + Bertrand). Divisor
  Local Factor, Bilinear Character Obstruction, Cofactor Progression
  Discrepancy all proved. Scalar-density Type-II orthogonality refuted.
- **Open:** Requires an averaged prime-progression theorem for
  `pi(I;d,−2) − pi(I)/phi(d)` matched to the divisor/interval range,
  plus a locally adapted bilinear estimate absorbing fixed local character
  modes. Distinct almost-prime program, not twin-prime.
- **Source:** `candidates/chen-type-almost-prime-survivor.md`

---

## Deferred (Data-Constrained or Primorial-Scale)

These are candidates that need new structural shortcuts or primorial-scale
data that do not yet exist: #5 (bounded-post-merge-spacer), #6
(controlled-merge-run), #7 (balanced-spacers), #9 (forbidden-copy-covered-run),
and the cumulative collision budgets #21/#22 (redundant for survival
unless new cancellation results are found).

---

## Related

- [properties/sieve-sequence/README.md](../README.md) — full property catalogue
- [candidates/analysis/README.md](/candidates/analysis/README.md) — candidate stress-test infrastructure
- [LEARNINGS.md](/LEARNINGS.md) — verified techniques and pitfalls
- [articles/learnings/learnings-capacity-argument.md](/articles/learnings/learnings-capacity-argument.md) — capacity argument boundary
