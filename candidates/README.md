# Candidate Conditions for Square-Safe 2-Gap Survival

This folder records research hypotheses that would be sufficient to force
2-gap survival near the head of a sieve sequence. These hypotheses are not
known properties of the merge process and may be false. They are kept outside
`properties/`, which is reserved for established mathematical results.

Each note separates four things:

1. an unproved candidate hypothesis;
2. a proved implication from that hypothesis to square-safe survival;
3. established inputs already documented under `properties/sieve-sequence/`;
4. the exact limitation or missing research obligation.

## Empirical status summary

Each candidate carries an `**Empirical status:**` tag at the top of its note.
The taxonomy (and the question you asked that produced it):

| Status | Meaning | Candidates |
|--------|---------|------------|
| **REINFORCED** | data seems to reinforce the current belief (stated condition holds across measurements) | #1, #2, #8, #11, #14, #15, #17, #18 |
| **SMALL-PRIME CAVEAT** | fails for small primes but likely changes for big primes (recovers at scale) | #3 |
| **INCONCLUSIVE** | data neither contributes to the thesis nor refutes it (proxy-only, unmeasured-as-stated, or low-power) | #4, #10, #12, #13 |
| **DEFERRED (UNMEASURED)** | whole-period or expanded-zone quantity; not touched by the window or lineage passes | #5, #6, #7, #9, #16 |
| **ALGEBRA-FIRST (UNMEASURED)** | derived from a proved algebraic bound after the empirical program; next action is proof, not measurement | #19, #20, #21, #22, #23 |
| **REFUTED** | exact proposed statements defeated by a valid counterexample | [refuted subclaims catalog](refuted/README.md) |

**No numbered candidate note has been fully refuted.** Zero negative margins anywhere (`surplus`
min +4, `c12_margin` min +12, `c13_margin` min +15.9851); no stated condition
failed at scale. The one small-prime failure (#3 at (5,7)) recovers at scale
(clusters grow to 248). The honest frontier is therefore: reinforced where
measured, inconclusive where the mechanism is period-scale, deferred for the
whole-period candidates, and open everywhere for "does it hold for *all* Q".
Some stronger auxiliary formulations have been falsified and are now recorded
under [refuted subclaims](refuted/README.md); for example, candidate #18's
monotone separator-reconstruction laws fail even though candidate #18 itself
remains open.
For #14 specifically, exact finite `k=2` certificates now cover 53 heads and
1,837 defined layers through Q997, and the runner's selected `k\le10` spacing
fields are exact under the proved admissible-diameter profile.
For #17 and #18, an expanded exact sweep covers 53 heads and 1,837 layers:
every capacity minimum occurs at `r=7`, and neither the disjoint nor canonical
block certificate count vanishes.

## Common Notation

Let `p` be the prime installed by a transition and `q` the next prime head. The
eligible 2-gap-start window is

```math
W_q=\{x:q\le x\text{ and }x+2<q^2\}.
```

Let `S_old` be the pre-filter 2-gap starts and `S_q` the starts that remain
after installing `p`. A point of `S_q` in `W_q` is a square-safe twin-prime
certificate.

A condition holding at one stage gives one certificate. Holding at infinitely
many stages gives infinitely many certificates. Holding eventually at every
stage is a stronger requirement than is needed.

## Candidate Index

Each entry's empirical status (from the window-scale stress-test,
`candidates/analysis/`, p to ~19000) distinguishes a direct condition test from
a partial proxy or a deferred measurement. Every note includes its own
strategic assessment; see `candidates/analysis/FINDINGS.md` for the corrected
cross-candidate synthesis.

1. [Protected endpoints](protected-endpoints.md) — **[outcome measured]** 186/186; not a distinct mechanism
2. [Local surplus](local-surplus.md) — **[directly measured]** 186/186; terminal sufficient target
3. [Protected clusters](protected-cluster.md) — **[directly measured]** 185/186 (fails at (5,7))
4. [Bounded consecutive destruction](bounded-consecutive-destruction.md) — **[window-linear proxy]** flat, max run 2; cyclic condition unmeasured
5. [Bounded post-merge spacers](bounded-post-merge-spacer.md) — **[deferred]** whole-period
6. [Controlled merge runs](controlled-merge-run.md) — **[deferred]** composite, needs whole-period ingredient
7. [Balanced spacers](balanced-spacers.md) — **[deferred]** whole-period; local compressed-separator prefixes do not measure its cyclic maximum
8. [Distinguished head spacer](distinguished-head-spacer.md) — **[outcome measured]** 186/186; near-restatement of local survival
9. [Forbidden-copy covered runs](forbidden-copy-covered-run.md) — **[deferred]** copy-index / whole-period
10. [Short-window discrepancy](short-window-discrepancy.md) — **[post-filter E_q measured]** one-sided form holds 24/24 lineage layers; two-sided bound still pending
11. [Random-like merge survival](random-like-merge-survival.md) — **[benchmark measured]** favorable rate; deterministic transference unmeasured
12. [Local pattern-residue balance](local-pattern-residue-balance.md) — **[stated margin measured]** `νE<N(1−ν/r)` holds in 1,890/1,890 exact lineage layers across 53 heads
13. [Uniform local observable sampling](uniform-local-observable-sampling.md) — **[one-sided margin measured]** `H(2L/N+b₊)<L` holds in 1,890/1,890 exact lineage layers across 53 heads
14. [Hereditary shot-spacing capacity](hereditary-shot-spacing-capacity.md) — **[finite exact checks reinforced]** exact interval certificates hold at 4/4 defined Q17 layers and 23/23 defined Q101 layers, with proved spacing inputs through `k=10`; universal close-pair existence and population control remain open.
15. [Sharp admissible shot-spacing profile](sharp-admissible-shot-spacing-profile.md) — **[proved through k=14; recurrence program open]** fixed-`k` stabilization and exact `D(2)..D(14)=(2,6,8,12,16,20,26,30,32,36,42,48,50)` are proved by explicit witnesses and finite residue-cover certificates. Recurrence inequalities, scalable bounds, and extremal classification beyond `k=14` remain open.
16. [Expanded-zone exterior-capacity localization](expanded-zone-exterior-capacity.md) — **[unmeasured]** asks for an exactly countable expansion whose surviving total exceeds the maximum exterior capacity, or alternatively a safe copy-index branch that remains below a later square-certification horizon. The naive complete-copy lift is already shown insufficient by count alone.
17. [Seven-layer capacity floor](seven-layer-capacity-floor.md) — **[base floor proved; finite lower envelope reinforced]** `rho(Q,7)>1` is proved for every integer `Q>=17`; all 53 measured heads and 1,837 layers satisfy `rho(Q,r)>=rho(Q,7)`, with every chain minimum at `r=7`.
18. [Redundant close-pair capacity](redundant-close-pair-capacity.md) — **[density conversion and attrition bounds proved; finite redundancy reinforced]** `P` is exactly the short compressed-separator count; sharp bounds `P_new>=P_old-2H` and `D_new>=D_old-H` are proved, while monotone `P` and `D` are empirically refuted.
19. [Sixfold harmful-residue capacity](sixfold-harmful-residue-capacity.md) — **[algebra-first; unmeasured separately]** the one-layer destruction bound `K_r(W_Q)<=2(floor((Q^2-Q-3)/(6r))+1)` is proved from the common `5 modulo 6` phase; the open hereditary population floor is asymptotically `G_r(W_Q)>Q^2/(3r)`.
20. [Conditioned residue-collision energy](conditioned-residue-collision-energy.md) — **[algebra-first; unmeasured]** the collision reduction is proved; the candidate bound `C_r<=N_r+N_r^2/r` reduces the needed population to `6` gaps at `r=5`, `4` at `r=7`, and `3` at every `r>=11`, but the relative four-point correlation estimate is open.
21. [Cumulative weighted collision budget](cumulative-weighted-collision-budget.md) — **[primary composition framework; unmeasured]** the chain recurrence, corrected stopping index, first-deletion split, and orthogonal energy reduction are proved; it consumes weighted harmless dispersion plus the two scalar endpoint errors.
22. [Conditioned harmless-class collision energy](conditioned-harmless-class-collision-energy.md) — **[primary missing distribution theorem; unmeasured]** asks for `U_i<=N_{i+1}` after the two harmful classes are removed, with a weaker weighted aggregate preferred; together with #13 endpoint sampling, #23 accepted-strike density, and the proved orthogonal decomposition, it supplies the components needed by #21.
23. [Accepted-anchor strike density](accepted-anchor-strike-density.md) — **[primary missing scalar theorem; unmeasured]** isolates `epsilon_i=H_i/A_i-1/r_i`, gives the exact bridge `b_i=H_i beta_i+2N_i epsilon_i`, and asks for a weighted strike-error bound normalized by the initial main term rather than by an unknown final population.

## Established Background

The conditional arguments use established facts documented in the
[sieve-sequence property catalog](../properties/sieve-sequence/README.md):
filtering copies or merges gaps, later filtering cannot create a missing
2-gap, post-3 2-gaps are endpoint-disjoint, each new prime forbids two copy
classes, and a square-safe surviving pair is prime. Those established facts do
not establish any candidate hypothesis in this folder.

## Next Steps (algebraic proof program)

The finite experiments have served their candidate-selection purpose. The
active program is now to derive universal inequalities from the exact
copy/filter algebra. Existing data remains useful as a falsifier for a sharply
stated lemma, but extending the empirical range is not itself a next step.

### Cross-cutting algebraic priority

The main dependency chain is now:

```text
#23 accepted-strike density + #13 unsigned/signed endpoint sampling
    -> total harmful excess b_i and endpoint imbalance Delta_i
#22 harmless-class collision energy
    -> harmless dispersion U_i
orthogonal decomposition
    -> full residue energy V_i
#21 cumulative weighted collision budget
    -> hereditary survival
    -> local surplus / square-safe certificate (#2)
```

The first algebraic objective is the weakest weighted aggregate bound on
`sum_i w_i U_i` that fits #21 after symbolic endpoint-sampling and
accepted-strike error budgets are subtracted. Pointwise
`U_i<=N_{i+1}` is candidate #22's convenient benchmark, not a mandatory
per-layer premise. Any derivation must be audited against the final-layer
parity barrier: it must not assume a positive final population or normalize by
an unproved lower bound for it.

### REINFORCED — next step is proof, not measurement

For these the stated conditions hold across measurements; more data is unlikely
to add as much as a proof attempt would.

- **#2 Local-surplus (terminal target).** Prove `L(p,q) > A(p,q)` at infinitely
  many consecutive-prime transitions; the conditional implication then yields
  infinitely many twin-prime certificates. The empirical `p^1.6` surplus growth
  is the proof target — a lower bound of the form `L(p,q) - A(p,q) >= p^alpha`
  for some `alpha > 0` at large p. Highest value of any next step.
- **#14 Hereditary-shot-spacing.** Exact `k=2` interval certificates now hold
  across 53 heads and 1,837 defined layers; selected spacing fields through
  `k=10` are exact under the proved profile. Additional filters provably cannot
  decrease minimum `k`-span, but neither that fact nor the exact profile
  proves that an adequately close pair exists in every future square window. A bounded
  chain-population investigation also falsified the exact multiplicative and
  constant-error recurrences; the surviving unit-square-root recurrence is
  candidate #12 specialized to `2E <= sqrt(G)`. Proving that conditioned
  short-window discrepancy uniformly would still be twin-prime-strength.
- **#15 Sharp admissible shot-spacing.** The universal stabilization theorem
  and exact `D(2)..D(14)` profile are proved. For `k>14`, seek explicit upper
  witnesses together with transparent residue-cover lower certificates, then
  develop recurrence inequalities and scalable extremal bounds for `D(k)`.
- **#17 Seven-layer capacity floor.** The strict early floor is proved for
  every integer `Q>=17` and converges to `6/5`; the remaining proof target is
  the later-layer lower envelope
  `(r-1)(G_r(W_Q)-1) >= 6(G_7(W_Q)-1)`. Seek a cumulative conditioned-count
  invariant rather than false stepwise monotonicity.
- **#18 Redundant close-pair capacity.** The density-to-matching conversion is
  proved and captures a positive matching bound on every measured layer.
  Transition attrition is sharply bounded by `P_new>=P_old-2H` and
  `D_new>=D_old-H`, but monotone reconstruction is false. The remaining target
  is a uniform or unbounded lower envelope for
  `(Delta_r(G_r(W_Q)-1)-L_Q)/(Delta_r-6)`, with any stronger recovery term
  requiring an independent structural lower bound.
- **#19 Sixfold harmful-residue capacity.** The one-layer theorem is proved:
  the two harmful start classes contain at most
  `2(floor((Q^2-Q-3)/(6r))+1)` gaps. Next: attack the exact conditioned
  population floor `G_r(W_Q)>=2 floor((Q^2-Q-3)/(6r))+3`. Do not sum the
  per-layer maxima; that loses cross-prime overlap and introduces the divergent
  sum of reciprocal primes. Seek an overlap-aware batch inequality or a
  hereditary lower envelope.
- **#20 Conditioned residue-collision energy.** Same-residue pairs have the
  exact autocorrelation expansion
  `C_r=N_r+2 sum_h A_r(6rh)`. Next: derive an upper bound for the four-point
  correlation sum relative to the actual `N_r`, with the target
  `C_r<=N_r+N_r^2/r`. An absolute upper-bound-sieve estimate is insufficient
  until its normalization by `N_r` is justified independently.
- **#21 Cumulative weighted collision budget.** This is the primary algebraic
  composition framework. The proved identity
  `V_i=U_i+r_i b_i^2/(2(r_i-2))+Delta_i^2/2` replaces the earlier opaque
  stopped-kernel target. Next: combine #23 accepted-strike density with #13
  unsigned/signed endpoint sampling to bound `b_i,Delta_i`, then
  combine #22 or an aggregate harmless-dispersion theorem to bound `U_i`.
  Candidate #10 does not directly supply the strike-density estimate. Generic
  Fourier, black-box large-sieve, worst-difference, and symmetric
  class-capacity routes have already failed their algebraic audits.
- **#22 Conditioned harmless-class collision energy.** This is the primary
  missing distribution theorem. Prove or obstruct the weakest weighted
  aggregate that fits #21; the stronger pointwise benchmark is
  `U_i<=N_{i+1}`, equivalently
  `sum_{a notin {0,-2}}c_{i,a}^2<=N_{i+1}+N_{i+1}^2/(r_i-2)`.
  This is candidate #20's relative-collision scale on the smaller harmless
  alphabet. A weighted aggregate bound may suffice even if the pointwise
  version fails.
- **#23 Accepted-anchor strike density.** This is the primary missing scalar
  theorem. Bound `epsilon_i=H_i/A_i-1/r_i` in the weighted form consumed by
  #21. The exact target is obtained after inserting #13's endpoint error into
  `b_i=H_i beta_i+2N_i epsilon_i`; do not normalize by a positive final or
  late-layer 2-gap population.
- **#11 Random-like.** The real destruction rate is `~ p^-1.6`, well below the
  `2/p` benchmark. Next: a *deterministic* transference bound deriving
  `destruction_rate <= 2/p` (or stronger) from the modular arithmetic, not from
  a probabilistic model. Supplies target margins for #2.
- **#1, #8 (outcome formulations).** Not mechanisms — proof work should use them
  as the terminal statement a structural candidate (#2, #14) discharges. No
  independent next step.

### SMALL-PRIME CAVEAT — next step is a small-primorial measurement + a scope fix

- **#3 Protected-cluster.** Fails only at (5,7); clusters grow to 248 at scale.
  Next: (a) measure small complete periods to confirm the failure is genuinely
  restricted to the smallest window (cheap, `M_r` small there); (b) decide
  whether to restate the candidate to exclude `(5,7)`-class tiny windows, or
  handle the singleton case via #2's surplus. Proof priority medium.

### INCONCLUSIVE — next step is to close each one's specific measurement gap

- **#4 Bounded-consecutive-destruction.** The cyclic run is the *one* quantity
  genuinely unmeasurable at scale (period-scale, no stable shortcut like
  `sigma_r`). Next: either find a structural bound on the cyclic run (proof) or
  a small-primorial measurement to characterize `R_p` for small `M_r`. Proof
  priority high — characterizing the simultaneous-congruence requirements for a
  run of three destroyed starts could refute `R=2` or make it a real mechanism.
- **#10 Short-window-discrepancy.** The one-sided form is a restatement of
  survival. Algebraically, a useful next result must be a non-circular
  two-sided or averaged discrepancy estimate derived from the filter weights.
  Audit any proposed norm against the known Type II/parity boundary.
- **#12 Local-pattern-residue-balance.** The exact stated margin is now
  positive on the completed finite sweep. Restrict the theorem to the word
  `(2)` and, more sharply, to the sum of the two harmful classes. Candidate
  #19 shows that phase rigidity alone already supplies an absolute two-class
  cap; the open question is whether a smaller conditioned bound is provable.
- **#13 Uniform-local-observable-sampling.** The exact one-sided margin is now
  positive on the completed finite sweep. Restrict the algebra to the minimal
  unsigned endpoint indicator and signed left-minus-right endpoint observable.
  They control endpoint bias and `Delta_i`; candidate #23 supplies the
  separately required accepted-strike-density target for `b_i`. Do not seek a
  universal observable class first.

### DEFERRED (UNMEASURED) — next step is to scope each before any measurement

These need primorial-scale data. Do not run them blindly — first determine
whether a stable-wheel-type shortcut (like the one `sigma_r` turned out to
have) exists for each one's specific quantity.

- **#5 Bounded-post-merge-spacer.** Quantities: `D_max(q)` and the average
  spacer. Next: investigate whether the maximum spacer over the primorial wheel
  has a small-`k` stable structure (it may not — extreme values don't stabilize
  the way sums do). If not, measure only small complete periods to estimate the
  extreme-to-average ratio. Proof priority low as a direct route.
- **#6 Controlled-merge-run.** Composite of #4 + #5. Next: defer until at least
  one component (#4's cyclic run or #5's `D_max`) is understood independently.
- **#7 Balanced-spacers.** Quantity: complete-period imbalance factor `C(q)`.
  Local compressed-separator distributions inform #18 but cannot measure this
  cyclic maximum. Same next step as #5 — investigate a whole-period shortcut
  before measuring. Proof priority remains low in this form.
- **#9 Forbidden-copy-covered-run.** Copy-index view; has a fixed-seed scale
  problem once the target window moves beyond the seed period. Next: restate
  with the seed stage moving with the target head, or aggregate many seed
  2-gaps; the current form is low-priority.
- **#16 Expanded-zone exterior capacity.** First construct the smallest
  exactly countable expansion for several finite heads, then report
  `L_q-U_q`, where `L_q` is the rigorous expanded survivor lower bound and
  `U_q` is the exterior capacity. Separately measure the minimum safe copy
  index along the lifted branch tree against the square horizon. A full-copy
  total without exterior subtraction does not test the candidate.

### Separate effort, not candidate-specific

**Close the formal-verification gap.** The isolation lemma and five of the
"established inputs" cited across the candidate notes are not Stainless-verified,
and `verifyGeneralizedGrowth` (cited in `articles/learnings/learnings-capacity-argument.md`)
does not exist in any `.scala` file. Closing this is a separate formal-
verification effort; it underpins every candidate that leans on the isolation
lemma (#2, #3, #4, #11, #13, #14 and others).

## Historical Next Steps (superseded)

The earlier "fixed-future-window multi-layer lineage experiment" priority is
**complete** — it ran at Q=17 (pilot) and Q=101 (24-layer chain), validated
against hand-derived ground truth, and its findings are recorded in each
candidate note's "Empirical status" section and in
`candidates/analysis/FINDINGS_lineage.md`. The experiment bypassed the
`sigma_r` primorial wall with a finite-table shortcut, but that shortcut is an
unproved extrapolation at larger stages. The per-candidate next steps above
replace this section.
