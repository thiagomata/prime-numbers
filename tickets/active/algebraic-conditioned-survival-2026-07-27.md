# Algebraic Conditioned Survival

## START HERE

Read the exact definitions in candidates #12, #13, and #14, then express the
smallest deterministic counting lemma that would make candidate #14 hereditary.
Do not run a new empirical sweep. The immediate task is to separate genuine
algebraic reductions from statements equivalent to the desired survivor.

## Goal

Develop and critically evaluate an algebraic proof program for forcing a
2-gap to survive every conditioned filter below a future square window. This
ticket is complete when the strongest defensible next theorem has an exact
statement, its dependencies on proved properties are explicit, circular or
twin-prime-equivalent formulations have been rejected, and the next formal
lemma is small enough to prove or falsify directly.

## Strategy

Treat candidate #14 as the consumer of a population-distribution theorem, not
as the theorem to attack directly. Audit three possible algebraic bridges:

1. a two-class discrepancy bound specialized to 2-gap starts (candidate #12);
2. an endpoint-observable sampling bound (candidate #13);
3. a recurrence or conserved quantity for conditioned local counts.

Prefer identities and inequalities derived from the exact copy/filter action.
Use the existing empirical results only to choose among statements; do not
collect more data. At every reduction, check whether the proposed premise is
strictly weaker than the final existence claim or merely restates it.

## Current State

- The project has strong finite support for candidates #12, #13, and #14.
- The spacing/capacity side of candidate #14 has a proved small-`k` foundation.
- The remaining obstacle is conditioned population control: bounding how many
  current 2-gaps land in the two harmful residue classes of the next prime.
- A new deterministic one-layer bound has been derived. If
  `L_Q=Q^2-Q-3`, then the harmful-hit count at incoming prime `r>=5` satisfies

  ```math
  K_r(W_Q)
  \le
  2\left(
  \left\lfloor\frac{L_Q}{6r}\right\rfloor+1
  \right).
  ```

  Consequently,

  ```math
  G_r(W_Q)
  \ge
  2\left\lfloor\frac{L_Q}{6r}\right\rfloor+3
  ```

  forces at least one 2-gap to survive that layer. This is not a discrepancy
  assumption: it follows because every post-3 start is `5 modulo 6`, while the
  incoming filter can destroy starts only in two classes modulo `r`.
- Exact multiplicative recurrence and constant additive-error approaches have
  already failed; neither should be retried without a new invariant.
- The current work is checking this bound carefully, comparing it with the
  existing order-only `k=2` threshold, and deciding how to promote the result
  as a proved property plus a narrower hereditary candidate.
- The result has now been promoted as
  `properties/sieve-sequence/harmful-residue-capacity-after-filter-three.md`
  and candidate #19,
  `candidates/sixfold-harmful-residue-capacity.md`.
- A second-moment refinement has been derived. If `c_a` counts current 2-gap
  starts in class `a modulo r`, `N=sum_a c_a`, and

  ```math
  V_r=\sum_{a\bmod r}\left(c_a-\frac Nr\right)^2,
  ```

  then the exact harmful count `K=c_0+c_{-2}` satisfies

  ```math
  K\le\frac{2N}{r}+\sqrt{2V_r}.
  ```

  Also,

  ```math
  V_r
  =
  \sum_{a\bmod r}c_a^2-\frac{N^2}{r},
  ```

  where `sum c_a^2` is the exact ordered-pair count for starts whose
  difference is divisible by `r`. This gives an alternative averaged
  algebraic target to candidate #12's worst-class discrepancy.
- The collision reduction is now promoted as
  `properties/sieve-sequence/two-class-survival-from-collision-energy.md`.
  For post-3 starts it has the exact autocorrelation form

  ```math
  C_r(S)
  =
  N+
  2\sum_{1\le h\le\lfloor L/(6r)\rfloor}
  A_S(6rh),
  ```

  where each `A_S(6rh)` counts the four-point endpoint pattern
  `{0,2,6rh,6rh+2}`.
- A concrete new candidate benchmark has emerged:

  ```math
  C_r(S)\le N+\frac{N^2}{r}.
  ```

  Together with the proved collision lemma, this forces survival whenever

  ```math
  N>\frac{2r^2}{(r-2)^2}.
  ```

  The exact integer floors are `N>=6` for `r=5`, `N>=4` for `r=7`, and
  `N>=3` for every prime `r>=11`.
- Candidate #20 has been created as
  `candidates/conditioned-residue-collision-energy.md`.
- The one-layer energy inequality unrolls exactly across a conditioned chain.
  For incoming primes `r_0<...<r_{m-1}`, define

  ```math
  a_i=1-\frac{2}{r_i},
  \qquad
  e_i=\sqrt{2V_i}.
  ```

  If `N_i` is the actual 2-gap population before layer `i`, then

  ```math
  N_{i+1}\ge a_iN_i-e_i
  ```

  and induction gives

  ```math
  N_m
  \ge
  N_0\prod_{j<m}a_j
  -
  \sum_{i<m}
  e_i
  \prod_{i<j<m}a_j.
  ```

  This exposes a cumulative weighted-energy theorem that could replace
  pointwise discrepancy at every layer.
- The chain recurrence is now promoted as
  `properties/sieve-sequence/weighted-collision-energy-chain-survival.md`.
  Every changing population has an exact fixed-initial-set representation:

  ```math
  f_i(x)=\prod_{j<i}\mathbf 1_{r_j\nmid x(x+2)},
  ```

  and

  ```math
  \sum_iw_iV_i
  =
  \sum_{x,y\in S_0}\sum_i
  w_if_i(x)f_i(y)
  \left(
  \mathbf 1_{r_i\mid(x-y)}-\frac1{r_i}
  \right).
  ```
- Define the deletion time `tau(x)` as the first layer that hits `x` or `x+2`,
  or `m` if no layer does. Then

  ```math
  f_i(x)f_i(y)
  =
  \mathbf 1_{i<\min(\tau(x),\tau(y))}.
  ```

  For a pair difference `d=x-y`, the inner energy kernel is therefore a
  stopped weighted divisor sum over primes dividing `d`.
- Candidate #21 has been created as
  `candidates/cumulative-weighted-collision-budget.md` and is the primary
  algebraic target.
- The centering part of every stopped kernel telescopes exactly. With
  `w_{-1}=A_{0,m}`,

  ```math
  \frac{w_i}{r_i}=\frac{w_i-w_{i-1}}2,
  ```

  so the pair kernel stopped at `t>=1` is

  ```math
  \sum_{\substack{i<t\\r_i\mid d}}w_i
  -
  \frac{w_{t-1}-A_{0,m}}2.
  ```

  A difference with no relevant incoming prime divisor contributes
  nonpositively.

## Expected State

- One exact primary theorem and, if useful, one weaker fallback are written in
  algebraic form.
- Every term is grounded in the existing sieve-sequence definitions.
- A dependency chain shows precisely how the theorem would imply candidate
  #14 and then local survival.
- Known proof barriers and falsifiers are recorded.
- The first formalizable lemma is identified without claiming the open theorem
  has been proved.

## Similar Tickets

- [Prove hereditary shot spacing](prove-hereditary-shot-spacing-2026-07-23.md)
  contains the detailed boundary analysis for candidate #14.
- [Exact Q sweep for top candidates](../done/exact-q-sweep-top-candidates-2026-07-27.md)
  records the completed finite evidence and explains why more of the same is
  not the present bottleneck.

## Alternatives Considered

- **More empirical sampling:** rejected for this ticket because it cannot
  establish the required all-level statement and the existing footprint is
  already sufficient for prioritization.
- **Attack candidate #2 directly:** deferred because its local-surplus
  inequality hides the same harmful-hit distribution problem.
- **Prove more shot-spacing constants:** deprioritized because candidate #14's
  current obstruction is the supply and distribution of useful 2-gaps, not
  the geometry of a fixed finite cluster.
- **Use a probabilistic independence heuristic:** rejected as a proof unless
  converted into a deterministic finite-group or character-sum statement.

## Assumptions And Hypotheses

- **Assumption:** after filter `3`, distinct 2-gaps have disjoint endpoints.
  Validate against the proved isolation property.
- **Assumption:** a filter by prime `r > 2` destroys a 2-gap exactly when its
  start lies in one of two harmful residue classes modulo `r`.
  Validate from the filter definition and endpoint arithmetic.
- **Hypothesis:** the useful bridge can be stated as one-sided discrepancy for
  these two residue classes, rather than uniformity over every residue class.
  Validate by deriving the survivor inequality exactly.
- **Hypothesis:** a square-root-scale error is sufficient at every conditioned
  layer when combined with the existing local-count/capacity inequality.
  Validate symbolically; do not infer it from samples.
- **Risk:** a discrepancy bound strong enough at the last layer may be
  equivalent in difficulty to the twin-prime conclusion. Test logical strength
  before promoting it as progress.

## Validation

- Check definitions against candidate files and proved property notes.
- Derive every implication symbolically with named quantities and explicit
  inequalities.
- Search existing `.holds` lemmas before proposing any new Scala lemma.
- For any proposed recurrence, test it algebraically against the exact
  copy/filter decomposition already documented; existing data may be used only
  as a known counterexample source, not extended.
- Markdown-only changes require link and formatting checks, not Stainless.

## What is Learned

- Candidate #14 should be viewed as a deterministic capacity consumer.
- The prospective missing theorem concerns conditioned distribution into two
  harmful residue classes, not raw 2-gap density alone.
- A proof must exploit more structure than the average over residue classes:
  the next filter selects a particular pair of classes.
- Candidate #12 is stronger than necessary because it controls every residue
  class. For direct 2-gap survival, only the sum of the `0` and `-2` start
  classes matters.
- The installed filters `2` and `3` supply useful phase rigidity. Every 2-gap
  start is `5 modulo 6`; within any one residue class modulo a new odd prime
  `r`, two starts differ by a multiple of `6r`. Hence a start interval of
  diameter `L_Q` contains at most `floor(L_Q/(6r))+1` starts in that class.
- Summing the capacities of the two harmful classes gives a non-probabilistic
  destruction bound and the sufficient population threshold
  `2 floor(L_Q/(6r))+3`.
- The new threshold is asymptotically `L_Q/(3r)`, compared with the existing
  order-only close-pair threshold `L_Q/(2r)`. It directly forces one-layer
  survival but does not necessarily produce candidate #14's close pair.
- Cauchy--Schwarz converts the two-class harmful excess into the `L2` residue
  variance `V_r`. Parseval-by-counting rewrites that variance as the excess
  number of same-residue ordered pairs. This may be more tractable than
  pointwise equidistribution because it asks for a count of divisible
  differences, not control of every class.
- The collision criterion and the sixfold capacity theorem are not uniformly
  ordered. If `m=max_a c_a`, then `sum c_a^2<=mN`, but this implies the
  collision criterion only under the stronger count condition

  ```math
  N>
  \frac{m}{
  \frac12-\frac1r+\frac{2}{r^2}
  }.
  ```

  Candidate #19 needs only `N>2m` when the two harmful classes each have
  capacity `m`. For small `r`, the global energy condition can be worse because
  it charges variance in harmless classes. Collision energy is useful only if
  the exact difference structure yields a substantially sharper bound than
  `sum c_a^2<=mN`.
- The relative collision benchmark replaces candidate #19's order-`Q`
  population requirement at late layers by a constant population requirement.
  The price is a four-point correlation upper bound normalized by the actual
  conditioned population `N`, not by the complete-period main term.
- The threshold simplification is exact:

  ```math
  \left(
  \frac12-\frac1r+\frac{2}{r^2}
  \right)-\frac1r
  =
  \frac{(r-2)^2}{2r^2}.
  ```
- A pointwise collision benchmark `V_i<=N_i` gives
  `e_i<=sqrt(2N_i)`. Iterating that worst-case error is a constant-sensitive
  route: heuristic main-term and accumulated-error scales can both be of order
  `Q^2/log^2 Q`. Therefore the coefficient cannot be discarded as lower order.
- The unrolled formula suggests a genuinely different target: control the
  weighted sum of the actual `V_i` across the chain, possibly by a large-sieve
  or dispersion inequality, instead of bounding every selected harmful phase
  separately.
- The fixed-set bilinear identity resolves the changing-domain objection but
  not the changing-coefficient objection. The deletion-time form compresses
  those coefficients into one stopping index per start.
- Because `|x-y|<Q^2`, the positive prime-divisor terms in each off-diagonal
  stopped kernel satisfy a product constraint. Large incoming prime divisors
  cannot occur arbitrarily many times in one difference. The negative
  centering sum `-sum w_i/r_i` is part of the same exact kernel and should not
  be discarded.
- The multiplicative survival weights were chosen by the recurrence, and their
  centering terms are discrete derivatives. This is the first exact
  cancellation mechanism found in the algebraic pass.
- Algebraic route ranking:
  1. **Cumulative weighted energy (prospective #21):** best current research
     target because it matches hereditary composition and permits averaged
     control across layers.
  2. **#19 absolute harmful-class capacity:** strongest unconditional
     one-layer result; keep as the fallback if a population lower envelope can
     be proved.
  3. **#20 pointwise relative collision:** useful local testbed and source of
     the energy recurrence, but requiring its benchmark at every layer is more
     rigid than a cumulative budget.
  4. **#12/#13:** broader pointwise frameworks; use only their specialized
     two-class or endpoint consequences.
  5. **#14:** retain as a consumer/composition theorem, not the primary missing
     algebraic estimate.

## Failed Paths

- **Exact multiplicative recurrence for the local 2-gap count.** It fails
  because square-window boundaries and conditioning introduce non-multiplicative
  boundary terms. Retry only if an augmented state closes exactly under the
  copy/filter action.
- **Uniform constant additive correction.** Existing counterexamples rule out
  the tested constant bound. Retry only if the correction is allowed to scale
  with a proved boundary statistic.
- **Treating average residue occupancy as occupancy of the harmful classes.**
  The average does not control the particular classes chosen by the next
  filter. Retry only with a structural symmetry or discrepancy theorem that
  identifies those classes.
- **Additional finite sweeps as proof progress.** They can falsify but cannot
  supply the universal algebraic step. Reconsider only to test a genuinely new,
  sharply stated algebraic identity.
- **Summing the absolute one-layer harmful capacities through the chain.**
  Starting from a post-3 population of order `L_Q/6`, the cumulative bound
  subtracts a main term proportional to
  `(L_Q/3) sum_{r<Q} 1/r`. The reciprocal-prime sum is unbounded, so this
  bookkeeping eventually loses the entire initial population even before
  floor errors. It also double-counts gaps harmful to several primes. Retry
  only with an overlap-aware batch count or a potential that credits repeated
  coverage.

## Open Concerns

- The precise normalization used by candidates #12 and #13 may obscure a
  simpler integer inequality.
- The square-root premise may be sufficient but still too strong to prove from
  current properties.
- Boundary contributions from copies entering and leaving `[Q,Q^2)` may need a
  separate deterministic lemma before any discrepancy argument can close.
- It is not yet known whether endpoint observables give strictly more algebraic
  leverage than direct counts of 2-gap starts.
- The new harmful-class capacity still requires a conditioned population lower
  bound of order `Q^2/r`; at late layers this is order `Q`. Establishing that
  bound for all relevant future heads may still encounter the parity barrier.
- Iterating the per-layer absolute capacities by a union bound is expected to
  be too lossy; the divergent reciprocal-prime factor confirms this
  algebraically.
- A collision-energy bound strong enough at the final layer may still encode
  the parity problem. Its logical strength must be audited before it is treated
  as a route around the known discrepancy wall.
- Standard upper-bound sieve estimates naturally bound four-point counts in
  terms of window length and local densities, whereas the proposed benchmark
  is relative to the unknown actual `N`. Converting an absolute upper bound
  into `N+N^2/r` without already having a strong lower bound for `N` may
  reintroduce the parity problem.
- The conditioned sets `S_i` change with `i`, so a classical large-sieve
  inequality for one fixed set does not apply verbatim. A viable cumulative
  theorem must either embed all `S_i` into one fixed weighted population or
  prove a monotone comparison that survives conditioning.
- A per-pair upper bound for the stopped divisor kernel may be too coarse when
  summed over `S_0^2`. Any proposed divisor-budget lemma must be checked at the
  aggregate scale required by the weighted-energy survival inequality.

## Next Action

Split the fixed-set bilinear form into diagonal and off-diagonal contributions.
For the off-diagonal part, group pairs by `d=x-y` and derive the sharpest
deterministic aggregate bound obtainable from:

1. the exact stopped/telescoped kernel;
2. `0<|d|<Q^2-Q`;
3. the product constraint on incoming prime divisors of `d`;
4. the nesting of deletion times.

Before promoting any bound, substitute it into candidate #21's exact weighted
budget. If a worst-difference estimate scales like `N_0^2` with an
unaffordable constant, record that route as failed rather than weakening the
target.

## Learning Log

| Date | Learning | Action |
|---|---|---|
| 2026-07-27 | Finite evidence has served candidate selection; the proof bottleneck is conditioned two-class distribution. | Opened an algebra-only proof-program ticket and excluded new sweeps from its strategy. |
| 2026-07-27 | Post-3 phase rigidity bounds each harmful residue class by `floor((Q^2-Q-3)/(6r))+1`; two classes give a new one-layer survival threshold asymptotic to `Q^2/(3r)`. | Recorded the exact derivation, its improvement over the `k=2` order threshold, and the remaining population/parity concern. |
| 2026-07-27 | Promoted the sixfold capacity theorem and candidate #19. A sharper Cauchy--Schwarz route replaces worst-class discrepancy by same-residue collision energy. Naive cumulative subtraction fails algebraically because it introduces the divergent reciprocal-prime sum and loses overlap. | Made collision energy the next theorem and recorded cumulative absolute capacity as a failed path. |
| 2026-07-27 | Correction: the global collision-energy criterion does not automatically recover candidate #19 from the per-class cap. It can be stronger at small `r` because harmless-class variance contributes to the energy. | Reclassified collision energy as an alternative route whose value depends on a sharper divisible-difference count. |
| 2026-07-27 | Same-residue collisions equal a diagonal plus four-point autocorrelations at shifts `6rh`. The benchmark `C<=N+N^2/r` would reduce the needed population to 6 gaps at `r=5`, 4 at `r=7`, and 3 at every `r>=11`. | Promoted the exact identity as a property and selected a relative-collision candidate for formal comparison with #12 and #19. |
| 2026-07-27 | The one-layer energy loss unrolls into a multiplicative main term minus a weighted sum of actual layer energies. This meets the earlier failed chain route's retry condition because it seeks cumulative structural control rather than a pointwise square-root assumption. | Made the weighted cumulative-energy theorem the primary next algebraic target, with changing conditioned sets recorded as the central obstacle. |
| 2026-07-27 | Nested conditioned populations embed exactly into one initial set. Deletion times turn the cumulative energy kernel into a stopped, centered prime-divisor sum for each pair difference `|d|<Q^2`. | Ranked cumulative energy first and selected an aggregate divisor-kernel bound as the next concrete lemma. |
| 2026-07-27 | The centering weights telescope: `w_i/r_i=(w_i-w_{i-1})/2`. Hence only differences with relevant incoming prime divisors can contribute positively to the off-diagonal cumulative kernel. | Created candidate #21, promoted the chain and stopping-time identities, and narrowed the next proof loop to an aggregate divisor-incidence bound with an immediate budget check. |
