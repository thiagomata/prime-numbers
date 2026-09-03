# Backward Bound to a Prior Head 2-Gap

## START HERE

Determine whether every canonical sieve sequence with current head `p_n` has
a **recent** predecessor whose head gap is `2`, uniformly within a backward
window of `f(p_n)` prime stages. A fixed ancient 2-gap is not allowed to answer
the question for all later heads. Keep predecessor-stage distance distinct
from distance within a periodic gap cycle, and do not infer positional
recurrence from global 2-gap abundance.

## Goal

State and justify the strongest available sliding-window upper bound on the
number of canonical predecessor stages needed to encounter an earlier head
2-gap. The bound must exclude every fixed historical anchor asymptotically.
The work is complete when the user's proposed `p`-step spread argument is
formalized or corrected, candidate improvements are classified by strength,
and the exact missing positional invariant is identified.

## Current State

The question has been corrected to a sliding backward-window theorem. The
earlier bound obtained by walking to `5 -> 7` is mathematically true but does
not answer this goal: it permits the same fixed event to witness every later
head. Existing inspected lemmas prove exact global/full-period 2-gap abundance
and `p - 2` copy survival, but do not control the position of a surviving
2-gap relative to later heads. No non-vacuous universal recurrence bound is
currently established. The balanced adversarial companion shows only that the
selected per-parent/global count laws are compatible with a fixed final head
2-gap. It is not a valid value-level filter: independently chosen per-parent
deletions need not assemble into one coherent arithmetic shot set and can
violate the proved shot-spacing, cyclic-sum, shared-endpoint, and rigid CRT
placement constraints. It is therefore not a countermodel satisfying all
proved real-sieve properties. A compact representation of the missing
coherence is now available: harmful copy offsets evolve as a modular phase walk
driven by the old gap prefix sums. The ingredients are proved separately, but
the recurrence has not yet been packaged as a named property. Its intended use
is deterministic and extremal, not random: maximize head damage over every
schedule allowed by the proved constraints and show that even this constrained
adversary cannot sustain permanent suppression.

The full coherent feasibility problem is now reduced exactly. For every prime
head `q>=5`, absence of a head 2-gap is equivalent to `q+2` being composite,
which is equivalent to some prime `r<=sqrt(q+2)<q` satisfying
`q == -2 mod r`. Thus permanent suppression is exactly eventual coverage of
all prime heads by the real shifted shot families `-2 mod r`. These families
already satisfy the spacing, cyclic-sum, shared-endpoint, and CRT constraints;
the fully coherent adversary has no residual choice.

This exact reduction is now promoted as
`properties/sieve-sequence/coherent-head-suppression-is-shifted-prime-shot-coverage.md`
and registered in the sieve-sequence property catalog. The note proves the
pointwise, finite-block, and eventual equivalences while explicitly making no
deterministic noncoverage or backward-recurrence claim.

The active investigation now steps back from the fully fixed CRT endpoint to
the coherent middle adversary. Its purpose is to determine whether fixed
within-parent separation plus one cross-parent phase already forces a local
destruction ceiling below the safe threshold, or whether a coherent relaxed
schedule can still attain complete target coverage.

The finite-layer question is now settled exactly. If `n_a` counts target
2-gap starts in residue `a mod r`, a shared affine phase `s` destroys
`D_r(s)=n_s+n_(s-2)`, so its worst damage is the maximum of this two-bin
histogram. Extinction occurs exactly when the support is contained in one
pair `{s,s-2}`. With the proved per-class capacity `B`, the sharp
capacity-only safety condition remains `N>2B`; shared phase and fixed pair
distance alone do not improve it. A read-only pass over 187 complete stored
windows found no coherent-phase extinction and measured
`w*=r*max_s(D_r(s))/(2N)` between `1` and `2.506667`; every measured stage
from `r=67` onward lay below `(1/2)log(r)`. These are finite observations.

The fixed shifted-residue cross-layer model is also classified. Choose once
and forever, in the absolute integer coordinate, one removed residue `c_r`
for each prime filter `r`, and require every canonical prime `q` to survive
all earlier filters before its head stage. Then every `c_r` must be zero: a
nonzero `c_r` is coprime to `r`, so Dirichlet's theorem supplies a prime
`q>r` in that residue and filter `r` removes it too early. The case `r=2` is
immediate. Dirichlet's theorem is an external mathematical dependency, not a
project-verified property. Zero shifts recover the real sieve's per-filter
absolute residue-removal family; no claim about reconstructing the complete
implementation is needed. This closes the fixed-one-residue shifted
adversary branch, while leaving the original real-filter recurrence problem
open.

The combined finite-layer and cross-layer classification is promoted as
`properties/sieve-sequence/coherent-phase-adversary-safety-boundary.md` and
registered in the sieve-sequence property catalog. The intermediate-adversary
investigation is complete; the ticket remains active only because its original
backward-recurrence goal is open.

The user's 2-focused adjacency observation opens a distinct route that the
phase-histogram analysis did not test. In the focused pattern `[2,R,2]`, the
four endpoints are `x,x+2,x+R+2,x+R+4`. Both neighboring 2-gaps can be
destroyed by filter `p>=5` only if `p` divides one of `R`, `R+2`, or `R+4`.
Therefore a separator satisfying `p` divides none of those three values
protects at least one of its adjacent 2-cells. This is the existing Pair Local
Factor theorem with start separation `d=R+2`, now used as a local deletion
graph rather than as a complete-period count.

The deletion graph gives an exact quantitative bound. If `B_p` of the `N`
cyclic focused separators are bad and `D_p` 2-cells are destroyed, then
`D_p<=floor((N+B_p)/2)` and at least `ceil((N-B_p)/2)` survive. A run of `k`
destroyed 2-cells requires `k-1` consecutive bad separators. Because every
run sum is positive and even, every bad separator has value at least `2p-4`;
therefore `R<2p-4` is automatically good, exactly candidate #14's `k=2`
close-pair certificate.

Over a complete pre-filter period, such a certificate always exists. The
average focused run is `P/N-2`, and
`P/N=6*product_(prime 5<=r<p)(r/(r-2))<=2p-4` by comparison with the
telescoping product over all odd integers. Hence the average is at most
`2p-6`, below the minimum bad value. This locates a protected adjacent pair
somewhere in the primorial period, not necessarily in the head-relative square
window. In 186 complete stored immediate windows with `p>=5`, none was
all-bad; the median bad fraction was zero, the maximum was `0.6` at `p=7`,
the maximum bad run was `2`, only 16 windows contained any bad separator, and
none did after the measured stage `p=463`. These are finite observations.

The graph theorem, complete-period corollary, measurement, and exact local
obligation are promoted as
`properties/sieve-sequence/two-focused-bad-separator-deletion-bound.md` and
registered in the property catalog. Existing transition work shows that raw
or matching close-pair counts are not monotone; the durable bounds are
`P_new>=P_old-2H` and `D_new>=D_old-H`. Thus adjacency protection is genuine,
but hereditary propagation still needs a conditioned lower envelope that
dominates attrition.

The bad-separator frequency is now explicit. If `C_p(R)` is the complete-period
focused run-value histogram, the three disjoint counts are sums of `C_p` on
three progressions modulo `6p`. For `p==1 mod 6`, their first values are
`A_4:2p-4`, `A_0:4p`, `A_2:6p-2`; for `p==5 mod 6`, they are
`A_0:2p`, `A_4:4p-4`, `A_2:6p-2`. Every later value adds `6p`.
Consequently `B_p/N<=average(R)/(2p-4)`. The complete-period average is
`P/N-2=O(log(p)^2)` by the classical Mertens product estimate already used in
the project, so the global bad-separator frequency is
`O(log(p)^2/p)->0`. This is a global rarity theorem, not a head-relative
noncoverage theorem.

In the 186 stored immediate windows, 646,492 separators split as
`A_0=12`, `A_2=0`, `A_4=16`; only 159 separators reached the possible bad
range `R>=2p-4`, of which 28 were bad. Exact small complete periods show that
`A_2` is not identically zero: it first appears in the checked chain at
incoming `p=23`.

The user then restored the investigation to its positional meaning. The
ambient value interval is `[q,q^2)`, while the eligible complete 2-gap-start
window is `W_q={x:q<=x and x+2<q^2}`; `L` counts pre-filter 2-gap starts in
`W_q`. On that population, cross-layer lineage is unnecessary if a fresh
one-transition surplus can be proved infinitely often. With `q=p+d`, the
exact accepted destructive capacity is
`A(p,q)=pi(p+2d+floor((d^2-1)/p))-pi(p-1)` and unconditionally `A<=3p`.
The exact complete-period pre-filter density defines the recorded
ambient-coordinate benchmark
`L_hat=(q^2-q)delta_p~kappa*p^2/log(p)^2`, so the projected ratio even against
the loose `3p` capacity diverges like `p/log(p)^2`. This is now recorded in
`candidates/local-surplus.md` and its candidate-index entry.

The scale separation is not yet a local theorem. Exactly
`L=L_hat+E_pre`, and no proved result prevents the distinguished-window error
`E_pre` from cancelling the main term. In 186 measured transitions, however,
the exact `A` histogram was `2:90, 3:68, 4:20, 5:8`, while actual `L/L_hat`
stayed between approximately `0.808` and `1.132` and the surplus reached
`1,431,886` at `p=19429`.

Proof status is explicit: exact `A`, `A<=3p`, and the conditional implication
`L>A => survivor` are proved; the asymptotic is proved only for the defined
benchmark `L_hat`; agreement of actual `L` with that benchmark is finite
empirical evidence; and actual `L>A` at infinitely many transitions remains
open.

## Expected State

- Define predecessor-stage distance exactly.
- Verify or correct the `p`-step baseline.
- Express a sliding-window claim as an explicit bound `R(n) <= f(p_n)`.
- Require `n - f(p_n) -> infinity`, so every fixed historical anchor is
  eventually outside the permitted window. A clean stronger target is
  `f(p_n) = o(n) = o(pi(p_n))`.
- Determine which existing properties imply such a bound and which only imply
  global abundance.
- If no improvement follows, isolate the weakest new positional statement that
  would suffice.

## Strategy

First formalize the canonical history relation. When the full
`SpecSieveSequence` is retained, its prime history can define the ancestor by
removing current heads; reconstructing a parent from only `(head, gap cycle)`
is a separate inverse problem and may be non-unique. Then translate a head
2-gap into the corresponding statement about consecutive prime heads, verify
the `p`-step pigeonhole/counting argument, and test whether exact 2-gap spread
properties bound the *maximum backward head-free run*. Prefer a direct
combinatorial recurrence bound; do not substitute average density for a
maximum-gap bound.

Use a hierarchy of increasingly faithful worst-case models:

1. Free per-parent adversary — rejected as an invalid filter.
2. Per-layer coherent adversary — chooses one initial phase; prefix sums then
   determine every harmful class in that layer.
3. Cross-layer coherent adversary — phases must also respect head rotation and
   predecessor/next consistency.
4. Full real CRT schedule — the initial phase is arithmetically fixed, leaving
   no adversarial choice.

Random and friendly companions are benchmarks only. No independence,
expectation, or random-survival premise belongs in the desired proof.

For the current micro-goal, separate two restrictions that the companion
article conflates: fixed separation inside each harmful pair, and shared phase
evolution across distinct parents. Test the first analytically before adding
the second; then express coherent destruction as an incidence maximum over the
finite phase set rather than as an independent per-parent hazard.

For the reopened adjacency route, work directly on the cyclic alternating
2-focused graph. Mark separator `R_i` bad for filter `p` exactly when `p`
divides `R_i(R_i+2)(R_i+4)`. Bound the number and run length of destroyed
2-cells by the bad separator set, then ask whether the focused transition law
prevents all separators in a relevant block from being bad.

For the current local-surplus micro-goal, work on a fresh positional population
at each transition rather than tracking one 2-gap lineage. Keep the exact
accepted capacity `A(p,q)` separate from the raw-multiple bound and write the
actual pre-filter count as `L=L_hat+E_pre`. Seek a deterministic lower bound on
`L` or on the incremental population `L_D` that beats `A` or `A-1`; do not
replace that bound by the complete-period-density projection or its finite
fit.

## Similar Tickets and Notes

- `tickets/active/sieve-sequence-property-catalog.md` catalogs exact global
  counts, survival, rotation, and the short-window discrepancy boundary.
- `tickets/active/algebraic-conditioned-survival-2026-07-27.md` studies the
  distribution obstruction and residue-class energy.
- `tickets/future/sieve-property-landscape.md` distinguishes global 2-gap
  abundance from maximum dead-interval/positional statements.
- `properties/sieve-sequence/reverse-engineered-eventual-head-scenario.md`
  gives a forward certificate for an eventual head 2-gap but does not provide
  a uniform recurrence-time bound.
- `articles/learnings/learnings-capacity-argument.md` records why global
  surplus does not force a local/head event.

## Definitions and Candidate Claim

Write the prime heads as `p_1=2, p_2=3, ...`. Let

```text
E(k) := p_(k+1) - p_k == 2
```

be the event that the stage headed by `p_k` has head gap `2`. Define the
backward recurrence distance

```text
R(n) = least j >= 1 such that E(n-j).
```

The desired theorem has the form `R(n) <= f(p_n)` for every sufficiently large
`n`, together with `n - f(p_n) -> infinity`. The latter condition is equivalent
to requiring `f(p_n) < n-C` eventually for every fixed `C`; it prevents any
fixed early event from serving forever. The stronger target `f(p_n)=o(n)` is
especially clear. A logarithmic bound is one example, not the fixed target.

The exact obstruction scenario is

```text
exists t: E(t) && forall k > t: !E(k).
```

Then `R(n)=n-t` for every `n>t`; the distance to the latest head 2-gap grows
forever even though the complete-period 2-gap population may grow at every
stage.

## Coherent Harmful-Offset Phase Walk

Let `M` be the old modulus, `r` the incoming prime, `a_i` the ordered old
accepted positions, and `g_i=a_(i+1)-a_i`. Define the harmful copy index of the
left endpoint by

```text
k_i = -a_i * M^(-1) mod r.
```

Then

```text
k_(i+1) - k_i = -g_i * M^(-1) mod r
```

and telescoping gives

```text
k_j - k_i = -M^(-1) * sum(g_t, i <= t < j) mod r.
```

For a 2-gap, the right-endpoint harmful class is always
`k_i-2*M^(-1) mod r`. Over one complete old period, `sum(g)=M`, so advancing
one unwrapped parent period changes the harmful phase by `-1 mod r`. This is
the coherent winding law that independent per-parent adversaries discard.

At one layer, `k_0` determines every `k_i`. A coherent adversary therefore has
at most `r` global phase choices, rather than independent choices for every
parent. Head suppression becomes a finite structured hitting-set problem over
those coherent schedules.

At full real-filter fidelity, that hitting-set problem is

```text
for every prime head q in the target block,
choose no witness freely; verify that q belongs to -2 mod r
for at least one actual earlier prime r <= sqrt(q+2).
```

The block is head-2-gap-free exactly when this coherent shifted-divisor cover
contains every prime head in it.

## Alternatives Considered

1. Use total 2-gap count in the full period. This is available but does not by
   itself bound a head-free run.
2. Invert the current gap cycle to reconstruct its parent. This may be useful
   computationally, but it is logically separate from walking retained prime
   history and invertibility is not established.
3. Translate the question directly to recurrence gaps between twin-prime lower
   members in prime-index space. This is the cleanest mathematical comparison
   and will reveal the strength of a proposed bound.
4. Use empirical data to estimate `B(p)`. This can suggest candidate functions
   but cannot prove a universal bound.

## Risks, Assumptions, and Hypotheses

- **Assumption:** canonical ancestors exist in the retained prime history.
  **Validation:** inspect `SpecSieveSequence` fields and `next` construction.
- **Assumption:** a head gap of `2` is equivalent to consecutive prime heads
  differing by `2`. **Validation:** inspect the proved head-prime and
  `apply(1) == nextPrime` lemmas.
- **Open hypothesis:** the user's `p`-predecessor guarantee follows from the
  proved spread structure in a genuinely sliding sense. **Validation:** state
  the exact set of predecessor stages being counted and show why at least one
  *head position*—not merely one cyclic/lifted 2-gap—must occur in that window.
- **Hypothesis:** exact spread supplies a maximum head-free-run bound.
  **Validation:** inspect the statement and body of every relevant `.holds`
  lemma, especially whether it mentions position/head rather than only count.
- **Risk:** every non-vacuous universal recurrence bound with
  `n-f(p_n)->infinity` forces an unbounded family of head 2-gaps and hence
  infinitely many twin primes. A quantitative bound such as `O(log p_n)` is
  substantially stronger than infinitude alone.

## What is Learned

- A head 2-gap is a positional event; full-period abundance is a global event.
- Exact survival of `p-2` copied descendants does not locate a descendant at a
  later head.
- “Walk to an ancestor” and “reconstruct a parent from current observable
  state” are different problems.
- The relevant statistic is the maximum backward run of prime stages with no
  head 2-gap, not the average density of 2-gaps inside a primorial period.
- Walking to the fixed `5 -> 7` event gives a true bound but answers a different,
  vacuous question. It supplies no recent-event recurrence.
- Since `p_n > n`, a window of `p_n` predecessor stages is larger than the
  entire available stage history. The user's asserted `p`-step spread argument
  must therefore be reconstructed carefully to determine whether its “steps”
  mean prime predecessors or another object such as lift/cycle positions.
- `SpecSieveSequence` retains the complete descending prime prefix in `primes`,
  and `AllPrimesSoFarList.tail` exposes the canonical earlier prefix.
- `SpecSieveSeqTwoGapProperties.assertExactlyHeadMinusTwoCopiesSurvive` proves
  a copy count only; its statement contains no later-head position guarantee.
- `Balanced Adversarial 2-Gap Companion::Targeted Head Suppression` realizes
  the fixed-last-event scenario exactly. Whenever a parent has a child at the
  prospective head, the companion spends one deletion there. At most one child
  of a parent can occupy that point, so the head remains empty while every
  parent still has exactly `r-2` global descendants.
- This is a countermodel to deductions from shared placement-blind properties,
  not to the real sieve. Real harmful indices are fixed as
  `{-a*M^-1, -(a+2)*M^-1} mod r`; they cannot be independently chosen for each
  parent to target the head.
- Real shots arise from one coherent accepted-multiple set. For each fixed
  `k`, their proved span has the form `sigma_r(k)=r*s_r(k)`, and cyclic shot-gap
  sums are fixed by the underlying period. A removed value is also shared by
  every incident 2-gap, so parent-level deletion decisions are not independent.
- Consequently the free adversary does not answer whether **all** proved
  properties permit permanent head suppression. It answers only whether the
  smaller placement-blind invariant family permits it.
- The coherent spacing/sum constraints invalidate that countermodel but do not
  yet prove recurrence: the Fixed-k Shot Spacing property explicitly constrains
  shot capacity without locating a surviving 2-gap at the head or in a target
  window.
- Raw shot coordinates need not be stored. One initial harmful phase plus the
  existing gap prefix sums reconstructs every later harmful phase through the
  telescoping recurrence above; `CycleIntegral` already provides the natural
  prefix-sum representation.
- The full-period sum supplies only the net winding `-1 mod r`. It does not
  control the local phase discrepancy of partial sums, so it cannot alone rule
  out a long interval of head avoidance.
- The desired conclusion is worst-case: if maximum head damage over all
  coherent, cross-layer-compatible schedules is smaller than the available
  target set, one target survives deterministically.
- Per-layer coherence may still be too weak. If a fresh global phase can be
  chosen at every layer, the adversary may align it with that layer's single
  prospective head target. Cross-layer head/rotation consistency is essential.
- Under the full real CRT rule, the initial phase is uniquely determined by
  absolute residue arithmetic rather than selected adversarially.
- The exact coherent cover automatically preserves the user's fixed shot sums:
  every witness is an actual multiple `q+2` of an earlier prime `r`, and all
  witnesses for the same `r` lie on its one arithmetic shot train.
- Therefore total shot sums and spacing invalidate the free adversary but do
  not themselves contradict permanent suppression. The missing statement is a
  deterministic noncoverage theorem: some prime head must escape every shifted
  family `-2 mod r` with `r<=sqrt(q+2)`.
- That noncoverage statement is exactly the twin-prime lower-bound/parity
  boundary in coherent-shot language, not a random-survival question.
- For one shared layer phase, the random benchmark is not an assumption but
  the exact phase average: `sum_s D_r(s)/r=2N/r`. The adversarial quantity is
  the maximum of the same phase-incidence function.
- The coherent phase is safe exactly when the target residue support escapes
  every translated harmful pair. Therefore a proof that the coherent maximum
  is below the article's frontier is a concrete two-class discrepancy theorem,
  not a consequence of the fixed distance itself.
- In 187 complete stored square windows, the coherent worst-phase relative
  factor remained bounded by `2.506667` and was below the article's
  `(1/2)log(r)` head frontier at every measured stage `r>=67`. This locates a
  plausible theorem target but supplies no asymptotic or deterministic bound.
- The 2-focused adjacency graph is strictly more local than the phase
  histogram: one good separator gives a concrete pair of which at least one
  2-gap survives, without estimating the total destruction rate.
- Complete-period density is enough to force a good separator globally, via
  the telescoping odd-integer product. The unresolved step is localization:
  force one good separator inside the relevant conditioned window at every
  needed layer.
- This is precisely the already-open hereditary close-pair route (candidate
  #14), now expressed as a forbidden simultaneous-deletion condition on the
  alternating 2-focused sequence.
- Globally, bad focused separators have vanishing frequency
  `O(log(p)^2/p)`. The estimate uses only the minimum size of a bad run and the
  exact average; it does not assume uniform residues.
- The exact progression split is asymmetric in `p modulo 6`. In particular,
  the `R+2` channel begins only at `6p-2`, explaining its absence in the
  immediate-window sample without proving it is always absent.
- Cross-layer CRT compatibility by itself permits arbitrary fixed residues
  `c_r`, but preservation of every canonical prime head rigidifies those
  residues to `c_r=0`. Any nontrivial absolute shifted-filter family therefore
  ceases to model the canonical prime-head history.
- Fresh local surplus bypasses individual cross-layer lineage: if
  `L(p,q)>A(p,q)` at infinitely many transitions, one local 2-gap survives
  each such transition and the moving window excludes any fixed ancient pair.
- The two sides have sharply separated projected scales. Accepted capacity is
  exact and at most `3p`, while the complete-period-density projection is
  `L_hat~kappa*p^2/log(p)^2`. The divergence of their projected ratio is
  unconditional algebra once the projection is adopted; transferring the
  density to the distinguished window remains unproved.
- Local surplus and bad-separator deletion use different representations.
  Local surplus lives in the all-gaps integer-coordinate representation and
  compares the pre-filter start set `S_i` with accepted strikes. The deletion
  graph lives in the 2-focused compression and compares 2-cell vertices with
  focused run-cell edges. The explicit bridge gives `N_i=|S_i|` focused
  2-cells and `max(N_i-1,0)` internal separators in a window-induced linear
  block; coordinate length, cell count, strike count, separator count, raw
  density, and focused `1/2` cell share are not interchangeable.

## Failed Paths

- **Pre-empted: infer the desired bound directly from global spread/count.**
  Existing analysis shows that intra-period count does not constrain head
  position. Retry only if a new lemma connects gap positions to successive
  canonical rotations/heads.
- **Pre-empted: treat `next` as automatically invertible.** The forward
  construction may discard parent information. Retry only after proving
  uniqueness or carrying explicit history as part of the input.
- **Pre-empted: claim every uniform finite backward bound proves twin-prime
  infinitude.** A bound reaching the fixed `5 -> 7` event needs no later twin
  pair. Retry only when a proposed bound eventually excludes every fixed
  historical anchor.
- **Rejected as the answer: fixed-anchor prime-counting bound.** The earlier
  `pi(p)-3` route measures distance to `5 -> 7`; it does not bound the most
  recent event by a sliding window. It remains only as a sanity baseline.
- **Rejected overclaim: the adversarial companion preserves every proved
  real-sieve property.** It preserves exact global descendant/count laws and
  placement-blind consequences, but replaces one coherent arithmetic shot set
  with free per-parent choices. Those choices can violate fixed shot spans,
  cyclic sums, shared-endpoint consistency, and rigid CRT placement. Retry only
  with a coherent-shot construction satisfying those value-level identities.
- **Closed: fixed within-pair distance plus one freely chosen layer phase
  forces safety.** The exact damage is `max_s(n_s+n_(s-2))`, which can equal
  the whole population whenever its residue support lies in one translated
  harmful pair. The verdict changes only with an independent population or
  two-class discrepancy theorem; distance coherence alone is exhausted.
- **Closed: fixed nonzero absolute residue shifts as a coherent middle
  model.** Dirichlet's theorem makes every nonzero shift remove a later
  canonical prime head. The verdict changes only if prime-head preservation
  is weakened to a finite prefix or shifts are allowed to change later, both
  of which abandon the original infinite canonical-history requirement.
- **Insufficient: complete-period average run below `2p-4`.** It proves a
  protected pair somewhere in each enormous primorial period but does not put
  it near the head or in `[q,q^2)`. Retry only with a localization or
  hereditary transition law for focused run values.

## Open Concerns

- Small heads may require exclusions or an inclusive `j = 0` convention.
- Existing “spread” terminology may refer to copy-index residue classes rather
  than spacing between head events.
- The user's “`p` predecessors” may use a different step unit from canonical
  prime-stage predecessors; this must be made explicit before proving it.
- Any claimed use of spread must identify a lemma connecting cyclic placement
  to the distinguished head across successive ancestors.
- It remains open whether real CRT-coupled harmful indices permit permanent
  head suppression. Ruling it out proves infinitely many head 2-gaps; proving
  it establishes an eventual end to twin primes.
- It is not yet known whether the proved coherent shot-spacing and sum
  constraints alone already rule out permanent suppression, or whether a
  placement satisfying them but lacking the full CRT formula can still do it.
- The consecutive harmful-offset phase recurrence appears not to be packaged
  as a named property even though its ingredients exist. Before adding code,
  its exact consumers and required prefix-discrepancy statement must be fixed.
- It is unknown precisely which proved cross-layer identity prevents—or fails
  to prevent—a fresh globally rotated shot schedule at every layer.
- **Resolved:** after enforcing the literal real shot families, there is no
  freely rotated cross-layer schedule to optimize. The feasibility question is
  exactly whether the shifted divisor families cover every sufficiently large
  prime head. Retry phase-optimization only for an explicitly relaxed model.

## Validation of Final Result

1. Quote the exact source definitions for the canonical ancestor relation.
2. Read the bodies of all load-bearing `.holds` lemmas, not only their names.
3. Derive the `p` baseline with explicit indices and boundary cases.
4. Translate every candidate `f(p)` into an ordinary prime/twin-prime
   recurrence statement as a strength sanity check.
5. If empirical evidence is used, label it separately from proof.
6. Run no Scala/Stainless gate unless source code is changed; this ticket is a
   read-only mathematical investigation.

## Next Action

Investigate a deterministic fresh-population lower bound for the positional
window: prove `L(p,q)>A(p,q)` or the sharper incremental
`L_D(p,q)>A(p,q)-1` for an infinite transition family. Start from the exact
period-density decomposition `L=L_hat+E_pre`, but treat control of `E_pre` as
the theorem rather than importing the favorable projection. The bad-separator
route remains a possible mechanism for bounding actual destruction, not the
primary population target.

## Learning Log

| Date | Learning | Action |
|---|---|---|
| 2026-08-29 | The user clarified that `log(p)` was illustrative; the actual goal is any justified improvement over an asserted `p` predecessor-stage bound. | Opened this ticket with `B(p)` as the recurrence statistic and made verification of the baseline the first task. |
| 2026-08-29 | Existing project analysis separates full-period 2-gap abundance from head-relative position and individual persistence. | Pre-empted global-density and automatic-inversion arguments pending a genuine positional bridge. |
| 2026-08-29 | Walking from head `p >= 7` to the known head 2-gap at `5` takes exactly `pi(p)-3` prime-indexed stages. | Replaced the loose `p` baseline by the exact fixed-anchor bound; recorded PNT and mod-6 consequences. |
| 2026-08-29 | The verified two-gap copy lemma proves `p-2` surviving lifts but does not locate a survivor at a future head. | Classified improvement below the fixed-anchor `pi(p)` scale as requiring a new positional bridge. |
| 2026-08-29 | User corrected the goal: the theorem must bound the most recent prior head 2-gap in a sliding predecessor window, not distance to one fixed old event. | Rejected the fixed-anchor route as an answer and defined the recurrence statistic `R(n)`. |
| 2026-08-29 | Excluding all fixed anchors requires `n-f(p_n)->infinity`; merely requiring `f(p_n)<n-C` for one fixed `C` is insufficient. | Adopted the correctly quantified non-vacuity condition and retained `o(n)` as a stronger clean target. |
| 2026-08-29 | The central obstruction is a fixed final event `t`, after which `R(n)=n-t` grows forever. | Reframed the question as compatibility of permanent head suppression with the proved property families. |
| 2026-08-29 | Targeted Head Suppression proves the balanced adversarial companion can suppress every future head while retaining exact `r-2` global growth. | Concluded that shared/global properties cannot rule out a fixed last head 2-gap; kept transfer to the rigid real CRT sieve open. |
| 2026-08-29 | User identified that independent per-parent adversarial deletions need not preserve the fixed sum/spacing between real filter shots. Inspection confirmed real shots have coherent scaled spans `sigma_r(k)=r*s_r(k)`, fixed cyclic geometry, and shared-value coupling. | Retracted the companion as a countermodel to all proved properties; retained it only against the placement-blind subset and set a coherent-shot adversary as the next test. |
| 2026-08-31 | Coherent shot placement can be compressed into the phase recurrence `k_(i+1)-k_i=-g_i*M^(-1) mod r`, with segment displacement determined by a gap prefix sum and full-period winding `-1 mod r`. | Replaced the proposed raw shot table with a CycleIntegral/prefix-phase representation; isolated local partial-sum discrepancy as the remaining information. |
| 2026-08-31 | User clarified that random survival is already understood and is not the target; the theorem must defeat the worst adversary allowed by every proved structural constraint. | Recast the phase model as a deterministic maximum-damage/hitting-set problem and separated per-layer coherence from essential cross-layer phase consistency. |
| 2026-08-31 | Enforcing the actual coherent shots collapses head suppression to an exact cover: no head 2-gap at prime `q` iff `q` lies in `-2 mod r` for some prime `r<=sqrt(q+2)`. | Resolved the constrained-adversary feasibility formulation; isolated deterministic noncoverage of shifted prime shot families as the exact remaining theorem and selected a proved boundary-property note for promotion. |
| 2026-08-31 | The exact coherent-cover reduction has been promoted and cataloged with pointwise, finite-block, and eventual formulations. | Closed the structural-reformulation step; any further progress now requires a named parity-breaking/noncoverage estimate rather than another rearrangement of the existing invariants. |
| 2026-08-31 | The user asked to exhaust the coherent middle model before ending the research. | Reopened the finite-layer extremal question: replace independent adversarial hazards by the maximum target incidence over one shared phase and compare it with the safe threshold. |
| 2026-08-31 | One shared phase has exact damage `max_s(n_s+n_(s-2))`; capacity permits extinction up to the sharp boundary `N<=2B`. In 187 stored complete windows, no phase extinguished the population and `w*<=2.506667`, with all measured `r>=67` below `(1/2)log(r)`. | Closed distance coherence alone as a proof route; retained the observed constant-scale worst phase as a precise discrepancy target and advanced to cross-layer/head-preservation rigidity. |
| 2026-08-31 | A once-for-all absolute shifted residue `c_r!=0` removes a later prime in that progression, by external Dirichlet, so preserving every canonical prime head forces all shifts to zero. | Closed the fixed shifted-residue coherent middle model without closing the real-filter recurrence problem; selected a final boundary-property promotion. |
| 2026-08-31 | The coherent-phase incidence, sharp capacity line, finite measurements, and prime-head rigidity theorem are now promoted and cataloged. | Completed the intermediate-adversary investigation. Preserved the original ticket as open and recorded the two precise conditions under which this branch is worth reopening. |
| 2026-08-31 | User redirected the argument to adjacency in the alternating 2-focused compression. Exact endpoint arithmetic shows `[2,R,2]` can lose both 2-cells only when `p` divides one of `R,R+2,R+4`; `p∤R` alone is insufficient under the repository's run-sum convention. | Reopened the ticket on a local deletion-graph route: derive survival from good separators and measure whether bad separators can cover relevant focused blocks. |
| 2026-08-31 | Bad focused separators control destruction exactly: `S_p>=ceil((N-B_p)/2)`, and bad run values are at least `2p-4`. The complete-period average is at most `2p-6`, forcing a global good edge, while 186 stored windows were never all-bad and only 16 contained any bad edge. | Identified the idea with candidate #14's close-pair mechanism, proved its graph form, and isolated localization/heredity—not aggregate sums—as the remaining obligation. |
| 2026-08-31 | The focused bad-separator theorem is promoted and cataloged. Existing separator-transition measurements refute monotone reconstruction, while sharp attrition `P_new>=P_old-2H`, `D_new>=D_old-H` remains proved. | Preserved adjacency as the correct mechanism and narrowed further work to a conditioned lower envelope strong enough to absorb attrition. |
| 2026-08-31 | User proposed measuring how frequently large focused run sums are multiples of the incoming prime. | Split the observable into the disjoint `R`, `R+2`, and `R+4` divisibility channels and opened an exact-count audit for consecutive focused separators. |
| 2026-08-31 | Bad separators lie on three explicit progressions modulo `6p`, and their complete-period frequency is at most `average(R)/(2p-4)=O(log(p)^2/p)`, hence tends to zero globally. The stored immediate windows contained only 28 bad edges among 646,492 separators. | Replaced the random-frequency question with an exact histogram formula and deterministic global rarity theorem; isolated local transfer of rarity as the remaining problem. |
| 2026-08-31 | On the positional danger window, fresh local surplus eliminates the need to propagate an individual 2-gap across layers. Exact accepted capacity has `A<=3p`, whereas the conditional density projection has `L_hat~kappa*p^2/log(p)^2`; all 186 measured transitions have large positive surplus. | Promoted the scale comparison into `candidates/local-surplus.md` and its registry entry; redirected the open theorem to an unconditional lower bound on actual `L` or `L_D`, explicitly preserving the uncontrolled local discrepancy. |
| 2026-08-31 | The projected scale separation concerns the defined benchmark `L_hat`, not the actual distinguished-window count `L`; only the capacity formulas and conditional survival implication are algebraically proved. | Added explicit `[Mathematically proved]`, `[Definition; benchmark]`, `[Empirically checked on a finite sample]`, and `[Open]` classifications to the primary candidate and registry, and mirrored the distinction in Current State. |
| 2026-08-31 | The all-gaps representation and 2-focused compression are different coordinate systems for the same stage; their populations, distances, densities, capacities, and boundary counts cannot be substituted directly. | Extended `VOCABULARY.md` with the cyclic raw-gap definition, 2-focused compression, `R_focus,j` coordinate bridge, window-induced focused-block boundary rules, and explicit non-equivalences. |
