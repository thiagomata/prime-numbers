# Deferred-Filter-Three Cluster Survival

**Candidate hypothesis:** Unproved and potentially false.

**Conditional implication:** Mathematically proved (a surviving 2-run of
length `>=3` at the deferred-3 stage forces a 2-gap that also survives
reinstalling filter `3`).

**Status of the originally proposed three-lemma plan:** The proposed
"cluster-growth" lemma is **mis-stated**: growth is real and exact, but it
comes from *deferring* more primes, not from a recurrence over installed
primes (see "Correction: The Growth Mechanism Is Exact, Not A Recurrence"
below); the corrected mechanism still does not reach the window-localization
target, so it collapses into the erosion lemma. The proposed
"reintroduce 3" step is **not** a separate open estimate: it is a proved
exact corollary (Lemma C below) once a length-`>=3` survivor is found. The
genuine open content of this candidate is therefore a single unified target,
stated in "The Actual Open Target."

## Motivation

Filter `3` is installed immediately after filter `2` in every existing
sieve-sequence note. That convention is why 2-gap starts are endpoint-disjoint
(`two-gap-isolation-after-filter-three.md`) and separated by at least `6`
(`x\equiv5\pmod6`), which is exactly what all of candidates #2--#4 rely on.

This candidate asks what happens if the same primes below a future head `Q`
are installed in a different order — every prime `<Q` except `3`, then `3`
last — before certifying survivors in the eligible square-safe window `W_Q`.
Reordering does not change the final accepted set (`gcd(n,P(Q))=1` does not
depend on the order the factors of `P(Q)` were multiplied in), so this is a
proof strategy, not a different target.

Without filter `3`, 2-gap starts are **not** isolated: three consecutive
accepted values `x,x+2,x+4` can all survive at once, producing runs
("2-runs" below) of more than one consecutive 2-gap. The motivating idea is
to track these runs as a unit instead of tracking individual 2-gaps.

## Setup

Fix a future head `Q`. Let the **deferred-3 conditioned chain to `Q`**
install every prime `r<Q` with `r\ne3`, in increasing order, starting from
filter `2`. Call its accepted set `A_Q^{(3)}`.

A **2-run of length `L`** at a stage is a maximal block of `L+1` accepted
values

```math
y,\ y+2,\ y+4,\ \ldots,\ y+2L
```

(automatically consecutive, since no integer lies strictly between two odd
values 2 apart) with `y-2` and `y+2L+2` not accepted. It contains `L`
2-gaps.

## Correction: The Growth Mechanism Is Exact, Not A Recurrence

**Lemma A (sharp prime cap on 2-run length). Mathematically proved.** If an
odd prime `p` is installed, every 2-run has length at most `p-2`, and this
bound is exactly attained somewhere in the complete period.

*Proof.* A 2-run of length `L` is `L+1` terms of an arithmetic progression
with common difference `2`. Since `\gcd(2,p)=1`, consecutive terms cycle
through all `p` residues mod `p` with period `p`. If `L+1\ge p`, the block
contains a full period and therefore a value `\equiv0\pmod p`, contradicting
that every term survives filter `p`; so `L\le p-2`. Conversely, removing the
single forbidden residue `\equiv0\pmod p` from the cyclic order leaves one
arc of exactly `p-1` consecutive surviving residues, i.e. `p-2` consecutive
gaps — achievable, by CRT, at a stage where `p` is the only relevant
obstruction. `[Q.E.D.]`

Consequently, at any stage, the global maximum 2-run length equals
`p_{\min}-2`, where `p_{\min}` is the **smallest currently installed odd
prime**. This is the correct, exact version of "no growth from installing
more primes": installing a larger prime on top of an already-installed
smaller one cannot relax the cap, because `p_{\min}` does not change. That
is exactly why the finite check above shows length `3` after installing
`\{2,5\}` and *still* length `3` after adding `7` — `5` remains `p_{\min}`.

**Growth is real, and it is exact — it comes from deferring more primes,
not installing more.** Deferring `3` makes `p_{\min}=5`, cap `3`. Deferring
`3,5` makes `p_{\min}=7`, cap `5`. Deferring `3,5,7` makes `p_{\min}=11`,
cap `9`. In general, deferring every prime below some threshold `p_0` gives
cap `p_0-2`, and `p_0` can be pushed arbitrarily high by deferring further
— this is confirmed directly: installing only `\{2,7\}` (deferring `3,5`)
gives accepted residues `\{1,3,5,9,11,13\}\pmod{14}`, and `9,11,13,15,17,19`
is a genuine run of length exactly `5=7-2`, bounded by the removed points
`7` and `21`.

**What this does not give you.** The cap `p_{\min}-2` is the maximum over
the *entire period* of every prime from `p_{\min}` up to `Q` — a modulus of
size `\sim e^Q`, unaffected by how many small primes were deferred. Pushing
`p_{\min}` higher raises the theoretical ceiling, but says nothing about
whether a run anywhere near that ceiling lands inside the specific shrinking
window `W_Q`. That is exactly the localization question in "The Actual Open
Target" below, and deferring more primes does not touch it: the modulus that
matters for landing inside `W_Q` is still generated by every prime between
`p_{\min}` and `Q`, not by the (small, fixed) deferred set.

This is the natural dual of `stable-small-k-shot-spacing.md`'s monotonicity
lemma (`s_B(k)\ge s_A(k)` for minimum span): that property proves survivors
only get *more spread out* as filters accumulate; Lemma A proves the exact
complementary ceiling on how *unbroken* a run can stay, and identifies
`p_{\min}` as the single quantity controlling it.

## Generalization: Deferring More Than One Prime

Everything above generalizes cleanly to deferring any fixed finite set of
odd primes `\{p_1,\ldots,p_m\}` (e.g. `\{3,5,7\}`), reinstalled together at
the end:

- **Cap.** The maximum 2-run length at the deferred stage is
  `p_{\min}-2`, where `p_{\min}` is the smallest prime *not* in the deferred
  set (Lemma A applies verbatim).
- **Guaranteed reinstatement (generalizes Lemma C).** Let
  `M=p_1p_2\cdots p_m`. By CRT, a 2-gap start `x` survives reinstalling all
  of `p_1,\ldots,p_m` simultaneously iff `x` avoids the two harmful residues
  mod each `p_i`, i.e. iff `x` lands in one of `\prod_i(p_i-2)` good residues
  mod `M` out of `M` total. A run of `L` consecutive starts is guaranteed
  (deterministically) to contain a good one once `L` is at least the worst-
  case gap between good residues in the cyclic (step-by-`2`) order mod `M` —
  a fixed, finite, computable threshold depending only on `\{p_1,\ldots,
  p_m\}`, generalizing Lemma C's `L\ge3` for `\{3\}` alone. This candidate
  does not compute that threshold for `\{3,5,7\}`; the exact value is a
  finite check, not an open question, but is left unverified here.
- **The trade-off.** Deferring more primes raises the achievable cap
  `p_{\min}-2` but also raises the reinstatement threshold (more simultaneous
  congruence conditions to satisfy). Neither side of this trade-off touches
  the localization question: whichever threshold is required, it must still
  be met *inside* `W_Q`, using only the primes between `p_{\min}` and `Q`
  that are not deferred — the same open obstruction as the single-prime
  case, independent of how large the deferred set is.
- **Connection to candidate #25.** Letting the deferred set grow with `Q`
  (defer every prime below a threshold `z(Q)`, rather than a fixed finite
  set) is structurally the same move as the `z=Q^{2\alpha}` construction in
  [Chen-type almost-prime survivor](chen-type-almost-prime-survivor.md) and
  its Divisor Local Factor, Bilinear Character Obstruction, and Cofactor Progression Discrepancy properties. This candidate's natural generalization likely
  reduces to, or at least shares its exact obstruction with, that existing
  program rather than being an independent route.

## Corrected Erosion Accounting

**Lemma B (run erosion is a path vertex cover). Mathematically proved.**
Inside a 2-run of length `L` (a path with `L` edges), a single filter strike
on an *interior* accepted value destroys exactly two of the `L` 2-gaps
(merging them into one 4-gap); a strike on either boundary value of the run
destroys exactly one. Consequently:

- `k` strikes destroy at most `\min(L,2k)` of the run's 2-gaps, with equality
  achievable by placing `k` interior strikes no two of which are adjacent;
- destroying every 2-gap in the run requires at least `\lceil L/2\rceil`
  strikes (the minimum vertex cover of a path with `L` edges).

This differs from `two-gap-isolation-after-filter-three.md`, where every
strike destroys at most **one** 2-gap because 2-gaps cannot be adjacent once
`3` is installed. In the deferred-3 chain that guarantee does not hold, and
`bounded-consecutive-destruction.md`'s existing destroyed-start-run analysis
(built for the isolated, post-3 case) does not transfer as-is: any survival
argument here must use the factor-2 vertex-cover accounting, not a
one-strike-one-gap count.

## The Reintroduce-3 Step Is Solved, Not Open

**Lemma C (any length-`>=3` run survives reinstalling `3`). Mathematically
proved.** A 2-gap start `x` survives filter `3` if and only if `x\equiv2
\pmod3` (the other two residues kill `x` or `x+2` outright). A run of length
`L` has `L+1` accepted values but only `L` *starts* — its final value is an
endpoint only, not the start of a gap inside the run — so the relevant
population is the `L` consecutive starts, not the `L+1` values.

The threshold is `L\ge3`, not `L\ge2`. A length-`2` run has only two starts
`x,x+2`, with residues `x,x-1\pmod3` — only two of the three residue
classes, so the class `\equiv2\pmod3` can be entirely missed. Concretely,
`x\equiv1\pmod3` gives starts with residues `1,0`, neither `\equiv2`, so
*neither* 2-gap of that run survives filter `3`. (This is not a corner case:
it happens for exactly one residue of `x` in three.)

A run of length `L\ge3` has at least three consecutive starts
`x,x+2,x+4,\ldots`, and any three consecutive starts already cover all of
`\{0,1,2\}\pmod3`:

```math
x,\quad x+2\equiv x-1,\quad x+4\equiv x+1
\pmod3.
```

```math
\boxed{
\text{A surviving 2-run of length}\ge3\text{ at the deferred-3 stage
contains a 2-gap start}\equiv2\pmod3,
}
```

hence a 2-gap that survives reinstalling `3`. `[Q.E.D.]`

This is exact and deterministic — not a density or equidistribution
estimate — and it is still a modest, fixed requirement (three consecutive
2-gaps, independent of `Q`), not the unbounded length the original plan's
Lemma 1 mistakenly asked for.

## The Actual Open Target

Combining Lemmas A--C, the entire three-lemma plan reduces to one statement:

```math
\text{For infinitely many prime heads }Q\text{, the deferred-3 chain's
accepted set }A_Q^{(3)}\text{ contains a 2-run of length}\ge3\text{ inside
}W_Q.
```

If this holds, Lemma C converts it into a genuine square-safe 2-gap
survivor after reinstalling `3`, i.e. a twin-prime pair in `[Q,Q^2)`.

This target is **not** known to be easier than the standing local-window
problem that every other candidate in this catalog is stopped by. A
fixed-length admissible pattern (Lemma A's starting point plus `H=\{0,2,
\ldots,2L\}`) is easy to place *somewhere* in a complete period by the same
CRT technique as `stable-small-k-shot-spacing.md` — and, without a mod-`3`
constraint to satisfy, that placement step is if anything easier than in the
standard order. But that file's own stated limitation applies verbatim
here: complete-period existence for fixed `L` does not localize to the
specific shrinking window `W_Q`, and `W_Q` is a vanishingly small fraction
of the full deferred-3 period. Growing `L` with `Q` (needed here, since the
window shrinks relative to the period) only sharpens the same obstruction.
No route around it is proposed by this candidate.

## Finite Consistency Check

Skipping `3`, installing `2` then `5`: accepted residues mod `10` are
`\{1,3,7,9\}`. Reading the cyclic gap word `2,4,2,2` and unrolling it (the
word both starts and ends in `2`, so consecutive periods glue at the
boundary), the maximum 2-run has length `3`: `7,9,11,13` (gaps `2,2,2`),
recurring once per period, bounded by `4`-gaps.

Installing `2,5,7` (still skipping `3`): accepted residues mod `70` are the
`28` candidates coprime to `10` minus the four values struck by filter `7`
(`7,21,49,63`), leaving `24` residues. Direct computation of the cyclic gap
sequence gives a maximum run of `3` again — e.g. `27,29,31,33`,
`37,39,41,43`, and, across the period boundary, `67,69,71,73` (`\equiv
67,69,1,3\pmod{70}`) — now occurring three times per period instead of once.
The run count scales with the period, but the *maximum length* did not grow
at this step, exactly as Lemma A predicts: `5` remains `p_{\min}` whether or
not `7` is also installed, so the cap stays `5-2=3` both times.

These are falsifiers of the hand computation, not a proof of the general
erosion rate.

The length-`3` run `7,9,11,13` also checks Lemma C concretely. Its two starts
`7,9` have residues `1,0\pmod3`: dropping the run to length `2` (just
`7,9,11`) would leave *no* surviving start, matching the counterexample in
Lemma C's proof. The third start `11\equiv2\pmod3` is what rescues it: `11`
and `13` are both nonzero mod `3`, so `(11,13)` genuinely survives
reinstalling filter `3`, exactly as Lemma C predicts, and only because the
run reached length `3`.

## Established Inputs

- [Fixed-`k` shot spacing: monotonicity and eventual stability](
  ../properties/sieve-sequence/stable-small-k-shot-spacing.md) — source of
  Lemma A's dual (span monotonicity) and of the complete-period-vs-window
  limitation this candidate inherits.
- [Isolation of 2-gaps after filtering by 3](
  ../properties/sieve-sequence/two-gap-isolation-after-filter-three.md) —
  the property that fails in the deferred-3 chain and motivates Lemma B.
- [Bounded consecutive destruction](bounded-consecutive-destruction.md) —
  the closest existing attempt at an erosion-run bound, in the isolated
  (post-3) setting; its refuted `R=2` conjecture and "unmeasurable at scale"
  cyclic quantity are a realistic difficulty precedent for Lemma B's
  compounded (multi-stage) form, not yet addressed by this candidate.
- [Protected cluster](protected-cluster.md) — the nearest existing
  survives-if-fewer-hits-than-gaps argument, built for endpoint-disjoint
  2-gaps; Lemma B supplies the corrected accounting needed to reuse this
  style of argument on non-isolated runs.

## Limitation

- Lemma A, B, and C are proved, but none of them supplies the open target.
  Lemma A gives an exact ceiling (`p_{\min}-2`) and identifies deferring more
  primes as the only lever that raises it; Lemma B corrects the per-strike
  destruction count; Lemma C disposes of the mod-`3` step. None of them
  bounds how much of a run near that ceiling survives by the time the chain
  installs every prime from `p_{\min}` up to `Q`, restricted to landing
  inside `W_Q` specifically.
- A 2-gap survives the whole chain iff neither endpoint is ever struck by
  any filter, so Lemma B's vertex-cover count already applies to the *total*
  strikes a run absorbs across every stage `5,7,11,\ldots,<Q` (skipping
  `3`), not only one filter. What Lemma B does **not** supply is a bound on
  that total strike count itself — how many of a given run's `L+1` values
  get struck, in total, by the whole remaining chain. Bounding that count is
  exactly the open erosion-rate question; Lemma B only converts a strike
  count into a destroyed-gap count once the former is known.
- No claim is made that the deferred-3 reordering is easier than the
  standard order for the hard part (local existence in `W_Q`). The concrete
  benefit demonstrated here is confined to Lemma C (mod-`3` reinstatement is
  free) and to the removal of one admissibility constraint in the
  easy, complete-period half of the argument.

## Relation To Other Candidates

This does not weaken the target the way candidate #25 does: a survivor here
is a genuine twin-prime pair, not an almost-prime. It is a proof-strategy
variant of the standing twin-prime candidates (#1--#24), sharing their exact
final target and, as far as this note establishes, their exact obstruction.
