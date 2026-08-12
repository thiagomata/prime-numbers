# Realized Filter Adversariality Score

**Status:** Mathematically proved algebraic diagnostic. This note does not
claim Stainless verification, filter intent, or deterministic randomness.

## Purpose and Setup

The raw fraction of locally destroyed 2-gaps does not place a random filter at
the fixed midpoint `1/2`: its natural benchmark depends on the filter prime.
This note declares a continuous piecewise-linear normalization with the
requested anchors:

- `0`: no gap in the typed local population is destroyed;
- `1/2`: destruction matches the random-residue/complete-copy benchmark;
- `1`: every gap in the typed local population is destroyed.

This normalization is useful but not unique. It measures a realized outcome,
not friendly or adversarial intent.

Let `p>2` be prime. For one explicitly chosen local pre-filter population, let

```math
L>0,
\qquad
0\le K\le L
```

be respectively the number of 2-gaps before filter `p` and the number destroyed
by that filter. Define

```math
f=\frac KL,
\qquad
d_p=\frac2p.
```

The score is undefined when `L=0`. An empty population is neither assigned a
friendly score nor an adversarial score.

## Why the Benchmark Is `2/p`

The benchmark has two compatible meanings.

First, choose one forbidden residue class uniformly modulo `p`. The two
endpoints of a 2-gap occupy distinct residue classes because `p>2`. The chosen
class hits one endpoint with probability

```math
d_p=\frac2p.
```

Second, follow one inherited 2-gap through its `p` translated copies in a
complete copy block. One copy places its left endpoint in the forbidden class
and a different copy places its right endpoint there. Exactly two of the `p`
copies are destroyed, again giving `2/p`.

The second statement is an exact complete-copy/global proportion. It does not
assert that a shorter deterministic local window has the same proportion.

## Definition

Define the realized filter adversariality score by

```math
C_p(f)=
\begin{cases}
\dfrac{f}{2d_p},&0\le f\le d_p,\\[6pt]
\dfrac12+\dfrac{f-d_p}{2(1-d_p)},&d_p\le f\le1.
\end{cases}
```

The first branch stretches destruction below the benchmark across `[0,1/2]`.
The second branch stretches destruction above the benchmark across `[1/2,1]`.

## Anchors, Continuity, and Monotonicity

The three anchors follow directly:

```math
\begin{aligned}
C_p(0)&=0,\\
C_p(d_p)&=\frac12,\\
C_p(1)&=
\frac12+\frac{1-d_p}{2(1-d_p)}
=1.
\end{aligned}
```

Both branches equal `1/2` at `f=d_p`, so the score is continuous. Their slopes
are

```math
\frac1{2d_p}>0,
\qquad
\frac1{2(1-d_p)}>0,
```

because `0<d_p<1`. Therefore `C_p` is strictly increasing on `[0,1]`.

For a finite integer population, the value `K/L=d_p` may be unattainable.
Score `1/2` remains the declared benchmark anchor even when no integer `K`
lands exactly on it.

The score regions mean only

```math
\begin{aligned}
C_p(f)<\frac12&\iff f<d_p,\\
C_p(f)=\frac12&\iff f=d_p,\\
C_p(f)>\frac12&\iff f>d_p.
\end{aligned}
```

They mean below, equal to, or above the benchmark destruction rate. They do not
prove friendly intent, random behavior, or extinction.

## Exact Survival Limit

Strict monotonicity and the endpoint anchor give

```math
\begin{aligned}
L-K>0
&\iff K<L,\\
&\iff \frac KL<1,\\
&\iff C_p(K/L)<1.
\end{aligned}
```

Thus the exact limit is

```math
C_p<1.
```

Score `1` is local extinction. Every realized score strictly below `1` leaves
at least one member of the chosen population alive. This is an outcome
equivalence, not a recurrence theorem.

## Exact Excess-Removal Allowance

Suppose an integer `x` appears in the one-sided bound

```math
K\le d_pL+x.
```

This bound alone forces survival exactly while its right side remains below
`L`:

```math
d_pL+x<L
\iff
x<(1-d_p)L.
```

The largest integer satisfying that strict inequality is

```math
x_{max}
=
\left\lceil(1-d_p)L\right\rceil-1
=
\left\lceil\left(1-\frac2p\right)L\right\rceil-1.
```

This threshold is necessary and sufficient relative to only the assumptions
`0<=K<=L` and `K<=d_pL+x`. At the next integer value, the bound no longer
excludes `K=L`. A larger allowance does not claim that the actual sieve causes
extinction; it means this bound alone no longer guarantees survival.

## Turning a Capacity Theorem into a Score Bound

Let `H>=0` be a proved upper bound on destruction for the same typed population
counted by `L`:

```math
K\le H.
```

Then

```math
\frac KL
\le
\min\!\left(1,\frac HL\right).
```

Monotonicity gives the rigorous adversariality bound

```math
C_p(K/L)
\le
C_p\!\left(
\min\!\left(1,\frac HL\right)
\right).
```

The right side is a proved upper bound on the realized score. It is not an
observed score or an estimate of typical behavior. If `H<L`, this upper bound
is strictly below `1`, so survival is guaranteed even under worst-case use of
the proved capacity.

## Full-Window and Annular Instances

For consecutive primes `p<q` with `p>=5`, use the actual full square-safe
pre-filter counts `L(p,q),K(p,q)`. Because filter `3` is already installed,
endpoint isolation and the exact accepted-strike count give

```math
K(p,q)\le A(p,q).
```

Therefore

```math
C_p(K(p,q)/L(p,q))
\le
C_p\!\left(
\min\!\left(1,\frac{A(p,q)}{L(p,q)}\right)
\right).
```

For consecutive primes `p<q` with `p>=5`, the refined annular population
inherits the preconditions of the Danger-Annulus Decomposition property. Require `L_D(p,q)>0` so that its
score is defined. The Danger-Annulus Decomposition property gives

```math
K_D(p,q)
\le A(p,q)-1
\le R_V(p,q)-1.
```

Hence

```math
C_p(K_D(p,q)/L_D(p,q))
\le
C_p\!\left(
\min\!\left(1,\frac{A(p,q)-1}{L_D(p,q)}\right)
\right).
```

The exact annular survival condition remains `K_D(p,q)<L_D(p,q)`. The
exact-accepted-capacity sufficient condition is

```math
L_D(p,q)>A(p,q)-1,
```

with the weaker raw sufficient condition

```math
L_D(p,q)>R_V(p,q)-1.
```

Without a positive lower bound for `L_D`, these formulas do not prove an
annular score below `1`.

## Observed, Benchmark, and Proved Quantities

These three uses must remain separate:

- observed `K,L` determine the realized fraction `K/L` and score `C_p(K/L)`;
- `d_p=2/p` is exact over complete copies and is the random-residue model
  expectation, but need not equal a local observed fraction;
- a capacity `H` supplies a rigorous upper bound on the score, but does not
  predict the realized score.

The score cannot manufacture a missing population lower bound. It also does
not prove deterministic random-like transference, annular abundance,
recurrence, or infinitely many surviving heads.

## Finite Full-Window Evidence

**Evidence status:** The numbers in this section are finite observations from
measured full square-safe windows. They are not annular results, asymptotic or
recurrence theorems, or evidence that the deterministic filters are random.

The source files are
[the dense measurements](../../data/candidates/window-measurements.csv) and
[the sparse measurements](../../data/candidates/window-measurements-sparse.csv).
Together they contain 192 data rows. After excluding the two `p=3` rows, 190
clean rows remain. Merging by unique `(p,q)` finds four duplicate keys:
`(5,7)`, `(7,11)`, `(11,13)`, and `(557,563)`. The duplicates agree in
`G_local`, `destroyed`, `destruction_rate`, and `A_worst`, leaving 186 unique
clean transitions.

For these `p>=5` transitions, the CSV column `A_worst` equals the exact accepted
strike count `A(p,q)`. Define the observed score and the proved capacity ceiling
by

```math
C_{obs}
=
C_p\!\left(\frac{\mathtt{destroyed}}{\mathtt{G\_local}}\right),
\qquad
C_{cap}
=
C_p\!\left(
\min\!\left(1,\frac{\mathtt{A\_worst}}{\mathtt{G\_local}}\right)
\right).
```

The realized full-window scores are:

| Statistic | `C_obs` |
|---|---:|
| count | 186 |
| minimum | 0 |
| median | 0 |
| unweighted mean | 0.044177363545902307 |
| maximum | 0.47727272727272724 |
| zero-score transitions | 95 |
| below / equal to / above `1/2` | 186 / 0 / 0 |

The proved full-window capacity ceilings are:

| Statistic | `C_cap` |
|---|---:|
| count | 186 |
| minimum | 0.006784399338495748 |
| median | 0.1285745802948713 |
| unweighted mean | 0.16908125524560394 |
| maximum | 0.5545454545454546 |
| below / equal to / above `1/2` | 177 / 1 / 8 |
| below `1` | 186 |

The midpoint classifications use exact integer comparisons, not rounded
scores. For observations, compare `pK` with `2L`; the counts below, equal to,
and above are `186 / 0 / 0`. For capacity ceilings, compare `pA` with `2L`;
the counts are `177 / 1 / 8`. The unique capacity equality occurs at
`(p,q)=(17,19)`, where `L=17`, `A=2`, and `pA=2L=34`.

The closest observed transition to the random/global benchmark, and the
maximum observed score, is `(p,q)=(7,11)`:

```math
L=11,
\qquad
K=3,
\qquad
A=4,
```

```math
\frac{K/L}{2/p}
=
\frac{21}{22},
\qquad
C_{obs}
=
\frac{21}{44}.
```

The same transition has the maximum capacity ceiling

```math
C_{cap}=\frac{61}{110}.
```

Thus every measured observed score lies below `1/2`: these finite full windows
were less destructive than the benchmark rate. This does not prove random-like
transference or friendly intent. The capacity ceiling is a rigorous per-row
worst-case bound, not typical behavior. Its value may exceed `1/2` while the
realized score remains below `1/2`.

All 186 capacity ceilings are below `1` because `A(p,q)<L(p,q)` in every
measured clean full window. This is the already-recorded finite full-window
local-surplus certificate expressed on the new scale, not a new abundance
theorem.

Neither CSV contains `L_D,K_D`. Consequently, no observed annular score or
numeric annular capacity ceiling is reported.

## Global-Window and Danger-Annulus Recurrence Are the Same Question

This section states a logical equivalence, not a new existence result. It
follows from definitions already established elsewhere in this repository and
needs no additional empirical input.

For consecutive primes `p<q`, the
[safe-window certification theorem](safe-window-two-gaps-certify-twin-primes.md)
makes `(x,x+2)` a genuine twin-prime pair whenever it is accepted after every
filter below some prime `Q` with `Q<=x` and `x+2<Q^2`. A fixed pair therefore
satisfies the full-window membership condition `W_Q=[Q,Q^2)` only for primes
`Q` in the bounded range

```math
\sqrt{x+2}<Q\le x.
```

Consequently, no finite set of twin-prime pairs can supply
`G_{\mathrm{surviving}}(p,Q)>0` (equivalently `C_p(K/L)<1` on the full window,
per the Exact Survival Limit above) at infinitely many transitions: each
pair's coverage of `Q` is finite, so infinitely many qualifying transitions
require infinitely many distinct pairs.

Consecutive value annuli `V_{p_i,p_{i+1}}=[p_i^2,p_{i+1}^2)`, defined in the
[incremental danger-annulus decomposition](incremental-danger-annulus-decomposition.md),
partition the integers above `p_1^2` with no gaps or overlaps. Every
twin-prime pair therefore belongs to exactly one annulus -- the one in which
it is newly exposed -- and survives filter `p_{i+1}` there because it is
genuinely prime forever.

Combining both facts:

```math
\begin{aligned}
&G_{\mathrm{surviving}}(p,Q)>0
\text{ at infinitely many transitions}\\
\Longleftrightarrow\quad
&K_D(p,q)<L_D(p,q)
\text{ at infinitely many danger-annulus transitions}\\
\Longleftrightarrow\quad
&\text{infinitely many twin primes exist.}
\end{aligned}
```

### Limitation

This equivalence is unconditional but content-free: it does not establish
either side. The identical argument, run on the contrapositive, is equally
valid: if only finitely many twin primes exist, the danger annulus is
eventually permanently empty of survivors, at exactly the transitions where
the global window's surplus would also vanish for good. The equivalence says
the two framings share a fate; it does not say which fate they share. Proving
either side at infinitely many transitions remains open -- see
[Local surplus](../../candidates/local-surplus.md) and
[Short-window discrepancy](../../candidates/short-window-discrepancy.md).

For why "danger zone" undersells what this annulus actually is -- a single
decisive last-chance test, not sustained exposure -- and a worked toy model of
why positional distance from the head is not the same as remaining-filter
count, see Section 24 of
[Learnings: Capacity Argument](../../articles/learnings/learnings-capacity-argument.md#24-the-queue-thinning-analogy-distance-from-the-head-is-not-a-filter-count).

## Three Compounding Trajectories: Running The Score Forward

Everything above evaluates `C_p(f)` at one transition. This section runs the
same three anchors -- `0`, `1/2`, `1` -- forward across many transitions,
starting from a real anchor count `N_0` (some measured `G_local(p_0,q_0)`,
e.g. from `data/candidates/window-measurements.csv`), instead of evaluating
the score once. Each line is a projection under a stated assumption about
every future filter's behavior, not a claim about what the real sequence
does.

### The three anchor trajectories

```math
\begin{aligned}
N_{\mathrm{friendly}}(Q)&=N_0
&&\text{(}f=0\text{ at every step; trivial ceiling, survivors can never exceed }N_0\text{)}\\[4pt]
N_{\mathrm{random}}(Q)&=N_0\prod_{p_0<r\le Q}\left(1-\frac2r\right)
&&\text{(}f=d_p=2/r\text{ at every step; Section 24's anchored projection)}\\[4pt]
N_{\mathrm{adversarial}}(Q)&=\max\!\left(0,\;N_0-\!\!\sum_{p_0<r\le Q}\!\!A(\cdot,r)\right)
&&\text{(}f=1\text{ applied only up to the proved capacity }A\text{ at each step)}
\end{aligned}
```

`N_friendly` is flat by construction. `N_adversarial` uses the already-proved
capacity bound `A(p,q)` from "Turning a Capacity Theorem into a Score Bound"
above, run forward instead of stopping after one transition -- it is the
tightest *provable* worst case, not the degenerate hypothetical of `f=1`
applied literally forever (that version zeroes `N_0` at the very first step
and is a looser, less informative bound). `N_random` is `C_p=1/2` compounded,
already established in Section 24 of the Learnings file linked above.

### The fourth line: what was actually measured

The three lines above are all projections under a stated assumption. There is
a fourth line that is not a projection at all -- the literal measured counts,
`N_{\mathrm{empirical}}(Q) = G_{\mathrm{local}}(p,Q)` (or `G_{\mathrm{surviving}}`),
read directly off `data/candidates/window-measurements.csv` and the lineage
run behind `candidates/short-window-discrepancy.md`. Unlike the other three,
it has no closed form and cannot be extended past where it was actually
computed: `p` up to `~19000` for the 186 window-scale transitions, `Q=101`
across 24 layers for the lineage chain.

Where it sits relative to the other three, from data already recorded in this
file and in Section 24's lineage note: the observed destruction score `C_obs`
stayed *below* `1/2` in all 186 measured transitions (see "Finite Full-Window
Evidence" above -- maximum `C_obs=21/44`), and the lineage `E_q` was positive
at all 24 measured layers. Both point the same way: so far, the empirical
line has tracked *above* `N_random` and *below* `N_friendly` at every point
checked -- closer to the friendly end of the axis than the random one, but
never touching the friendly ceiling itself. It has never approached
`N_adversarial`. This is a finite, checked observation, not a proved bound;
the next transition beyond `~19000` could in principle land anywhere the
proved `N_adversarial` floor still permits.

### Mixtures between the anchors

`C_p(f)` is a strictly increasing bijection on `[0,1]`, so any intermediate
score `s` has a unique inverse `f(s,r)` at filter `r` (with `d_p=2/r`):

```math
f(s,r)=
\begin{cases}
2s\,d_p, & 0\le s\le\tfrac12,\\[4pt]
d_p+(1-d_p)(2s-1), & \tfrac12\le s\le1.
\end{cases}
```

so `N_s(Q)=N_0\prod_{p_0<r\le Q}(1-f(s,r))`. Two concrete cases:

- **Half random, half adversarial** (`s=3/4`): `f(r) = 1/2 + 1/r`.
- **Half friendly, half random** (`s=1/4`): `f(r) = 1/r`.

### Status

Every line in this section is a projection under a stated per-step
assumption, not a theorem about the real sequence -- `N_friendly` and
`N_random` are unproved-in-general models (see Section 24's discrepancy
caveat), while `N_adversarial` alone is a genuine proved worst-case bound,
inherited unchanged from the capacity section above. The gap between what is
proved (`N_adversarial` never falls below the real count) and what is
observed (real counts have run above `N_random` in every measured case so
far, per Section 24's lineage-experiment note) is exactly the same open
question tracked throughout this file and in
`candidates/local-surplus.md` / `candidates/short-window-discrepancy.md` --
this section only gives it three comparable curves instead of one.

### Built and computed

This is no longer only a formula. `empirical/sieve-sequence/src/sieve_sequence_empirical/four_lines.py`
implements all three projections and `four_lines_cli.py` anchors them at a
real layer of an existing lineage chain, writing
`data/candidates/four-lines-Q101.csv`;
`presentations/sieve-sequence-visualization/figures/four_lines_chart.py`
plots all four together (`out/four-lines-Q101.svg`). Tests are in
`empirical/sieve-sequence/tests/test_four_lines.py`.

Run at `Q=101` anchored at layer 7 (`r=23`, `N_0=361`, the point where `2/r`
first drops under `10%` -- see Section 24's crossover note): `N_adversarial`
reaches exactly `0` at `r=67` and stays there, `N_friendly` stays flat at
`361`, and the real trajectory (`N_empirical_post`) ends at `202`, comfortably
between the two and never close to either. `N_random` tracks close to the
real trajectory throughout and, notably, is *not* strictly below it here: at
`r=29` (the layer immediately after the anchor) `N_random≈336.1` briefly
exceeds the real `334` before falling back under it for the rest of the
chain. This differs from the always-below-`1/2` pattern in "Finite
Full-Window Evidence" above because that comparison re-derives the density
from the very first filter each time, while this one starts fresh from a
mid-chain anchor -- a reminder that "the real line stays above random" is an
observed pattern for one specific comparison, not a property guaranteed to
survive re-anchoring.

### `N_random` here is not the same model as the provable conditional

**Correction:** an earlier version of this note claimed `N_random(Q)`,
extended to `Q\to\infty`, provably goes to `0`. That claim was wrong --
not imprecise, wrong -- and the error is worth recording rather than quietly
fixing, since it is an easy one to make again.

`N_random(Q)` is anchored at one real, fixed window (`Q=101` in
`data/candidates/four-lines-Q101.csv`), compounding through the filters
`r` below that same `Q`. By the certification theorem
([safe-window-two-gaps-certify-twin-primes.md](safe-window-two-gaps-certify-twin-primes.md)),
once every filter below `Q` is installed, that window is *done*: anything
still alive is permanently prime, immune to every later filter forever.
There is no physically meaningful way to "keep applying more filters" to
this same window past that point -- the process terminates, at a specific,
final, computable number. Extending the formula `\prod(1-2/r)` to primes far
beyond `Q` (as the earlier version of this note did) does not model
"the same cohort facing more filters"; it computes an abstract number with
no corresponding physical continuation of this window's process. That is a
category error, not a subtlety.

Within its actual, physically meaningful range -- `r` from the anchor up to
the last prime below `Q=101` -- `N_random` never reaches `0`. Checked
directly against `data/candidates/four-lines-Q101.csv`: it ends at
`\approx194`, comfortably positive, same as the friendly and empirical
lines. Only `N_adversarial` reaches `0` within this chart's own range.

**The question "does a random-behaving filter survive forever" is real, but
needs a different, correctly-scoped model to ask it, not an extension of
this chart's anchored line past its own certification boundary.** Two
distinct, correctly-scoped versions of that question exist:

- **Larger windows, not more filters on one window:** the *growing*-window
  prediction `main_term(Q)=|W_Q|\delta_Q`, which diverges to infinity because
  `|W_Q|\sim Q^2` outruns the shrinking density, as `Q` itself increases --
  see [short-window-discrepancy.md's "Big Picture" section](../../candidates/short-window-discrepancy.md#big-picture-what-the-filter-behaves-as-random-would-prove).
  This is a different chart entirely (x-axis `Q`, not `r`), not yet built.
- **A genuinely randomized filter, replacing the deterministic one outright:**
  keep the same proved structural growth (each element copied `r` times per
  installed filter, exactly 2 of the `r` copies destroyed) but replace the
  deterministic residue-class choice of *which* two die with a uniformly
  random choice. See
  [Balanced randomized 2-gap companion process](../../candidates/balanced-randomized-2-gap-companion-process.md)
  for the precise setup: global survival is deterministic and certain under
  this model, and safe-window / head persistence are proved conditional on
  a spatial-uniformity premise via the Borel-Cantelli lemmas. Its sibling,
  [the balanced adversarial 2-gap companion](../../candidates/balanced-adversarial-2-gap-companion-process.md),
  shares the identical proved global growth but chooses which two copies
  die to *maximize* local damage instead, proving unconditionally that the
  same global divergence is compatible with the head never landing on a
  2-gap again -- demonstrating that population size alone settles nothing
  about position, in either direction.

Do not read the anchored `N_random` line in this file as evidence about
either of those -- it answers "does thinning alone eventually win with no
replenishment, within one already-fixed window," which is a real and
correctly-answered question (no, not within this window's own range), just
not the same question as "does the real sequence keep producing new twin
primes forever."

## Related

- [Random-like merge survival](../../candidates/random-like-merge-survival.md)
- [Local surplus](../../candidates/local-surplus.md)
- [Short-window discrepancy](../../candidates/short-window-discrepancy.md)
- [Balanced randomized 2-gap companion process](../../candidates/balanced-randomized-2-gap-companion-process.md)
- [Balanced adversarial 2-gap companion process](../../candidates/balanced-adversarial-2-gap-companion-process.md)
- [Incremental danger-annulus decomposition](incremental-danger-annulus-decomposition.md)
- [Safe-window 2-gaps certify twin primes](safe-window-two-gaps-certify-twin-primes.md)
- [Exact accepted local filter strikes](exact-accepted-local-filter-strikes.md)
- [2-gap isolation after filter 3](two-gap-isolation-after-filter-three.md)
