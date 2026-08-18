# Balanced Randomized 2-Gap Companion Process

**Candidate hypothesis:** Unproved (the spatial-uniformity/mixing premise
below is the open piece).

**Conditional implication:** Mathematically proved, in two parts of
different strength (see "What Is Proved" below).

**Empirical status:** Not yet measured (no simulation run).

## Revision Note

An earlier version of this file used a per-copy independent-Bernoulli
offspring model (each of the `r` copies survives independently with
probability `1-2/r`), which allows a single parent to be wiped out entirely
by chance and only supported a loose union-bound argument. It was replaced
with "exactly 2 of `r` copies die per parent, chosen at random," which
mirrors the real sieve's exact structural guarantee and admits a rigorous
Borel-Cantelli treatment. This revision formalizes that model precisely and
names it: not a "random sieve" (too vague -- randomizes everything) and not
a "randomized integer sequence" (too vague the other way -- doesn't specify
what stays fixed). It is a **constrained stochastic companion to the real
sieve**, designed specifically to preserve the real sieve's known 2-gap
reproduction mechanics and randomize only the one part that is otherwise
governed by residue arithmetic.

## Definition

Let `\mathcal G_k` be the collection of 2-gap descendants at layer `k`. When
the next filter prime is `r`, each `g \in \mathcal G_k`:

1. Produces `r` indexed copies: `(g,0),(g,1),\ldots,(g,r-1)`.
2. Chooses a uniformly random two-element subset
   `K_{g,r} \subseteq \{0,\ldots,r-1\}`, `|K_{g,r}|=2`.
3. Removes the two copies indexed by `K_{g,r}`.

Thus

```math
\mathcal G_{k+1} = \bigcup_{g\in\mathcal G_k} \{(g,j) : j \notin K_{g,r}\},
```

and every parent has exactly `r-2` children:

```math
|\mathcal G_{k+1}| = (r-2)|\mathcal G_k|.
```

## What Was Randomized

In the real sieve, the harmful pair is determined by modular arithmetic. For
a 2-gap `(a,a+2)`, the two killed copy indices have the exact form (proved
in `properties/sieve-sequence/copy-index-filter-frequency.md`):

```math
K^{\mathrm{real}}_{g,r} = \{-aM^{-1},\ -(a+2)M^{-1}\} \pmod r.
```

This companion process replaces that deterministic pair with

```math
K^{\mathrm{random}}_{g,r} \sim \operatorname{Uniform}\binom{\mathbb Z/r\mathbb Z}{2}.
```

Only the *locations* of the two casualties are randomized. Their *number* is
not -- that is fixed at exactly 2, matching the real sieve exactly.

## What It Preserves

- The real sequence of filter primes.
- The `r`-fold expansion at filter `r`.
- Exactly two harmful copies per old 2-gap.
- Exactly `r-2` surviving descendants.
- Lineage across filters.
- Copy coordinates, if the simulation tracks them.
- The exact global 2-gap recurrence (`exact-global-two-gap-count.md`).

## What It Does Not Preserve

- A coherent sequence of surviving integers.
- CRT correlations between different 2-gaps.
- The fact that one removed integer can affect several surrounding gaps.
- Gap merging and the evolution of non-2 gaps.
- The deterministic relationship between residue and killed copy index.

## Formal Classification

> A branching spatial point process in a deterministic varying environment,
> with fixed offspring number and randomized harmful-copy indices.

In plainer project language:

> The balanced randomized 2-gap companion keeps the sieve's exact 2-gap
> reproduction law but replaces the modular selection of the two destroyed
> descendants with uniform selection without replacement.

Its role is as a **null model**: not a claim about the real sieve, but a
reference point that reveals what local and head survival would look like
if the real filter's difficult positional arithmetic behaved like balanced
random selection instead. The gap between this null model and the real
sieve is exactly the "CRT correlations between different 2-gaps" item in
"What It Does Not Preserve" above.

## Global Persistence Is Immediate, Not Probabilistic

Because exactly two of every parent's `r` copies die -- never more, never
fewer, regardless of which two -- the total population obeys

```math
N_{k+1} = (r_k - 2) N_k,
\qquad
N(Q) = N_0 \prod_{p_0 < r < Q} (r-2),
```

identical to the proved deterministic recurrence in
`exact-global-two-gap-count.md`. Every factor is positive for `r>=5`, so
global extinction is impossible by construction -- this needs no probability
theory at all. The interesting question is not whether the *count* survives
(it provably does, trivially), but whether the *positions* of survivors
behave well enough to guarantee a 2-gap keeps landing where it is needed.

### Why This Model Choice Matters: Extinction Cannot Confound The Experiment

Contrast with the discarded independent-Bernoulli model (`N_{k+1}\mid N_k
\sim \operatorname{Binomial}(r_kN_k,\,1-2/r_k)`): there, every finite
population has a nonzero probability `(2/r_k)^{r_kN_k}` of total elimination
at the very next step, so `0 < \Pr(\text{global survival forever}) < 1` --
global extinction is a real, if extremely unlikely, possible outcome.

| Model | Global 2-gap survival |
|---|---|
| Independent random deletion (discarded) | Very likely, but `<100%` |
| Balanced exact-two deletion (this file) | Exactly `100%` |
| Safe-window / head survival, either model | Still requires spatial analysis |

This is precisely why the balanced model is the right choice here, not just
a simpler one: with global survival exactly `100%` by construction, any
future failure to reproduce safe-window or head persistence in this model
*cannot* be blamed on population extinction -- it can only come from the
survivors' spatial distribution. The independent-Bernoulli model could not
offer that isolation, since a null result there might mean "the spatial
distribution failed" or might just mean "this particular run got unlucky
and the whole population died" -- two different explanations the model
cannot distinguish. The balanced model removes that confound entirely,
leaving the positional questions below as the *only* thing left to prove.

What is proved so far is only:

> At least one 2-gap exists somewhere in the complete period at every layer.

Not yet proved: a 2-gap survives in every square-safe window; a 2-gap
reaches the head infinitely often; this companion process produces a
genuine analogue of infinitely many twin primes. Those are exactly the
positional questions taken up next.

## Safe-Window Persistence (Borel-Cantelli I -- no independence required)

Let `M(Q) = M_0 \prod_{p_0<r<Q} r` be the period, `L_Q \approx Q^2-Q` the
square-safe window length, and `\delta_Q = N(Q)/M(Q)` the global 2-gap
density. As established in `properties/sieve-sequence/realized-filter-adversariality-score.md`
and `python/src/sieve_sequence/spacing.py`:

```math
\delta_Q = \delta_0 \prod_{p_0<r<Q}\left(1-\frac2r\right) \asymp \frac{C}{(\log Q)^2}.
```

**Additional premise for this section (not yet proved -- see "What Remains
Open"):** the `N(Q)` surviving starts are distributed as a uniformly random
size-`N(Q)` subset of the `M(Q)` possible positions.

Under that premise, the expected count in the safe window is

```math
\lambda_Q = L_Q \delta_Q \asymp C\frac{Q^2}{(\log Q)^2} \to \infty,
```

confirmed numerically to grow explosively (`\lambda_{101}\approx193`,
`\lambda_{100003}\approx3.1\times10^7`, matching
`short-window-discrepancy.md`'s `main_term`). The exact probability the
window is empty, sampling `N(Q)` positions without replacement from `M(Q)`,
is hypergeometric:

```math
\Pr(X_Q=0) = \frac{\binom{M(Q)-L_Q}{N(Q)}}{\binom{M(Q)}{N(Q)}}
\le \left(1-\frac{L_Q}{M(Q)}\right)^{N(Q)}
\le e^{-\lambda_Q}
```

(the middle inequality is the standard hypergeometric tail bound -- each of
the `N(Q)` factors in the ratio is `\le 1-L_Q/M(Q)`; the last uses
`1-x\le e^{-x}`. Verified numerically, e.g. `M=1000,L=50,N=40`: exact
`0.1232 \le` bound `0.1285 \le e^{-\lambda}` `0.1353`.) Since `\lambda_Q`
grows like `Q^2/(\log Q)^2`, `e^{-\lambda_Q}` collapses far faster than any
polynomial, so

```math
\sum_{Q\text{ prime}} \Pr(X_Q=0) < \infty.
```

**By the first Borel-Cantelli lemma -- which needs no independence
assumption at all, only this convergent sum -- almost surely only finitely
many safe windows are empty.** So, under the uniform-position premise, with
probability `1`, every *sufficiently large* square-safe window contains a
2-gap, not merely infinitely many of them.

## Head-Event Persistence (Borel-Cantelli II -- independence required)

A stronger, different question: does one *specific distinguished* location
(the head) land on a 2-gap infinitely often? Under the same uniform-position
premise, `\Pr(\text{head is a 2-gap at stage }Q) = \delta_Q \asymp C/(\log Q)^2`.
Unlike the safe-window case, the relevant sum **diverges**:

```math
\sum_{Q\text{ prime}} \frac{1}{(\log Q)^2} = \infty
```

(confirmed numerically: partial sums `9.2` at `Q\sim1000`, `97.7` at
`Q\sim10^5`, still climbing -- matches the classical `\sim x/(\log x)^3`
growth from partial summation against `\pi(x)\sim x/\log x`, a divergent
rate). **If** head-events at successive layers are independent, or
sufficiently weakly dependent, the *second* Borel-Cantelli lemma applies --
and second Borel-Cantelli genuinely needs that independence, unlike the
first -- giving `\Pr(\text{head is a 2-gap infinitely often}) = 1`.

## What Is Proved, Precisely

- Global count survives forever: **proved unconditionally**, under this
  companion process, no premise needed.
- Every sufficiently large safe window contains a 2-gap: **proved
  conditional** on the uniform-random-position premise (needs no
  independence beyond that -- Borel-Cantelli I is premise-light).
- The head lands on a 2-gap infinitely often: **proved conditional** on the
  uniform-random-position premise *and* independence (or adequate weak
  mixing) between layers -- a strictly stronger requirement than the
  safe-window case.

**Why the uniform-position premise is doing real work, not being cautious
for its own sake:** see
[the balanced adversarial 2-gap companion](balanced-adversarial-2-gap-companion-process.md),
a sibling process sharing the exact same proved global recurrence
`N(Q)=N_0\prod(r-2)`, that instead chooses which two copies die to
*maximize* local damage. It proves, unconditionally, that the global count
can diverge to infinity while the head is deliberately kept 2-gap-free
forever. So the positive conclusions in this file are not automatic
consequences of unbounded growth -- they depend entirely on the
uniform-position premise being true, which a companion sharing the identical
growth law but a different placement rule shows is not guaranteed by growth
alone.

## What Remains Open

"Destroy exactly two copies per parent, chosen uniformly at random" does
not, by itself, establish that the resulting set of survivor positions is a
uniformly random subset of `M(Q)`, nor that head-events across layers are
independent or weakly mixing enough for Borel-Cantelli II. Precisely: this
process randomizes `K_{g,r}` *independently within each parent `g`*, but
says nothing about correlations *across different parents* -- exactly the
"CRT correlations between different 2-gaps" item under "What It Does Not
Preserve" above. This is the same underlying difficulty as everywhere else
in this program -- compare `short-window-discrepancy.md`'s open discrepancy
bound and `local-surplus.md`'s missing local-abundance proof -- just
relocated: instead of asking whether the *real, deterministic* filter's
survivors happen to be equidistributed, this asks whether *this specific
companion process* actually produces the needed spatial uniformity across
parents, or whether the underlying CRT/copy-index structure would introduce
correlations even if it were run for real. Two next steps, neither done yet:

1. Prove (or disprove) that this process's survivor positions satisfy the
   uniform-subset premise, from the actual copy-index mechanics (the same
   residue-class machinery already exact in
   `properties/sieve-sequence/copy-index-filter-frequency.md`), rather than
   assuming it.
2. Monte Carlo simulate this exact process (deterministic count, random
   position within each parent's `r` copies) against the real sequence of
   primes, as an empirical check while (1) is worked out analytically.

## Relation To Other Candidates

Different from [Short-window discrepancy](short-window-discrepancy.md): that
candidate asks whether the *real, deterministic* filter's behavior tracks a
random-model prediction closely enough to force survival in one specific
fixed window. This candidate asks about a genuinely randomized companion
process (replacing the deterministic filter outright, but faithfully
preserving its exact structural growth and exact per-parent casualty count),
with a much sharper, largely-resolved answer given the uniform-position
premise -- narrowing "does the random model survive forever" down to one
precisely stated open premise (cross-parent correlation), rather than
leaving the whole question open.

## Related

- [Balanced adversarial 2-gap companion process](balanced-adversarial-2-gap-companion-process.md)
- [Short-window discrepancy](short-window-discrepancy.md)
- [Local surplus](local-surplus.md)
- [Exact global 2-gap count](../properties/sieve-sequence/exact-global-two-gap-count.md)
- [Copy-index filter frequency](../properties/sieve-sequence/copy-index-filter-frequency.md)
- [Realized filter adversariality score](../properties/sieve-sequence/realized-filter-adversariality-score.md)
