# Randomized-Filter Branching Survival

**Candidate hypothesis:** Unproved (the spatial-uniformity/mixing premise
below is the open piece).

**Conditional implication:** Mathematically proved, in two parts of
different strength (see "What Is Proved" below).

**Empirical status:** Not yet measured (no simulation run).

## Revision Note

An earlier version of this file used a per-copy independent-Bernoulli
offspring model (each of the `r` copies survives independently with
probability `1-2/r`), which allows a single parent to be wiped out entirely
by chance and only supported a loose union-bound argument. The model below
replaces it with a cleaner, more faithful one -- "exactly 2 of the `r`
copies die, chosen at random" -- that mirrors the real sieve's *exact*
structural guarantee precisely (only the *position* of the destruction is
randomized, not the count), and admits a genuinely rigorous treatment via
the Borel-Cantelli lemmas. This is a strictly better setup; the rest of this
file uses it exclusively.

## The Model

Fix an initial population `N_0 >= 1`. At each step, for the next prime `r`:

1. **Copy** (structural, exactly as the real sieve proves --
   `exact-global-two-gap-count.md`, `exact-global-two-gap-cluster-count.md`):
   every currently-alive 2-gap produces `r` copies.
2. **Destroy exactly two, chosen uniformly at random** (this is the one
   change from the real sieve, which instead determines the two via residue
   class): of each parent's `r` copies, exactly two are destroyed, chosen
   uniformly at random from that parent's own `r` copies, independently
   across parents.

## Global Persistence Is Immediate, Not Probabilistic

Because *exactly* two of every parent's `r` copies die -- never more, never
fewer, regardless of which two -- every parent has *exactly* `r-2`
surviving children, deterministically. So the total population obeys

```math
N_{k+1} = (r_k - 2) N_k,
\qquad
N(Q) = N_0 \prod_{p_0 < r < Q} (r-2),
```

identical to the proved deterministic recurrence in
`exact-global-two-gap-count.md`. Every factor is positive for `r>=5`, so
global extinction is impossible by construction -- this needs no probability
theory at all under this model. The interesting question is not whether the
*count* survives (it provably does, trivially), but whether the *positions*
of survivors behave well enough to guarantee a 2-gap keeps landing where it
is needed.

## Safe-Window Persistence (Borel-Cantelli I -- no independence required)

Let `M(Q) = M_0 \prod_{p_0<r<Q} r` be the period, `L_Q \approx Q^2-Q` the
square-safe window length, and `\delta_Q = N(Q)/M(Q)` the global 2-gap
density. As established in `properties/sieve-sequence/realized-filter-adversariality-score.md`
and `empirical/sieve-sequence/src/sieve_sequence_empirical/spacing.py`:

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
  randomized-position model, no premise needed.
- Every sufficiently large safe window contains a 2-gap: **proved
  conditional** on the uniform-random-position premise (needs no
  independence beyond that -- Borel-Cantelli I is premise-light).
- The head lands on a 2-gap infinitely often: **proved conditional** on the
  uniform-random-position premise *and* independence (or adequate weak
  mixing) between layers -- a strictly stronger requirement than the
  safe-window case.

## What Remains Open

"Destroy exactly two copies per parent, chosen uniformly at random" does
not, by itself, establish that the resulting set of survivor positions is a
uniformly random subset of `M(Q)`, nor that head-events across layers are
independent or weakly mixing enough for Borel-Cantelli II. This is the same
underlying difficulty as everywhere else in this program -- compare
`short-window-discrepancy.md`'s open discrepancy bound and
`local-surplus.md`'s missing local-abundance proof -- just relocated: instead
of asking whether the *real, deterministic* filter's survivors happen to be
equidistributed, this asks whether *this specific random model* (random
choice of which two copies die, not fully independent per-copy coin flips)
actually produces the needed spatial uniformity, or whether the underlying
CRT/copy-index structure introduces correlations that break it. Two next
steps, neither done yet:

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
fixed window. This candidate asks about a genuinely *randomized* process
(replacing the deterministic filter outright, but faithfully preserving its
exact structural growth), with a much sharper, largely-resolved answer given
the uniform-position premise -- narrowing "does the random model survive
forever" down to one precisely stated open premise, rather than leaving the
whole question open.

## Related

- [Short-window discrepancy](short-window-discrepancy.md)
- [Local surplus](local-surplus.md)
- [Exact global 2-gap count](../properties/sieve-sequence/exact-global-two-gap-count.md)
- [Realized filter adversariality score](../properties/sieve-sequence/realized-filter-adversariality-score.md)
