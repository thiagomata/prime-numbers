# Randomized-Filter Branching Survival

**Candidate hypothesis:** Unproved.

**Conditional implication:** Not yet proved (partial bound established below).

**Empirical status:** Not yet measured (no simulation run).

## Candidate Hypothesis

Fix an initial population `N_0 >= 1` (a count of 2-gaps). Define a randomized
process, using the same structural growth step the real sieve provably has
(`exact-global-two-gap-count.md`, `exact-global-two-gap-cluster-count.md`),
but replacing the real filter's deterministic residue-class removal with an
independent random one:

At each step, for the next prime `r`:

1. **Copy** (structural, deterministic, exactly as in the real sieve): every
   currently-alive element produces `r` copies.
2. **Remove at random** (this is the change from the real sieve): each of
   those copies independently survives with probability `1-2/r`, instead of
   the deterministic rule "exactly 2 of the `r` copies die, determined by
   residue class."

Equivalently: if the population right before installing `r` is `N`, the
population right after is `Binomial(N*r, 1-2/r)`.

**Hypothesis:** this process survives forever (population never hits `0`)
with probability `1`, for any finite `N_0 >= 1`.

## Why The Mean Alone Does Not Settle It

The expected population after installing `r` is exactly
`N*r*(1-2/r) = N*(r-2)` -- identical to the proven deterministic recurrence
`G_2(p) = prod(r-2)` (`exact-global-two-gap-count.md`), which diverges to
infinity. But a diverging mean does not by itself rule out extinction: the
randomized version has variance the deterministic version does not, so the
mean growing forever is necessary but not sufficient for "survives with
probability 1."

## What Is Established

Let `N` be the population right before installing `r`. Because survivors
are `Binomial(N*r, 1-2/r)`, the probability of *total* wipeout at this one
step is exact:

```math
P(\text{wiped out at this step} \mid N) = \left(\frac2r\right)^{Nr}.
```

This is a real, computable bound, not an estimate. For `N` and `r` both of
realistic size (e.g. `N=361, r=23`, matching the anchor used in
`data/candidates/four-lines-Q101.csv`), `(2/23)^(361*23)` is not merely
small, it is astronomically small -- and it shrinks faster than exponentially
in *both* `N` and `r`, so it collapses even faster as the population grows
(which, in expectation, it does at every step, by at least a factor of `3`).

A union bound over all future steps,

```math
P(\text{ever wiped out}) \le \sum_k \left(\frac{2}{r_k}\right)^{N_{k-1} r_k},
```

is very plausibly a convergent, tiny sum given how fast the terms collapse
once `N` leaves the single digits (which happens almost immediately in
practice -- see the real data in `data/candidates/lineage-Q101.csv`, already
in the thousands after the first couple of layers). This supports "survives
with probability very close to `1`."

## What Remains Open

The union bound above gives "probability close to 1," not the stronger
"probability exactly 1" the hypothesis claims. Closing that gap needs one of:

1. A rigorous summability argument (the sum above is genuinely finite, so a
   Borel-Cantelli-style argument applies cleanly across infinitely many
   steps despite `N_{k-1}` itself being random, not fixed); or
2. Direct application of an established theorem for branching processes in
   varying environments with offspring means diverging to infinity (this is
   a well-studied class, e.g. Jirina- or Church-type extinction criteria for
   time-inhomogeneous Galton-Watson processes -- the applicable exact
   criterion has not yet been located and verified against this specific
   process here); or
3. A direct Monte Carlo simulation using the real sequence of primes, as a
   strong empirical read while (1) or (2) is worked out analytically.

None of these has been done yet. This file records the open bound, not a
completed proof.

## Relation To Other Candidates

This is a different question from
[Short-window discrepancy](short-window-discrepancy.md): that candidate asks
whether the *real, deterministic* filter's behavior tracks a random-model
prediction closely enough (the discrepancy `E_Q`) to force survival in one
specific fixed window. This candidate instead asks about a genuinely
*randomized* process (replacing the deterministic filter outright), with no
fixed window at all -- it is a question about the random model's own internal
consistency, not about whether reality matches it. A positive resolution
here would not by itself prove anything about the real sieve; it would
establish that "behaves randomly" is at least an internally coherent
scenario in which 2-gaps provably never run out, sharpening exactly what the
open half of `short-window-discrepancy.md`'s conditional is being compared
against.

## Related

- [Short-window discrepancy](short-window-discrepancy.md)
- [Local surplus](local-surplus.md)
- [Exact global 2-gap count](../properties/sieve-sequence/exact-global-two-gap-count.md)
- [Realized filter adversariality score](../properties/sieve-sequence/realized-filter-adversariality-score.md)
