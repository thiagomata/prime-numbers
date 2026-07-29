# Chen-Type Almost-Prime Survivor

> **READ ME FIRST — this candidate is a DIFFERENT KIND OF TARGET.**
>
> Every other note in `candidates/` is a *sufficient condition for square-safe
> 2-gap survival*: a hypothesis whose proved implication yields a genuine
> twin-prime pair `(p, p+2)` with both endpoints certified prime. Every such
> condition that has been pushed converges to the same twin-prime-strength
> short-window positivity wall (see `properties/sieve-sequence/research/
> recent-prime-producing-sieves-deep-dive.md` and the negative-results
> properties `black-box-large-sieve-does-not-fit-weighted-collision-budget`,
> `pointwise-two-class-margin-does-not-imply-collision-budget`,
> `one-layer-harmful-ellipses-do-not-compose`).
>
> **This candidate is not that.** It deliberately *weakens the conclusion*:
> instead of requiring both `p` and `p+2` to be prime (a 2-gap), it requires
> only that `p` be a certified-prime survivor and that `p+2` have **at most
> two prime factors** (prime, or a product of two primes). It therefore does
> **not** force a 2-gap and does **not** certify a twin-prime pair. It is a
> fallback *prime-producing milestone*, weaker than twin primes but stronger
> than "the sieve weights have positive complete-period density." It belongs
> here because it shares the survivor/cofactor machinery of the other
> candidates and is the natural next target if the twin-prime wall is absolute.
>
> The candidate catalog is otherwise complete for *2-gap* conditions; this
> entry is the one relaxation of the *goal*.

**Candidate hypothesis:** Unproved and potentially false.

**Conditional implication:** Mathematically proved (a certified-prime `p` with
`p+2` an almost-prime is a Chen-type pair; the implication is "this count is
positive at infinitely many heads").

**Empirical status:** NOT EVALUATED — this is a target/milestone candidate
derived from the analytic deep-dive, not from an empirical sweep. No new data
collection is proposed.

## Scope and Expectation

- **What this is:** a research milestone, not a 2-gap sufficient condition.
  Success means the sieve-sequence weights provably support *some* genuine
  prime production (a prime `p` whose `p+2` is prime-or-semiprime), which
  would be the project's first positive prime-producing result.
- **What this is not:** a twin-prime theorem. A successful proof does not
  certify any twin-prime pair, because `p+2` is allowed to be a semiprime.
  Do not read a positive result here as progress toward twin primes by
  itself — it is progress toward *almost-prime* production.
- **Why it may be reachable when twin primes are not:** Chen's theorem (1966,
  classical) proves infinitely many primes `p` have `p+2` with at most two
  prime factors, *without* solving twin primes. The mechanism is that bounding
  the number of prime factors of `p+2` is an *upper*-bound problem on
  factorization depth, which does not face the parity barrier in the same way
  a *lower* bound on twin-prime pairs does. The property
  `two-class-survival-from-collision-energy` notes exactly this asymmetry:
  "Upper bounds do not face the parity problem in exactly the same way as
  positive lower bounds."
- **Relationship to the deep-dive:** this is the realization of Stage 5 of
  `recent-prime-producing-sieves-deep-dive.md` ("target an almost-perfect
  scenario first"), restated as a candidate so it has a home in the catalog.

## Setup

Fix a future prime head `Q`. A square-safe survivor is an integer

```math
p\in W_Q=[Q,Q^2)
```

that is coprime to every prime below `Q`. By the safe-window certification
([safe-window-two-gaps-certify-twin-primes](../properties/sieve-sequence/safe-window-two-gaps-certify-twin-primes.md)),
such a `p` is **prime**. The twin-prime target additionally requires `p+2` to
be prime. The Chen-type target relaxes this to:

```math
\Omega(p+2)\le 2,
```

where `\Omega(n)` counts prime factors with multiplicity. Equivalently, `p+2`
is either prime or the product of two primes (a semiprime).

## Candidate Hypothesis

For infinitely many prime heads `Q`, there exists a certified-prime survivor
`p\in[Q,Q^2)` such that `p+2` has at most two prime factors.

A stronger, stage-parameterized form (matching the deep-dive's ladder) is:

```math
\forall\,\alpha>1/3,\quad
\text{the relaxed weight } A_{q,z}(n)=\mathbf 1_{\gcd(n(n+2),P(z))=1}
\text{ with } z=X^\alpha,\ X=q^2,
```

detects a prime `n=p` with `\Omega(p+2)\le 2` for infinitely many `q`.

## Why The Relaxation Escapes The Twin-Prime Wall

The wall every 2-gap candidate hits is a *lower* bound on twin-prime-pair
counts in `[Q,Q^2)` — parity-strength, requiring Type II cancellation that
does not exist for the affine pair `(x, x+2)`. This candidate does not need a
lower bound on prime *pairs*. It needs:

1. a survivor `p` (certified prime — already the easy side, established by
   the survivor machinery); and
2. an *upper* bound on the prime-factor count of `p+2`.

Requirement (2) is an upper-bound-sieve problem on factorization depth.
Classical Chen theory and its modern descendants handle exactly this with
linear-sieve + bilinear estimates that are known to escape the parity barrier
at the almost-prime level. The project's existing four-point correlation
machinery (`two-class-survival-from-collision-energy`,
`fourier-two-gap-correlation-prefix-bound`) is upper-bound machinery and is
therefore of the right type for this target, even though it could not
certify the (lower-bound) twin-prime target.

## Conditional Implication (proved)

If the candidate holds, then for infinitely many `Q` there exists a prime
`p\in[Q,Q^2)` with `\Omega(p+2)\le 2`. This is a Chen-type pair. It is not a
twin-prime pair unless `p+2` happens to be prime, which the candidate does not
require.

The implication "candidate holds `=>` infinitely many Chen-type pairs" is
immediate from the definitions; no additional theorem is needed.

## Proof Target And Open Estimate

Concretely, the target is to prove, for some `\alpha>1/3` and infinitely many
`q`,

```math
\sum_{\substack{n\in[Q,Q^2)\\ n\text{ prime}\\ \Omega(n+2)\le 2}}
A_{q,z}(n)
>0,
\qquad z=Q^{2\alpha}.
```

This is a Type-I-plus-bilinear problem in the sense of the deep-dive, but at
the almost-prime level where parity is not a barrier. The open estimate is a
short-interval almost-prime lower bound for the sieve-sequence weights —
strictly weaker than the twin-prime lower bound every other candidate needs,
and with a classical precedent (Chen, 1966) suggesting it is tractable.

A minimal first milestone, weaker than the full candidate: prove that for
infinitely many `Q` the relaxed weight detects *some* prime `p` with
`\Omega(p+2)\le C` for a constant `C>2`. This would already validate that the
weights support genuine prime production.

## Limitation

- The candidate is unproved. Stating it does not advance the proof; it
  identifies the target.
- It is strictly weaker than the twin-prime goal. A successful proof would be
  the project's first prime-producing result, but it would not resolve the
  twin-prime conjecture or any 2-gap candidate.
- It is possible that even the almost-prime target is out of reach for the
  sieve-sequence weights specifically, in which case the candidate fails as a
  fallback. That failure would itself be informative: it would say the
  weights cannot support prime production even at Chen-type strength, a much
  sharper negative result than the current "cannot reach twin-prime strength."

## Established Inputs

- [Square-safe certification](../properties/sieve-sequence/safe-window-two-gaps-certify-twin-primes.md)
  — supplies "survivor in `[Q,Q^2)` is prime."
- [Two-class survival from residue collision energy](
  ../properties/sieve-sequence/two-class-survival-from-collision-energy.md)
  — supplies the upper-bound / four-point-correlation machinery of the right
  type for an almost-prime target, and the asymmetry observation motivating
  this candidate.
- [Stage 5 of the prime-producing-sieves deep-dive](
  ../properties/sieve-sequence/research/recent-prime-producing-sieves-deep-dive.md)
  — the source of the `z=X^\alpha`, `\alpha>1/3` ladder.

## Relation To Other Candidates

- **All 2-gap candidates (#1-#24):** these force a twin-prime pair and all
  converge to the parity wall. This candidate does not force a 2-gap and is
  not subject to the same wall. It is the natural next target if the wall is
  absolute.
- **#14 (hereditary shot-spacing) and #19 (sixfold harmful-residue capacity):**
  supply survivor-population machinery that may be reusable here for the `p`
  side, even though the `p+2` side is handled differently (factorization
  depth, not pair certification).
- **The terminal-scalar candidates #21/#24:** their weighted-energy machinery
  is upper-bound in flavor and may transfer more naturally to this almost-
  prime target than to the twin-prime one.

## Success and Failure Criteria

- **Success:** a proved lower bound on Chen-type pairs produced by the
  sieve-sequence weights, for infinitely many heads. Validates prime
  production.
- **Partial success:** the same for `\Omega(p+2)\le C`, `C>2` constant.
- **Failure:** a proof that the weights cannot produce Chen-type pairs
  infinitely often — a sharp negative boundary on the program.
