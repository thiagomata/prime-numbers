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

**Existence status:** Externally established by Chen's theorem together with
Bertrand's postulate; it is not an open existence conjecture of this project.

**Project-specific candidate hypothesis:** Unproved and potentially false for
the sieve-sequence/relaxed-weight mechanism stated below.

**Conditional implication:** Mathematically proved (positivity of the stated
relaxed weight gives a certified-prime `p` with `p+2` an almost-prime).

**Empirical status:** NOT EVALUATED — this is a target/milestone candidate
derived from the analytic deep-dive, not from an empirical sweep. No new data
collection is proposed.

## Scope and Expectation

- **What this is:** a research milestone, not a 2-gap sufficient condition.
  Success means the sieve-sequence weights themselves prove positive
  production of a prime `p` whose `p+2` is prime-or-semiprime. The objects are
  already known to exist by Chen's theorem; the open contribution is deriving
  them from this project's mechanism.
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

## Externally Established Existence Statement

For infinitely many prime heads `Q`, there exists a certified-prime survivor
`p\in[Q,Q^2)` such that `p+2` has at most two prime factors.

This follows from classical results. Chen's theorem supplies infinitely many
primes `p` for which `Omega(p+2)<=2`. For each sufficiently large such `p`,
Bertrand's postulate supplies a prime

```math
\sqrt p<Q<2\lceil\sqrt p\rceil<p.
```

Consequently `p\in[Q,Q^2)`. Because `p` is prime, it survives every filter
below `Q`. Hence bare existence is not the open candidate.

## Project-Specific Candidate Hypothesis

Let `S_Q` be the integers in `[Q,Q^2)` surviving every prime filter below `Q`,
and let `P(z)` be the product of the primes below `z`. The open candidate is
that there exists a fixed `\alpha>1/3` such that, for infinitely many prime
heads `Q`,

```math
\sum_{n\in S_Q}
\mathbf 1_{\gcd(n+2,P(Q^{2\alpha}))=1}
>0.
```

This is a statement about what the sieve-sequence/relaxed weights can prove,
not merely about whether Chen pairs exist.

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
therefore potentially relevant to this target, even though no theorem yet
transfers it to the required relaxed-weight lower bound.

## Conditional Implication (proved)

Every `p\in S_Q` is prime by square-safe certification. Put `X=Q^2` and
`z=X^\alpha`. For fixed `\alpha>1/3`, three prime factors of `p+2`, all at
least `z`, would have product at least

```math
z^3=X^{3\alpha}>X+1\ge p+2
```

for all sufficiently large `Q`, a contradiction. Therefore positivity of the
candidate sum gives `\Omega(p+2)\le2`. This is a Chen-type pair, not
necessarily a twin-prime pair.

The implication uses only square-safe certification and the elementary
factor-size comparison above.

## Established Algebraic Advance: Exact Divisor Local Factor

Property #84 derives the comparison sequence that a project-specific Type-I
argument must use. Put

```math
X=Q^2,
\qquad
z=X^\alpha,
\qquad
\frac13<\alpha<\frac12.
```

Then `P(z)` divides `P(Q)`. For an interval `I subset [Q,Q^2)`, let
`N_m(I)` count the candidate's relaxed-weight integers `n in I` with `m|n`.
The exact one-divisor formula is

```math
\boxed{
N_m(I)
=
\mathbf1_{\gcd(m,P(Q))=1}\rho_{Q,z}\ell_m+E_m(I),
}
```

where `ell_m` is the number of multiples represented after writing `n=mk`,
and

```math
\boxed{
\rho_{Q,z}
=
\frac12
\prod_{2<p<z}\left(1-\frac2p\right)
\prod_{z\le p<Q}\left(1-\frac1p\right).
}
```

Thus wheel-sharing divisors contribute zero, while every divisor coprime to
the installed wheel has the same explicit local density. The first product
has sieve dimension two and the second has sieve dimension one.

The remainder `E_m(I)` is exactly the discrepancy of the one incomplete CRT
period. Property #84 proves only the trivial pointwise bound by the complete
primorial modulus. It therefore does **not** prove a Type-I estimate. The first
honest accumulated obligation is cancellation in

```math
\sum_{m\le M}\alpha_mE_m(I)
```

for the coefficient class and divisor range needed by the relaxed sieve.
Complete-period density by itself cannot supply that cancellation.

## Established Bilinear Reduction And A Refuted Shortcut

Property #85 factors the final relaxed indicator at `x=mn`. After both factor
variables are restricted to be coprime to `P(Q)`, centering by the conditional
scalar density gives the exact pointwise remainder

```math
\sum_{d\mid P(z)/2}
\mu(d)
\left(
\mathbf1_{n\equiv-2m^{-1}\ (\mathrm{mod}\ d)}
-\frac1{\varphi(d)}
\right).
```

Each bracket is exactly a sum of nonprincipal character products
`chi(m)chi(n)`. This is the first genuine bilinear family exposed by the
relaxed weight.

It also refutes one tempting formulation. On a complete reduced wheel,
choosing both coefficient sequences to be the nonprincipal character modulo
`3` makes the centered correlation equal the entire relaxed survivor count.
Thus subtracting only the scalar density does **not** make the final sifted
indicator pseudorandom against arbitrary product coefficients.

This does not refute the candidate or every short-domain bilinear estimate.
It blocks the route that applies a black-box arbitrary-coefficient Type-II
bound directly to the scalar-centered final indicator. A viable sieve
formulation should instead begin before the last relaxed filtering step, with

```math
\mathcal A_Q
=
\{n+2:n\in S_Q\},
```

and study its shifted divisor counts

```math
A_d(I)
=
\#\{n\in S_Q\cap I:d\mid n+2\}.
```

The next Type-I question is whether these counts have the expected reduced-
residue factor `1/phi(d)` on average over squarefree `d|P(z)`. Any later
bilinear theorem must be formulated for the remainders of this pre-sieved
base sequence, or use a comparison that already contains the fixed local
character modes.

Property #86 proves the exact reduction

```math
\boxed{
A_d(I)-\frac{A_1(I)}{\varphi(d)}
=
\pi(I;d,-2)-\frac{\pi(I)}{\varphi(d)}
}
```

for odd `d|P(z)` in the square-safe window. Thus the remaining Type-I input is
an averaged theorem for primes in the progression `-2 modulo d`. This is the
specific new arithmetic information the project must obtain or import;
complete-period sieve algebra determines the main factor but cannot supply
the average cancellation.

## Proof Target And Open Estimate

Concretely, the target is to prove, for some fixed `\alpha>1/3` and infinitely
many prime heads `Q`,

```math
\sum_{n\in S_Q}
\mathbf 1_{\gcd(n+2,P(Q^{2\alpha}))=1}
>0.
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
  the project's first derivation of prime production from these particular
  weights, but the underlying existence theorem is already classical. It
  would not resolve the twin-prime conjecture or any 2-gap candidate.
- It is possible that even the almost-prime target is out of reach for the
  sieve-sequence weights specifically, in which case the candidate fails as a
  fallback. That failure would itself be informative: it would say the
  weights cannot support prime production even at Chen-type strength, a much
  sharper negative result than the current "cannot reach twin-prime strength."

## Established Inputs

- [Relaxed cofactor divisor sum is a prime-progression discrepancy](
  ../properties/sieve-sequence/relaxed-cofactor-divisor-sum-is-prime-progression-discrepancy.md)
  — proves the exact shifted-divisor comparison and identifies its accumulated
  remainder as the missing prime arithmetic-progression estimate.
- [Relaxed almost-prime bilinear remainder has a character obstruction](
  ../properties/sieve-sequence/relaxed-almost-prime-bilinear-character-obstruction.md)
  — gives the exact inverse-residue/character family and proves the complete-
  wheel scalar-comparison obstruction.
- [Refuted scalar-density Type-II orthogonality](
  refuted/relaxed-weight-scalar-density-type-ii.md)
  — preserves the exact auxiliary route that must not be retried; it does not
  refute this candidate.
- [Relaxed almost-prime weight has an exact divisor local factor](
  ../properties/sieve-sequence/relaxed-almost-prime-divisor-local-factor.md)
  — supplies the exact divisor-dependent comparison density and isolates the
  signed incomplete-period remainder that the first Type-I theorem must sum.
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

- **Success:** a proved positive relaxed-weight sum for infinitely many heads,
  deriving Chen-type pairs from the sieve-sequence weights.
- **Partial success:** the same for `\Omega(p+2)\le C`, `C>2` constant.
- **Failure:** a proof that this relaxed-weight positivity statement cannot
  hold infinitely often. This would refute the proposed mechanism, not the
  externally established existence of Chen-type pairs.
