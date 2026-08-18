# Recent Prime-Producing Sieves: A Deep-Dive For The Perfect-Scenario Problem

**Date:** 2026-07-20
**Status:** Research assessment. No twin-prime theorem is claimed.
**Primary conclusion:** Recent work gives a much sharper way to state and test
the missing hypothesis, but no established result currently supplies that
hypothesis for the sieve-sequence perfect scenarios.

## 1. Executive Conclusion

The project already has exact information of the following kind:

- a complete-period count of cyclic 2-gaps;
- exactly two forbidden copy-index classes for each new odd prime filter;
- an exact CRT survivor count over a complete batch modulus;
- a finite certificate showing that a survivor in the square-safe window is a
  genuine twin-prime pair.

Those are strong **local-factor** and **complete-period** statements. They do
not yet control cancellation inside the much shorter square-safe interval.

The most relevant recent advance is Kevin Ford and James Maynard's 2024
framework for prime-producing sieves. It proves, in a general setting, that:

1. Type I information, which measures divisibility distribution, is not enough
   to force primes even when it is extremely strong.
2. A substantial Type II range, which measures bilinear cancellation against
   arbitrary coefficients, is genuinely necessary.
3. Given quantified Type I and Type II ranges, their framework can determine
   whether those ranges force a positive prime lower bound, an asymptotic, or
   no positive lower bound at all.

This changes the project question from

```text
Are the repeated 2-gaps sufficiently well distributed?
```

to the testable question

```text
Can the perfect-scenario weights satisfy a nontrivial arbitrary-coefficient
bilinear estimate over a long enough factor range?
```

The exact CRT results resemble the input to Type I analysis, but they do not
yet prove even the full Ford--Maynard Type I norm in the required short
interval. Nothing currently in the property catalog proves Type II
cancellation.

There is also an important scale conflict. If the initial prime `p` and final
prime `q` obey the proposed common-square condition `q<p^2`, then the old
primorial period is eventually much larger than the final safe window:

```math
M_p=\prod_{r<p}r,
\qquad
\log M_p=\vartheta(p)\sim p,
\qquad
q^2<p^4.
```

Therefore

```math
\frac{M_p}{q^2}
>
\frac{\exp((1+o(1))p)}{p^4}
\longrightarrow\infty.
```

For all sufficiently large such scenarios, a fixed old residue class occurs
at most once in `[q,q^2)`. Repetition still distributes all copies perfectly
over a complete global period, but there are not many copies of one fixed seed
inside the safe window. Any analytic averaging argument must therefore average
over many seed residues, relax `q<p^2`, or introduce a different source of
averaging.

That scale calculation and the missing Type II estimate are the two main
research constraints.

## 2. Exact Project Target

Let

```math
P(z)=\prod_{r<z}r,
```

where `r` ranges over primes. At a final prime head `q`, consider the upper
part of the safe window

```math
J_q=\{n:q^2/2<n\le q^2-3\}.
```

Define the symmetric pair-survivor weight

```math
A_q(n)
=
\mathbf 1_{\gcd(n(n+2),P(q))=1}.
```

If `n` is prime and `A_q(n)=1`, then `n+2` has no prime divisor below `q`.
Because `n+2<q^2`, a composite `n+2` would have a prime factor smaller than
`q`. Consequently,

```math
\sum_{\substack{n\in J_q\\n\text{ prime}}}A_q(n)>0
```

produces a twin-prime pair inside the square-safe window.

This formulation is intentionally direct. It shows why proving the desired
positivity for unbounded `q` is already a twin-prime-strength result. Calling
the surviving values "sieve elements" does not weaken the prime-pair content
once the square certification is applied.

### Copy-index formulation

For an old seed `(a,a+2)` with period `M_p`, write its copies as

```math
(a+jM_p,a+2+jM_p).
```

Every future prime `r` forbids exactly two classes of `j` modulo `r`:

```math
j\equiv-aM_p^{-1}\pmod r,
\qquad
j\equiv-(a+2)M_p^{-1}\pmod r.
```

Thus the project can also ask whether the geometrically eligible index interval
intersects the indices that avoid every forbidden class. This is an exact
finite covering problem. The endpoint-weight and copy-index formulations are
equivalent descriptions of the same survival event, but they expose different
parts of the difficulty:

- copy indices expose the exact CRT structure;
- endpoint weights expose the prime-detection and parity problem.

## 3. What Complete-Period CRT Really Gives

For a finite batch `R` of new odd primes, the number of allowed copy-index
classes in one complete batch period

```math
B_R=\prod_{r\in R}r
```

is exactly

```math
\prod_{r\in R}(r-2).
```

The corresponding density is

```math
\prod_{r\in R}\left(1-\frac2r\right).
```

This proves that allowed classes exist globally and that every residue imposed
by one filter has the expected frequency over a complete period. It also
handles overlaps between filters exactly.

It does **not** imply that an arbitrary interval shorter than `B_R` contains an
allowed class. If `I` is the eligible copy-index interval, the local count is

```math
N_R(I)
=
|I|\prod_{r\in R}\left(1-\frac2r\right)+E_R(I),
```

where the CRT formula determines the main density but gives no adequate
general lower bound for the discrepancy `E_R(I)`.

Rotation translates the periodic pattern. It does not make `E_R(I)` random,
and it does not bound the longest run covered by the forbidden classes.

### Why this is not automatically Ford--Maynard Type I

Type I estimates sum local discrepancies over many divisor scales and require
strong uniformity over subintervals. A full-period identity modulo a primorial
does not give that norm when the modulus is larger than the observation
interval. To claim Type I, the project must derive a uniform error estimate and
then show that the weighted sum of those errors is small.

The current CRT results are therefore best classified as **Type I algebraic
input**, not as a completed Type I theorem.

## 4. The Ford--Maynard Diagnostic

Ford and Maynard study nonnegative sequences `(a_n)` and comparison sequences
`(b_n)` supported on `X/2<n<=X`. Put

```math
w_n=a_n-b_n.
```

For parameters

```math
0<\gamma<1,
\qquad
0\le\theta<\frac12,
\qquad
0<\nu\le1-\theta,
```

their hypotheses include the following two kinds of estimate. The formulas
below retain the paper's parameterization and suppress only harmless endpoint
conventions.

### Type I

For every interval `I`, one needs a bound of the shape

```math
\sum_{m\le X^\gamma}
\tau_B(m)
\max_I
\left|
\sum_{\substack{X/2<mn\le X\\n\in I}}w_{mn}
\right|
\le
\frac{X}{(\log X)^B}.
```

This asks whether the candidate sequence and its comparison model agree after
testing divisibility by many `m`, uniformly in the remaining variable.

### Type II

For every pair of coefficient sequences satisfying divisor-type bounds, one
needs

```math
\left|
\sum_{\substack{(X/2)^\theta<m\le X^{\theta+\nu}\\X/2<mn\le X}}
\xi_m\kappa_n w_{mn}
\right|
\le
\frac{X}{(\log X)^B},
```

with

```math
|\xi_m|\le\tau_B(m),
\qquad
|\kappa_n|\le\tau_B(n).
```

This is much stronger than saying that removals have the correct total density.
The coefficients may choose signs and correlate adversarially with the residue
pattern. Type II therefore detects hidden alignment that survives all
unweighted counting.

### The hard conclusions from their theory

- If `gamma+nu>1`, classical identities already give an asymptotic under their
  strong hypotheses.
- Their new method can produce optimal lower and upper bounds in additional
  ranges by using all Type I and Type II information simultaneously.
- Their Theorem 2.1 proves that, for every fixed `gamma<1`, some positive
  minimum amount of Type II information is necessary. If the Type II range is
  too short, there are bounded nonnegative sequences satisfying the stated
  Type I and Type II estimates that contain no primes at all.
- Their criteria are not summarized by one universal density threshold; the
  optimal constants can change discontinuously as the Type I/II ranges change.

This last point answers a central project question. No sufficiently large
global number of 2-gaps, by itself, creates a universal threshold forcing a
prime pair in the local window. A threshold becomes reliable only after adding
quantitative distribution hypotheses strong enough to exclude the
prime-free counterexample sequences.

## 5. A Non-Circular Candidate Sequence

A direct but circular-looking choice would be

```math
a_n=\mathbf 1_{n+2\text{ is prime}}.
```

Proving the required estimates for that weight would simply hide the twin-prime
problem inside the hypotheses.

A better staged family is

```math
a_n^{(z)}
=
\mathbf 1_{\gcd(n+2,P(z))=1},
```

possibly combined with the old-wheel condition and restricted to one dyadic
subinterval of the safe window. Then

```math
\sum_p a_p^{(z)}
```

counts primes `p` for which `p+2` has no prime factor below `z`.

This gives a natural ladder:

- `z=X^alpha` with `alpha>1/3` would force `p+2` to have at most two prime
  factors, yielding a Chen-type almost-prime target.
- `z` just beyond `X^(1/2)` would force `p+2` itself to be prime and would
  reach the twin-prime target.

The comparison sequence `b_n` cannot be chosen as a naive constant density.
Divisibility by `m` changes the local factors, especially when `m` shares
primes with `P(z)`. Constructing a tractable `b_n` with the correct divisor-
dependent local model is part of the Type I problem, not bookkeeping to be
assumed.

## 6. Mapping The Existing Properties To Type I And Type II

| Existing project fact | Analytic role | What is still missing |
|---|---|---|
| Exactly two forbidden classes modulo each new prime | Local sieve dimension two | Uniform accumulated error in short intervals |
| Exact product count over a complete batch modulus | Correct global main density | Control when the interval is shorter than the modulus |
| Repetition of old gaps | Periodic source of copies | Enough copies inside the chosen local interval |
| Rotation | Translation of the periodic pattern | Cancellation or a maximum-covered-run bound |
| Exact accepted local strikes | One-filter capacity information | Correlations among many filters |
| Safe-window certification | Converts survival into primality | A positive survivor count |
| Reverse-engineered finite scenario | Finite certificate | Infinitely many certificates |
| No arbitrary-coefficient estimate | None yet | The Type II theorem |

The project is therefore not blocked by an unknown total density. It is blocked
by the possibility that the allowed residue classes align badly with the
particular short window, and by the stronger possibility that this alignment
persists under bilinear tests.

## 7. The Fixed-Seed Scale Conflict

The proposed perfect scenario asks for a consecutive prime chain from `p` to
`q` with

```math
q<p^2.
```

This makes the number of transition filters comparatively short. But the old
period is the primorial

```math
M_p=\prod_{r<p}r.
```

By the prime number theorem in Chebyshev-theta form,

```math
\log M_p=\sum_{r<p}\log r\sim p.
```

The safe window has length below `q^2<p^4`, whereas `M_p` grows like `e^p`.
Hence, eventually,

```math
M_p>q^2.
```

Two consequences follow.

1. A fixed seed residue `(a,a+2) mod M_p` has at most one representative in
   the final safe window.
2. Its complete-period frequency cannot, on its own, force that representative
   to be present or allowed.

There is a genuine tradeoff:

- To have many copies in the safe window, one wants `M_p<<q^2`, which
  heuristically requires `p` no larger than a constant multiple of `log q`.
- To keep `q<p^2`, one needs `p>sqrt(q)`.

These conditions are incompatible for sufficiently large `q`.

This does not disprove the finite perfect scenario. It shows that the proof
cannot simultaneously rely on a short prime chain and on many local copies of
one fixed old seed. A viable averaging argument should instead consider one of
the following:

- all old 2-gap residues `a` at once;
- a much earlier seed stage, accepting a long chain of future filters;
- an average over several final heads `q`;
- an additional factorization or additive structure that creates a bilinear
  family.

## 8. What Green--Sawhney Contributes

Ben Green and Mehtaab Sawhney proved infinitely many prime values of
`p^2+nq^2`, with both variables prime, for the stated congruence classes of
`n`. Their proof uses Type I/II sums in a quadratic number field. The main new
ingredient is a Type II estimate obtained through quantitative Gowers-norm
concatenation and a quasipolynomial inverse theorem.

The current arXiv version is revision 3 from June 2026 and is accepted for
publication in *Acta Mathematica*. That makes it an established modern example
of successful Type II innovation, not merely an unreviewed analogy.

This is relevant because it demonstrates a modern route through a difficult
parity barrier: expose extra variables, turn the obstruction into a bilinear or
higher-order correlation, and prove that structured correlation cannot persist.

It does not transfer directly to `(x,x+2)`. Their polynomial form, two prime
variables, and number-field factorization provide structure that the affine
twin pair does not automatically possess.

For this project, the lesson is conditional and concrete. Search for a Type II
decomposition after averaging over seed residue, copy index, factor split, and
possibly final head. If that enlarged family has a Gowers-uniform or bilinear
description, the Green--Sawhney machinery becomes conceptually relevant. If no
extra variable or nontrivial factorization appears, citing their theorem does
not advance the proof.

## 9. Other Recent Results And Their Exact Relevance

### Matomaki--Merikoski--Teravainen

Their sieve detects primes in certain multiplicatively structured sets and
gives, among other applications, an `L`-function-free proof of primes in
intervals of length `X^(39/40)` for all sufficiently large `X`.

Potential use here: a one-prime or almost-perfect milestone, if the averaged
copy family can be represented by the required multiplicative convolutions and
its Type I/II conditions can be verified.

Boundary: the current copy-index forbidden-class description is periodic, but
periodic is not the same as multiplicatively structured in the sense required
by their theorem. Their result also detects one prime, not the fixed pair
`(n,n+2)`.

### Lichtman's modified linear sieve

Jared Lichtman's modified linear sieve reaches an effective level
`X^(10/17-epsilon)` for suitable weights and improves the best published upper
bound for the twin-prime counting function by about `2.94%`.

This is useful negative evidence. Better levels of distribution and sharper
sieve weights materially improve how many twin primes could exist from above,
yet do not prove that the count is positive from below. The result strengthens
the warning that distribution density alone does not cross the parity barrier.

### Lichtman's large-modulus distribution work

The earlier level `66/107` result for triply well-factorable weights also gives
new upper bounds for twin primes and Goldbach representations. Its direction
is again upper, not a positive twin-pair lower bound.

### Guth--Maynard short intervals

Guth and Maynard prove prime asymptotics in intervals of length
`X^(17/30+o(1))`. This is a major improvement for locating individual primes.

The project safe window near `X=q^2` has macroscopic length, so individual
prime scarcity is not the bottleneck. The missing event is the correlation
between `n` and `n+2`. Short-interval prime theorems do not supply that pair
correlation.

### Purported complete twin-prime proofs

Recent preprints that announce a full twin-prime proof but have no established
validation, accepted publication, or independently confirmed argument are not
used as evidence in this assessment. A heuristic model can be useful for
experiments, but it cannot supply the missing theorem.

## 10. Concrete Research Program

### Stage 0: choose one scale and one weight

Use `X=q^2` and a dyadic interval contained strictly below `q^2`. Define both:

```math
A_q(n)=\mathbf 1_{\gcd(n(n+2),P(q))=1}
```

and the relaxed family

```math
A_{q,z}(n)=\mathbf 1_{\gcd(n(n+2),P(z))=1},
\qquad z<q.
```

Record whether the experiment averages over all old seed residues or fixes one
seed. Do not mix those two models.

### Stage 1: prove a genuine Type I theorem

For each relevant divisor `m`, derive the correct local density rather than a
single global density. Then prove a bound of the form

```math
\sum_{m\le X^\gamma}
\tau_B(m)
\max_I |R_m(I)|
\ll_B \frac{X}{(\log X)^B},
```

where `R_m(I)` is the difference between the actual count and its complete
local-factor model.

This stage must explicitly handle:

- divisors sharing primes with the wheel;
- intervals shorter than the primorial;
- boundary effects from the rotation;
- the growth of `z` with `X`;
- averaging over seed residues, if used.

If this estimate cannot be proved beyond a trivial range, stop calling the CRT
distribution a Type I result.

### Stage 2: perform a computational Type II audit

This is evidence, not proof. For moderate `X`, form matrices representing

```math
w_{mn}
```

over candidate factor ranges. Measure:

- unweighted bilinear sums;
- spectral norms or large singular values;
- correlations with residue-class characters;
- worst observed signed coefficient patterns;
- how the norm changes when averaging over seed residues or final heads.

The purpose is to discover whether the repeated/filter structure creates
cancellation or merely relocates a rigid periodic obstruction. A persistent
large singular direction is a concrete warning against the proposed analytic
route.

### Stage 3: prove a Type II estimate

The theoretical target is an arbitrary-coefficient estimate over an interval
`[theta,theta+nu]`, not only the correct unsigned count. Candidate mechanisms
to investigate are:

- dispersion after averaging over all seed residues;
- character-sum cancellation across copy-index residue classes;
- a factorization identity for the pair-survivor weight;
- Gowers-uniformity after introducing an additional averaging variable;
- well-factorable weights adapted to the batch product.

Every proposed mechanism must identify the actual source of sign cancellation.
Independence language is not a substitute for an estimate.

### Stage 4: apply the Ford--Maynard range test

Once numerical values of `gamma`, `theta`, and `nu` are proved, feed exactly
those ranges into the Ford--Maynard criteria.

Possible outcomes are:

1. the ranges force an asymptotic;
2. the ranges force a positive but non-asymptotic lower bound;
3. the ranges are too short, and their construction method permits a
   prime-free comparison sequence.

Outcome 3 is still valuable: it is a rigorous certificate that the chosen
information cannot prove positivity without a stronger estimate.

### Stage 5: target an almost-perfect scenario first

Before taking `z` to `sqrt(X)`, prove positivity with `z=X^alpha` for some
`alpha>1/3`. This would seek a prime `p` for which `p+2` has at most two prime
factors. Such a result would not prove twin primes, but it would validate that
the sieve-sequence weights support genuine prime production rather than only
complete-period density.

## 11. Go/No-Go Criteria

The research direction should be considered **promising** only if all of the
following become true:

- a non-circular nonnegative endpoint weight is fixed;
- a comparison model with correct divisor-dependent local factors is fixed;
- a short-interval Type I norm is proved, not inferred from a full period;
- a positive-length Type II range is proved with arbitrary coefficients;
- the proved range passes a Ford--Maynard lower-bound criterion;
- the averaging family still implies the original perfect-scenario event.

The direction should be considered **blocked in its current form** if any of
the following is established:

- the only available fact is the product density over the complete CRT period;
- a fixed seed has at most one local copy and no additional averaging variable;
- Type II correlations remain of main-term size;
- the provable Type II range falls in a Ford--Maynard zero-lower-bound region;
- the weight includes future primality and therefore assumes the desired pair
  correlation in its definition or hypotheses.

## 12. Final Assessment

Recent research does not currently prove that perfect sieve scenarios occur
infinitely often. It does provide a better boundary than the informal phrase
"parity problem."

The exact missing theorem is now best stated as:

```text
Construct a non-circular averaged perfect-scenario weight and prove enough
short-interval Type I uniformity plus enough arbitrary-coefficient Type II
cancellation to enter a Ford--Maynard positive-lower-bound region.
```

The current property catalog supplies the local factors and finite
certification. The next mathematical work is not another global 2-gap count.
It is either:

1. a genuine Type I/Type II analysis of an averaged seed family; or
2. a deterministic maximum-covered-run theorem strong enough to bypass the
   analytic prime-producing framework.

The fixed-seed scale conflict means that the averaging choice must be made
explicit before either route can plausibly succeed.

## Primary Sources

- Kevin Ford and James Maynard,
  [On the theory of prime producing sieves](https://arxiv.org/abs/2407.14368),
  2024. See especially the Type I/II definitions and Theorems 2.1--2.2.
- Ben Green and Mehtaab Sawhney,
  [Primes of the form p^2 + nq^2](https://arxiv.org/abs/2410.04189),
  2024; revision 3, June 2026; accepted for publication in *Acta Mathematica*.
- Kaisa Matomaki, Jori Merikoski, and Joni Teravainen,
  [Primes in arithmetic progressions and short intervals without L-functions](https://arxiv.org/abs/2401.17570),
  2024.
- Jared Duker Lichtman,
  [A modification of the linear sieve, and the count of twin primes](https://msp.org/ant/2025/19-1/ant-v19-n1-p01-s.pdf),
  *Algebra & Number Theory* 19 (2025).
- Jared Duker Lichtman,
  [Primes in arithmetic progressions to large moduli, and Goldbach beyond the square-root barrier](https://arxiv.org/abs/2309.08522),
  2023.
- Larry Guth and James Maynard,
  [New large value estimates for Dirichlet polynomials](https://arxiv.org/abs/2405.20552),
  2024.

## Related Project Notes

- [Candidate Property: Infinitely Many Perfect Sieve Scenarios](../../../candidates/infinite-perfect-scenario-property.md)
- [Batched Short-Window Discrepancy Boundary](../batched-short-window-discrepancy-boundary.md)
- [Exact Batched 2-Gap Survival](../exact-batched-two-gap-survival.md)
- [Exact Filter Frequency Across Repeated Copies](../copy-index-filter-frequency.md)
- [Reverse-Engineered Initial Scenario](../reverse-engineered-eventual-head-scenario.md)
