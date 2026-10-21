# Continuous-contact research directions for sieve sequences

**Status:** Exploratory, unnumbered research directions. Elementary identities
are derived below; useful new quantitative estimates remain open. No
Stainless verification or new empirical investigation is claimed.

These four directions arise from the [continuous complex sieve notes](
../tickets/future/continuous-complex-sieve.md) and its [ManimGL visualization](
../presentations/continuous-complex-sieve/README.md). They are not additions to
the numbered catalog of sufficient conditions for square-safe 2-gap survival.
Their novelty relative to the full research literature is not established.

The [Uniform Continuous Divisor Sieve](
../properties/sieve-sequence/uniform-continuous-divisor-sieve.md) develops the
all-integer version: one filter per integer, continuous local stabilization,
divisor-count heights, prime/composite step behavior and exact pair contacts.
It supplies mathematical proofs without requiring a formal-code companion.
The quantitative survival questions below remain open.

## Common definitions and scope

The squared detector below is a normalized **Fejér kernel**, named for Lipót
Fejér; see his [1900 paper](https://history-of-approximation-theory.com/fpapers/fej1OCR.pdf).
Its integer sampling uses classical roots-of-unity orthogonality, with a
modern formal proof in Rodrigo Raya and Manuel Eberl's
[AFP development](https://isa-afp.org/browser_info/current/AFP/Gauss_Sums/document.pdf),
section4. These are established ingredients; priority of this exact activated
interpolation has not been determined.

For a finite set P of prime filters and real t >= 2, use the unweighted height

```math
\begin{aligned}
D_p(t)&=\frac1p\sum_{\ell=0}^{p-1}e^{2\pi i\ell t/p},\\
a_p(t)&=\min(1,\max(0,t-p)),\\
H_P(t)&=\sin^2(\pi t)+\sum_{p\in P}a_p(t)|D_p(t)|^2,\\
Z_P(t)&=t+iH_P(t).
\end{aligned}
```

All summands are nonnegative. Integer contacts are the integers n with
H_P(n)=0. Activation preserves previously selected primes as contacts, so
to identify contacts with the current sieve stream, restrict to n at or above
its current head, which exceeds every installed filter. For comparisons
without naming a head, use n > max P when P is nonempty.

These height-count and unit-threshold statements use unweighted filters.
Arbitrary positive weights preserve contacts but change heights and margins.
The activated infinite sum is locally finite; this observation is mathematical,
not a verified implementation claim.

## Direction 1: bounded-window contact stabilization

This is the classical square-root sieve certificate in contact notation;
see [NIST DLMF section27.18](https://dlmf.nist.gov/27.18), which describes
the sieve of Eratosthenes and the square-root divisor test.

**Derived statement:** For B >= 2, if P contains every prime p <= sqrt(B),
the integer contacts in [2,B] are exactly the primes in that interval.
Adding any further prime filters cannot change that contact set.

Every composite n <= B has a prime divisor p <= sqrt(n) <= sqrt(B), with
p<n. Its activation and squared detector are both one, so H_P(n)>=1.
At a prime n, smaller prime detectors vanish and all filters p>=n are
inactive. Thus H_P(n)=0. Nonintegers have sin^2(pi t)>0 and are not contacts.

The contact set therefore stabilizes before the entire curve necessarily
stabilizes. For example, a later filter can raise an already rejected multiple
without changing whether it touches the axis. Filters p>=B vanish on [2,B],
so the curve itself also stabilizes locally after finitely many filters.

**Research obligation:** Establish the exact bridge to existing sieve-stage
safe-window statements before treating this elementary fact as a new sieve
property. Investigate incremental certificates of contact stability; no
algorithmic improvement follows from the reformulation alone.

## Direction 2: height records overlapping filter strikes

The underlying arithmetic quantity is the classical number of distinct prime
divisors, denoted nu in [DLMF section27.2(i)](https://dlmf.nist.gov/27.2.i)
and often omega elsewhere. The activation excludes a prime's own divisor:
after all prime filters, this unweighted height is omega(n)-1_(n prime).
The truncated proper-divisor identity is not a claim to have discovered
a new arithmetic function.

**Derived identity:** At every integer n >= 2,

```math
H_P(n)=\sum_{p\in P}\mathbf 1_{p<n,\ p\mid n}.
```

The sine term vanishes. Each prime detector is one precisely at its integer
multiples, and activation excludes p itself. Hence height counts filtered
distinct proper prime divisors, without multiplicity. In particular,

```math
H_{P\cup\{q\}}(n)-H_P(n)
=\mathbf 1_{q<n,\ q\mid n}\in\{0,1\},\qquad q\notin P.
```

For P={2,3,5}, the exact examples are H_P(7)=0, H_P(25)=1 and H_P(30)=3.
Higher height distinguishes repeated strikes from the first rejection.

**Open direction:** Find height-distribution or overlap bounds on short,
conditioned sieve windows that constrain how many zero-height values remain.
Average height alone need not force a contact. Any proposed inequality must
be compared with existing residue-collision and deletion-conservation bounds;
the count identity itself supplies no new distribution estimate.

## Direction 3: two-gap survival as simultaneous contact

The zero-sum equivalence is an elementary consequence of nonnegativity.
Its role here is to encode a pair test, rather than assert a new general
theorem about zeros.

Define pair height for an integer start n >= 2 by

```math
B_P(n)=H_P(n)+H_P(n+2).
```

**Derived identity:** Nonnegativity gives

```math
B_P(n)=0
\quad\Longleftrightarrow\quad
H_P(n)=H_P(n+2)=0.
```

When 2 is installed and n is in the current stream's domain, both surviving
endpoints are consecutive survivors: the only intervening integer is even
and exceeds 2. This is therefore a 2-gap, rather than merely a pair at distance
two. Earlier retained prime contacts must not be counted as current-stream
members outside that domain.

For a new filter q not in P, pair-height increment is exactly

```math
B_{P\cup\{q\}}(n)-B_P(n)
=\mathbf 1_{q<n,\ q\mid n}
+\mathbf 1_{q<n+2,\ q\mid n+2}.
```

For q>2 it is at most one, since q cannot divide both endpoints.

**Open direction:** Bound the loss of simultaneous contacts in a specified
integer window under a new filter, or along a conditioned chain, strongly
enough to guarantee a surviving pair. For a future prime head Q, the
square-safe endpoint window is n>=Q and n+2<Q^2. An actual pair certificate
there requires the corresponding filters below Q; a finite-stage identity
is not a proof of infinitely many twin primes.

The [Two-Class Collision Survival](
../properties/sieve-sequence/two-class-survival-from-collision-energy.md)
property already expresses destruction through the two harmful residue
classes. Any useful contact-height bound must improve or complement that
interface, rather than rename it.

## Direction 4: exponentially damped counts of contacts

The finite-sum limit and error estimate below follow from a unit gap between
zero and positive integer heights. They are elementary threshold estimates;
the open task is an independent bound for these particular sieve sums.

For a finite integer window W contained in [2,infinity) and lambda>0, set

```math
S_P(\lambda)=\sum_{n\in W}e^{-\lambda H_P(n)},\qquad
N_0=\#\{n\in W:H_P(n)=0\}.
```

**Derived limit and error bound:** Since unweighted integer heights are
nonnegative integers, every rejected value has height at least one. Thus

```math
\begin{aligned}
0&\le S_P(\lambda)-N_0
\le (|W|-N_0)e^{-\lambda},\\
\lim_{\lambda\to\infty}S_P(\lambda)&=N_0,\\
N_0&\ge
\frac{S_P(\lambda)-|W|e^{-\lambda}}{1-e^{-\lambda}}.
\end{aligned}
```

Replacing H_P by B_P gives the same formulas for simultaneous contacts.
Adding filters makes these damped counts nonincreasing, because heights
increase pointwise.

**Open direction:** Obtain an independent, noncircular lower bound for the
damped count that makes the displayed lower bound positive. Directly computing
the sum by checking every value merely relocates survivor enumeration.
To address pair survival, the bound must apply to pair height on the intended
conditioned window. Passing to the limit alone gives no positivity estimate.

## Existing boundaries and recommended order

The [Weighted Deletion Conservation](
../properties/sieve-sequence/weighted-deletion-conservation-law.md) property
shows how a signed discrepancy can exactly encode terminal survival; avoid
presenting such an equivalent quantity as an independent survival proof.
The [Fourier Correlation Bound](
../properties/sieve-sequence/fourier-two-gap-correlation-prefix-bound.md)
already develops a finite Fourier approach, with its own localization limits.
The new notation does not bypass either boundary.

Prioritize Directions 2 and 3: define exact height and pair-height observables,
then audit their relation to existing arithmetic quantities. Direction 1 is
a foundational bridge; Direction 4 is a possible counting tool whose needed
independent estimate is still unspecified.

Curvature, area and valley width depend on how the function is interpolated
between integers. They become relevant to the sieve only after proving a
connection to integer contacts. No such connection or bound is claimed here.

For earlier gap-cycle research, Fred B. Holt and Helgi Rudd's
[2014 paper](https://arxiv.org/abs/1408.6002), section2 and Corollary6.3,
develops expansion/closure and complete-period 2-gap counts. This is relevant
prior work, not a source of a proved short-window bound for the activated
curves here. The [attribution inventory](../properties/sieve-sequence/research/continuous-sieve-attribution.md)
records source roles and unresolved historical priority.
