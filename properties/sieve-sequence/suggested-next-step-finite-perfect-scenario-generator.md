# Suggested Next Step: A Finite Perfect-Scenario Generator

**Status:** Suggested computational research step. Every returned scenario can
be certified finitely; infinitely many successful scenarios are not claimed.

## Purpose

The open infinitude property does not prevent the project from generating,
certifying, and studying individual perfect scenarios. A finite generator can
search one bounded safe window, return every survivor it finds, and attach a
complete certificate to each result.

This separates two different statements:

```text
Sound finite generation:
    Every returned scenario satisfies all required conditions.

Unbounded success:
    Successful scenarios occur beyond every finite bound.
```

The first is implementable and finitely checkable. The second remains the open
mathematical target.

## Search Coordinates

Let `q` be the prime head of the certification stage. Its square-safe starts
are the integers

```math
J_q=\{n:q\le n\text{ and }n+2<q^2\}.
```

Equivalently,

```math
J_q=\{q,q+1,\ldots,q^2-3\}.
```

Define

```math
P(q)=\prod_{r<q}r,
```

where `r` ranges over primes. A perfect safe-window survivor is an `n` such
that

```math
n\in J_q
\qquad\text{and}\qquad
\gcd(n(n+2),P(q))=1.
```

The generator can find these starts by initializing the finite interval `J_q`
and, for every prime `r<q`, removing the two residue classes

```math
n\equiv0\pmod r
\qquad\text{and}\qquad
n\equiv-2\pmod r.
```

This is the endpoint version of the existing copy-index rule. It searches all
old seed residues at once instead of fixing one seed and hoping that many of
its copies occur inside the safe window.

## Why Every Output Is Certified

Suppose the generator returns `n`. Then neither `n` nor `n+2` has a prime
divisor smaller than `q`. Both values are at least `q`, and

```math
n+2<q^2.
```

If either endpoint were composite, it would have a prime factor no larger than
its square root and therefore smaller than `q`. That contradicts the filter
certificate. Hence

```math
n\text{ is prime}
\qquad\text{and}\qquad
n+2\text{ is prime}.
```

Every returned start is therefore a genuine twin-prime pair and a valid finite
perfect scenario at head `q`.

## Reconstructing The Initial Seed

Choose any earlier prime stage `p<q` whose ancestry is to be recorded, and let

```math
M_p=\prod_{r<p}r.
```

For a returned endpoint `n`, define

```math
a=n\bmod M_p,
\qquad
j=\frac{n-a}{M_p}.
```

Then

```math
n=a+jM_p
```

and the old cyclic seed is `(a,a+2)` modulo `M_p`. Because the returned
endpoint survived every prime below `q`, it automatically survived all old
filters below `p` and all transition filters from `p` to `q`.

For each transition prime `r`, the certificate may also record that `j` avoids
the two forbidden copy-index classes

```math
j\not\equiv-aM_p^{-1}\pmod r,
\qquad
j\not\equiv-(a+2)M_p^{-1}\pmod r.
```

The product `M_p` need not be materialized when it becomes large. The
certificate can store the old prime list and compute only the modular values
needed for verification.

## Generator Contract

### Inputs

- a final prime `q`;
- optionally an earlier prime `p<q` for ancestry reconstruction;
- optionally a smaller subinterval of `J_q` for bounded experiments.

### Outputs

For every surviving start `n`, record:

- the endpoints `(n,n+2)`;
- the final head `q` and strict square-bound check;
- the list or range of installed prime filters;
- confirmation that both endpoints avoid every filter below `q`;
- the chosen initial stage `p`;
- the reconstructed seed residue `a` and copy index `j`;
- the two avoided copy-index classes for every transition prime, when a full
  ancestry certificate is requested.

### Guarantees

- A run over one fixed finite interval terminates.
- Every returned result is a valid finite perfect scenario.
- Exhaustive enumeration returns every scenario in the selected interval.
- A run may validly return no scenario for the selected `q` or subinterval.

### Non-Guarantees

- The generator is not proved to succeed for every prime `q`.
- It is not proved to find a result beyond every requested lower bound.
- Repeated successful experiments do not prove infinitely many scenarios.
- A command that searches indefinitely for the next scenario is not proved to
  terminate.

## Two Equivalent Implementations

### Safe-window segmented filter

Work directly with all starts `n` in `J_q` and strike the two classes modulo
every prime below `q`. This is the simplest complete finite search and produces
the endpoint certificate directly.

### Sieve-sequence ancestry search

Start from all cyclic 2-gaps at an earlier stage `p`, intersect all of their
absolute representatives with `J_q`, and apply the transition filters from `p`
through the prime immediately before `q`. This retains the complete sequence
history and should produce exactly the same endpoint survivors.

Comparing these implementations is itself useful. Equality of their outputs
tests the bridge between the cyclic sieve representation and direct absolute
filtering.

## Recommended Measurements

The generator should collect more than successful pairs. For every `(p,q)` or
safe-window slice, record:

- total old 2-gap starts entering the window;
- survivors after each transition filter;
- expected complete-period density and actual local count;
- local discrepancy from that expected density;
- longest consecutive run of covered copy indices;
- which seed residues produce survivors;
- whether survivors cluster by prime-gap chain or rotation position;
- bilinear or signed-correlation statistics proposed by the Type I/Type II
  research assessment.

These measurements cannot prove infinitude, but they can falsify naive
distribution models and identify which additional averaging variables might
support a future theorem.

## Why This Is The Right Finite Experiment

Under the restricted condition `q<p^2`, the old primorial `M_p` eventually
exceeds the length of the final safe window. One fixed seed then has at most one
local representative, so its complete-period repetition frequency cannot force
local placement.

Searching all old seed residues, equivalently all safe-window endpoints, keeps
the exact residue distribution without relying on unavailable local
multiplicity. A successful result can still be assigned to one seed afterward
through `a=n mod M_p`.

## Suggested Success Criterion

The first implementation milestone is complete when the generator can:

1. enumerate one finite safe window or slice;
2. produce endpoint and ancestry certificates for every survivor;
3. independently verify each certificate;
4. compare direct filtering with sieve-sequence ancestry filtering;
5. export local-discrepancy and covered-run measurements.

That milestone would establish a reliable experimental platform. It would not
change the status of the infinite perfect-scenario property.

## Related Properties

- [Exact Filter Frequency Across Repeated Copies](copy-index-filter-frequency.md)
- [Safe-Window 2-Gaps Certify Twin Primes](safe-window-two-gaps-certify-twin-primes.md)
- [Reverse-Engineered Initial Scenario](reverse-engineered-eventual-head-scenario.md)
- [Candidate Property: Infinitely Many Perfect Sieve Scenarios](../../candidates/infinite-perfect-scenario-property.md)
- [Recent Prime-Producing Sieves Research Assessment](research/recent-prime-producing-sieves-deep-dive.md)
