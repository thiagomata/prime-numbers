# Protected arithmetic families of twin candidates

**Status:** Unnumbered exploratory candidate. The one-filter statements and
admissibility deductions below are mathematically proved. Persistence and
reconstruction are open directions, not established survival mechanisms.
No Stainless verification or historical-priority claim is made.

**Empirical status:** No systematic experiment. Explicit arithmetic examples
refute two stronger shortcuts without refuting every possible research fork.

## Setup and objective

After installing a finite set of prime filters containing 2 and 3, consider K
existing candidate pairs with equally spaced starts

```math
x_j=a+jd,\qquad (x_j,x_j+2),\qquad 0\le j<K,
```

where a and d are positive integers and a exceeds every installed prime.
Every endpoint must survive all installed filters. This assumption excludes
protected self-prime exceptions such as (3,5). Since each surviving start is
5 modulo6, d is a multiple of6 for
K>=2. These are candidate pairs, not assumed prime pairs.

For an incoming prime p>=5, rejection requires a proper-divisor hit at an
endpoint. In the proofs using residue classes, assume a>p so all endpoints
exceed p. Without that assumption, divisibility is still a sufficient upper
test for possible deletion, but the prime's own value must be protected.

The aim is to select configurations for which all members cannot be rejected.
Single-filter protection and protection against future filters collectively
are distinct objectives.

## Three candidates protect against one filter

Suppose K>=3 and p does not divide d. The first three starts have distinct
residues modulo p. Indeed, equality of two would imply

```math
p\mid(j-i)d,\qquad 1\le j-i\le2,
```

which is impossible because p>=5 is prime and p does not divide d.
The only harmful start residues are 0 and p-2. Three distinct residues cannot
all lie in those two classes. Therefore

```math
p\nmid d
\Longrightarrow
\exists j\in\{0,1,2\}:\quad
p\nmid x_j\ \text{and}\ p\nmid(x_j+2).
\qquad[\text{Q.E.D.}]
```

This is a one-filter guarantee for an existing family. It does not prove
existence of that family after the previous filters.

If p divides d, all starts have the same residue. Arbitrarily many members
can all be rejected when that residue is harmful. No family-size guarantee
independent of its location applies in that case.

## Two candidates can suffice

For two starts a and a+d, the possible cross-endpoint differences are
d-2,d,d+2. If p rejected both pairs, it would divide one of those differences.
Consequently

```math
p\nmid d(d-2)(d+2)
\Longrightarrow
\text{at least one of the two pairs survives filter }p.
\qquad[\text{Q.E.D.}]
```

This is sufficient, not necessary: a bad difference permits joint rejection
but does not force it for every translation. It is the same endpoint
arithmetic as the established [Bad-Separator Deletion property](
../properties/sieve-sequence/two-focused-bad-separator-deletion-bound.md).

## Old filters constrain which families exist

Let

```math
H_{K,d}=\{jd,jd+2:0\le j<K\}.
```

For an installed prime r, a surviving translated family requires

```math
a+h\not\equiv0\pmod r\quad\text{for every }h\in H_{K,d}.
```

Such an a exists modulo r exactly when H_{K,d} omits at least one residue
modulo r. Thus full residue coverage by these offsets is an obstruction.

Conversely, if the offsets omit a residue for every prime in a finite old
filter set, choose an allowed translation for each prime. The Chinese
remainder theorem combines those choices. Arbitrarily large positive
translations then exist, avoiding self-prime exceptions. This establishes
existence somewhere, not in a specified bounded domain or square window.

One necessary condition is particularly restrictive. If K>=r and r does not
divide d, the first r starts a+jd occupy every residue modulo r. Therefore

```math
K\ge r,\ r\text{ installed prime}
\Longrightarrow
r\mid d
\quad\text{for any surviving equally spaced family}.
```

This condition is not sufficient; shifted endpoints may still cover all
residues when the starts alone do not.

### Correction: three candidates spaced by six

For K=3,d=6, the six endpoint offsets are

```math
0,2,6,8,12,14
\equiv0,2,1,3,2,4\pmod5.
```

They cover every residue modulo5. No translation can make all three pairs
survive filter5. Thus the tempting choice of a permanent equally spaced
triple with d=6 is impossible after that stage.

Two starts spaced by6 remain possible. They have the stronger two-candidate
protection against every individual incoming prime p>=5, because no such
prime divides 4*6*8. That does not supply collective protection.

## Counterexample: different filters eliminate different members

Consider the three candidate pairs

```math
(24731,24733),\qquad(24761,24763),\qquad(24791,24793).
```

Their starts are equally spaced by30. Every start is 11 modulo30 and every
second endpoint is 13 modulo30, so all pairs survive installed filters2,3,5.
Every future prime p>=7 avoids d=30; the three-candidate one-filter theorem
therefore applies to each such prime. Nevertheless,

```math
24731=7\cdot3533,\qquad
24761=11\cdot2251,\qquad
24791=13\cdot1907.
```

By the time filters7,11,13 have been installed, none of the three pairs
survives. An earlier removal only reinforces this conclusion. Every cited
divisor is proper. Thus even one-filter protection for every future prime
does not force a permanent member of the family.

## Functional formulation and quantifier boundary

Define E_p(x) to be one when p properly divides x or x+2, and zero otherwise.
For the protected family at a given incoming filter,

```math
\prod_{j=0}^{K-1}E_p(x_j)=0.
```

This says that the filter cannot reject every candidate. Collective survival
would instead require, for the finite original family C,

```math
\exists x\in C\quad\forall p\text{ relevant future prime}:\ E_p(x)=0.
```

The individual theorem has the reversed quantifiers: for every p some member
survives that filter, possibly a different member each time. The explicit
counterexample shows why interchanging those quantifiers is invalid.

For a fixed finite family, a finite horizon suffices: if B is its largest
endpoint, every composite endpoint has a prime divisor at most sqrt(B).
Having installed all missing primes through that bound certifies every
remaining pair. This does not prove that a pair remains.

## Research forks

### A. Preserve a configuration through conditioning

Seek an arithmetic invariant of the actual surviving family that guarantees
another protected configuration after the next filter. It need not retain
every original member or the original spacing. Existence and closure under
deletion both require proofs; the one-filter theorem alone supplies neither.

### B. Rebuild inside a fixed finite domain

Fix an initial finite candidate set C and a horizon covering all primes up
to sqrt(B). At each step choose a protected subfamily from the candidates
that have survived every preceding step. If such a subfamily exists before
every filter, the full surviving set stays nonempty to certification.

This permits the selected subfamily to change. It does not permit importing
new candidates outside C or moving the domain indefinitely. Proving the
reconstruction premise, rather than assuming it, is the research obligation.

### C. Adapt the spacing to the installed primes

Use the necessary divisibility conditions on d and the exact offset-coverage
test to search for admissible families. Increasing d can protect against old
filters while retaining p not dividing d for the next prime. But it also
increases the family's span; CRT does not guarantee a suitable location in
a chosen finite domain. This is a construction fork, not a persistence proof.

### D. Replace equal spacing with residue diversity

For one incoming p, any three existing starts occupying three distinct
residues suffice; arithmetic progression is unnecessary. More generally, a
family not contained in the two harmful classes has a survivor. Seek
structural relations that preserve such diversity in the conditioned set,
without assuming a density model or returning to cumulative shot counts.

The [Redundant Close-Pair candidate](redundant-close-pair-capacity.md) and
[Matching Attrition property](../properties/sieve-sequence/filtering-attrition-bound-close-pair-matching.md)
study related certificate persistence by another route. Their results are
not a proof of any of these forks.

## Open target and limitation

The proposed target is an admissible candidate-family invariant that can be
maintained or reconstructed through a specified finite certification horizon.
Its local protection clauses are proved above; its existence and preservation
clauses remain open. To infer infinitely many twin primes would additionally
require successful certified families with unbounded pair starts. A single
successful family, or translated old-filter candidates alone, does not suffice.

This direction complements the [Primorial-Neighbor research](primorial-neighbor-twin-pairs.md)
while retaining actual sieve candidates rather than selecting only centers
at primorials.
