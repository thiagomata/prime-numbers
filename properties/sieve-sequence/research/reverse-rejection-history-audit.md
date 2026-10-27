# Bounded audit of reverse rejection histories

**Status:** Research audit. The finite trace is checked by exact integer
arithmetic; the finite-pattern CRT construction has an elementary proof below.
Neither is a counterexample to twin-prime infinitude or a proof against every
possible backward argument. No Stainless verification or novelty is claimed.

## Question

Assume a hypothetical final twin pair (L,L+2). Every later candidate would
need a proper rejecting prime before head arrival. Does reconstructing the
parents of neighboring candidates expose a joint inconsistency that is hidden
when they are treated separately?

This bounded audit tests that ingredient in an actual value-aligned sieve.
It does not assume the selected numerical cluster lies beyond a last twin
pair. No such last pair is known. A finite counterexample tests a proposed
local implication, not the global last-pair assumption.

## Exact local trace

Take the accepted integers in the closed interval [157,173]. With filters2,3,5
installed, the complete list is

```math
157,161,163,167,169,173.
```

The middle four endpoints form the two candidate pairs (161,163),(167,169),
with intervening gap word [2,4,2]. Exact transitions give:

| Installed filters | Accepted integers in [157,173] | Internal gaps |
|---|---|---|
| 2,3,5 | 157,161,163,167,169,173 | 4,2,4,2,4 |
| 2,3,5,7 | 157,163,167,169,173 | 6,4,2,4 |
| 2,3,5,7,11 | 157,163,167,169,173 | 6,4,2,4 |
| 2,3,5,7,11,13 | 157,163,167,173 | 6,4,6 |

These lists follow by testing coprimality with each listed filter. All values
are above the incoming heads, so self-prime protection and head rotation do
not change this local calculation. This is a bounded slice of the actual
sieve, not a freely chosen deletion schedule.

Filter7 removes161=7*23. This merges the gap from157 to161 with the gap
from161 to163:

```math
(161-157)+(163-161)=4+2=6.
```

Filter11 removes nothing in this slice. Filter13 removes169=13^2 and merges
the gaps around it:

```math
(169-167)+(173-169)=2+4=6.
```

Reverse these steps with the known filter and absolute coordinates. Insert169
between167 and173, splitting6 into2+4; then insert161 between157 and163,
splitting6 into4+2. Both insertions restore exactly the correct previously
accepted multiples. The final internal gaps [6,4,6] contain no2-gap, although
the earlier slice contained two.

Thus different prime filters can destroy both neighbors while respecting
actual first-rejection times, endpoint sharing, gap sums, and inverse merges.
Their start separation is6: it prevents a shared rejecting prime>=5, not the
two distinct rejecting primes7 and13. This confirms the boundary recorded
in [Protected arithmetic families](../../../candidates/protected-arithmetic-families.md).

## A general control: fixed finite shapes can be translated to fail

Let S be a finite old-prime filter set containing2,3. Suppose a positive
translation a0 of a finite endpoint-offset pattern H survives those filters.
Let its designated candidate pairs have offsets (h_i,h_i+2), with i=1,...,K.
Put

```math
W=\prod_{s\in S}s.
```

Choose distinct primes q_i larger than every old filter and larger than the
span of H. Impose the congruences

```math
\begin{aligned}
a&\equiv a_0\pmod W,\\
a&\equiv-h_i\pmod{q_i}\quad(1\le i\le K).
\end{aligned}
```

The moduli are pairwise coprime, so CRT supplies a solution and arbitrarily
large positive representatives. Choose one with all endpoints larger than
all q_i. Then

```math
\begin{aligned}
\gcd(a+h,s)&=1 &&(h\in H,\ s\in S),\\
q_i&\mid a+h_i,\qquad a+h_i>q_i &&(1\le i\le K).
\end{aligned}
```

Every designated pair therefore exists at the old-filter stage and has a
proper future rejecting factor. The offsets and all distances are unchanged.
Fixing a modulo W also preserves the entire old-stage acceptance pattern at
every relative integer position, including any intervening rejected values.
Thus an exact seeded finite gap shape can be preserved, not just its endpoints.

The q_i are not asserted to be the first rejecting primes; an earlier prime
may remove a member first. Actual first rejectors still exist and are coherent
because these are real composite integers. All designated pairs are absent
after a sufficiently long finite batch. Reversing that genuine history cannot
create an arithmetic inconsistency.

This is an elementary CRT control argument, consistent with the old-filter
admissibility analysis in the linked candidate. It is not a new assertion
about distribution or short-window placement.

## What the control rules out

A universal claim of the following kind is false:

> A fixed finite pattern of candidate endpoints, protected against the old
> filters and considered only up to translation, forces one of its pairs to
> survive all future filters.

For any realizable such shape, the construction gives translations where
every designated pair is composite. Absolute coordinates matter. Recording
all inverse merges of one of those genuine translations does not repair the
claim; the history is already consistent.

## What it does not rule out

- A relation anchored to the actual hypothetical last primes L and L+2.
  The CRT translation does not preserve arbitrary relations to fixed anchors
  or guarantee that a specified translated endpoint is prime.
- A theorem in a prescribed finite domain with a fixed certification horizon.
  Arbitrarily large CRT representatives do not provide a counterexample in
  that domain.
- An invariant coupling an unbounded family of stages, including a genuine
  return or reconstruction theorem. This audit treats bounded configurations.

These are exclusions from the counterargument's scope, not evidence that
the remaining routes succeed. Any claimed new constraint must state which
additional arithmetic premise it uses.

## Assessment against existing work

The [Coherent Head-Suppression property](../coherent-head-suppression-is-shifted-prime-shot-coverage.md)
already encodes the last-pair assumption as eventual coverage of prime heads
by actual shifted prime-multiple trains. It is an equivalence, not a proof
that such eventual coverage is impossible.

The [First-Deletion Reindexing property](../accepted-strike-first-deletion-coordinate-reindexing.md)
similarly shows that a particular first-deletion variance calculation returns
exactly to the original strike energy. Its algebra alone provides no new gain.

The present trace confirms a parallel caution for inverse merges: forward
and reverse bookkeeping recover coherent divisibility, without automatically
adding a contradiction. It does not establish a new obstruction beyond the
underlying arithmetic.

## Outcome

The bounded inspection found no additional incompatibility. A useful next
claim would need to incorporate absolute arithmetic tied to the hypothetical
last pair, a prescribed finite horizon, or a nontrivial cross-stage theorem.
No such claim is proved here, and no further candidate is introduced from
the inverse-merge identities alone.
