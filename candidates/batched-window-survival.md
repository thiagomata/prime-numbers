# Batched Window Survival from a Known Sieve Cycle

**Candidate hypothesis:** OPEN — no positive generic lower bound is proved.

**Conditional implications and batch identities:** Mathematically proved below
or in the linked established properties; Stainless verification is not claimed.

**Empirical status:** BOUNDED AUDIT — 36 starting-head/destination cases checked
with exact overlap certificates. No generic threshold or uniform positive
bound is established; see the finite evidence section below.

See the [current progress summary](../properties/sieve-sequence/research/batched-survival-progress.md)
for the analytical proof chain and the remaining actual-margin obligation.

## Research Goal

Start with a complete, known sieve cycle at head p, including its period, actual
gap arrangement, and total number of 2-gaps. Expand to a later head in one batch,
then apply all new prime filters together. Seek a generic positive lower bound
for surviving pairs in the destination safe window, derived from the starting
cycle and the combined arithmetic rather than intermediate recursive states.

A large empirically calculated cycle can supply a concrete starting input.
Its full arrangement permits exact local calculations. A theorem expressed
only in terms of the total number of 2-gaps would be stronger: it must justify
why that total suffices for the actual sieve cycles under consideration.

## Fixed Setup and Exact Batch Construction

Let p>=5 be a prime head, with every prime smaller than p already installed.
Let q be any later prime head. Its choice is part of the research question:
it may be the next prime, a longer batch destination, or the first prime above
p squared. The last rule was the original example, not a requirement of the
batch construction. Define

```math
\begin{aligned}
M_p&=\prod_{\substack{r<p\\r\ \mathrm{prime}}}r,\\
\mathcal B&=\{r:r\ \mathrm{prime},\ p\le r<q\},\\
K&=\prod_{r\in\mathcal B}r,\qquad M_q=M_pK,\\
W_q&=\{a\in\mathbb Z:q\le a,\ a+2<q^2\}.
\end{aligned}
```

Let G_p count cyclic 2-gaps in one complete old period. Repeating the old gap
cycle K times, filtering the union of multiples of primes in the batch, and
reconstructing cyclic gaps with final anchoring at q gives exactly the q sequence.
Over its complete period,

```math
G_q=G_p\prod_{r\in\mathcal B}(r-2).
```

These are the established [exact batch identities](../properties/sieve-sequence/exact-batched-two-gap-survival.md).
The total G_q and its local portion in W_q are different quantities.

The initial and surviving local pair-start sets have direct descriptions:

```math
\begin{aligned}
\mathcal A&=\{a\in W_q:\gcd(a(a+2),M_p)=1\},\\
\mathcal S&=\{a\in\mathcal A:\gcd(a(a+2),K)=1\}.
\end{aligned}
```

Equivalently, each old cyclic pair start a_0 in [0,M_p) contributes its
translated copies a=a_0+jM_p that lie in W_q. Such a copy survives exactly when
gcd(a(a+2),K)=1. This describes the entire batch without following intermediate
rotations or rejection histories.

## Candidate Generic Threshold Theorem

Choose a specified prime-valued destination rule Q(p)>p. Seek fixed integers
X>=1, Y>=1, and a threshold p_0 such that

```math
\forall p\ge p_0\text{ prime},\qquad
G_p\ge X\quad\Longrightarrow\quad |\mathcal S|\ge Y,
\qquad q=Q(p).
```

The original square-jump subcandidate specifies
Q(p)=min{r>p^2:r prime}; it remains open. Other rules can be investigated without
assuming that this particular rule must succeed. The destination rule should be
specified from the research inputs, not selected after finding a future twin.

No values of X, Y, or p_0 are established for such a theorem. This is the proposed
bound, not a consequence already obtained from the complete-period count. A
quantitative fork seeks |S|>=Y(p,q,G_p), positive for all sufficiently large p
under the chosen destination rule.
Another fork can retain information about the old arrangement, provided its
extra hypotheses are explicitly proved for the relevant sieve sequences.

## Exact Destruction Counts and Sufficient Certificates

Let C=|A| and let D count initial pairs rejected by at least one new filter.
Let V be the old accepted values in the same endpoint window, and T the number
of distinct such values removed by the entire batch:

```math
\begin{aligned}
\mathcal V&=\{n\in\mathbb Z:q\le n<q^2,\ \gcd(n,M_p)=1\},\\
T&=|\{n\in\mathcal V:\gcd(n,K)>1\}|,\\
D&=|\{a\in\mathcal A:\gcd(a(a+2),K)>1\}|.
\end{aligned}
```

Because p>=5, the old filters include 2 and 3. Distinct candidate pairs have
disjoint endpoints: two pairs sharing an endpoint would require three accepted
values x,x+2,x+4, one of which is divisible by 3. Thus each removed value can
destroy at most one initial pair. Consequently,

```math
\begin{aligned}
D&\le T,\\
|\mathcal S|&=C-D\ge\max(0,C-T).
\end{aligned}
```

In particular, C>T certifies a survivor. More generally, any proved upper bound
D<=U<C is sufficient. A pair-specific U can be sharper than counting all removed
values, since many removed values are not endpoints of initial pairs.

Filter order changes neither the retained set nor the total number of distinct
removed values. Deletion is a union. A static sum of separate prime-hit counts
can count a value repeatedly; that sum is a conservative upper bound, not an
exact distinct-removal count. Overlap is therefore an issue for that chosen
estimate, not a defect in the exact batch construction.

## Why a Generic Positive Bound Would Suffice

Every pair in S avoids all primes below q, has both endpoints at least q, and
has both endpoints below q squared. A composite endpoint would have a prime
factor smaller than q, contradicting survival. Thus every member of S is a
twin-prime certificate.

The complete-period formula makes G_p unbounded as p grows: after the small
initial filters each new prime multiplies the count by r-2>1. Consequently any
fixed threshold X is eventually reached. If the candidate theorem holds with
Y>=1, it supplies a surviving pair for arbitrarily large p, whose start is at
least q=Q(p)>p. These starts are unbounded, hence there are infinitely many
distinct twin pairs. The windows need not be disjoint for this implication.

This recurrence would be a consequence of the generic theorem itself. It is
not an additional premise to attach to a collection of isolated computations.

## Low-Order Overlap Certificate and Finite Evidence

For each old local pair a, let h(a) count distinct batch primes dividing a(a+2),
and let I_k=sum over a of binomial(h(a),k), with I_0=C. Classical Bonferroni gives

```math
|\mathcal S|\ge L_3=C-I_1+I_2-I_3.
```

The [overlap audit](../properties/sieve-sequence/research/batched-survival-overlap-audit-2026-10-27.md)
derives the bound, cites Pollack's exposition, supplies exact old-cycle/CRT
expressions for the moments, and includes its executed diagnostic. Across nine
heads p=5 through 31 and four destination rules, L_3 was positive in all 36
cases. The first-order pair-incidence bound C-I_1 was positive in 27; all nine
square-jump cases were rescued by the cubic correction.

For p=31, q=967, the initial population was 31005, the cubic certificate
guaranteed 5591 survivors, and the independent prime sieve found 7688. This is
finite evidence for these cases. The diagnostic computes exact hit patterns;
it does not prove uniform moment estimates or generic positivity of L_3.

The [analytical main-term and error study](../properties/sieve-sequence/research/batched-survival-analytic-main-and-error.md)
separates L_3 into an explicit density term and a signed local discrepancy.
It proves that the cubic density factor is at least 1/16-3/(4p)>0 when
p>=13 and sum over batch primes of 2/r is at most 3/2. Mertens' estimate and
Bertrand's theorem imply eventual positivity of this density factor for the
original square-jump rule. It also proves that a particular termwise absolute
floor-error budget cannot certify survival when the window is shorter than the
old period. Neither statement settles actual local positivity: controlling the
combined signed discrepancy remains open, and sharper error estimates are
not ruled out.

The [signed-error and propagation check](../properties/sieve-sequence/research/batched-survival-propagation-check-2026-10-27.md)
proves that L_3 cannot decrease when the starting head advances while the
destination stays fixed. For a moving destination, its exact transport is
L_next=L_current+A+N-R-J, where A>=0 is the fixed-target improvement, N and R
are signed new/lost-region contributions, and J>=0 is the extra shared-region
overlap penalty. Each shared endpoint receives at most one new prime hit;
certified pairs receive none. Nine early square-jump error checks and moving
balances passed, but positive actual-margin preservation remains open.
Fixed-target preservation certifies one
finite window and by itself supplies no infinite induction.

The [component-bound proofs](../properties/sieve-sequence/research/batched-survival-component-bounds.md)
establish R<=ceil(min(t-q,q^2-q-2)/6) for the lost-region contribution. Under
the square-jump rule this upper budget is negligible relative to the positive
density main term F at sufficiently large heads, which is not a statement
about actual L. They also prove J<=10K_1+9K_2 at every square-rule p>=5, where
K_i counts shared candidates receiving exactly i new prime hits. This initial
per-pair estimate alone did not bound the affected populations.

The [filtered shot bound](../properties/sieve-sequence/research/batched-survival-filtered-shot-bound.md)
now supplies an independent population estimate. For square destinations,
either t=q and J=0, or q<s^2 and every new-hit endpoint has a prime cofactor.
This proves K_1+2K_2<=bP and J<=3K_1+K_2<=3bP, with b counting primes in
[q,t) and P counting primes in [s,q). The ordinary prime number theorem then
proves actual J/F->0. Together with the R cap, this establishes eventual
smallness of the positive loss budget relative to F. It is a proved property,
not an imposed hypothesis.

The [new-region bound](../properties/sieve-sequence/research/batched-survival-new-region-bound.md)
also proves |N|<=35(t^2-q^2)/6 and, using the quantitative classical prime
number theorem, |N|/F->0. Thus the actual nonnegative combined budget
B=|N|+R_cap+J satisfies B/F->0 and L_next>=L_current-B. For every fixed
eta>0, sufficiently late transitions with L_current>=eta F have
L_next>=eta F/2>0, measured in the old F. The positive-margin premise has
not been proved eventually, and this implication halves rather than
reproduces the reserve. Sustaining or replenishing an actual positive margin
remains open; no infinite induction follows from small relative losses alone.

The [block reserve proof](../properties/sieve-sequence/research/batched-survival-block-reserve.md)
now controls actual cumulative losses across roughly p/(log p)^4 consecutive
heads in [p,p(1+1/(log p)^3)]. Their sum divided by the starting F tends to
zero. Consequently a fixed positive starting reserve protects every stage
of that finite block. The starting premise and its renewal between blocks
remain open; overlapping windows need not supply distinct twin pairs.

The [higher-order analysis](../properties/sieve-sequence/research/batched-survival-propagation-check-2026-10-27.md#fifth-order-weights-eliminate-the-shared-penalty)
eliminates the shared penalty exactly for fifth and higher odd orders.
It also proves L_7=S-H_8 with H_8/F->0. A sufficient positive starting
L_3 or L_7 reserve then retains a positive L_7 throughout heads [p,Cp] for
any fixed C>1, eventually. This is not preservation of L_3 over that larger
range. It retains existing twins, supplies no fresh pairs, and does not allow
C to grow without bound at one fixed seed. Actual reserve renewal remains open.

The [density calibration](../properties/sieve-sequence/research/batched-survival-analytic-main-and-error.md#6-high-order-moments-require-nonnegligible-density-corrections)
proves that individual E_7/(H*delta) and E_8/(H*delta) have nonzero negative
limits, despite near-exact L_7. It does not determine the combined signed error.
The same analysis reduces the fifth penalty to a count T_33 of squarefree
three-batch-prime endpoint products two apart, plus a negligible nonnegative
remainder. T_33 is only a possible leading contribution: neither its size nor
its comparison with the twin count S is proved. Ninth-order equality with S
also confirms that increasing the truncation order alone is not a positive
survival estimate.

The [classical lower-sieve audit](../properties/sieve-sequence/research/batched-survival-classical-sieve-input.md)
provides an independent local input for a modified rule: when q is the first
prime above p^(11/5), the actual old-candidate count is at least a positive
constant times (q^2-q-2)/log^2(p), eventually. The cubic density factor is
also eventually positive. Under the square rule the tested standard DHR
lower main term is zero, a limitation of that theorem/level/cutoff only.
The Section4 count alone leaves the whole remaining batch uncontrolled;
no final-survivor or T_33 bound follows, and the square-specific retention
estimates do not automatically transfer.

The [prime-endpoint refinement](../properties/sieve-sequence/research/batched-survival-classical-sieve-input.md#6-a-large-subfamily-with-an-already-prime-endpoint)
strengthens partial survival. It proves a subfamily of size at least a
positive constant times H/log squared p whose first endpoint is prime and
whose partner avoids every prime below z=(q^2-3)^(6/25). Eventually p<z<q,
so this family survives an initial segment of the remaining batch. Its
partner is prime or has two to four prime factors counted with multiplicity.
Rejection must act on that partner using a prime at least z. The composite
partner population remains unestimated and might exhaust the guaranteed
family; neither final survival nor a positive cubic certificate follows.
The same classical input permits any fixed destination exponent greater
than2 with a suitable cutoff, but does not establish the square boundary.

A stronger [rough Chen input](../properties/sieve-sequence/research/batched-survival-classical-sieve-input.md#7-a-rough-chen-family-at-the-original-square-jump)
does establish actual old-candidate abundance at the original square rule.
With X=q^2-3 and Z=(X/2)^(3/11), its subfamily in (X/2,X] has at least a
positive constant times H/log squared p members. Each first endpoint is
prime; the partner is prime or a product of two distinct primes greater
than Z. Since p<Z<q eventually, all survive filters below Z. This uses the
classical Chen theorem with Iwaniec's roughness improvement as formulated
by Green and Tao; it does not improve the earlier DHR lower function.
The semiprime partners can still exhaust the guaranteed family. The upper
bound below is not sharp enough to separate a positive prime-partner count.
A hypothetical last twin is compatible with that outcome. Final
prime partners, positive L_3 and reserve renewal therefore remain open.

The [uniform first-rejection bound](../properties/sieve-sequence/research/batched-survival-classical-sieve-input.md#8-a-uniform-upper-bound-for-each-first-rejection-prime)
now proves at most K*Y/(u*log squared Y) members can be assigned to a
particular smaller factor u, where Y=q^2-1. Summing over smaller factors
gives an actual upper bound weighted by their reciprocal-prime sum. For
the whole semiprime range this remains O(Y/log squared Y), the same scale
as the lower supply, without a favourable constant comparison.

The [late-band consequence](../properties/sieve-sequence/research/batched-survival-classical-sieve-input.md#9-late-filters-cannot-exhaust-the-family-by-first-rejections)
proves that for some fixed eta in (6/11,1), at least half of the family
is outside the class first rejected in [q^eta,q), eventually. That
complement consists of twins or semiprimes rejected earlier; it is not
a population known to reach q^eta. A later larger factor does not count
as another first rejection. The band is narrow in logarithmic exponent,
not additive length. This restriction remains compatible with a last twin.

## Development Plan and Remaining Obligations

The research direction is retained provisionally: the failed shortcuts do
not refute its proved identities. Further priority depends on an independent
arithmetic estimate improving the survival argument. Small losses alone,
purification as assumed fresh supply, and near-exact scores as assumed
accurate individual density predictions are insufficient. A tactic yielding
only another formulation of the unknown count should be paused and reassessed.

1. Select an existing complete cycle with known period, G_p, and gap arrangement.
2. Calculate its old candidate population in the fixed destination window.
3. Compare destination rules using the same old cycle. Analyze the union of
   divisibility conditions and the low-order overlaps without intermediate
   coordinate changes. Bound their actual local counts rather than assuming
   complete-period proportions.
4. Seek a lower bound uniform across actual sieve cycles, identifying exactly
   what input beyond G_p is required, if any.
5. State and prove explicit thresholds or a positive quantitative bound.

Computational speed is not a validity condition: a slow exact construction is
still a valid mathematical description. A bound that allows too much destruction
may fail to certify survival, but that does not refute survival or batching.
Likewise, obtaining the same q sequence is expected; the research aim is to
discover useful properties of the combined construction.

The open mathematical obligation is local: derive a positive bound for S rather
than substitute complete-period density for its actual window population. No
counterexample or proof of the stated generic threshold is claimed here.

## Related Results and Evidence Boundaries

- [2-gap endpoint isolation](../properties/sieve-sequence/two-gap-isolation-after-filter-three.md)
  justifies the distinct-removal certificate.
- [Local surplus](local-surplus.md) treats a related consecutive-head transition;
  its notation and measurements must not be transferred to this longer batch.
- [Fixed-window shot-budget audit](../properties/sieve-sequence/research/fixed-window-shot-budget-2026-10-26.md)
  demonstrates finite certificates, not this universal threshold statement.

This is an unnumbered research proposal. No historical novelty or established
proof of twin-prime infinitude is asserted.
