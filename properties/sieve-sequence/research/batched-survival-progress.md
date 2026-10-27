# Batched Survival Research: Current Progress

**Status:** Research summary, updated 2026-10-28. Mathematical proofs and
finite observations are distinguished below. No infinite twin-prime theorem,
historical novelty, or Stainless verification of these research proofs is claimed.

## The Idea in Simple Terms

Start with one sieve sequence, expand it to accommodate many future filters,
then apply those filters together. This gives exactly the same final sequence
as applying the steps individually. The research question is whether this
description can guarantee twin-pair candidates survive in a particular finite
window, rather than somewhere in the enormous complete repeating cycle.

The earlier analysis uses a conservative survival score L=L_3, the classical
cubic Bonferroni certificate. Positive L guarantees an actual surviving pair.
Negative L does not prove absence of survivors. F is its positive density
benchmark, not a proved lower bound for actual L. Subsequent refinements use
fifth- and seventh-order scores L_5 and L_7; these must be distinguished from L_3.

## What Has Been Established

| Result | Status and scope | Derivation |
|---|---|---|
| One combined jump produces the exact destination sequence. | Proved finite identity, including anchor and cyclic wrap. | [Exact batching](../exact-batched-two-gap-survival.md) |
| Complete-period 2-gap counts multiply by r-2 per added prime r. | Proved global count; local placement does not follow. | [Exact batching](../exact-batched-two-gap-survival.md) |
| Cubic overlap weights give a conservative survival certificate. | Classical Bonferroni application; 36 declared early cases had positive certificates. | [Overlap audit and attribution](batched-survival-overlap-audit-2026-10-27.md) |
| The density term F is eventually positive for square destinations. | Proved analytically; this does not establish positivity of actual L. | [Main term and signed error](batched-survival-analytic-main-and-error.md) |
| L_next=L+A+N-R-J, with A>=0 and J>=0. | Proved exact transition; N and R are signed. | [Transport](batched-survival-propagation-check-2026-10-27.md) |
| Advancing the old head at fixed destination cannot decrease L. | Proved finite preservation of the same final window. | [Transport](batched-survival-propagation-check-2026-10-27.md) |
| The lost-region upper budget R_cap is negligible relative to F. | Proved actual upper bound R<=R_cap; not an absolute bound on R. | [Component bounds](batched-survival-component-bounds.md) |
| The shared-region cost J is negligible relative to F. | Proved actual population and weight bounds, using ordinary PNT. | [Filtered shot bound](batched-survival-filtered-shot-bound.md) |
| The absolute fresh-region contribution is negligible relative to F. | Proved actual finite bound and eventual comparison, using quantitative classical PNT. | [New-region bound](batched-survival-new-region-bound.md) |
| The total possible loss across a growing block is negligible relative to the starting F. | Proved for actual transitions; positive certificates throughout require a positive starting reserve. | [Block reserve](batched-survival-block-reserve.md) |
| Fixed-target purification gain exactly repays the initial cubic penalty. | Proved; the actual twin count stays unchanged. | [Penalty exhaustion](batched-survival-propagation-check-2026-10-27.md#purification-repays-exactly-the-fixed-target-penalty) |
| Fifth and higher odd orders have no shared-region penalty. | J_5=0 exactly for square-rule transitions; cubic J can be nonzero. | [Fifth-order transport](batched-survival-propagation-check-2026-10-27.md#fifth-order-weights-eliminate-the-shared-penalty) |
| The seventh-order score differs from the true twin count by a small nonnegative remainder. | Proved: L_7=S-H_8 and H_8/F=O(1/log^2 p). No positive count follows. | [Seventh-order remainder](batched-survival-propagation-check-2026-10-27.md#seventh-order-penalty-is-small-relative-to-the-cubic-benchmark) |
| A positive starting reserve retains a positive L_7 across any fixed-factor head interval. | Conditional retention, possibly from an L_3 seed; no fresh-pair or renewal theorem. | [Fixed-factor retention](batched-survival-propagation-check-2026-10-27.md#conditional-retention-through-a-fixed-factor-head-interval) |
| Seventh/eighth individual moment errors have nonzero negative normalized limits. | Proved for E_k/(H*delta), k=7,8; no combined-error limit or sign follows. | [Density calibration](batched-survival-analytic-main-and-error.md#6-high-order-moments-require-nonnegligible-density-corrections) |
| The fifth-order penalty is a balanced squarefree triple-product count plus a small remainder. | Proved L_5=S-T_33-D with D>=0 negligible relative to F; T_33 is unestimated. | [Triple-product reduction](batched-survival-analytic-main-and-error.md#7-the-fifth-penalty-reduces-to-a-balanced-triple-product-correlation) |
| Original square windows contain many candidates with a prime first endpoint and a prime-or-semiprime partner. | Classical rough Chen consequence; survives filters below Z, but final prime partners remain uncounted. | [Rough Chen input](batched-survival-classical-sieve-input.md#7-a-rough-chen-family-at-the-original-square-jump) |
| Actual first rejections have a uniform per-prime upper bound. | Whole-range bound has the same scale as supply; a fixed late logarithmic band cannot first reject more than half the family. The complement may die earlier. | [Uniform bound and band consequence](batched-survival-classical-sieve-input.md#8-a-uniform-upper-bound-for-each-first-rejection-prime) |

For the square rule, p is the starting prime, s its successor, q the first
prime greater than p squared, and t the first prime greater than s squared.
The proved bounds combine as

```math
\begin{aligned}
|N|&\le\frac{35}{6}(t^2-q^2),\\
B(p)&:=|N|+R_{\mathrm{cap}}+J\ge0,\\
B(p)/F(p,q)&\longrightarrow0,\\
L(s,t)&\ge L(p,q)-B(p).
\end{aligned}
```

Thus, for every fixed eta>0, all sufficiently late transitions satisfy

```math
L(p,q)\ge\eta F(p,q)
\quad\Longrightarrow\quad
L(s,t)\ge\frac\eta2F(p,q)>0.
```

This is a proved conditional next-step result. The premise about actual L
has not been proved eventually. The conclusion uses the OLD F(p,q).

The [block proof](batched-survival-block-reserve.md) strengthens this to a
whole consecutive run. For heads from p to the last prime at most
p(1+1/(log p)^3), the number m of transitions is asymptotic to p/(log p)^4,
and the actual cumulative budget satisfies

```math
\frac{\sum_{i<m}B_i}{F_0}=O(1/\log p)\longrightarrow0.
```

This estimate is proved without a positive-margin assumption. If the starting
L_0>=eta F_0 for fixed eta>0, every step in that finite block eventually
satisfies L_j>=eta F_0/2>0. The starting benchmark is used throughout;
the reserve is not halved at each step. Overlapping windows may certify the
same twin pair, and the starting premise remains unproved at unbounded heads.

## Higher-Order Refinement

The signed-gain audit shows that fixed-target purification improves the
certificate by removing its old negative penalties; it does not create twins.
Changing the weights gives a more useful simplification: fifth-order scores
have J_5=0 exactly. Seventh-order scores satisfy L_7=S-H_8, where H_8 counts
eight-hit candidates and is negligible relative to the original cubic F.

This yields a stronger retention range. For any fixed C>1 and eta>0,
sufficiently late starting primes satisfy

```math
L_3(p,q_p)\ge\eta F_0
\quad\Longrightarrow\quad
L_7(r,q_r)\ge\frac\eta2F_0>0
\quad(p\le r\le Cp,\ r\text{ prime}).
```

Here q_r is the first prime above r squared and F_0=F(p,q_p). An L_7 seed
of the same size also suffices. The conclusion preserves L_7, not necessarily
the original L_3. It follows by retaining initial twins above the moving
lower window boundary and bounding the remaining certificate penalty.
It guarantees no new pairs. Constants and thresholds depend on C and eta;
one cannot take C to infinity at a fixed starting seed.

## Density Calibration and the Remaining Product Correlation

Near-exactness of L_7 does not justify replacing each overlap count by its
full-cycle density prediction. Actual seventh and eighth moments are
negligible relative to H*delta, but their density terms have positive limits
on that scale. Their individual errors therefore have nonzero negative
normalized limits. The alternating sum of errors used by a certificate is
a separate quantity; no one-sided estimate sufficient for positive survival
is obtained here.

The fifth-order remainder has a concrete refinement:

```math
L_5=S-T_{33}-D,\qquad
D\ge0,\qquad D/F=O(1/\log^2p).
```

T_33 counts pairs two apart where each endpoint is a squarefree product of
three distinct batch primes. It is the only possible leading fifth-penalty
contribution on this scale, but its abundance, negligibility, and comparison
with S are not established. This identifies a shifted-product correlation
to investigate; defining the population is not estimating it.

The same bounded hit count makes a ninth-order score equal S exactly.
Higher order alone can therefore remove representation error without
providing a positive lower bound. Fresh supply needs independent arithmetic
information beyond these identities and calibrations.

## A Classical Sieve Input and a Longer Destination

The [lower-sieve audit](batched-survival-classical-sieve-input.md) checks the
local root densities, weighted remainders and uniform dimension condition
against the classical Diamond–Halberstam–Richert sieve. For the square rule,
the tested lower-sieve parameter tends to4, below its positive threshold
approximately4.266. This particular standard bound supplies no positive
old-candidate lower main term; it does not show absence of candidates or
failure of the branch.

For q the first prime above p to the power11/5, the parameter instead tends
to22/5. The verified theorem gives the actual local old-candidate bound

```math
C(p,q)\gg\frac{q^2-q-2}{(\log p)^2}.
```

The cubic density factor also has a positive limit under this rule. These
are proved classical arithmetic inputs, not empirical observations or
assumptions of local full-cycle proportions. The destination has changed;
the square-rule transport and small-penalty results cannot be imported.

These candidates still face the remaining primes from p to q. Sifting all
the way to q gives parameter2 in the same tested theorem, so it yields no
positive final-survivor bound. The new candidate input does not estimate
T_33 or renew a twin reserve. The precise classical statements and primary
references are in the linked derivation.

The [prime-endpoint refinement](batched-survival-classical-sieve-input.md#6-a-large-subfamily-with-an-already-prime-endpoint)
now gives a stronger independent input from the classical linear sieve:
there are at least a positive constant times H/log squared p candidates
whose first endpoint is prime and whose partner has no prime factor below
z=(q^2-3)^(6/25). Since p<z<q eventually, this family survives an initial
segment of the remaining batch. Its partner is either prime or composite
with two to four prime factors, counted with multiplicity. Every remaining
rejection must act on that partner, with a prime at least z. The composite
partner population is still unestimated; it could account for the whole
guaranteed family. Thus this strengthens partial survival, without proving
final twin survival or a positive cubic score. The abundance refinement
also permits any fixed destination exponent greater than2, with a suitable
cutoff and constants depending on that exponent.

## Stronger Classical Input at the Original Square Rule

The [rough Chen refinement](batched-survival-classical-sieve-input.md#7-a-rough-chen-family-at-the-original-square-jump)
now establishes actual old-candidate abundance at the original square rule
too. It uses the stronger published Chen input, with Iwaniec's roughness
improvement as stated by Green and Tao, rather than the dimension-two
lower bound tested above. Put X=q^2-3 and Z=(X/2)^(3/11). In the
interval (X/2,X], contained in W_q, there are at least a positive constant
times H/log squared p
candidates with a prime first endpoint and a partner that is prime or a
product of two distinct primes greater than Z. Eventually p<Z<q, so these
candidates survive every filter below Z. The derivation includes the
negligible deletion of prime-square partners and the precise source scope.

This removes raw square-rule candidate abundance as a missing input. It
also narrows this guaranteed family's composite partners from up to four
factors to exactly two. Those semiprime partners can still account for the
whole lower bound: their smaller factor lies between Z and q and can
reject the pair later. A hypothetical last twin would force precisely
that all-semiprime outcome, which is compatible with the classical input.
Final twins, positive L_3 and reserve renewal remain unproved. No estimate
subtracting every composite partner from the earlier family is asserted.

## Quantitative First-Rejection Bounds

The [uniform switched estimate](batched-survival-classical-sieve-input.md#8-a-uniform-upper-bound-for-each-first-rejection-prime)
now bounds actual semiprime partners. With Y=X+2, the number assigned to
a particular smaller prime factor u is at most K*Y/(u*log squared Y),
with K independent of u. Summing over a set of smaller factors bounds
their first rejections by K*Y/log squared Y times that set's reciprocal-prime
sum. This follows from Green and Tao's coefficient-uniform theorem; the
derivation checks the local factors and the conversion from Fourier norm
to count. The whole semiprime range gives O(Y/log squared Y), the same
scale as the guaranteed family. It is not a sharp enough comparison to
force a positive prime-partner count.

The [late-band consequence](batched-survival-classical-sieve-input.md#9-late-filters-cannot-exhaust-the-family-by-first-rejections)
proves that some fixed eta in (6/11,1) leaves at least half of G outside
the class first rejected in [q^eta,q), eventually. These members are twins
or semiprimes first rejected earlier. It does not prove that half the
family reaches q^eta. Under a hypothetical last twin, that entire complement
must be rejected earlier, consistently with the hypothesis. The band is
narrow in logarithmic exponent, not additive length; eta and the onset
are not numerically evaluated. Actual rejection-location control is proved,
while final survival remains open.

The [exact-product-window refinement](batched-survival-classical-sieve-input.md#10-keeping-the-exact-product-window-in-the-upper-bound)
retains v>u and X/2<uv-2<=X rather than counting every v<=N. Its
integer interval has length L<=ceil(N/2). A finite interval kernel and
Hölder's inequality give a bound proportional to
N^(3/4)*L^(1/4)/(log N)^2, with unchanged polynomial coefficients. Compared
with the displayed Section8 bound before coarsening constants, the ratio
of these upper expressions has a uniform asymptotic upper bound of
(2/3)^(1/4). This
does not assert that the actual semiprime population falls by that factor.
The ambient N^(3/4) remains, the total order is unchanged, and no favourable
comparison with the Chen lower bound or positive twin count follows.

## What Remains Open

The branch is retained provisionally. The results rule out automatic reserve
renewal from small losses, purification gain interpreted as fresh supply,
and negligible individual density errors inferred from near-exact scores.
They do not invalidate the proved batching, transport or retention results.
The next priority test is an independent arithmetic estimate that strengthens
the survival argument. If a proposed tactic only reformulates the unknown
twin count, that is a reason to pause that tactic, not discard all results.

The bound consumes part of the guaranteed reserve. We have not proved that
the reserve is retained or replenished through arbitrarily many jumps.
Small relative changes at each step can accumulate; neither the finite sample
nor the limit B/F->0 closes that argument. The block proof controls cumulative
loss over its specified range, but does not renew a reserve for infinitely
many consecutive blocks.

The next analytical target is a comparison of actual accumulated improvements
and losses that sustains a positive certificate, or forces positive
certificates at unboundedly many destination heads. A sufficient condition
must be distinguished from a proof that real sieve sequences satisfy it.
Higher-order retention improves the certificate and the range over which an
existing reserve is protected, but a source of fresh twins or an independently
sustained reserve remains unproved. The fixed-target repayment identity
alone cannot supply it.
Changing the destination rule is allowed, but the square-rule estimates
cannot automatically be transferred to another rule.

The [generic window-survival candidate](../../../candidates/batched-window-survival.md)
and [short-window discrepancy bound](../batched-short-window-discrepancy-boundary.md)
remain open. Complete-period uniformity and a positive benchmark do not
establish a positive count in a prescribed shorter window. Classical inputs
and their primary references are recorded in the linked derivations.
