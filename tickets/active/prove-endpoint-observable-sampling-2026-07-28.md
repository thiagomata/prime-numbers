# Prove The Endpoint-Observable Sampling Bound

**Created:** 2026-07-28
**Status:** In progress
**Candidate:** #13 uniform local observable sampling, restricted to the two
endpoint observables
**Depends on:**
`verify-19-21-escape-wall-2026-07-27.md`,
`algebraic-conditioned-survival-2026-07-27.md`,
`prove-accepted-strike-mean-square-2026-07-27.md`

> Persistent-memory ticket. Update continuously per `TICKET_DISCIPLINE.md`.

## START HERE

Candidate #23's generic algebraic audit is complete; its arithmetic
mean-square estimate remains open. The active top-candidate algebra work is
now candidate #13, restricted to the unsigned endpoint indicator and signed
left-minus-right endpoint observable actually consumed by candidate #21.

Do not attempt a theorem for every bounded local observable. Do not collect
more data. Begin with the exact joint feasible region of the two endpoint
hit counts.

## Goal

Prove, refute, or classify the weakest noncircular aggregate estimate for
candidate #13's endpoint-sampling bias `beta_i` and signed imbalance
`Delta_i` that composes with candidates #23, #22, and #21.

The ticket is complete when either:

1. a sound algebraic bound for `mathcal E_beta` and `mathcal E_Delta` is
   proved and promoted to `properties/`; or
2. all generic finite-population/capacity routes are reduced to a precise
   missing residue-correlation theorem, with failed paths recorded.

## Strategy

Work with the two endpoint classes directly.

1. Replace the broad observable-sampling statement by left and right endpoint
   hit counts.
2. Derive their exact feasible polygon from endpoint isolation, the anchor
   population, and the hit population.
3. Maximize the exact #21 scalar energy over that polygon.
4. Compare the sharp combinatorial envelope with candidate #21's allowance.
5. If the envelope is too large, identify the weakest additional arithmetic
   constraint on the actual incoming residue class.

This route was selected because separate absolute bounds on `beta_i` and
`Delta_i` may double-count the same two endpoint-class deviations.

Property #58 refines the strategy: prefer a direct joint bound for the two
harmful start-residue deviations, which can bypass separate #13 and #23
budgets and preserve their correlation. Retain the separated interface as a
fallback.

## Current State

At layer `i`, let:

```math
A_i=|V_i|,
\qquad
H_i=|D_i|,
\qquad
G_i=\text{number of complete isolated 2-gaps}.
```

Let `k_(i,L)` and `k_(i,R)` count hits on left and right endpoints. Existing
property #34 proves

```math
K_i=k_{i,L}+k_{i,R},
\qquad
\Delta_i=k_{i,L}-k_{i,R},
```

and

```math
\beta_i
=
\frac{K_i}{H_i}-\frac{2G_i}{A_i}
```

when `H_i>0`.

Define the centered endpoint-class deviations

```math
e_{i,L}
=
k_{i,L}-\frac{G_iH_i}{A_i},
\qquad
e_{i,R}
=
k_{i,R}-\frac{G_iH_i}{A_i}.
```

Then exactly

```math
H_i\beta_i=e_{i,L}+e_{i,R},
\qquad
\Delta_i=e_{i,L}-e_{i,R}.
```

Property #37 currently bounds the two resulting budgets separately. No sharp
joint aggregate theorem is proved.

Property #56 solves the sharp one-layer capacity envelope. With

```math
\ell_i=\max(0,H_i+2G_i-A_i),
\qquad
u_i=\min(H_i,2G_i),
```

the maximum is attained among total endpoint-hit counts
`s in {ell_i,u_i}` and `s=G_i` when feasible, with maximum orientation
imbalance `|d|=min(s,2G_i-s)`.

Property #57 gives a one-layer capacity-admissible configuration with
`k_L=G`, `k_R=0`. Its imbalance cost `G^2/2` is strictly larger than
candidate #21's complete one-layer allowance
`G^2(1-2/r)^2/2`.

Property #58 proves

```math
b_i=\delta_{i,0}+\delta_{i,-2},
\qquad
\Delta_i=\delta_{i,0}-\delta_{i,-2},
```

where `delta_(i,a)=N_(2),a-G_i/r_i`. Candidate #13 plus #23 is exactly a
decomposition of this direct two-class error.

Property #59 constructs, for every prime `r>=5`, an integral residue
histogram satisfying candidate #12's pointwise bound and strict survival
margin while violating candidate #21's scalar ellipse in the same-sign
harmful direction.

Property #60 proves the sharp box maximum

```math
\max_{|\delta_0|,|\delta_{-2}|\le E}
\mathcal Q_r
=
\frac{2r}{r-2}E^2
```

and the exact one-layer threshold

```math
E<
\frac T2\sqrt{\frac{r-2}{r}}.
```

The existing-estimate audit found:

- sixfold harmful capacity is local and directly bounds each harmful count;
- global residue collision energy includes all harmless classes and is
  stronger than the direct scalar target;
- complete-period pair correlation and CRT local factors do not control the
  short conditioned window;
- the black-box large-sieve scale is already proved too large for #21.

Property #61 composes the sixfold capacity `B` with the total population `G`.
It proves the sharp scalar maximum by checking

```math
s\in\{\ell,u\}
\cup
\left(
\{B\}\text{ if }\ell\le B\le u
\right),
```

where `ell=max(0,G-(r-2)B)` and `u=min(G,2B)`.

Property #62 solves that maximum exactly. With

```math
\rho_*(r)
=
\frac{2r\sqrt r}{2\sqrt r+(r-2)^{3/2}},
```

the capacity envelope fits candidate #21's one-layer harmful scalar allowance
if and only if

```math
G>\rho_*(r)B.
```

For every `r>=5`, `2<rho_*(r)<3`, and `rho_*(r)` tends to `2`.

Property #63 compares the resulting population obligation with candidates
#14 and #19. In the square-window domain,

```math
2B<\rho_*(r)B<T_{14},
```

so #14's count floor always implies the scalar criterion. Candidate #19's
floor `T_19=2B+1` implies it exactly when

```math
B<\kappa(r)=\frac1{\rho_*(r)-2},
```

where `kappa(r)/r` tends to `1/2`.

Property #64 proves the uniform bound

```math
\kappa(r)>\frac r2
```

and therefore the explicit late-layer implication

```math
\left[
Q^2-Q-3<3r(r-1)
\ \text{and}\
G\ge2B+1
\right]
\Longrightarrow
G>\rho_*(r)B.
```

The simpler condition `r>=Q/sqrt(3)+1` is sufficient. Thus candidate #19's
ordinary floor, if proved, already controls the harmful scalar energy in that
late part of the chain.

Property #65 corrects the scope of properties #62--#64. They compare each
layer's scalar energy with its own one-step allowance

```math
\frac12(a_iN_i)^2.
```

Candidate #21 instead provides the single global allowance

```math
\frac{(N_0A_{0,m})^2}{2\sum_iw_i}.
```

Even if every layer uses only half its local allowance on the ideal
multiplicative population scale, the weighted scalar sum exceeds the global
allowance for every chain of at least two layers.

Property #66 gives the later aggregate classification. If

```math
E_b
=
\sum_iw_i\frac{r_i}{2(r_i-2)}b_i^2
```

is below candidate #21's global allowance, then `N_m>0` already. Therefore a
successful aggregate bound for the larger realized capacity envelopes
`sum_iw_iC_i` is a terminal survival theorem, not a scalar component waiting
for candidate #22.

## Expected Theorem Shape

Candidate #21 consumes, at each layer,

```math
w_i
\frac{r_i}{2(r_i-2)}
(H_i\beta_i)^2
+
\frac{w_i}{2}\Delta_i^2.
```

The preferred theorem is a joint aggregate estimate for this exact
two-dimensional quadratic form, rather than two unrelated uses of
`|beta_i|,|Delta_i|<=eta_i`.

It must not divide by a late or final 2-gap population. Property #66 proves
that success at candidate #21's global scale is already terminal; it need not
leave a separate survival allowance for candidate #22.

## Assumptions And Validation

- **Assumption:** post-filter-3 endpoint isolation makes the `G_i` left
  endpoints, `G_i` right endpoints, and `A_i-2G_i` non-endpoints disjoint.
  **Validation:** read and cite the exact isolation property before using the
  capacity polygon.
- **Hypothesis:** joint optimization improves materially on separate
  `eta_i` bounds.
  **Validation:** solve the convex quadratic maximum on every vertex of the
  exact feasible polygon.
- **Risk:** a sharp finite-population maximum is still attained by placing
  hits on endpoints and is too large for #21.
  **Validation:** compare its symbolic scale with the available main term
  before attempting residue arithmetic.
- **Risk:** using `H_i/A_i` as if it were `1/r_i` silently imports candidate
  #23.
  **Validation:** retain `A_i,H_i` exactly throughout the #13 calculation.

## What is Learned

- Candidate #13 needs only two endpoint observables for the current
  collision-energy program.
- Their errors are not independent: they are the sum and difference of the
  same left/right centered hit counts.
- The accepted-strike density `H_i/A_i-1/r_i` belongs to candidate #23 and
  must remain symbolic here.
- Endpoint isolation and population capacities permit worst-case
  concentration in one endpoint orientation; they do not provide sampling.
- Capacity-only information is quantitatively insufficient for #21, not
  merely non-sharp: an allowed orientation vertex exceeds the full budget.
- A direct joint estimate for the two harmful start-residue deviations is
  weaker and potentially sharper than proving #13 and #23 separately.
- Candidate #12's current threshold `E<T/2` is strictly weaker than the
  threshold required to control the same-sign quadratic direction.
- The exact additional price for a symmetric pointwise theorem is the factor
  `sqrt((r-2)/r)`.
- The sixfold capacity theorem has the correct local scope, but its natural
  geometry is an asymmetric rectangle around the uniform mean, not the
  symmetric deviation box of property #60.
- The sharp capacity criterion is homogeneous in `G,B`; its true population
  parameter is the ratio `rho=G/B`.
- The exact ratio threshold is controlled by the filled-harmful corner
  `c_0=c_(-2)=B`; all other capacity branches fit once `G/B>=2`.
- Candidate #19's ordinary survival floor `G>=2B+1` does not by itself supply
  the stronger ratio `G>rho_*(r)B` when `B` is large.
- Candidate #14's count-forced-close-pair floor is strictly stronger than the
  harmful scalar population threshold at every square-window layer.
- Property #62 is therefore a genuine intermediate obligation: weaker than
  #14, but stronger than #19 outside the explicit range `B<kappa(r)`.
- The difficult order-`Q` late layers do not require a population premise
  stronger than candidate #19: their small capacity satisfies
  `B<kappa(r)` automatically once `L<3r(r-1)`.
- The remaining scalar gap is concentrated in early and middle layers, where
  `B` can exceed the cutoff. This is a layer-range statement, not a proof of
  candidate #19's floor.
- One-layer scalar control in the late range does not mean those layers are
  paid for inside candidate #21. The global budget is smaller and requires a
  genuinely weighted aggregate theorem for the realized capacity envelopes.
- Property #66 proves that this genuinely weighted harmful theorem is already
  terminal. Candidate #22 remains an independent harmless-distribution
  question, not an additional survival obligation after scalar feasibility.

## Failed Paths

- **Universal bounded-observable theorem first:** much stronger than #21
  needs and introduces irrelevant observables. Retry only if the two-endpoint
  theorem is proved and a broader publication claim is desired.
- **Treating candidate #10 as the strike-density input:** its population and
  denominator differ from `H_i/A_i`. Retry only with a proved bridge.
- **Separate pointwise `eta_i` bounds as the starting algebra:** can lose the
  joint geometry of `beta_i` and `Delta_i`. Retry only after the exact joint
  envelope is known.
- **Capacity treated as representative sampling:** property #56 proves the
  capacity polytope contains vertices concentrated in one endpoint
  orientation. Retry only with an arithmetic reason the incoming residue
  class cannot realize those vertices.
- **Capacity-only certification of #21:** property #57 supplies an admissible
  one-layer countermodel whose imbalance term alone exceeds the allowance.
  Retry only after adding residue-correlation information that suppresses
  orientation concentration.
- **Treating #13 and #23 as obligatorily separate:** property #58 proves both
  components recombine exactly into two harmful residue deviations. Retry the
  separated route only if it admits estimates unavailable for the direct
  two-class target.
- **Using candidate #12's existing pointwise survival margin for #21:**
  property #59 gives an integral histogram satisfying the margin but
  violating the scalar ellipse. Retry only with a stronger threshold or a
  genuinely joint norm.
- **Complete-period correlation/local factors:** exact over a full primorial
  period but give only a trivial prefix error in the relevant short-window
  regime. Retry only with a short-prefix correlation theorem.
- **Black-box large sieve:** its fixed-set scale exceeds #21's allowance even
  before the changing conditioned populations are handled. Retry only with a
  structure-specific gain.
- **Full residue collision energy as the scalar estimate:** includes
  dispersion in the `r-2` harmless classes that belongs to candidate #22.
  Retry only if a proved global estimate is unexpectedly sharper than the
  restricted two-class norm.
- **Composing properties #62--#64 layer by layer into candidate #21:**
  property #65 proves the inference false at the inequality level. On the
  ideal multiplicative scale, energies equal to one half of every local
  allowance still exceed the global allowance by at least a factor
  `m^2/2`. Retry only with a direct weighted estimate for the realized
  envelopes or new cross-layer correlation; local ellipse membership alone
  is insufficient.
- **Treating `sum_iw_iC_i` as a preparatory scalar component:** property #66
  proves that any successful bound at candidate #21's global scale already
  forces final survival through its harmful-excess subterm. Retry only as an
  explicitly terminal arithmetic theorem.

## Open Concerns

- Candidate #13 trims boundary-crossing neighborhoods; all counts must use
  the same complete-endpoint convention.
- A purely combinatorial envelope may be sharp but quantitatively useless.
- Candidate #13 alone does not control total harmful excess because #23's
  accepted-strike density remains separate. Once their assembled scalar bound
  clears the global allowance, property #66 gives survival without #22.
- The `H_i=0` case must remain division-free and is automatically harmless.

## Next Action

Stop checkpoint: the one-layer threshold program has been classified, but it
does not certify candidate #21's cumulative scalar budget.

If this route is continued, the terminal target can be written directly as

```math
\sum_iw_iC_i
<
\frac{T^2}{2W},
```

where `C_i` is property #61's exact realized capacity envelope. Property #66
proves that success is already strong enough to force `N_m>0`. Resume only
with new arithmetic information about the actual population ratios `N_i/B_i`
or their cross-layer correlation; the pointwise thresholds provide none.

Do not sum local ellipse allowances, do not collect additional empirical
evidence, do not treat properties #62--#64 as a cumulative result, and do not
describe candidate #22 as a remaining survival allowance after this scalar
target.

## Validation

- Check the feasible-region and vertex formulas with exact rational
  arithmetic on bounded integer parameters.
- Finite checks validate algebra only; they do not prove sampling.
- Markdown-only work requires `git diff --check`; no Stainless run is needed.
- Any Scala change must begin from a green verification baseline and follow
  the one-change verification cycle.

## Learning Log

| Date | Learning | Action |
|------|----------|--------|
| 2026-07-28 | Candidate #13's minimal useful errors are the sum and difference of two centered endpoint-class hit counts; the broad observable statement is unnecessary for #21. | Opened the dedicated algebraic ticket and selected the exact joint feasible-polygon maximum as the first micro-goal. |
| 2026-07-28 | The exact capacity polygon reduces to at most three endpoint-hit totals; its worst orientation concentrates hits on one endpoint class. Capacity alone therefore does not express representative sampling. | Promoted property #56, synchronized candidate #13, and selected a one-layer concentrated-orientation countermodel against #21's allowance. |
| 2026-07-28 | A capacity-admissible layer can hit every left endpoint and no right endpoint; its `Delta^2/2` term is larger than #21's full one-layer allowance for every `r>2`. | Promoted property #57, synchronized candidate #13, ruled out capacity-only certification, and selected the exact centered residue-correlation normal form. |
| 2026-07-28 | Endpoint sampling and accepted-strike density recombine exactly into the sum and difference of the two harmful start-residue deviations. This direct restricted #12 interface retains correlation lost by Minkowski. | Promoted property #58, synchronized candidates #12/#13/#23, made the direct two-class theorem primary, and selected a strength test of #12's existing pointwise margin against #21. |
| 2026-07-29 | Candidate #12's current pointwise margin is not strong enough for #21: an integral same-sign harmful histogram satisfies `2E<T` but exceeds the scalar ellipse by factor `1+1/(r(r-2))`. | Promoted property #59, synchronized candidate #12, recorded the existing threshold as insufficient, and selected the sharp inscribed-box threshold. |
| 2026-07-29 | The maximal scalar energy over `|delta_0|,|delta_(-2)|<=E` is `2rE^2/(r-2)`, so the sharp one-layer box threshold is `E<(T/2)sqrt((r-2)/r)`. | Promoted property #60, synchronized candidate #12, and selected an applicability audit of existing harmful-residue estimates at the exact required scale. |
| 2026-07-29 | Complete-period correlation has the wrong scope, the black-box large sieve has the wrong scale, and full collision energy includes harmless dispersion. Sixfold harmful capacity is the only existing theorem directly matching the two classes locally. | Selected the exact asymmetric capacity rectangle as the next composition and recorded the other theorem routes with their failed hypotheses. |
| 2026-07-29 | Combining all `r` one-class capacities with total population reduces the exact harmful energy maximum to at most three feasible totals. This yields a deterministic criterion without equidistribution. | Promoted property #61, synchronized candidate #12, and selected the scale-free threshold `rho_*(r)` for `G/B`. |
| 2026-07-29 | The exact capacity threshold is `G/B>rho_*(r)`, where `rho_*(r)=2r sqrt(r)/(2 sqrt(r)+(r-2)^(3/2))`, lies strictly between `2` and `3`, and tends to `2`. The decisive obstruction is both harmful classes filled to capacity. | Promoted property #62, synchronized candidate #12, and selected an exact implication audit against candidates #14 and #19. |
| 2026-07-29 | The scalar population threshold lies strictly below #14's count floor. Candidate #19's `2B+1` floor clears it exactly for `B<1/(rho_*(r)-2)`, whose cutoff is asymptotic to `r/2`. | Promoted property #63 and selected an explicit `Q,r` layer-range theorem for when #19 already supplies the scalar criterion. |
| 2026-07-29 | The exact cutoff satisfies `kappa(r)>r/2`; hence #19's floor supplies the scalar criterion whenever `Q^2-Q-3<3r(r-1)`, in particular for `r>=Q/sqrt(3)+1`. | Promoted property #64 and localized the remaining scalar problem to the early/middle weighted layers. |
| 2026-07-29 | One-layer scalar ellipse membership does not compose into #21's global allowance. Even at half of every local allowance on the ideal multiplicative scale, weighted Cauchy gives a global overrun factor at least `m^2/2`. | Promoted property #65, recorded the local-to-global route as failed, and stopped before treating #62--#64 as cumulative progress. |
| 2026-07-29 | Property #66 proves the weighted harmful-excess lower bound `E_b >= (T-N_m)^2/(2W_-)` with `W_-<W`; the scalar target below #21's allowance already forces final survival. | Reclassified `sum_iw_iC_i` as a terminal theorem and removed #22 as a subsequent survival obligation. |
