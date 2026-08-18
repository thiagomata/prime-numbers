# Layer Strikes Are Innovations Of The Layer Filtration

**Status:** Mathematically proved. Stainless verification is not claimed.

## Meaning

The Cross-Layer CRT Orthogonality property proves that distinct layers'
centered observables are pairwise orthogonal on the complete period. This
property proves the strictly stronger statement behind it: each layer's
centered strike observable has **conditional expectation exactly zero given
the entire past**, and is therefore the *innovation* of the layer
filtration. Consequently the new layer is orthogonal not merely to each
previous observable but to **every function of all previous layers
simultaneously** — the exact global form of the requirement that a new
sequence carry low correlation with all the previous ones.

Three consequences follow exactly: orthogonality to arbitrary
past-measurable test functions (including products and adaptive weights),
annihilation of every product of distinct innovations, and exact variance
additivity with **adaptive** coefficients — a martingale-difference
Pythagoras. The complete-period variance identities in this catalog are
instances of this single source.

The property also fixes the correct local target: a window is not a
uniform average over the period, so the window-restricted analogue is a
separate claim — interval typicality for an explicit CRT-factorable class.
That local claim is recorded as candidate #27 and is not supplied here.

## Setup

Let

```math
P_{i+1}=P_i r_i
\qquad(0\le i<m),
```

where `P_0` is squarefree, the `r_i` are distinct primes not dividing
`P_0`, and `gcd(P_i,r_i)=1`. Let `a` be uniform on `Z/RZ` with `R=P_m`.
The centered layer observable is

```math
g_i(a)
=
\mathbf 1_{\gcd(a,P_i)=1}
\left(
\mathbf 1_{r_i\mid a}-\frac1{r_i}
\right).
```

Define the layer filtration

```math
\mathcal F_i:=\sigma(a\bmod P_i),
```

the information of the first `i` installed layers. Note that `g_i` is
`F_{i+1}`-measurable (it depends on `a mod P_{i+1}`), and its past is
`F_i`.

## Innovation Identity

Fix `i<m`. Condition on `a mod P_i`:

```math
\begin{aligned}
\gcd(a,P_i)\neq1
&\Longrightarrow g_i(a)=0
&&[\text{Support}]\\
\gcd(a,P_i)=1
&\Longrightarrow
\mathbb E\left[\mathbf 1_{r_i\mid a}\,\middle|\,\mathcal F_i\right]=\frac1{r_i}
&&[\text{CRT: }r_i\text{-Coordinate Uniform Given }a\bmod P_i].
\end{aligned}
```

In both cases the centered value has conditional mean zero:

```math
\boxed{
\mathbb E\left[g_i(a)\,\middle|\,\mathcal F_i\right]=0.
}
\qquad[\text{Q.E.D.}]
```

The second line is the whole content: among residues with `a mod P_i`
fixed and coprime to `P_i`, CRT makes the `r_i` coordinate exactly
uniform, so the strike indicator equals its own mean.

## Span Orthogonality

Let `h(a)` be any `F_i`-measurable function — any function of the first
`i` layers, built from previous observables, their products, survival
indicators, or adaptive weights. Then

```math
\begin{aligned}
\mathbb E\left[g_i(a)h(a)\right]
&=\mathbb E\left[h(a)\,\mathbb E\left[g_i(a)\,\middle|\,\mathcal F_i\right]\right]
&&[\text{Tower Property};\ h\ \mathcal F_i\text{-Measurable}]\\
&=0.
&&[\text{Innovation Identity}]
\end{aligned}
```

Every previous observable `g_j` (`j<i`) is `F_i`-measurable, so the
[Cross-Layer CRT Orthogonality](
accepted-strike-cross-layer-crt-orthogonality.md) pairwise result is the
special case `h=g_j`. Taking `h` equal to products `g_{j_1}\cdots g_{j_k}`
of distinct earlier observables also gives

```math
\boxed{
\mathbb E\left[g_{j_1}\cdots g_{j_k}g_i\right]=0
\qquad(j_1<\cdots<j_k<i):
}
```

every product of distinct innovations averages to zero on the complete
period.

## Adaptive Pythagoras

Let `h_i(a)` be any `F_i`-measurable coefficient (an adaptive weight that
may depend on all layers before `i`, but not on `a mod r_i`). Then

```math
\begin{aligned}
\mathbb E\left[\left(\sum_{i<m}h_i(a)g_i(a)\right)^2\right]
&=\sum_{i<m}\mathbb E\left[h_i(a)^2g_i(a)^2\right].
\end{aligned}
```

For the cross terms with `i<j`, the product
`h_ih_jg_i` is `F_j`-measurable, so

```math
\mathbb E\left[h_ih_jg_ig_j\right]
=
\mathbb E\left[h_ih_jg_i\,\mathbb E\left[g_j\middle|\mathcal F_j\right]\right]
=0,
```

and only the diagonal survives. With constant weights `h_i=1` this
recovers exact variance additivity for sums of layer observables. The
measurability constraint is load-bearing: a weight that inspects
`a mod r_i` (the current layer's own residue) sees the strike indicator it
multiplies, and the identity fails — see the negative control below.

## Boundary Of The Result

Everything above averages `a` **uniformly over the complete period**. For
an interval `I` of length `L<=R`, the window sum
`sum_{a in I} g_i(a)h(a)` is an empirical average over `L` consecutive
residues, not a uniform expectation, and no complete-period identity
bounds it by itself: this is the localization gap already isolated by the
`LR` obstruction in Cross-Layer CRT Orthogonality. What this property
contributes to the local problem is the correct target (typicality of the
explicit class `{g_i h : h past-measurable}`) and the correct null (the
window sum is exactly zero in uniform expectation). The local claim
itself is [candidate #27](../../candidates/window-innovation-orthogonality.md).

## Validation

Exact rational checks for the chain
`(P_0;r_0,r_1,r_2)=(6;5,7,11)`, `R=2310` (the same chain used by the
Cross-Layer CRT Orthogonality property):

- Conditional means `E[g_i | a mod P_i]` vanish for **all** residue
  classes: 6 of 6 for `i=0`, 30 of 30 for `i=1`, 210 of 210 for `i=2`.
- Span orthogonality against explicit past-measurable test functions
  (`g_0`, `g_1`, `g_0 g_1`, the survival indicator of layer 1, and a
  nonconstant function of `a mod 210`): all inner products exactly zero.
- Product annihilation `sum g_0 g_1 g_2 = 0` exactly.
- Adaptive Pythagoras with admissible weights (functions of `a mod 6`,
  `a mod 30`, `a mod 210` respectively): both sides equal
  `62366236/385` exactly.
- Negative control: replacing the `a mod 30`-measurable weight by one
  that also inspects `a mod 7` (the current layer's residue) breaks the
  identity — confirming the measurability requirement is not decorative.
- Squared norms match the filed formula
  `R*phi(P_i)/P_i*(r_i-1)/r_i^2` (`616/5`, `528/7`, `480/11`), consistent
  with the Cross-Layer CRT Orthogonality validation.

These finite checks validate the arithmetic; the theorem itself is proved
above and does not rest on them.

## Related

- [Past-span saturation does not determine placement](
  past-span-saturation-does-not-determine-placement.md) — the sharp
  complement: this property's constraint family is saturated, and every
  fiber-admissible placement satisfies these identities identically.
- The CRT step at this property's core (unique forbidden lift per
  survivor fiber) is verified in code as
  `BezoutUtils.coprimeStepZeroOffset` in
  `src/main/scala/v1/chapter5/prime/BezoutUtils.scala`, whose existence
  and per-endpoint uniqueness postconditions are Stainless-verified; the
  identities above are the period-averaged consequences of that kernel.
- [Accepted-strike cross-layer CRT orthogonality](
  accepted-strike-cross-layer-crt-orthogonality.md) — the pairwise special
  case with exact norms and the Bessel bound.
- [Accepted-strike quadratic variation](
  accepted-strike-quadratic-variation.md),
  [Accepted-strike first-deletion variance identity](
  accepted-strike-first-deletion-variance-identity.md),
  [Accepted-strike active two-class variance identity](
  accepted-strike-active-two-class-variance-identity.md) — instance
  variance identities sharing this source.
- [Window innovation orthogonality](
  ../../candidates/window-innovation-orthogonality.md) — the local
  (window) form, open.
- [Sub-CRT strike decoherence](
  ../../candidates/sub-crt-strike-decoherence.md) — the frequency-resolved
  companion of the local question.
