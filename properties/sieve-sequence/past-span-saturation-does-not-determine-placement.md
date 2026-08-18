# Past-Span Saturation Does Not Determine Placement

**Status:** Mathematically proved. Stainless verification is not claimed.

## Meaning

The [Layer Innovation Orthogonality property](
layer-strike-innovation-orthogonality.md) proves that each layer's centered
strikes are orthogonal to every function of all previous layers — the
strongest global constraint family available. This property answers the
natural next question: as previous primes accumulate, do these
restrictions become strong enough to *shape* — to determine — the next
filter's strike placement?

The answer is no, provably and permanently. The complete past-span
constraint system is **saturated**: its entire content is the per-fiber
quota "each old survivor's `r` lifts lose exactly one lift". Every
placement satisfying that quota — there are `r^(phi(P))` of them, of which
the real sieve's divisibility rule is a single point — satisfies every
innovation identity. No function of the first CRT coordinate can restrict
a function of the second, and additional past primes only enlarge the
already-exhausted first coordinate. Accumulating global constraints can
never substitute for a local theorem.

## Setup

Retain the notation of the innovation property:
`P_{i+1}=P_i r_i`, `R=P_m`, `a` uniform on `Z/RZ`, filtration
`F_i=sigma(a mod P_i)`. A **placement** at layer `m` is a set `S` of
survivor residues; its centered observable is

```math
g_S(a)=\mathbf 1_{a\in S}-\frac{\mathbf 1_{\gcd(a,P_m)=1}}{r_m}.
```

Call `S` **fiber-admissible** if every survivor fiber — every class
`a mod P_m` coprime to `P_m`, which has exactly `r_m` lifts in `Z/RZ` —
loses exactly one lift:

```math
|S\cap F_c|=1
\qquad\text{for each of the }\varphi(P_m)\text{ survivor fibers}.
```

The real sieve's placement is `S_real={a: r_m|a}` — the divisible lift of
each fiber.

## Equivalence: The Full Past Span Is Exactly The Fiber Quota

For any placement `S` with the survivor-supported observable `g_S`:

```math
\begin{aligned}
\langle g_S,h\rangle=0\ \text{for every }\mathcal F_m\text{-measurable }h
&\Longleftrightarrow
\sum_{a\in F_c}g_S(a)=0
&&[\text{Group Inner Products By Fiber}]\\
&\Longleftrightarrow
|S\cap F_c|=1\ \text{for every fiber}
&&[\text{Substitution}].
\end{aligned}
```

The strongest constraint family expressible from the past — the entire
span of all previous primes' information, products and adaptive weights
included — is *equivalent* to fiber-admissibility. It forces the count
structure completely and says nothing about which lift each fiber loses.
`[Q.E.D.]`

## The Admissible Space

Each fiber-admissible placement is an independent choice of one of `r_m`
lifts in each of the `phi(P_m)` fibers:

```math
\#\{\text{fiber-admissible placements}\}=r_m^{\varphi(P_m)}.
```

The constraints reduce the space of all quota-correct strike sets from
`binom(phi(P_m) r_m, phi(P_m))` to `r_m^(phi(P_m))` — an enormous shaping
of the *allocation between* fibers — while leaving the *within-fiber*
choice, `phi(P_m) log_2 r_m` bits, entirely free. The real sieve is one
point of this space, selected by divisibility.

## Placement-Blindness Of Every Innovation Identity

Every identity of the Layer Innovation Orthogonality property —
conditional mean zero, span orthogonality, annihilation of distinct-layer
innovation products, adaptive Pythagoras — was proved using **only** the
fiber-sum-zero property. Consequently each holds verbatim with the real
`g_m` replaced by any fiber-admissible `g_S`, at that layer or at several
layers simultaneously (mixed real/adversarial chains included). The
entire statistics class of the innovation apparatus — period sums of
products of layer observables and past-measurable functions — cannot
distinguish `S_real` from any other fiber-admissible placement.

This is the single-value incarnation of what the phase-transition
companion family already exhibits at the 2-gap level: every companion
preserving the exact `r-2` descendant law shares all global identities,
which is precisely why the article's global persistence is
allocation-independent and why the companions exist as a controlled
family.

## Saturation: More Previous Primes Cannot Help

By CRT the period is a product:

```math
\mathbb Z/R\mathbb Z\cong\mathbb Z/P_m\mathbb Z\times\mathbb Z/r_m\mathbb Z.
```

Past information is the complete function space on the first factor —
already fully used, since the constraint family is the *entire* span
`L^2(F_m)`, not a growing subset of it. Placement lives on the second
factor. On a product space, orthogonality to all functions of one factor
is exactly fiber-sum-zero and constrains functions of the other factor
not at all — not weakly, not asymptotically, at no depth. Installing more
primes enlarges the exhausted first factor; the second factor's
invisibility is permanent. Unlike a pseudorandom generator whose state
eventually determines its output, the CRT product structure never closes.

## Strategic Consequence

This closes a proof-strategy class: **accumulating enough global
( complete-period ) constraints to force local placement behavior is
futile in principle.** The only observables coupled to `a mod r_m` — and
therefore the only ones that can see placement — are those already
depending on the new layer's residue geometry: windows, intervals, the
distinguished head. The local questions of
[candidate #26](../../candidates/sub-crt-strike-decoherence.md) and
[candidate #27](../../candidates/window-innovation-orthogonality.md) are
therefore not merely unsolved; they are structurally necessary. No
complete-period identity can substitute for them.

The placement rule itself (divisibility) is of course known — it is the
sieve's definition; what remains open everywhere in this catalog is the
*statistical* behavior of that rule inside finite windows.

## Validation

Exact rational checks:

- Chain `(P_0;r_0,r_1,r_2)=(6;5,7,11)`, `R=2310`. An adversarial
  fiber-admissible placement at layer 2 (each fiber loses the lift
  `k=(c^2+3) mod 11`, not the divisible lift) passes the complete
  identity battery the real sieve passes: all 210 conditional class means
  zero; inner products with `g_0`, `g_1`, `g_0 g_1`, the layer-1 survival
  indicator, and a nonconstant function of `a mod 210` all exactly zero;
  `g_0 g_1 g_S=0`; mixed real/adversarial adaptive Pythagoras exact.
- Tiny chain `P_0=6`, `r_0=5`, `R=30`: exhaustive enumeration gives
  exactly `5^2=25` fiber-admissible placements, matching
  `r^(phi(P))=5^phi(6)=25`, with the real sieve among them.

These checks validate the arithmetic; the theorem above does not rest on
them.

## Related

- [Layer Strikes Are Innovations Of The Layer Filtration](
  layer-strike-innovation-orthogonality.md) — the constraint family this
  property exhausts.
- [Accepted-strike cross-layer CRT orthogonality](
  accepted-strike-cross-layer-crt-orthogonality.md) — the pairwise
  subfamily, with the `LR` localization obstruction marking where local
  input becomes necessary.
- [CRT-coupled real-sieve transfer](
  ../../companions/candidates/crt-coupled-real-sieve-transfer.md) — the
  transfer obligation; this property proves global identities alone
  cannot discharge it.
- [Sub-CRT strike decoherence](
  ../../candidates/sub-crt-strike-decoherence.md) and
  [window innovation orthogonality](
  ../../candidates/window-innovation-orthogonality.md) — the local
  questions this property proves necessary.
