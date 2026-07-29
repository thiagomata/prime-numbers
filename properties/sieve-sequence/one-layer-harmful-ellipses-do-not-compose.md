# One-Layer Harmful Ellipses Do Not Compose

**Status:** Mathematically proved comparison obstruction.
Stainless verification is not claimed.

## Meaning

Properties #62--#64 identify exactly when sixfold capacity places one layer's
two harmful scalar terms below that layer's complete survival allowance.
Candidate #21, however, has one global second-moment allowance for the entire
conditioned chain.

This property proves that even generous strict success at every one-layer
comparison does not imply the global candidate #21 scalar budget. The local
thresholds remain useful structural information, but they must be combined
through a genuinely weighted aggregate estimate.

## Setup

Let a conditioned chain contain `m>=2` incoming filters. Define

```math
a_i=1-\frac2{r_i},
\qquad
w_i=A_{i+1,m}>0,
\qquad
W=\sum_{i=0}^{m-1}w_i.
```

Let

```math
T=N_0A_{0,m}>0
```

be candidate #21's final multiplicative main term. Its complete weighted
second-moment allowance is

```math
\boxed{
\frac{T^2}{2W}.
}
```

At layer `i`, write

```math
M_i=a_iN_i
```

for the one-step multiplicative main term, and let `Q_i>=0` denote the two
harmful scalar energy

```math
Q_i
=
\frac{r_i}{2(r_i-2)}b_i^2
+
\frac12\Delta_i^2.
```

The one-layer ellipse used by properties #60--#64 is

```math
Q_i<\frac{M_i^2}{2}.
```

## The Ideal Multiplicative Scale

Consider the most favorable main-term population scale

```math
N_i=N_0A_{0,i}.
```

Then

```math
\begin{aligned}
M_i
&=N_0A_{0,i+1}\\
&=\frac{N_0A_{0,m}}{A_{i+1,m}}\\
&=\frac{T}{w_i}.
\end{aligned}
```

Thus even before population losses are introduced, the local main terms grow
backward like `1/w_i` relative to the final main term.

## Counterexample To Local-To-Global Composition

For every layer, choose the numerical scalar energy

```math
Q_i=\frac{M_i^2}{4}.
```

Every local ellipse holds strictly:

```math
Q_i=\frac{M_i^2}{4}<\frac{M_i^2}{2}.
```

But the weighted scalar energy is

```math
\begin{aligned}
\sum_iw_iQ_i
&=
\frac14\sum_iw_i\frac{T^2}{w_i^2}\\
&=
\frac{T^2}{4}\sum_i\frac1{w_i}.
\end{aligned}
```

For positive weights, Cauchy--Schwarz gives

```math
\left(\sum_iw_i\right)
\left(\sum_i\frac1{w_i}\right)
\ge m^2.
```

Since `m>=2`,

```math
W\sum_i\frac1{w_i}
\ge m^2
\ge4
>2.
```

Therefore

```math
\boxed{
\sum_iw_iQ_i
>
\frac{T^2}{2W}.
}
```

The harmful scalar terms alone exceed candidate #21's complete global
allowance, even though every layer uses only one half of its local allowance.
`[Q.E.D.]`

## Exact Corrected Interface

Let property #61's sharp capacity envelope at layer `i` be

```math
C_i
=
\max_{s\in\mathcal S_i}
F_{r_i,N_i,B_i}(s).
```

Capacity proves only

```math
Q_i\le C_i.
```

An aggregate capacity theorem can therefore target

```math
\boxed{
\sum_iw_iC_i
<
\frac{T^2}{2W}.
}
```

Property #66 proves that this harmful estimate is already terminal. Its
harmful-excess subterm satisfies

```math
E_b
\ge
\frac{(T-N_m)^2}{2W_-},
\qquad
W_-<W.
```

Since

```math
E_b\le\sum_iw_iQ_i\le\sum_iw_iC_i,
```

the displayed aggregate capacity theorem already forces `N_m>0`; candidate
#22's harmless energy is not an additional survival requirement. A combined
harmful-plus-harmless estimate remains sufficient for candidate #21's full
collision budget, but it is stronger than needed merely to prove survival.

The pointwise comparisons

```math
C_i<\frac{M_i^2}{2}
```

from properties #62--#64 do not imply this weighted theorem.

## Consequences

1. Property #62 remains the exact one-layer capacity threshold.
2. Property #63 remains the exact hierarchy among one-layer population
   thresholds.
3. Property #64 remains a valid late-layer one-layer implication.
4. None of them, alone or together, proves candidate #21's cumulative scalar
   budget.
5. A direct aggregate theorem for the realized `C_i` at the complete #21
   allowance is terminal by property #66.

The next valid algebraic question can be the weighted sum of the exact
envelopes `C_i`, but it must be advertised as a terminal arithmetic theorem,
not an independently noncircular component.

## Boundary

The displayed `Q_i` values are an algebraic counterexample to the implication
between inequalities. They are not asserted to be realized by one actual
sieve chain.

That distinction is enough for the conclusion: any proof using only the local
ellipse inequalities lacks the information needed to derive the global
budget. An actual-chain theorem could still succeed by exploiting additional
correlation, population loss, or a much smaller realized fraction of each
capacity envelope. Property #66 proves that success at the required aggregate
harmful scale would itself settle final survival.

## Validation

The identity and strict failure were checked on positive chain weights from
prime sequences of lengths `2` through `25`. In every case,

```math
\frac{
\sum_iw_i(M_i^2/4)
}{
T^2/(2W)
}
=
\frac W2\sum_i\frac1{w_i}
\ge\frac{m^2}{2}>1.
```

These checks illustrate the exact proof; they are not empirical evidence
about sieve populations.

## Related

- [Sharp sixfold-capacity population-ratio threshold](
  sharp-sixfold-capacity-population-ratio-threshold.md
  )
- [Late-layer sixfold floor controls harmful energy](
  late-layer-sixfold-floor-controls-harmful-energy.md
  )
- [Weighted composition of endpoint and strike-density errors](
  weighted-scalar-error-composition.md
  )
- [Weighted harmful-excess energy is already terminal](
  weighted-harmful-excess-energy-is-terminal.md
  )
- [Cumulative weighted collision budget](
  ../../candidates/cumulative-weighted-collision-budget.md
  )
