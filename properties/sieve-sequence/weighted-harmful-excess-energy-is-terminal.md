# Weighted Harmful-Excess Energy Is Already Terminal

**Status:** Mathematically proved conditioned-chain theorem. Stainless
verification is not claimed.

## Meaning

Candidate #21 splits each layer's residue collision energy into harmless
dispersion, total harmful excess, and left/right harmful imbalance. The total
harmful excess looks like one component that might be bounded independently
and then combined with the other two.

This property shows that its quadratic budget is already terminal at candidate
#21's scale. If the weighted harmful-excess energy alone is smaller than the
complete candidate #21 allowance, then the conditioned chain already has a
positive final 2-gap-start population. No harmless-energy estimate is needed
for that implication.

This does not make the estimate circular by definition. It identifies its
exact strength: proving it universally for the required square windows would
already prove the desired survival conclusion.

## Setup

Fix a future head `Q` and a nonempty conditioned chain

```math
5\le r_0<r_1<\cdots<r_{m-1}<Q.
```

Let `N_i` be the number of complete 2-gap starts in the stated window
immediately before filter `r_i`, and let `N_m` be the actual final survivor
count. Define

```math
a_i=1-\frac2{r_i},
\qquad
A_{u,v}=\prod_{j=u}^{v-1}a_j,
```

```math
w_i=A_{i+1,m},
\qquad
w_{-1}=A_{0,m}.
```

Write

```math
T=N_0A_{0,m}
```

for the final multiplicative main term and

```math
b_i
=
\left(N_i-N_{i+1}\right)-\frac{2N_i}{r_i}
=
a_iN_i-N_{i+1}
```

for the signed total harmful excess at layer `i`.

Property #25 proves the exact weighted conservation law

```math
\boxed{
\sum_{i=0}^{m-1}w_ib_i=T-N_m.
}
```

Define the harmful-excess part of the weighted scalar energy by

```math
\boxed{
E_b
=
\sum_{i=0}^{m-1}
w_i
\frac{r_i}{2(r_i-2)}
b_i^2.
}
```

Finally, define the previous-weight sum

```math
W_-=\sum_{i=0}^{m-1}w_{i-1}
```

and candidate #21's ordinary weight sum

```math
W=\sum_{i=0}^{m-1}w_i.
```

## Exact Weighted Lower Bound

Let

```math
c_i=\frac{r_i}{2(r_i-2)}.
```

Weighted Cauchy--Schwarz gives

```math
\begin{aligned}
\left(\sum_iw_ib_i\right)^2
&=
\left(
\sum_i
\sqrt{w_ic_i}\,b_i
\sqrt{\frac{w_i}{c_i}}
\right)^2\\
&\le
\left(\sum_iw_ic_ib_i^2\right)
\left(\sum_i\frac{w_i}{c_i}\right)\\
&=
E_b
\left(
\sum_i
2w_i\frac{r_i-2}{r_i}
\right).
\end{aligned}
```

Because

```math
\frac{r_i-2}{r_i}=a_i
```

and

```math
a_iw_i
=
A_{i,m}
=
w_{i-1},
```

the dual weight sum is exactly

```math
\sum_i\frac{w_i}{c_i}
=
2\sum_iw_{i-1}
=
2W_-.
```

Insert the conservation law:

```math
\boxed{
E_b
\ge
\frac{(T-N_m)^2}{2W_-}.
}
\qquad[\text{Q.E.D.}]
```

This is a conditioned-chain lower bound. It is not a one-layer estimate and
does not use empirical sampling.

## Strict Comparison With Candidate #21

For every layer,

```math
0<a_i<1.
```

Therefore

```math
w_{i-1}=a_iw_i<w_i,
```

and summing gives

```math
\boxed{W_-<W.}
```

Suppose first that the final population is zero. Then

```math
E_b
\ge
\frac{T^2}{2W_-}.
```

If `T>0`, the strict weight comparison gives

```math
\frac{T^2}{2W_-}
>
\frac{T^2}{2W}.
```

If `T=0`, nonnegativity gives

```math
E_b\ge0=\frac{T^2}{2W}.
```

In either case, `N_m=0` makes the strict inequality

```math
E_b<\frac{T^2}{2W}
```

impossible. By contraposition,

```math
\boxed{
E_b
<
\frac{T^2}{2W}
\quad\Longrightarrow\quad
N_m>0.
}
\qquad[\text{Q.E.D.}]
```

Since the complete harmful scalar energy also contains the nonnegative
imbalance term

```math
\frac12\sum_iw_i\Delta_i^2,
```

any strict aggregate bound on the full harmful scalar energy below the same
allowance is terminal as well.

## Normalized-Population Form

The same result can be written as an exact quadratic variation of the
realized population profile.

Put

```math
P_i=A_{0,i},
\qquad
z_i=\frac{N_i}{P_i}.
```

Because `P_{i+1}=a_iP_i`,

```math
\begin{aligned}
b_i
&=
a_iN_i-N_{i+1}\\
&=
P_{i+1}(z_i-z_{i+1}).
\end{aligned}
```

Also

```math
w_i=\frac{P_m}{P_{i+1}}.
```

Consequently,

```math
\begin{aligned}
w_i
\frac{r_i}{2(r_i-2)}
b_i^2
&=
\frac{P_m}{P_{i+1}}
\frac1{2a_i}
P_{i+1}^2
(z_i-z_{i+1})^2\\
&=
\frac{P_mP_i}{2}
(z_i-z_{i+1})^2.
\end{aligned}
```

Thus

```math
\boxed{
E_b
=
\frac{A_{0,m}}2
\sum_{i=0}^{m-1}
A_{0,i}
(z_i-z_{i+1})^2.
}
```

The harmful-excess energy is therefore the weighted quadratic variation of
the actual population relative to the multiplicative survival profile.
Calling for a “weighted realized-population theorem” does not avoid the final
survival issue unless that theorem supplies genuinely new arithmetic control
of this variation.

## Consequences For The Candidate Program

1. Candidate #24 is the sharp conservation-only quadratic survival
   condition:

   ```math
   E_b<\frac{T^2}{2W_-}.
   ```

2. Candidate #21 remains a terminal consumer but is stronger than #24.
3. Restricted candidate #12's direct weighted harmful-residue norm is also
   terminal at the candidate #21 allowance because it contains `E_b`.
4. Candidate #22's harmless energy `U_i` remains independently noncircular:
   it vanishes when the actual harmless survivor population is zero.
5. Proving candidate #22 does not remove the terminal scalar obligation.
6. One-layer capacity thresholds remain valid local classifications, but
   property #65 already shows they do not bound this quadratic variation
   globally.

The next useful algebraic search should therefore not describe
`sum_i w_iQ_i` as merely one independent component. It must either:

- supply new arithmetic control strong enough to prove terminal survival; or
- change the composition framework so the signed conservation law is used
  without replacing it by this terminal square budget.

## Boundary

This theorem does not prove that the harmful-excess budget holds for any
unbounded family of future heads. It proves that such a budget, at candidate
#21's global scale, already has the strength to force a final survivor.

The conclusion is stronger than saying “every sufficient theorem implies
survival.” It locates the strength in one specific component by deriving an
exact lower bound from the final population. The imbalance and harmless
components play no role in the obstruction.

The theorem also does not refute candidates #12, #21, or #22. It reclassifies
the proof obligation and prevents an independently noncircular harmless
estimate from being mistaken for completion of the chain argument.

## Validation

- The definitions of `b_i`, `w_i`, and `T` match property #25 and candidate
  #21.
- The identity `a_iw_i=w_{i-1}` includes `i=0` through the declared extension
  `w_{-1}=A_{0,m}`.
- The `T=0` case is handled separately before contraposition.
- Every step is symbolic; no finite sample is used as proof evidence.

## Related

- [Weighted deletion conservation law](
  weighted-deletion-conservation-law.md
  )
- [Weighted collision-energy chain survival](
  weighted-collision-energy-chain-survival.md
  )
- [Orthogonal residue-energy decomposition](
  orthogonal-residue-energy-decomposition-after-two-class-filter.md
  )
- [One-layer harmful ellipses do not compose](
  one-layer-harmful-ellipses-do-not-compose.md
  )
- [Local pattern-residue balance](
  ../../candidates/local-pattern-residue-balance.md
  )
- [Weighted harmful-excess quadratic survival](
  ../../candidates/weighted-harmful-excess-quadratic-survival.md
  )
- [Cumulative weighted collision budget](
  ../../candidates/cumulative-weighted-collision-budget.md
  )
