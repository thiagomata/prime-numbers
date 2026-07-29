# Capacity Population-Threshold Hierarchy

**Status:** Mathematically proved comparison theorem.
Stainless verification is not claimed.

## Meaning

Three current routes ask for lower bounds on the same conditioned local
2-gap population:

- candidate #19 asks for just enough gaps to beat the two harmful capacities;
- property #62 asks for enough gaps to place one layer's harmful scalar
  energy inside its local collision ellipse;
- candidate #14's count-to-close-pair lemma asks for enough gaps to force two
  nearby occurrences.

Their one-layer thresholds are not equal. The local collision-energy
threshold is strictly stronger than ordinary capacity survival but strictly
weaker than the count-to-close-pair threshold. Candidate #19 implies the
local collision threshold only in an explicit small-capacity range.

## Setup

Let `Q>=7` and let `r` be an odd prime with

```math
5\le r<Q.
```

Put

```math
L=Q^2-Q-3,
\qquad
B=\left\lfloor\frac{L}{6r}\right\rfloor+1.
```

The common one-residue-class capacity is `B`. Define property #62's sharp
ratio

```math
\rho_*(r)
=
\frac{2r\sqrt r}{2\sqrt r+(r-2)^{3/2}}.
```

The three population levels are

```math
\begin{aligned}
T_{19}&=2B+1,\\
T_{\mathrm{energy}}&=\rho_*(r)B,\\
T_{14}&=
\left\lfloor\frac{L}{2r-2}\right\rfloor+2.
\end{aligned}
```

Here `T_19` is candidate #19's integer floor, `G>T_energy` is property #62's
strict scalar criterion, and `G>=T_14` is candidate #14's sufficient count for
the `k=2` interval premise.

## Preliminary Bounds

First, the square-window domain forces

```math
B\ge2.
```

Indeed, `r<=Q-2`, so

```math
\begin{aligned}
L-6r
&\ge Q^2-Q-3-6(Q-2)\\
&=Q^2-7Q+9\\
&>0
\end{aligned}
```

for every `Q>=7`. Hence `floor(L/(6r))>=1`.

Second, property #62 gives `rho_*(r)>2`. We also need the stronger uniform
upper bound

```math
\boxed{\rho_*(r)<\frac{12}{5}.}
```

Write

```math
\frac{\rho_*(r)}2
=
\frac{r}{
2+(r-2)\sqrt{1-2/r}
}.
```

For `r>=11`, the strict inequality

```math
\sqrt{1-\frac2r}>1-\frac2r
```

gives

```math
2+(r-2)\sqrt{1-\frac2r}
>
r-2+\frac4r
>
\frac{5r}{6}.
```

The last inequality is equivalent to

```math
r^2-12r+24>0,
```

which holds for `r>=11`. Therefore `rho_*(r)/2<6/5`.

For the two remaining primes, the same denominator comparison follows from

```math
\sqrt{\frac35}>\frac{13}{18}
\qquad(r=5)
```

and

```math
\sqrt{\frac57}>\frac{23}{30}
\qquad(r=7).
```

Squaring proves both because all terms are positive. Thus
`rho_*(r)<12/5` for every prime `r>=5`.

## Candidate #14 Always Clears The Energy Threshold

Let

```math
n=\left\lfloor\frac{L}{6r}\right\rfloor=B-1.
```

Since `L>=6rn`,

```math
\begin{aligned}
T_{14}
&=
\left\lfloor\frac{L}{2r-2}\right\rfloor+2\\
&\ge
\left\lfloor\frac{6rn}{2r-2}\right\rfloor+2\\
&=
3n+\left\lfloor\frac{3n}{r-1}\right\rfloor+2\\
&\ge3B-1.
\end{aligned}
```

Because `B>=2` and `rho_*(r)<12/5`,

```math
\begin{aligned}
(3-\rho_*(r))B
&>
\frac35B\\
&\ge\frac65\\
&>1.
\end{aligned}
```

Therefore

```math
3B-1>\rho_*(r)B.
```

Combining the inequalities gives

```math
\boxed{
T_{14}>\rho_*(r)B.
}
```

Consequently, candidate #14's count floor implies property #62's harmful
scalar criterion at every square-window layer in the stated domain.

## Exact Range Where Candidate #19 Is Enough

Candidate #19 guarantees only

```math
G\ge T_{19}=2B+1.
```

This floor certifies property #62 exactly when

```math
\begin{aligned}
2B+1&>\rho_*(r)B\\
1&>(\rho_*(r)-2)B\\
B&<\frac{1}{\rho_*(r)-2}.
\end{aligned}
```

Thus

```math
\boxed{
T_{19}>\rho_*(r)B
\quad\Longleftrightarrow\quad
B<\kappa(r),
}
```

where

```math
\kappa(r)
=
\frac{1}{\rho_*(r)-2}
=
\frac{
(\sqrt r+\sqrt{r-2})
\left(2\sqrt r+(r-2)^{3/2}\right)
}{
4(r-2)
}.
```

The second expression follows by rationalizing
`sqrt(r)-sqrt(r-2)`.

This is a guarantee classification. If `B>=kappa(r)`, candidate #19's stated
floor alone no longer proves the scalar inequality; the actual population may
still be larger than that floor.

Moreover,

```math
\rho_*(r)
=
\frac{2}{
2/r+(1-2/r)^{3/2}
}
=
2+\frac2r+o\left(\frac1r\right),
```

so

```math
\boxed{
\frac{\kappa(r)}r\longrightarrow\frac12.
}
```

Candidate #19's one-extra-gap margin therefore certifies the scalar criterion
only while the one-class capacity is roughly below `r/2`.

## Hierarchy

Property #62 already proves `rho_*(r)>2`. Together with the #14 comparison,

```math
\boxed{
2B
<
\rho_*(r)B
<
T_{14}.
}
```

Hence the population obligations form a strict hierarchy:

```text
ordinary two-class capacity
    < one-layer harmful scalar collision control
    < count-forced close-pair control.
```

The middle theorem is genuinely weaker than candidate #14, but it remains a
conditioned local-abundance statement. It does not remove the parity boundary;
it quantifies how much less population the scalar route needs.

## Boundary

This property compares sufficient population thresholds. It proves none of
the unproved hereditary lower bounds for the actual conditioned population.

It also concerns only one layer's two harmful scalar terms. Candidate #22's
harmless-class dispersion remains a separate distribution question, but
property #66 shows it is not an additional survival premise after a global
harmful bound succeeds.

Property #65 proves that satisfying the middle threshold at every layer does
not imply candidate #21's global weighted allowance. The hierarchy compares
local population strengths only; a direct aggregate estimate for
`sum_i w_i Q_i` remains open and is terminal at the required global scale by
property #66.

## Validation

The floor comparisons and the exact `T_19` cutoff were checked over prime
pairs

```math
7\le Q\le211,
\qquad
5\le r<Q,
```

and over additional symbolic integer values of `L>=6r`. No violation was
found. These checks validate the floor bookkeeping only; the proof is the
algebra above.

## Related

- [Sharp sixfold-capacity population-ratio threshold](
  sharp-sixfold-capacity-population-ratio-threshold.md
  )
- [Local count forces k=2 shot capacity](
  local-count-forces-k2-shot-capacity.md
  )
- [Sixfold harmful-residue capacity](
  ../../candidates/sixfold-harmful-residue-capacity.md
  )
- [Hereditary shot-spacing capacity](
  ../../candidates/hereditary-shot-spacing-capacity.md
  )
- [One-layer harmful ellipses do not compose](
  one-layer-harmful-ellipses-do-not-compose.md
  )
- [Weighted harmful-excess energy is already terminal](
  weighted-harmful-excess-energy-is-terminal.md
  )
