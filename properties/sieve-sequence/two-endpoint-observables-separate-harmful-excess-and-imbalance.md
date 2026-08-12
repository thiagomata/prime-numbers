# Two Endpoint Observables Separate Harmful Excess And Imbalance

**Status:** Exact observable identities and mathematically proved conditional
implications. The sampling and strike-discrepancy bounds are open. Stainless
verification is not claimed.

## Meaning

The usual endpoint indicator counts how many 2-gaps a filter destroys, but it
does not distinguish whether the filter hits their left or right endpoints.
The first-deletion energy identity needs both quantities:

- total harmful excess;
- imbalance between the two harmful endpoint classes.

Two bounded local observables separate them exactly. The unsigned endpoint
indicator controls total destruction. A signed left-versus-right observable
controls endpoint-class imbalance.

## Setup

Let `V` be the `A>0` accepted anchor values used by candidate #13 in one local
window, and let `D` be the `H` anchors hit by the incoming filter:

```math
A=|V|,
\qquad
H=|D|.
```

Let `G` count only complete post-3 2-gaps whose two endpoint anchors belong to
`V`. Exclude boundary-crossing gaps consistently from every quantity below.

Let

```math
k_L
```

be the number of counted gaps hit at their left endpoint and

```math
k_R
```

the number hit at their right endpoint. Since the filtering prime is greater
than `2`, it cannot hit both endpoints of one 2-gap. Define

```math
K=k_L+k_R,
\qquad
\Delta=k_L-k_R.
```

## Unsigned Endpoint Observable

Define

```math
c_+(v)
=
\begin{cases}
1,&v\text{ is either endpoint of a counted 2-gap},\\
0,&\text{otherwise}.
\end{cases}
```

Post-3 endpoint isolation gives

```math
\|c_+\|_\infty=1,
\qquad
\sum_{v\in V}c_+(v)=2G.
```

The hit sum counts one endpoint for each destroyed gap:

```math
\boxed{
\sum_{v\in D}c_+(v)=K.
}
```

## Signed Endpoint Observable

Define

```math
c_-(v)
=
\begin{cases}
+1,&v\text{ is the left endpoint of a counted 2-gap},\\
-1,&v\text{ is the right endpoint of a counted 2-gap},\\
0,&\text{otherwise}.
\end{cases}
```

Again,

```math
\|c_-\|_\infty=1.
```

Every counted gap contributes one left and one right endpoint to `V`, so

```math
\boxed{
\sum_{v\in V}c_-(v)=0.
}
```

The hit sum records the orientation imbalance:

```math
\boxed{
\sum_{v\in D}c_-(v)=\Delta.
}
```

## Consequence Of Candidate #13

Assume `H>0` and that candidate #13's sampling inequality holds for both
observables with error `eta`:

```math
\left|
\frac1H\sum_{v\in D}c_\pm(v)
-
\frac1A\sum_{v\in V}c_\pm(v)
\right|
\le
\eta.
```

Substituting the exact sums proves

```math
\boxed{
\left|
\frac KH-\frac{2G}{A}
\right|
\le
\eta
}
```

and

```math
\boxed{
|\Delta|
\le
H\eta.
}
```

If `H=0`, then no endpoint is hit, so `K=Delta=0` without a sampling
hypothesis.

## Exact Harmful-Excess Decomposition

Let `r` be the incoming prime. Define the endpoint-sampling bias

```math
\beta
=
\frac KH-\frac{2G}{A}
```

and the accepted-strike density discrepancy

```math
\varepsilon
=
\frac HA-\frac1r.
```

The harmful excess used by the weighted collision program is

```math
b
=
K-\frac{2G}{r}.
```

Since

```math
K
=
H\left(\frac{2G}{A}+\beta\right),
```

subtraction gives the exact bridge

```math
\boxed{
b
=
H\beta
+
2G\varepsilon.
}
```

Consequently, the two discrepancy bounds

```math
|\beta|\le\eta,
\qquad
|\varepsilon|\le\xi
```

imply

```math
\boxed{
|b|
\le
H\eta+2G\xi,
\qquad
|\Delta|\le H\eta.
}
```

## Boundary

Candidate #13's unsigned endpoint observable controls total destruction but
not orientation imbalance. Adding the signed observable controls `Delta`.
Control of the centered harmful excess `b` additionally needs the local strike
density `H/A` to be close to `1/r`. Candidate #10, as currently stated,
controls post-filter safe-window count discrepancy and does not directly
provide this estimate. A separate accepted-strike density theorem, built on
the exact local-strike count, is required.

These two observables control the terminal errors in the first-deletion energy
identity. They do not control how the surviving gaps distribute among the
`r-2` harmless residue classes. A separate harmless-dispersion theorem remains
necessary for an upper bound on the post-filter variance.

## Related

- [Uniform local observable sampling](
  ../../candidates/uniform-local-observable-sampling.md
  )
- [Exact accepted local filter strikes](
  exact-accepted-local-filter-strikes.md
  )
- [First-deletion pair terminal energy](
  first-deletion-pair-terminal-energy.md
  )
