# Seven-Layer Density Floor Maximizes Capacity Width

**Status:** Mathematically proved conditional bridge. Stainless verification
is not claimed.

## Meaning

Candidate #17 asks for a local population large enough to force a close pair
at every conditioned layer. Property #74 instead asks how far the same
population lies from the empty and full endpoints of the residue-capacity
box.

These requirements are compatible in the strongest possible way. Once
filter `5` is installed, candidate #17's local-count threshold places the
population in the middle regime of property #74. Its feasible harmful-count
interval then has the maximum possible width `2B`.

This theorem does not prove candidate #17's local-count hypothesis. It proves
what that hypothesis supplies to candidate #24 when it holds.

## Setup

Let

```math
Q\ge17,
\qquad
7\le r<Q,
```

and define

```math
L=Q^2-Q-3,
\qquad
B=\left\lfloor\frac{L}{6r}\right\rfloor+1.
```

Let `N` be the number of complete 2-gap starts in `[Q,Q^2)` immediately
before filter `r`. Because `r>=7`, filters `2`, `3`, and `5` are already
installed.

Assume candidate #17's one-layer count threshold:

```math
\boxed{
N\ge
\left\lfloor\frac{L}{2r-2}\right\rfloor+2.
}
```

## Lower Side Of The Middle Regime

Since `r<Q`, one has `r<=Q-1`. Therefore

```math
\begin{aligned}
L-6r
&\ge Q^2-Q-3-6(Q-1)\\
&=Q^2-7Q+3\\
&>0
\end{aligned}
```

for `Q>=17`. Hence `L>6r`. Moreover,

```math
\begin{aligned}
\frac{L}{2r-2}-\frac{2L}{6r}
&=
\frac{L(r+2)}{6r(r-1)}\\
&>
1.
\end{aligned}
```

Using `floor(x)>=x-1` and `floor(y)<=y`, this gives

```math
\left\lfloor\frac{L}{2r-2}\right\rfloor
\ge
2\left\lfloor\frac{L}{6r}\right\rfloor.
```

Consequently,

```math
\begin{aligned}
N
&\ge
\left\lfloor\frac{L}{2r-2}\right\rfloor+2\\
&\ge
2\left\lfloor\frac{L}{6r}\right\rfloor+2\\
&=\boxed{2B}.
\end{aligned}
```

## Upper Side From The Installed Filter Five

After filters `2`, `3`, and `5`, complete 2-gap starts occupy exactly the
three residue classes

```math
11,17,29\pmod{30}.
```

Later filtering can only remove starts. In a range of diameter `L`, each one
of these residue classes contributes at most `floor(L/30)+1` starts. Thus

```math
N
\le
3\left(
\left\lfloor\frac{L}{30}\right\rfloor+1
\right)
\le
\frac{L}{10}+3.
```

On the other hand,

```math
(r-2)B
\ge
\frac{(r-2)L}{6r}.
```

The difference between the latter lower bound and the former upper bound is

```math
\begin{aligned}
\frac{(r-2)L}{6r}
-\left(\frac{L}{10}+3\right)
&=
\frac{L(r-5)}{15r}-3\\
&\ge
\frac{2L}{105}-3\\
&>0,
\end{aligned}
```

because `r>=7` and `L>=17^2-17-3=269`. Therefore

```math
\boxed{N\le(r-2)B}.
```

## Maximal Population Slack

Combining the two sides gives

```math
\boxed{
2B\le N\le(r-2)B.
}
```

In particular,

```math
N\ge2B,
\qquad
rB-N\ge2B.
```

Property #74's population slack is consequently

```math
\boxed{
\sigma
=
\min(N,2B,rB-N)
=
2B.
}
```

Its capacity-envelope floor becomes

```math
\boxed{X\ge B^2.}
```

This is the largest lower bound obtainable from property #74's width
inequality, because the width can never exceed `2B`.

## Conditioned-Chain Consequence

Suppose candidate #17's threshold holds at each layer in a prefix. For the
layers with `r_i>=7`, the theorem gives `sigma_i=2B_i`. Omitting any earlier
nonnegative contribution, property #74 therefore yields

```math
\boxed{
e_k
\ge
\left(
\sum_{\substack{i<k\\r_i\ge7}}
\frac{B_i^2}{M_kd_ip_ia_i}
-s_k
\right)_+.
}
```

Property #73 then converts any positive excess at the required scale into an
explicit reduction of candidate #24's capacity-energy envelope.

## Boundary

The bridge removes uncertainty about which population-slack branch applies:
under candidate #17, it is always the maximal-width branch. It does not prove
that the resulting normalized sum exceeds `s_k`, nor that the resulting
hybrid gain clears candidate #24's extinction deficit.

The next algebraic question is now a parameter comparison: insert the proved
`B_i^2` contributions into the overflow and compare their scale with `s_k`
and the remaining extinction deficit. If that comparison fails, candidate
#17 can still prove survival directly through its close-pair mechanism, but
it will not close candidate #24 through property #74 alone.

No empirical evidence is used in this result.

## Related

- [Exact Seven-Layer Capacity Floor](exact-seven-layer-capacity-floor.md)
- [Seven-Layer Capacity Floor](../../candidates/seven-layer-capacity-floor.md)
- [Capacity-Envelope Width Floor Needs Population Slack](capacity-envelope-width-floor-needs-population-slack.md)
- [Native-Period Capacity Overflow Quantifies the Hybrid Gain](native-period-capacity-overflow-quantifies-hybrid-gain.md)
- [Candidate #24: Weighted Harmful-Excess Quadratic Survival](../../candidates/weighted-harmful-excess-quadratic-survival.md)
