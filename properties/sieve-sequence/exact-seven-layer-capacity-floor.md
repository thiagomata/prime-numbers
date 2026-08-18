# Exact Seven-Layer Capacity Floor

**Status:** Mathematically proved. Stainless verification is not claimed here.

## Meaning

Immediately before filter `7`, the installed filters are exactly `2`, `3`,
and `5`. This makes the complete 2-gap starts periodic modulo `30`. Counting
whole periods inside the square window proves, without an asymptotic estimate
or uniform-distribution assumption, that the normalized `k=2` shot capacity
is strictly above `1`.

This settles the early `r=7` side of the seven-layer capacity-floor candidate.
It does not prove that later conditioned layers remain above this floor.

## Setup

Fix any integer `Q>=17` and the half-open future square window

```math
W_Q=[Q,Q^2).
```

Let `G_7(W_Q)` be the number of complete 2-gaps `(x,x+2)` in this window
immediately before filter `7`. Thus

```math
Q\le x
\qquad\text{and}\qquad
x+2<Q^2.
```

Define

```math
L_Q=Q^2-Q-3
```

and the seven-layer capacity ratio

```math
\rho(Q,7)
=
\frac{12\bigl(G_7(W_Q)-1\bigr)}{L_Q}.
```

## Property

For every integer `Q>=17`,

```math
\boxed{\rho(Q,7)>1.}
```

Equivalently,

```math
\boxed{
12\bigl(G_7(W_Q)-1\bigr)>Q^2-Q-3.
}
```

Consequently, the local-count theorem forces two complete 2-gaps in `W_Q`
whose enclosing interval is shorter than `14`.

## Proof

An integer is accepted before filter `7` exactly when it is not divisible by
`2`, `3`, or `5`. The accepted residues modulo `30` are

```math
1,7,11,13,17,19,23,29.
```

Their cyclic successor differences are

```math
6,4,2,4,2,4,6,2.
```

Therefore the complete 2-gap starts are exactly

```math
x\equiv11,17,29\pmod{30}.
```

The possible integer starts satisfy

```math
Q\le x\le Q^2-3,
```

so their containing integer interval has

```math
\begin{aligned}
n
&=(Q^2-3)-Q+1
&&[\text{Inclusive Integer Count}]\\
&=Q^2-Q-2
&&[\text{Simplification}]\\
&=L_Q+1.
&&[\text{By Definition}]
\end{aligned}
```

By the division algorithm, write

```math
n=30k+t,
\qquad
0\le t<30.
```

Partition the first `30k` possible starts into `k` consecutive blocks of
length `30`. Every such block contains each residue modulo `30` exactly once,
and hence contains exactly three complete 2-gap starts. The remaining `t`
positions can only add starts. Therefore

```math
G_7(W_Q)\ge3k.
```

Since `Q>=17`,

```math
\begin{aligned}
n
&=Q^2-Q-2
&&[\text{By Definition}]\\
&\ge17^2-17-2
&&[\text{Monotonicity for }Q\ge17]\\
&=270.
&&[\text{Simplification}]
\end{aligned}
```

Because `n=30k+t` and `0<=t<30`, this implies `k>=9`. Now

```math
\begin{aligned}
12\bigl(G_7(W_Q)-1\bigr)-L_Q
&\ge12(3k-1)-(n-1)
&&[\text{By the Count Bound and }L_Q=n-1]\\
&=36k-12-(30k+t-1)
&&[\text{Substitution}]\\
&=6k-t-11
&&[\text{Simplification}]\\
&\ge6\cdot9-29-11
&&[\text{Since }k\ge9\text{ and }t\le29]\\
&=14\\
&>0.
&&[\text{Q.E.D.}]
\end{aligned}
```

Thus

```math
12\bigl(G_7(W_Q)-1\bigr)>L_Q.
```

Since `L_Q>0` for `Q>=17`, division by `L_Q` gives
`\rho(Q,7)>1`.

## Consequence for Candidate #17

The seven-layer capacity candidate contains two logically separate claims:

```math
\rho(Q,7)>1
```

and

```math
\rho(Q,r)\ge\rho(Q,7)
\quad\text{for every later conditioned layer }r.
```

This property proves the first claim for every integer `Q>=17`. The second
claim remains open. In particular, this proof does not infer short-window
behavior at later layers from a complete-period count.

## Related

- [A local count forces the k=2 shot-capacity premise](
  local-count-forces-k2-shot-capacity.md
  ) — converts the strict capacity inequality into a close pair.
- [Exact global 2-gap count](exact-global-two-gap-count.md) — gives the
  complete-period CRT count but does not localize it.
- [Seven-layer capacity floor](
  ../../candidates/seven-layer-capacity-floor.md
  ) — retains the open later-layer lower-envelope hypothesis.
