# Harmful Residue Capacity After Filter Three

**Status:** Mathematically proved (conditional local-count lemma). Stainless
verification is not claimed here.

## Meaning

After filters `2` and `3` are installed, every 2-gap start has the same phase
modulo `6`. An incoming odd prime `r` can destroy a 2-gap only when its start
belongs to one of two residue classes modulo `r`. Combining these two facts
forces starts in either harmful class to be separated by at least `6r`.

This gives an absolute upper bound on how many 2-gaps one filter can destroy
inside a square window. It uses no random model and assumes no
equidistribution among residue classes.

## Setup

Fix a future prime head `Q` and a conditioned filter layer with incoming prime
`r`, where

```math
5\le r<Q.
```

Let

```math
W_Q=[Q,Q^2)
```

and let `S_r(W_Q)` be the set of starts of complete 2-gaps present immediately
before filter `r`. Write

```math
N=|S_r(W_Q)|
```

and define the available start diameter

```math
L_Q=Q^2-Q-3.
```

Completeness means that every start `x` satisfies

```math
Q\le x\le Q^2-3.
```

## One-Class Capacity

For every residue class `a` modulo `r`,

```math
\#\{x\in S_r(W_Q):x\equiv a\pmod r\}
\le
\left\lfloor\frac{L_Q}{6r}\right\rfloor+1.
```

### Proof

Because filters `2` and `3` are already installed, every 2-gap start satisfies

```math
x\equiv5\pmod6.
```

Choose two distinct starts `x<y` in the same class `a` modulo `r`. Their
difference is divisible by both `6` and `r`:

```math
\begin{aligned}
y-x&\equiv0\pmod6
&&[\text{Common Post-3 Phase}]\\
y-x&\equiv0\pmod r
&&[\text{Common Residue Class}].
\end{aligned}
```

Since `r>=5` is prime,

```math
\gcd(6,r)=1,
```

so

```math
y-x\equiv0\pmod{6r}.
```

Thus distinct starts in one class modulo `r` are separated by at least `6r`.
If that class contains ordered starts

```math
x_1<x_2<\cdots<x_t,
```

then

```math
\begin{aligned}
(t-1)6r
&\le x_t-x_1
&&[\text{Minimum Separation}]\\
&\le (Q^2-3)-Q
&&[\text{Window Endpoints}]\\
&=L_Q.
&&[\text{By Definition}]
\end{aligned}
```

Therefore

```math
t
\le
\left\lfloor\frac{L_Q}{6r}\right\rfloor+1.
\qquad[\text{Q.E.D.}]
```

## Two Harmful Classes

Filter `r` destroys a 2-gap starting at `x` exactly when

```math
x\equiv0\pmod r
\qquad\text{or}\qquad
x\equiv-2\pmod r.
```

The two classes are distinct because `r>2`. If `K_r(W_Q)` is the number of
destroyed complete 2-gaps, the one-class capacity gives

```math
\boxed{
K_r(W_Q)
\le
2\left(
\left\lfloor\frac{Q^2-Q-3}{6r}\right\rfloor+1
\right).
}
```

No union-bound over arbitrary classes is hidden here: these are exactly the
two classes selected by the filter.

## Local Survival Threshold

At least

```math
N-K_r(W_Q)
```

complete 2-gaps survive filter `r`. Consequently, the integer condition

```math
\boxed{
N
\ge
2\left\lfloor\frac{Q^2-Q-3}{6r}\right\rfloor+3
}
```

implies

```math
\begin{aligned}
N-K_r(W_Q)
&\ge
\left(
2\left\lfloor\frac{L_Q}{6r}\right\rfloor+3
\right)
-
2\left(
\left\lfloor\frac{L_Q}{6r}\right\rfloor+1
\right)\\
&=1.
\qquad[\text{Q.E.D.}]
\end{aligned}
```

Thus at least one complete 2-gap survives the layer.

## Comparison With The Order-Only Capacity Bound

The existing `k=2` local-count theorem uses only the order of starts and needs
approximately

```math
\frac{L_Q}{2r}
```

starts to force two gaps into an interval shorter than the shot spacing `2r`.
The new threshold needs approximately

```math
\frac{L_Q}{3r}.
```

The improvement comes from the extra congruence `x=5 modulo 6`. The two
theorems have different conclusions:

- the order-only theorem produces candidate #14's close-pair interval;
- this theorem directly forces one-layer survival, without necessarily
  producing a close pair.

## Limitation

The theorem bounds destructive capacity but does not prove the required
conditioned population lower bound. Near the last incoming prime `r<Q`, the
threshold is of order `Q`. Proving that every relevant conditioned square
window contains that many pre-filter 2-gaps remains an open local-abundance
problem and may still encounter the parity barrier.

Summing the one-layer capacities over all future filters is also too coarse
without controlling overlap: different primes may target the same 2-gaps.
The theorem should therefore be used layer by layer with the actual remaining
population, or inside a sharper batched argument that counts overlaps.

## Related

- [Isolation of 2-gaps after filtering by 3](
  two-gap-isolation-after-filter-three.md
  ) — supplies the common `5 modulo 6` start phase.
- [Exact filter frequency across repeated copies](
  copy-index-filter-frequency.md
  ) — supplies the two forbidden classes in copy-index coordinates.
- [A local count forces the k=2 shot-capacity premise](
  local-count-forces-k2-shot-capacity.md
  ) — the order-only threshold compared above.
- [Hereditary shot-spacing capacity](
  ../../candidates/hereditary-shot-spacing-capacity.md
  ) — the existing close-pair route.
