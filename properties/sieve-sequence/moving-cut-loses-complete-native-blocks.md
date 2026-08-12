# Moving Cut Loses Complete Native Blocks

**Status:** Mathematically proved conditional obstruction. The asymptotic
corollary uses Bertrand's postulate and the prime number theorem as explicit
external mathematical dependencies. Stainless verification is not claimed.

## Meaning

The Fixed Native Cut Failure property proves that a native cut capable of clearing candidate #24's
original threshold cannot remain fixed: its first suffix prime must grow at
least on the order of the square root of the chain length.

Moving the cut creates the opposite pressure. The native modulus is the
product of every prime preceding that suffix prime. Once this product exceeds
the square-window start length, the interval contains no complete native
block. The Native-Period Hybrid Envelope property can still apply Bessel to the one incomplete block, but it
loses the exact complete-block cancellation that motivated the moving cut.

The exact theorem below isolates the two requirements. The prime number
theorem then shows that they are eventually incompatible.

## Setup

Let `Q` be a future prime head, and let the complete conditioned chain contain
every prime

```math
5\le r_i<Q.
```

Write

```math
m=\pi(Q)-3,
```

because `Q` itself is not installed and the primes `2,3` belong to the base
modulus. Define

```math
D=Q^2-Q-3,
\qquad
H=D+1=Q^2-Q-2.
```

Fix a cut

```math
2\le k<m.
```

Its native modulus is

```math
M_k
=
\prod_{p<r_k}p
=
2\cdot3\prod_{i<k}r_i.
```

Let

```math
\vartheta(x)
=
\sum_{p\le x}\log p.
```

Since `r_(k-1)` is the prime immediately before `r_k`,

```math
\boxed{
\log M_k
=
\vartheta(r_{k-1}).
}
```

## Exact Conditional Modulus Bound

Assume all of the following:

1. candidate #17's local-count threshold holds at the first suffix layer
   `r_k`;
2. the cut clears candidate #24's original threshold,

   ```math
   \mathcal U_k^{\mathrm{hyb}}
   <
   \frac{T^2}{2W_-};
   ```

3. the native modulus fits inside the start interval,

   ```math
   M_k\le H;
   ```

4. for some constant `c>0`,

   ```math
   \vartheta(r_{k-1})\ge c r_{k-1};
   ```

5. Bertrand's inequality holds for the consecutive primes,

   ```math
   r_k<2r_{k-1}.
   ```

The Fixed Native Cut Failure property gives the necessary moving-prime bound

```math
r_k
\ge
2+
\frac{\sqrt{7m/3}}{1+6/D}.
```

On the other hand,

```math
\begin{aligned}
\log H
&\ge\log M_k
&&[M_k\le H]\\
&=\vartheta(r_{k-1})
&&[\text{Native Primorial Identity}]\\
&\ge c r_{k-1}
&&[\vartheta\text{ Lower Bound}]\\
&>\frac c2r_k
&&[\text{Bertrand}].
\end{aligned}
```

Combining the lower and upper requirements for `r_k` gives

```math
\log H
>
\frac c2
\left(
2+
\frac{\sqrt{7m/3}}{1+6/D}
\right).
```

Rearranging and squaring yields the exact necessary condition

```math
\boxed{
m
<
\frac37
\left(1+\frac6D\right)^2
\left(
\frac{2\log H}{c}-2
\right)^2.
}
```

Thus a threshold-clearing cut with at least one complete native block forces
the chain length to be at most logarithmic-squared in the window length,
provided the stated `theta` lower bound holds.

## Prime-Number-Theorem Corollary

The following inputs are external to the project's Stainless verification:

```math
\vartheta(x)\sim x,
\qquad
\pi(x)\sim\frac{x}{\log x}.
```

Choose any fixed `0<c<1`. The first asymptotic gives

```math
\vartheta(x)\ge cx
```

for all sufficiently large `x`. Bertrand's postulate supplies the consecutive
prime inequality used above.

For the actual full chain,

```math
m
=
\pi(Q)-3
\sim
\frac{Q}{\log Q},
```

whereas

```math
H=Q^2-Q-2
```

gives

```math
\log^2 H
\sim
4\log^2Q.
```

Therefore

```math
\frac{m}{\log^2H}
\sim
\frac{Q}{4\log^3Q}
\longrightarrow\infty.
```

The exact logarithmic-squared necessary condition consequently fails for all
sufficiently large future prime heads. Hence, under candidate #17 at the first
suffix layer,

```math
\boxed{
\mathcal U_k^{\mathrm{hyb}}
<
\frac{T^2}{2W_-}
\quad\Longrightarrow\quad
M_k>H
}
```

for every sufficiently large `Q` and every cut `k`.

Since `0<H<M_k`, the Native-Period Hybrid Envelope property's remainder is then

```math
\boxed{
s_k
=
H\bmod M_k
=
H.
}
```

There are no complete native blocks to cancel.

## Boundary

This theorem does not prove that no moving-cut Bessel estimate can work.
When `M_k>H`, the Native-Period Hybrid Envelope property still gives an orthogonality constraint on the
single incomplete interval block. The result proves only that complete-block
cancellation disappears for every sufficiently large cut that avoids the
suffix obstruction.

It also does not address the capacity-relaxed threshold

```math
\frac{T^2}{2W_-}+\Gamma_{\mathrm{cap}}.
```

Finally, the asymptotic conclusion depends explicitly on classical external
prime-distribution theorems. The exact logarithmic-squared inequality remains
valid under its five stated finite hypotheses without invoking the full PNT.

The Incomplete-Block Bessel Bound property subsequently answers the one-incomplete-block question: at the
moving-prime scale forced by the Fixed Native Cut Failure property, the normalized capacity box fits
inside `s_k=H`, so `e_k=0`. Thus the capacity-plus-native-Bessel framework is
exhausted for the original threshold under full candidate #17. The Capacity Stability Gap property
then proves that `Gamma_cap` cannot rescue the separate capacity envelope.
The remaining routes are localized control of actual harmful excess or a
genuinely different cross-layer inequality.

No empirical evidence is used in this result.

## Related

- [Every Fixed Native Cut Fails The Original Threshold](every-fixed-native-cut-fails-original-threshold.md)
- [Native-Period Bessel and Capacity Give a Sharp Hybrid Envelope](native-period-bessel-capacity-hybrid-envelope.md)
- [Incomplete-Block Bessel Excludes No Capacity](incomplete-block-bessel-excludes-no-capacity.md)
- [Recent Prime-Producing Sieves: A Deep-Dive For The Perfect-Scenario Problem](research/recent-prime-producing-sieves-deep-dive.md)
- [Weighted Harmful-Excess Quadratic Survival](../../candidates/weighted-harmful-excess-quadratic-survival.md)
