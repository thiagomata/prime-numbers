# Incremental Danger-Annulus Decomposition

**Status:** Mathematically proved. This note does not claim Stainless
verification or an annular 2-gap population theorem.

## Preconditions

Let `p<q` be consecutive primes with `p>=5`. Consider the transition that
installs filter `p` after every prime filter below `p` has already been
installed.

The full square-safe value window remains

```math
W_q=[q,q^2).
```

It is the correct certification region: a surviving 2-gap wholly below `q^2`
after all filters below `q` certifies a twin-prime pair. The decomposition below
does not replace that theorem. It separates the part already covered by the
previous square threshold from the values newly exposed at this transition.

## Value Annulus and Newly Exposed Starts

Define the accepted-value danger annulus by

```math
V_{p,q}=[p^2,q^2).
```

For a gap of width `h`, its upper endpoint is newly exposed exactly when its
start `x` satisfies

```math
p^2\le x+h<q^2.
```

Thus the geometric newly exposed start interval is

```math
D^{(h)}_{p,q}=[p^2-h,q^2-h).
```

The lower boundary does not survive filter `p`:

```math
x=p^2-h
\quad\Longrightarrow\quad
x+h=p^2
\quad\Longrightarrow\quad
p\mid(x+h).
```

This statement is only about the numerical exposure range. It does not assert
that every coordinate in the interval starts an accepted gap.

## Phase-Compatible 2-Gap Coordinates

After filters `2` and `3`, every actual 2-gap start is congruent to `5` modulo
`6`. Every prime `p>=5` is congruent to `1` or `5` modulo `6`, and hence

```math
p^2\equiv1\pmod 6.
```

The geometric boundary start `p^2-2` is phase-compatible but is destroyed at
its upper endpoint `p^2`. The next phase-compatible coordinate is `p^2+4`.
Define

```math
X_D(p,q)=
\left\{
x\in\mathbb Z:
p^2+4\le x<q^2-2,
\quad x\equiv5\pmod6
\right\}.
```

This is the exact phase-compatible coordinate set after the forced boundary;
membership in `X_D(p,q)` does not imply that `(x,x+2)` is an actual pre-filter
2-gap.

Let `L_D(p,q)` be the number of actual pre-filter 2-gaps whose starts belong to
`X_D(p,q)`. Let `K_D(p,q)` be the number of those gaps destroyed when filter
`p` is installed.

## Accepted Strikes Are Confined to the Annulus

An accepted filter-`p` strike in `W_q` has the exact form

```math
pr,
\qquad r\text{ prime},
\qquad p\le r\le
\left\lfloor\frac{q^2-1}{p}\right\rfloor.
```

Therefore every accepted strike is at least `p^2` and lies in `V_{p,q}`. The
full-window and danger-annulus accepted strike-value counts are identical:

```math
A_{full}(p,q)
=A_{danger}(p,q)
=A(p,q).
```

This is an equality of accepted strike-value counts. It is not an equality of
the full-window and annular 2-gap populations.

## Raw Annular Capacity

Let

```math
d=q-p.
```

Because `p^2` is itself a multiple of `p`, the number of raw multiples of `p`
in the half-open value annulus is

```math
\begin{aligned}
R_V(p,q)
&=
\left\lceil\frac{q^2-p^2}{p}\right\rceil,\\
&=
\left\lceil\frac{(q-p)(q+p)}{p}\right\rceil,\\
&=
\left\lceil\frac{d(2p+d)}{p}\right\rceil,\\
&=
2d+\left\lceil\frac{d^2}{p}\right\rceil.
\end{aligned}
```

The exact accepted count is no larger than this raw count:

```math
A(p,q)\le R_V(p,q).
```

## Effective Destruction Capacity

The compulsory strike `p^2=p*p` is included in `A(p,q)`. Indeed, Bertrand's
postulate gives `q<2p`, and `2p<p^2` for `p>=5`, so

```math
q<p^2<q^2.
```

No prime below `p` divides `p^2`, so this value survives every old filter and
is removed only when filter `p` is installed.

However, `p^2` is not an endpoint of any gap counted by `L_D(p,q)`, because
every such start is at least `p^2+4`. After filter `3`, distinct 2-gaps do not
share endpoints, so every other accepted strike destroys at most one counted
gap. Consequently,

```math
\begin{aligned}
K_D(p,q)
&\le A(p,q)-1,\\
&\le R_V(p,q)-1,\\
&=
2d+\left\lceil\frac{d^2}{p}\right\rceil-1.
\end{aligned}
```

This is sharper than charging every full-window accepted strike against the
refined annular population.

## Limitation

The decomposition and capacity bound do not prove

```math
L_D(p,q)>0
```

or the sufficient surplus

```math
L_D(p,q)>A(p,q)-1.
```

Complete-period repetition gives exact global counts but does not force a
positive population inside this shorter annular interval. A short-window lower
bound, maximum-empty-arc bound, or another localization theorem remains
necessary.

## Related

- [Safe-window 2-gaps certify twin primes](safe-window-two-gaps-certify-twin-primes.md)
- [Exact accepted local filter strikes](exact-accepted-local-filter-strikes.md)
- [2-gap isolation after filter 3](two-gap-isolation-after-filter-three.md)
- [Sharp local 2-gap survival threshold](sharp-local-two-gap-survival-threshold.md)
