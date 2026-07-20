# Global Count Threshold That Forces Local Survival

**Status:** Proved sufficient condition. The condition is generally not met by
the known exact global count at large stages. Stainless verification is not
claimed here.

## Meaning

A global count normally says nothing about a particular short window. A local
conclusion becomes possible only when the global count is so large that all
2-gaps cannot physically fit outside the window. This property states that
extremal threshold exactly.

## Setup

Let `p>=5`, let `q` be the next prime, and let

```math
M=\prod_{r<p}r.
```

Assume the safe-window start positions map injectively modulo `M`; it is enough
that

```math
q^2-q<M.
```

Let `G_global(p)` be the complete-period 2-gap count. Define

```math
C(q)=
\left\lfloor\frac{q^2-8}{6}\right\rfloor
-\left\lfloor\frac{q-6}{6}\right\rfloor.
```

This is the number of integers `x` with

```math
q\le x,\qquad x+2<q^2,\qquad x\equiv5\pmod6.
```

Finally define the exact accepted strike count

```math
A(p,q)=
\pi\!\left(\left\lfloor\frac{q^2-1}{p}\right\rfloor\right)
-\pi(p-1).
```

## Property

The pre-filter local count obeys

```math
G_{\mathrm{local}}(p,q)
\ge
G_{\mathrm{global}}(p)
-\left(\frac M6-C(q)\right).
```

Therefore the purely global sufficient condition

```math
\boxed{
G_{\mathrm{global}}(p)
>
\frac M6-C(q)+A(p,q)
}
```

guarantees at least one surviving 2-gap in `[q,q^2)`.

## Proof

After filters `2` and `3`, every 2-gap start is `5 modulo 6`. One full period
of length `M` therefore has exactly `M/6` possible start slots. The safe window
contains `C(q)` of those slots, so its complement contains only `M/6-C(q)`.

Even if every complementary slot contains a 2-gap, any global gaps beyond that
capacity must lie inside the safe window. This proves the local lower bound.
At most `A(p,q)` local 2-gaps can then be destroyed by filter `p`. Strictly
exceeding the combined outside and destruction capacities forces a survivor.

## Practical Limitation

The exact global count has order roughly `M/log^2(p)`, while the outside-slot
capacity is close to `M/6` once `M` greatly exceeds `q^2`. Thus this sufficient
threshold quickly becomes much larger than the available global count.

The theorem is rigorous, but it demonstrates why global abundance alone is
too weak: a useful large-stage result needs positional information sharper
than worst-case placement outside the safe window.
