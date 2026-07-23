# Sharp Local 2-Gap Survival Threshold

**Status:** Proved conditional implication. The required local abundance is not
proved here. Stainless verification is not claimed here.

## Meaning

This property gives a one-transition survival guarantee from the number of
2-gaps already known to lie in the next safe window. It uses the exact accepted
strike count rather than the much larger count of all integer multiples.

## Setup

Let `p>=5` be the newly installed filter, `q` the next prime after `p`, and

```math
W=[q,q^2).
```

Let `G_local(p,q)` count the pre-filter 2-gaps `(x,x+2)` satisfying

```math
q\le x
\qquad\text{and}\qquad
x+2<q^2.
```

Let

```math
K=\left\lfloor\frac{q^2-1}{p}\right\rfloor,
\qquad
A(p,q)=\pi(K)-\pi(p-1).
```

## Property

The number of surviving local 2-gaps satisfies

```math
G_{\mathrm{surviving}}(p,q)
\ge G_{\mathrm{local}}(p,q)-A(p,q).
```

In particular,

```math
\boxed{
G_{\mathrm{local}}(p,q)>A(p,q)
\Longrightarrow
G_{\mathrm{surviving}}(p,q)>0.
}
```

Because the quantities are integers, `A(p,q)+1` local 2-gaps are sufficient.

## Proof

The new filter removes exactly `A(p,q)` previously accepted values from `W`.
Since filter `3` is already installed, 2-gaps are endpoint-disjoint: one
removed accepted value can destroy at most one local 2-gap. Therefore at most
`A(p,q)` of the `G_local(p,q)` gaps can be destroyed. Subtraction gives the
lower bound and the positivity implication.

## Why This Threshold Is Useful

The raw multiple count is approximately `p`, but the exact accepted strike
count `A(p,q)` is often only a few values. The condition can therefore be much
stronger than a bound based on every multiple of `p` in the window.

## Exact Boundary Of The Result

This theorem does not prove the antecedent

```math
G_{\mathrm{local}}(p,q)>A(p,q).
```

It proves that local abundance, once established by another argument, is
enough for one transition. Repeating the conclusion at every later stage
requires a fresh abundance bound for every later safe window.
