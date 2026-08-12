# Two-Gap Pair Local Factor By Separation

**Status:** Mathematically proved (complete-period theorem). Stainless
verification is not claimed here.

## Meaning

Two 2-gaps separated by `d` form the four endpoint offsets

```math
\{0,2,d,d+2\}.
```

For each installed prime, the number of forbidden translations depends only on
whether that prime divides `d`, `d-2`, or `d+2`. This gives an exact local
factor and, by CRT, an exact complete-period count for the paired pattern.

The factor explains why same-residue collisions are enhanced: when a prime
divides the separation, the two copies impose the same two forbidden classes
instead of four generic classes.

## Setup

Let `d>0` be a multiple of `6`. A translated pair of 2-gaps has endpoints

```math
x,\quad x+2,\quad x+d,\quad x+d+2.
```

For a prime `p`, define

```math
\nu_p(d)
=
\#\{0,-2,-d,-d-2\pmod p\}.
```

These are exactly the residue classes of `x modulo p` for which at least one
endpoint is divisible by `p`. Hence `p-\nu_p(d)` translations modulo `p`
survive that filter.

## Small Installed Primes

Because `d` is divisible by `6`, all four offsets are even. Modulo `2`, they
occupy one class:

```math
\nu_2(d)=1,
\qquad
2-\nu_2(d)=1.
```

Modulo `3`, the two offsets `0,d` agree and the two offsets `2,d+2` agree.
They form two distinct classes:

```math
\nu_3(d)=2,
\qquad
3-\nu_3(d)=1.
```

Thus filters `2` and `3` each leave one possible translation class.

## Local Factor For p At Least 5

For every prime `p>=5`,

```math
\boxed{
\nu_p(d)
=
\begin{cases}
2,&p\mid d,\\
3,&p\mid d-2\text{ or }p\mid d+2,\\
4,&p\nmid d(d-2)(d+2).
\end{cases}
}
```

### Proof

Within each 2-gap, the two offsets are distinct modulo `p` because `p>2`.
The only possible equalities between offsets from the two gaps are

```math
\begin{aligned}
0&\equiv d\pmod p
&&\Longleftrightarrow p\mid d,\\
0&\equiv d+2\pmod p
&&\Longleftrightarrow p\mid d+2,\\
2&\equiv d\pmod p
&&\Longleftrightarrow p\mid d-2,\\
2&\equiv d+2\pmod p
&&\Longleftrightarrow p\mid d.
\end{aligned}
```

If `p|d`, both corresponding offsets agree and the four offsets reduce to the
two classes `{0,2}`.

If `p|d-2` or `p|d+2`, exactly one cross-equality occurs, leaving three
classes. The two cases cannot occur simultaneously for `p>=5`, because that
would make `p` divide their difference `4`.

If `p` divides none of `d,d-2,d+2`, no cross-equality occurs and all four
offsets are distinct. These cases are exhaustive. `[Q.E.D.]`

The number of allowed translations modulo `p` is therefore

```math
\boxed{
p-\nu_p(d)
=
\begin{cases}
p-2,&p\mid d,\\
p-3,&p\mid d-2\text{ or }p\mid d+2,\\
p-4,&p\nmid d(d-2)(d+2).
\end{cases}
}
```

## Exact Complete-Period Count

Let `P` be a finite set of installed primes containing `2` and `3`, and let

```math
M=\prod_{p\in P}p.
```

The translations `x modulo M` for which all four endpoints are coprime to `M`
are obtained by independently choosing one allowed translation class modulo
each `p in P`. By the Chinese remainder theorem, their exact number is

```math
\boxed{
G_P^{(2,2)}(d)
=
\prod_{p\in P}
\left(p-\nu_p(d)\right).
}
```

Because the factors at `2` and `3` are both `1`, this can be written

```math
G_P^{(2,2)}(d)
=
\prod_{\substack{p\in P\\p\ge5}}
\begin{cases}
p-2,&p\mid d,\\
p-3,&p\mid d-2\text{ or }p\mid d+2,\\
p-4,&p\nmid d(d-2)(d+2).
\end{cases}
```

Every factor is positive for `p>=5`, so the paired pattern is admissible for
every separation `d` divisible by `6`.

## Collision Enhancement

For a generic prime not dividing `d(d-2)(d+2)`, the paired pattern has local
factor `p-4`. If `p|d`, the factor becomes `p-2`. The enhancement ratio is

```math
\frac{p-2}{p-4}.
```

Thus a separation divisible by the incoming prime has a larger paired-pattern
local density than a generic separation. Candidate #21's collision energy is
measuring the cumulative effect of exactly these enhanced separations.

Primes dividing `d-2` or `d+2` give the intermediate factor `p-3`.

## Limitation

The CRT product is exact only over a complete period modulo `M`. It does not
count occurrences in the shorter square window `[Q,Q^2)`.

Using this theorem in candidate #21 requires two additional inputs:

1. an average bound for the product of local enhancement factors over the
   relevant separations `d`;
2. control of the short-window error after conditioning on earlier filters.

The first is a singular-series averaging problem. The second is the existing
short-window boundary. Neither follows from the complete-period product alone.

## Related

- [Exact global `(2,4,2)` cluster count](
  exact-global-two-gap-cluster-count.md
  )
- [Two-class survival from residue collision energy](
  two-class-survival-from-collision-energy.md
  )
- [Weighted collision-energy chain survival](
  weighted-collision-energy-chain-survival.md
  )
- [Cumulative weighted collision budget](
  ../../candidates/cumulative-weighted-collision-budget.md
  )
