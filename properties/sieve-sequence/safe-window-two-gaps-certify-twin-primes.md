# Safe-Window 2-Gaps Certify Twin Primes

**Status:** Mathematically proved. Stainless verification is not claimed here.

## Meaning

The square boundary explains why local 2-gap survival matters. After every
prime below the current head has been installed, accepted values below the
head's square are not merely candidates: they are primes.

## Setup

Let `q` be prime and let

```math
P_q=\prod_{r<q}r,
```

where `r` ranges over primes. Consider an integer `n` satisfying

```math
q\le n<q^2
\qquad\text{and}\qquad
\gcd(n,P_q)=1.
```

## Property

The integer `n` is prime. Consequently, if both endpoints of a 2-gap satisfy

```math
q\le x
\qquad\text{and}\qquad
x+2<q^2
```

and both are accepted after all filters below `q`, then `(x,x+2)` is a genuine
twin-prime pair.

## Proof

Suppose `n` were composite. It would have a prime divisor `r<=sqrt(n)`. Since
`n<q^2`, we have `sqrt(n)<q`, so `r<q`. Therefore `r` divides `P_q`, contrary
to `gcd(n,P_q)=1`. Hence `n` is prime.

Apply the same argument independently to `x` and `x+2`. Their difference is
`2`, so they form a twin-prime pair.

## Endpoint Discipline

The interval is half-open. The strict condition `x+2<q^2` matters because the
boundary value `q^2` is composite but is not divisible by a prime smaller than
`q`.

## Consequence

After batching every filter below `q`, proving that even one 2-gap survives in
`[q,q^2)` proves that this interval contains twin primes.

## Limitation

This is a certification theorem, not an existence theorem. It identifies what
a surviving safe-window 2-gap means; it does not prove that such a gap exists.
