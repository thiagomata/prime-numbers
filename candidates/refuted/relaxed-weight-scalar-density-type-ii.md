# Scalar-Density Type-II Orthogonality For The Relaxed Weight

**Status:** Refuted exact auxiliary statement around candidate #25.

## Refuted Statement

Let `2|Z|W` be squarefree wheels and define

```math
a(x)
=
\mathbf1_{\gcd(x,W)=1}
\mathbf1_{\gcd(x+2,Z)=1}.
```

Let

```math
\vartheta_Z
=
\prod_{\substack{p\mid Z\\p>2}}
\left(1-\frac1{p-1}\right),
\qquad
w(x)=a(x)-\vartheta_Z\mathbf1_{\gcd(x,W)=1}.
```

The proposed shortcut was that subtracting this exact scalar local density
removes all complete-wheel bilinear character modes. In precise form, for
every pair of bounded coefficient functions on

```math
G_W=(\mathbb Z/W\mathbb Z)^\times,
```

one hoped that the centered sum was orthogonal, or at least uniformly smaller
than the relaxed survivor count:

```math
\sum_{m,n\in G_W}\xi_m\kappa_nw(mn)=0
```

or, for one universal `c<1`,

```math
\left|
\sum_{m,n\in G_W}\xi_m\kappa_nw(mn)
\right|
\le
c\sum_{m,n\in G_W}a(mn)
```

whenever `|xi_m|,|kappa_n|<=1`.

Both statements are false once `3|Z`.

## Exact Counterexample

Let `chi_3` be the nonprincipal real character modulo `3`, and take

```math
\xi_m=\chi_3(m),
\qquad
\kappa_n=\chi_3(n).
```

If `a(mn)=1`, then `m,n` are units modulo `3` and the relaxed condition gives

```math
mn+2\not\equiv0\pmod3.
```

Hence `mn=2 modulo 3`, so every allowed pair has

```math
\xi_m\kappa_n=\chi_3(mn)=-1.
```

It follows exactly that

```math
\sum_{m,n\in G_W}\xi_m\kappa_na(mn)
=
-\sum_{m,n\in G_W}a(mn).
```

CRT makes the reduced residues of `W` balanced between the two unit classes
modulo `3`. Therefore

```math
\sum_{m\in G_W}\chi_3(m)=0,
```

and the scalar comparison contributes zero. Consequently

```math
\boxed{
\left|
\sum_{m,n\in G_W}\xi_m\kappa_nw(mn)
\right|
=
\sum_{m,n\in G_W}a(mn).
}
```

The centered correlation equals the full relaxed survivor count. This
refutes exact orthogonality and every strict uniform contraction `c<1`.

For the smallest project-shaped check, take `W=30` and `Z=6`. There are eight
reduced residues, 32 allowed ordered pairs, centered weighted correlation
`-32`, and scalar-comparison correlation zero.

## Scope

The counterexample does **not** refute candidate #25. It refutes only the
shortcut that the exact scalar density makes the relaxed periodic weight
pseudorandom against arbitrary product coefficients.

It also does not by itself determine the short hyperbolic sum
`X/2<mn<=X`, whose domain is not a complete wheel. The following routes remain
logically possible:

1. a comparison sequence that includes all fixed local character modes;
2. a local `W`-trick before the arbitrary-coefficient test;
3. a coefficient class restricted by the actual almost-prime identity; or
4. cancellation after the signed divisor sum on the actual short domain.

Any future Type-II formulation must specify which of these mechanisms removes
the exact modulo-3 obstruction.

## Related

- [Relaxed Almost-Prime Bilinear Remainder Has A Character Obstruction](
  ../../properties/sieve-sequence/relaxed-almost-prime-bilinear-character-obstruction.md)
- [Chen-Type Almost-Prime Survivor](../chen-type-almost-prime-survivor.md)
