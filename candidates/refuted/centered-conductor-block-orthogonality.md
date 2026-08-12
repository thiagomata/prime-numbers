# Centered Conductor-Block Orthogonality

**Status:** Refuted exact auxiliary statement around candidate #22.

## Refuted Statement

Let `mathsf A_q` and `mathsf A_(q')` be the inverse-phase matrices for two
distinct exact Fourier conductors `q,q'|P`, and let `C` subtract the mean
across the harmless classes.

The proposed universal law was

```math
q\ne q'
\quad\Longrightarrow\quad
\mathsf A_q^*C\mathsf A_{q'}=0.
```

A stronger hoped-for specialization asserted the same conclusion whenever

```math
\gcd(q,q')=1.
```

Both statements are false.

## Exact Counterexample

Take

```math
P=30,
\qquad
r=7,
\qquad
A=11.
```

The inverse phases on the harmless classes are

```math
(15,28,11,23,19)
\pmod {30}.
```

For the distinct coprime conductors

```math
q=2,
\qquad
q'=3,
```

the exact centered Ramanujan trace calculation gives

```math
\boxed{
\|\mathsf A_2^*C\mathsf A_3\|_{\mathrm{HS}}^2
=
\frac{168}{25}
>
0.
}
```

Therefore

```math
\mathsf A_2^*C\mathsf A_3\ne0.
```

This single exact counterexample refutes both universal orthogonality laws.

## Scope

The counterexample does not refute candidate #22. It refutes only the shortcut
that distinct or coprime conductor blocks can be recombined by exact
orthogonality after harmless-class centering.

A weighted bilinear estimate using the actual CRT coefficients, interval
multipliers, or chain weights remains logically possible.

## Related

- [Centered Ramanujan cross-conductor geometry](
  ../../properties/sieve-sequence/centered-ramanujan-cross-conductor-geometry.md
  )
- [Conditioned harmless-class collision energy](
  ../conditioned-harmless-class-collision-energy.md
  )
