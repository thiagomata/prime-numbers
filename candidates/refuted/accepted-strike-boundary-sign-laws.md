# Accepted-Strike Boundary Sign Laws

**Status:** Refuted by an exact counterexample.

**Related live candidate:** #23, accepted-anchor strike density.

## Refuted Statement 1: Universal Sign

For every prime future head `Q` and every primorial old-filter modulus `P`
whose prime factors are smaller than `Q`, the centered accepted-anchor
boundary error

```math
E_P(Q,Q^2)
=
C_P(Q,Q^2)
-
(Q^2-Q)\frac{\varphi(P)}P
```

always has one fixed sign.

This statement is false.

## Refuted Statement 2: Sign Preservation

For a fixed prime-square window `[Q,Q^2)`, adjoining the next old prime filter
cannot change the sign of `E_P(Q,Q^2)`.

This statement is also false.

## Exact Counterexample

Fix

```math
Q=19,
\qquad
[Q,Q^2)=[19,361).
```

For

```math
P=2310=2\cdot3\cdot5\cdot7\cdot11,
```

exact finite inclusion--exclusion gives

```math
C_{2310}(19,361)=71,
\qquad
\varphi(2310)=480.
```

Therefore

```math
E_{2310}(19,361)
=
71-\frac{342\cdot480}{2310}
=
-\frac5{77}
<
0.
```

Adjoin the next prime filter `13`:

```math
P'=30030=2310\cdot13.
```

Exact finite inclusion--exclusion gives

```math
C_{30030}(19,361)=67,
\qquad
\varphi(30030)=5760.
```

Hence

```math
E_{30030}(19,361)
=
67-\frac{342\cdot5760}{30030}
=
\frac{1403}{1001}
>
0.
```

Thus the boundary error changes sign when filter `13` is installed:

```math
E_{2310}(19,361)<0<E_{30030}(19,361).
```

This one exact transition refutes both universal statements.

## What Remains Open

The counterexample does not refute candidate #23. In particular, it does not
exclude:

1. a weighted mean-square bound for the boundary errors;
2. cancellation after averaging across future heads;
3. a bound on the magnitude rather than the sign;
4. a theorem using additional arithmetic structure beyond the primality of
   `Q`.

Those possibilities require a new estimate for the Möbius-residue sum. They
cannot be justified by assuming favorable sign or sign preservation.

## Established Counterexample Source

- [Prime-square window boundary residue formula](
  ../../properties/sieve-sequence/prime-square-window-boundary-residue-formula.md
  )
- [Accepted-anchor strike density](
  ../accepted-anchor-strike-density.md
  )
