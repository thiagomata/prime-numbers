# Two-Class Survival From Residue Collision Energy

**Status:** Mathematically proved (conditional collision-energy lemma).
Stainless verification is not claimed here.

## Meaning

An incoming prime `r>2` destroys a 2-gap only when its start lies in one of two
specific residue classes modulo `r`. Pointwise equidistribution of every class
is therefore more information than the survival argument directly consumes.

This lemma bounds the two harmful classes using the second moment of the
residue histogram. The second moment has an exact combinatorial meaning: it
counts pairs of current 2-gap starts whose difference is divisible by `r`.
The result converts survival into a divisible-difference counting problem.

## Setup

Let `S` be a finite nonempty set of complete 2-gap starts immediately before
an incoming prime filter `r>2`. For every class `a modulo r`, define

```math
c_a=\#\{x\in S:x\equiv a\pmod r\},
\qquad
N=|S|=\sum_{a\bmod r}c_a.
```

Define the residue variance

```math
V_r(S)
=
\sum_{a\bmod r}
\left(c_a-\frac Nr\right)^2.
```

Let `K_r(S)` be the number of starts in `S` destroyed by filter `r`.

## Exact Harmful Count

A 2-gap starting at `x` has endpoints `x` and `x+2`. It is destroyed exactly
when

```math
x\equiv0\pmod r
\qquad\text{or}\qquad
x\equiv-2\pmod r.
```

The two classes are distinct because `r>2`. Therefore

```math
\boxed{
K_r(S)=c_0+c_{-2}.
}
```

## Second-Moment Bound

Write

```math
d_a=c_a-\frac Nr.
```

Then

```math
\begin{aligned}
K_r(S)-\frac{2N}{r}
&=d_0+d_{-2}
&&[\text{Exact Harmful Count}]\\
&\le |d_0+d_{-2}|\\
&\le\sqrt{2(d_0^2+d_{-2}^2)}
&&[\text{Cauchy--Schwarz}]\\
&\le\sqrt{2V_r(S)}.
&&[\text{By Definition of }V_r]
\end{aligned}
```

Hence

```math
\boxed{
K_r(S)
\le
\frac{2N}{r}+\sqrt{2V_r(S)}.
}
```

## Exact Collision Identity

Expanding the variance gives

```math
\begin{aligned}
V_r(S)
&=
\sum_{a\bmod r}
\left(
c_a^2-\frac{2Nc_a}{r}+\frac{N^2}{r^2}
\right)\\
&=
\sum_{a\bmod r}c_a^2
-\frac{2N}{r}\sum_{a\bmod r}c_a
+r\frac{N^2}{r^2}\\
&=
\sum_{a\bmod r}c_a^2-\frac{N^2}{r}.
\end{aligned}
```

Define the ordered collision count

```math
C_r(S)
=
\#\{(x,y)\in S^2:r\mid(x-y)\}.
```

For each residue class `a`, exactly `c_a^2` ordered pairs lie together in that
class. Therefore

```math
C_r(S)=\sum_{a\bmod r}c_a^2
```

and

```math
\boxed{
V_r(S)=C_r(S)-\frac{N^2}{r}.
}
```

## Autocorrelation Form For Post-3 Starts

Now suppose `S` is contained in a start interval of diameter `L` and filters
`2` and `3` are installed. Every start is `5 modulo 6`. For two starts
`x<y`, the collision condition

```math
r\mid(y-x)
```

is therefore equivalent to

```math
6r\mid(y-x),
```

because `gcd(6,r)=1`.

For a positive difference `d`, define the start autocorrelation

```math
A_S(d)
=
\#\{x:x\in S,\ x+d\in S\}.
```

Separating the `N` diagonal ordered pairs from the two orientations of every
off-diagonal pair gives the exact identity

```math
\boxed{
C_r(S)
=
N
+2
\sum_{1\le h\le\lfloor L/(6r)\rfloor}
A_S(6rh).
}
```

Each summand counts occurrences of the four endpoint offsets

```math
\{0,2,6rh,6rh+2\}.
```

Thus the open collision bound can be studied as an upper bound for a sum of
explicit four-point pattern counts, rather than as an abstract residue
histogram.

## Sufficient Energy Inequality

Because `r>2`, the quantity `N(1-2/r)` is positive. If

```math
\boxed{
2V_r(S)
<
N^2\left(1-\frac2r\right)^2,
}
```

then

```math
\begin{aligned}
K_r(S)
&\le\frac{2N}{r}+\sqrt{2V_r(S)}\\
&<
\frac{2N}{r}
+N\left(1-\frac2r\right)\\
&=N.
\end{aligned}
```

Thus not all `N` starts are destroyed, so at least one complete 2-gap survives
filter `r`.

Using the collision identity, the same sufficient condition is

```math
\boxed{
C_r(S)
<
N^2
\left(
\frac12-\frac1r+\frac{2}{r^2}
\right).
}
```

This is an exact algebraic reformulation of the stated energy criterion.

## Relation To Other Bounds

Candidate #12 controls the largest deviation of any residue class. The
present lemma instead consumes the global `L2` deviation and rewrites it as a
pair count. Neither criterion uniformly dominates the other at the constants
needed for survival.

The [sixfold harmful-residue capacity theorem](
harmful-residue-capacity-after-filter-three.md
) directly bounds the two harmful classes by their forced `6r` spacing. That
direct theorem can be stronger than global collision energy because variance
in harmless classes contributes to `V_r(S)`.

The energy route becomes useful only if sieve structure gives a collision
bound substantially sharper than the generic estimate

```math
C_r(S)\le N\max_a c_a.
```

The autocorrelation identity suggests a possible upper-bound-sieve approach to
the off-diagonal four-point patterns. Upper bounds do not face the parity
problem in exactly the same way as positive lower bounds. However, the
survival criterion is relative to `N^2`; an absolute upper bound for the
four-point correlations is useful only when paired with a sufficiently strong
lower bound for `N`.

## Limitation

The identities and the conditional implication are proved; the required upper
bound on `C_r(S)` is not. Complete-period uniformity computes the corresponding
energy over a full period but does not control a conditioned square window.

At a final conditioned layer, a collision estimate strong enough to satisfy
the displayed inequality may still encode the parity barrier. This lemma
changes the algebraic object to be studied—from worst residue occupancy to
divisible differences—but does not by itself lower the known analytic
difficulty.

## Related

- [Local pattern-residue balance](
  ../../candidates/local-pattern-residue-balance.md
  )
- [Sixfold harmful-residue capacity](
  ../../candidates/sixfold-harmful-residue-capacity.md
  )
- [Batched short-window discrepancy boundary](
  batched-short-window-discrepancy-boundary.md
  )
