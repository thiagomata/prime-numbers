# Complete-Period Uniformity Of Harmless 2-Gap Classes

**Status:** Mathematically proved exact identities. Stainless verification is
not claimed.

## Meaning

Candidate #22 measures nonuniformity among the `r-2` residue classes that
survive filter `r`. Over one complete CRT period, those harmless classes are
exactly uniform. The harmless energy is therefore zero.

If a longer interval contains complete periods plus a remainder prefix, the
complete periods add the same count to every harmless class and disappear
after centering. All harmless energy comes from the remainder.

Thus #22 is not missing a complete-period density theorem. It is entirely a
short-window localization problem.

## Setup

Let `P` be a squarefree product of installed primes containing `2` and `3`,
and let `r>=5` be a prime not dividing `P`. Set

```math
\mathcal M=Pr.
```

Consider the cyclic 2-gap starts `x modulo mathcal M` for which

```math
\gcd(x(x+2),\mathcal M)=1.
```

For a harmless residue

```math
a\notin\{0,-2\}\pmod r,
```

let

```math
d_a
=
\#\{
x\pmod{\mathcal M}:
x\equiv a\pmod r,\
\gcd(x(x+2),\mathcal M)=1
\}.
```

## Equal Count In Every Harmless Class

Fix a harmless class `a modulo r`. Its two endpoints avoid divisibility by
`r` by definition.

For every prime `p|P`, a 2-gap start must avoid the two classes

```math
0
\qquad\text{and}\qquad
-2
\pmod p.
```

At `p=2`, these coincide and leave one class. At `p=3`, they leave one
possible 2-gap-start class. Every installed prime `p>=5` leaves exactly `p-2`
classes.

The Chinese remainder theorem makes these choices independent of the fixed
harmless class modulo `r`. Therefore

```math
\boxed{
d_a
=
B_P
:=
\prod_{\substack{p\mid P\\p\ge5}}
(p-2)
}
```

for every `a notin {0,-2} modulo r`.

There are `r-2` harmless classes, so the complete-period survivor population
is

```math
\boxed{
M=(r-2)B_P.
}
```

## Zero Complete-Period Harmless Energy

The harmless-class mean is

```math
\frac{M}{r-2}=B_P.
```

Since every class count equals this mean,

```math
\boxed{
U
=
\sum_{a\notin\{0,-2\}}
\left(
d_a-\frac{M}{r-2}
\right)^2
=
0.
}
\qquad[\text{Q.E.D.}]
```

The same result appears in collision form:

```math
\sum_{a\notin\{0,-2\}}d_a^2
=(r-2)B_P^2
=
\frac{M^2}{r-2}.
```

## Complete Blocks Plus A Prefix

Now let an integer interval contain `q` complete periods modulo `mathcal M`
plus one remainder segment. Let `e_a` be the number of surviving starts in
the remainder whose residue modulo `r` is the harmless class `a`. Then the
total class counts are

```math
d_a=qB_P+e_a.
```

Write

```math
E=\sum_{a\notin\{0,-2\}}e_a.
```

The total survivor population is

```math
M=q(r-2)B_P+E,
```

so its harmless-class mean is

```math
\frac{M}{r-2}
=
qB_P+\frac{E}{r-2}.
```

Subtracting the mean cancels every complete-period contribution:

```math
d_a-\frac{M}{r-2}
=
e_a-\frac{E}{r-2}.
```

Consequently,

```math
\boxed{
U
=
\sum_{a\notin\{0,-2\}}
\left(
e_a-\frac{E}{r-2}
\right)^2.
}
\qquad[\text{Q.E.D.}]
```

The harmless energy of the whole interval is exactly the harmless energy of
its remainder prefix.

## Consequence For Candidate #22

Complete-period CRT uniformity contributes no error to candidate #22. The
open weighted theorem concerns only incomplete square-window prefixes.

At late conditioned layers, the primorial period is much larger than
`[Q,Q^2)`, so the square window contains no complete block. In that regime the
identity is a classification, not an estimate: it explains why
complete-period counting cannot bound the remaining prefix energy.

The theorem does show what any successful argument must improve upon. It must
control how a short consecutive prefix samples the exactly balanced cyclic
harmless classes.

## Limitation

Equal counts over a complete period do not imply small discrepancy in an
arbitrary short interval. The immediate bound obtained by treating the
remainder class counts independently can still be quadratic in the remainder
population.

Candidate #22 therefore needs a localization theorem, a short-prefix
correlation estimate, or another structural constraint on the order of the
cyclic harmless classes.

## Related

- [Harmless energy as a fixed-set pair correlation](
  harmless-energy-fixed-set-pair-form.md
  )
- [Complete-period two-gap pair-correlation average](
  complete-period-two-gap-pair-correlation-average.md
  )
- [Conditioned harmless-class collision energy](
  ../../candidates/conditioned-harmless-class-collision-energy.md
  )
