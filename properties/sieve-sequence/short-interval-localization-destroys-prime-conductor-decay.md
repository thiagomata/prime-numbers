# Short-Interval Localization Destroys Prime Conductor Decay

**Status:** Mathematically proved finite Fourier lemma. Stainless verification
is not claimed.

## Meaning

The complete CRT set of 2-gap starts has very little Fourier energy in
characters that are nontrivial at a fixed installed prime `p`: the exact
fraction is `2/p`. It is tempting to retain that decay after restricting the
starts to a short square-window interval.

The opposite happens at the level of a single prime projection. If the
interval is no longer than `n/p`, then it contains at most one point in each
fiber modulo `n/p`. For any indicator supported in that interval, the exact
fraction of Fourier energy in characters nontrivial at `p` is

```math
1-\frac1p.
```

Thus a conductor-block proof cannot simply transfer the complete-set weights
through interval localization. It needs cancellation involving the difference
sum, or some other structure beyond localized spectral mass.

## Setup

Let

```math
n=pm,
\qquad
\gcd(p,m)=1,
```

where `p` is prime. Use the CRT identification

```math
\mathbb Z/n\mathbb Z
\cong
\mathbb Z/p\mathbb Z
\times
\mathbb Z/m\mathbb Z.
```

Let

```math
g:\mathbb Z/n\mathbb Z\longrightarrow\{0,1\}
```

and write

```math
J=\sum_{x\bmod n}g(x).
```

For each quotient coordinate `y modulo m`, define the fiber population

```math
F(y)
=
\sum_{a\bmod p}g(a,y).
```

## Exact Prime-Projection Identity

Every additive character modulo `n` factors uniquely as

```math
\chi=\eta\psi,
```

where `eta` is a character modulo `p` and `psi` is a character modulo `m`.
When `eta=1`,

```math
\widehat g(1,\psi)
=
\sum_{y\bmod m}
F(y)\overline{\psi(y)}.
```

Parseval on `Z/mZ` therefore gives

```math
\sum_{\psi}
|\widehat g(1,\psi)|^2
=
m\sum_{y\bmod m}F(y)^2.
```

Parseval on the full group gives

```math
\sum_{\eta,\psi}
|\widehat g(\eta,\psi)|^2
=
n\sum_xg(x)^2
=
nJ.
```

Subtracting the characters trivial at `p` proves the exact identity

```math
\boxed{
\sum_{\substack{\eta\ne1\\\psi}}
|\widehat g(\eta,\psi)|^2
=
nJ
-
\frac np
\sum_{y\bmod m}F(y)^2.
}
```

## Short-Interval Specialization

Suppose `g` is supported in a cyclic interval `I` of length

```math
L\le m=\frac np.
```

Two distinct points in one fiber modulo `m` differ cyclically by a nonzero
multiple of `m`. An interval of at most `m` consecutive residues contains at
most one such point. Hence

```math
F(y)\in\{0,1\}
```

for every `y`, and

```math
\sum_yF(y)^2
=
\sum_yF(y)
=
J.
```

The prime-projection identity becomes

```math
\boxed{
\sum_{\substack{\eta\ne1\\\psi}}
|\widehat g(\eta,\psi)|^2
=
nJ\left(1-\frac1p\right).
}
```

Since the total energy is `nJ`, exactly the fraction

```math
1-\frac1p
```

lies in characters nontrivial at `p`.

## Contrast With The Complete CRT Set

Let `f=1_U` be the complete quotient set of 2-gap starts. At the local prime
`p`, exactly two residue classes are forbidden. For each allowed choice of the
other CRT coordinates, its fiber population is therefore

```math
F(y)=p-2.
```

There are `G/(p-2)` nonempty fibers, where `G=|U|`, so

```math
\sum_yF(y)^2
=
(p-2)G.
```

The same identity now gives

```math
\sum_{\substack{\eta\ne1\\\psi}}
|\widehat f(\eta,\psi)|^2
=
\frac{2}{p}nG.
```

The complete-set nontrivial fraction `2/p` is therefore transformed by a
short interval into the localized fraction `1-1/p`.

## Consequence For The Proof Strategy

Grouping the localized Fourier spectrum by the old complete-set conductor
weights cannot prove the desired rectangle estimate: those weights are not
stable under localization. For every prime satisfying `L<=n/p`, localization
places almost all `L2` energy in the nontrivial-at-`p` block.

This does not prove that Fourier analysis is impossible. It rules out a
specific strategy: bounding each localized conductor block as though it still
carried the complete CRT factor `2/p`. A viable argument must instead exploit
the joint interaction between these newly created high-conductor components
and the difference-prefix kernel `D_H`, or return to a physical-space
large-sieve or dispersion estimate normalized by the actual local population.

## Related

- [Localized two-gap correlation: Fourier boundary](
  localized-two-gap-correlation-fourier-boundary.md
  )
- [Fourier bound for two-gap correlation prefixes](
  fourier-two-gap-correlation-prefix-bound.md
  )
- [Cumulative weighted collision budget](
  ../../candidates/cumulative-weighted-collision-budget.md
  )
