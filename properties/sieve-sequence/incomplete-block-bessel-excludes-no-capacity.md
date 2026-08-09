# Incomplete-Block Bessel Excludes No Capacity

**Status:** Mathematically proved conditional obstruction. The asymptotic
corollary uses Bertrand's postulate and the prime number theorem as explicit
external mathematical dependencies. Stainless verification is not claimed.

## Meaning

Property #79 proves that a moving native cut far enough to avoid candidate
#24's suffix obstruction eventually has modulus larger than the entire
square-window start interval. The Bessel constraint then sees one incomplete
block and has remainder budget equal to the whole interval length.

This property proves that the normalized capacity box eventually fits inside
that budget. Hence the incomplete-block Bessel constraint excludes no
capacity mass, the overflow `e_k` vanishes, and the hybrid envelope equals the
all-capacity envelope at that cut.

Combined with the earlier fixed-cut obstruction, this exhausts the current
capacity-plus-native-Bessel interface for candidate #24's original threshold
under candidate #17. It does not exhaust the capacity-relaxed threshold or
localized residue estimates.

## Setup

Use the complete conditioned chain

```math
r_0=5<r_1<\cdots<r_{m-1}<Q
```

for a future prime head `Q>=17`. Define

```math
D=Q^2-Q-3,
\qquad
H=D+1=Q^2-Q-2,
```

```math
a_i=1-\frac2{r_i},
\qquad
P_i=\prod_{j<i}a_j.
```

Fix a cut `2<=k<m`. The paired-survivor density before filter `r_i` is

```math
d_i=\frac{P_i}{6},
```

because the base pair-start density after filters `2,3` is `1/6`.

Property #72's exact native norm is

```math
q_{i,k}
=
M_kd_i\frac2{r_i}a_i
=
\frac{M_kP_i(r_i-2)}{3r_i^2}.
```

## Universal Capacity Numerator Bound

At layer `i`, the harmful count satisfies

```math
0\le K_i\le N_i,
```

and `0<=2N_i/r_i<=N_i`. Hence

```math
\left|
K_i-\frac{2N_i}{r_i}
\right|
\le N_i.
```

Property #70's sharp endpoint maximum consequently obeys

```math
\boxed{X_i\le N_i^2.}
```

The conditioned populations decrease, so `N_i<=N_0`. Before filter `5`, all
complete 2-gap starts occupy one residue class modulo `6`, giving

```math
N_0
\le
\left\lfloor\frac D6\right\rfloor+1
\le
\frac D5,
```

where the last inequality uses `D>=269>30`. Therefore

```math
\boxed{X_i\le\frac{D^2}{25}.}
```

## Universal Native-Norm Denominator Bound

For every `i<k`, monotonicity gives

```math
P_i\ge P_k,
\qquad
r_i<r_k.
```

The function

```math
x\longmapsto\frac{x-2}{x^2}
```

is decreasing for `x>=4`. Hence

```math
\frac{r_i-2}{r_i^2}
\ge
\frac{r_k-2}{r_k^2}.
```

The exact norm therefore satisfies

```math
\boxed{
q_{i,k}
\ge
\frac{M_kP_k(r_k-2)}{3r_k^2}.
}
```

Combining numerator and denominator bounds and summing the `k` prefix
coordinates gives

```math
\boxed{
\sum_{i<k}
\frac{X_i}{q_{i,k}}
\le
\frac{
3kD^2r_k^2
}{
25M_kP_k(r_k-2)
}.
}
```

## Exact Zero-Overflow Criterion

Assume

```math
M_k>H.
```

Then property #72's interval remainder is

```math
s_k=H.
```

If additionally

```math
\boxed{
M_kP_k
\ge
\frac{
3kD^2r_k^2
}{
25H(r_k-2)
},
}
```

the normalized capacity bound gives

```math
\sum_{i<k}
\frac{X_i}{q_{i,k}}
\le H=s_k.
```

Property #73 defines

```math
e_k
=
\left(
\sum_{i<k}\frac{X_i}{q_{i,k}}-s_k
\right)_+.
```

Consequently,

```math
\boxed{e_k=0.}
```

The exact improvement criterion in property #72 then gives

```math
\boxed{
\mathcal U_k^{\mathrm{hyb}}
=
\mathcal U_{\mathrm{cap}}.
}
```

Thus the displayed finite product inequality is a complete sufficient
condition for one-incomplete-block Bessel to exclude no capacity mass.

## Prime-Number-Theorem Scale

The prefix product has the exact form

```math
M_kP_k
=
6\prod_{i<k}(r_i-2).
```

Since `r_i-2>=r_i/2` for `r_i>=5`,

```math
M_kP_k
\ge
\frac{M_k}{2^k}.
```

Using the prime number theorem externally,

```math
\log M_k
=
\vartheta(r_{k-1})
\sim
r_{k-1},
```

and

```math
k
=
\pi(r_{k-1})-2
\sim
\frac{r_{k-1}}{\log r_{k-1}}.
```

Therefore

```math
\boxed{
\log(M_kP_k)
\sim
r_{k-1}.
}
```

Now suppose, for contradiction, that a cut clears candidate #24's original
threshold under candidate #17 at its first suffix layer. Properties #78--#79
give

```math
r_k
\gg
\sqrt{\frac{Q}{\log Q}},
\qquad
r_{k-1}>\frac{r_k}{2},
\qquad
M_k>H,
```

where Bertrand and PNT are external inputs. Hence

```math
\log(M_kP_k)
\gg
\sqrt{\frac{Q}{\log Q}}.
```

The logarithm of the right side of the finite zero-overflow criterion is only
`O(log Q)`, because

```math
k<Q,
\qquad
D<H<Q^2,
\qquad
r_k<Q.
```

Thus, for every sufficiently large future head, the finite product inequality
holds and

```math
\boxed{e_k=0.}
```

at every cut that could otherwise avoid the suffix obstruction.

## Exhaustion Of The Original Native Hybrid

Assume the full candidate #17 lower-envelope hypothesis. In particular, it
holds at filter `11`. Property #77 then proves, for sufficiently long chains,

```math
\mathcal U_2^{\mathrm{hyb}}
>
\frac{T^2}{2W_-}.
```

Since every hybrid envelope is at most the all-capacity envelope,

```math
\mathcal U_{\mathrm{cap}}
\ge
\mathcal U_2^{\mathrm{hyb}}
>
\frac{T^2}{2W_-}.
```

For a potentially successful moving cut, the preceding section instead gives

```math
\mathcal U_k^{\mathrm{hyb}}
=
\mathcal U_{\mathrm{cap}}.
```

This contradicts threshold clearance. Fixed cuts are already excluded by
property #78. Therefore, using Bertrand/PNT explicitly as external inputs,

```math
\boxed{
\mathcal U_{\mathrm{hyb}}
\ge
\frac{T^2}{2W_-}
}
```

for every sufficiently large complete chain satisfying candidate #17.

The current capacity-plus-native-Bessel envelope therefore cannot certify
candidate #24's original threshold under candidate #17 on an unbounded family.

## Boundary

This is a method obstruction, not a refutation of candidate #17 or candidate
#24. Candidate #17 already implies survival directly through close-pair
capacity; the theorem says that feeding its density information into the
current #24 envelope loses too much.

The result does not address:

1. property #69's capacity-relaxed threshold
   `T^2/(2W_-)+Gamma_cap`;
2. an upper bound for actual `E_b` using localized residue information rather
   than coordinate capacity maxima `X_i`; or
3. a different cross-layer inequality not represented by native-period
   Bessel.

Property #81 subsequently proves that the first item cannot rescue the
separate capacity envelope under full candidate #17 on an unbounded family.
Thus the live routes are a smaller localized upper bound for actual `E_b` or
a genuinely different cross-layer inequality.

No empirical evidence is used in this result.

## Related

- [Moving Cut Loses Complete Native Blocks](moving-cut-loses-complete-native-blocks.md)
- [Every Fixed Native Cut Fails The Original Threshold](every-fixed-native-cut-fails-original-threshold.md)
- [Fixed Seven Cut Cannot Clear The Original Threshold](fixed-seven-cut-cannot-clear-original-threshold.md)
- [Native-Period Bessel and Capacity Give a Sharp Hybrid Envelope](native-period-bessel-capacity-hybrid-envelope.md)
- [Native-Period Capacity Overflow Quantifies the Hybrid Gain](native-period-capacity-overflow-quantifies-hybrid-gain.md)
- [Weighted Harmful-Excess Quadratic Survival](../../candidates/weighted-harmful-excess-quadratic-survival.md)
