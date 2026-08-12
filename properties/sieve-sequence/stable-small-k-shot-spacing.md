# Fixed-k Shot Spacing: Monotonicity and Eventual Stability

**Status:** Mathematically proved. Stainless verification is not claimed here.

## Meaning

For a periodic sieve stage, define the cofactor-spacing quantity

```math
s_r(k)
=
\min_{0\le i<T_r}
\sum_{t=0}^{k-2}g_{i+t},
\qquad
g_i\text{ are the cyclic cofactor gaps}.
```

This quantity cannot decrease when an additional filter removes accepted values. New
survivors form a subset of the old periodic accepted set, so any `k` new
survivors span at least the old minimum span of `k` accepted values.

This gives a genuine inherited lower bound for shot capacity. A separate
admissible-pattern argument supplies a uniform upper bound and proves more:
for every fixed `k`, the minimum span eventually stabilizes at the minimum
diameter of an admissible `k`-point pattern.

## Setup

Let `A` be an infinite periodic accepted set with period `M`, and let `B` be
the accepted set after installing one additional filter. Then

```math
B\subseteq A.
```

Write the elements of each set in increasing bi-infinite order. For either set
`X`, define the minimum span of `k` consecutive accepted values by

```math
s_X(k)
=
\min_i\left(x_{i+k-1}-x_i\right),
\qquad k\ge2.
```

For a primorial wheel, one period of `A` can be written as

```math
0\le e_0<e_1<\cdots<e_{T-1}<M,
\qquad
T=\varphi(M)=\prod_{q<r}(q-1).
```

and `s_A(k)` is equivalently the minimum sum of `k-1` consecutive cyclic
cofactor gaps:

```math
s_A(k)=\min_{0\le i<T}\sum_{t=0}^{k-2}g_{i+t}
```

(where the indices of `g` are periodic).

## Property

For every fixed `k` available in both stages,

```math
s_B(k)\ge s_A(k).
```

If an incoming filter `r` scales cofactor positions into shot positions, then
the corresponding shot span is `sigma_r(k)=r s_A(k)`. Any proved lower bound
for `s_A(k)` therefore gives the scaled lower bound for that layer.

## Proof

Choose any `k` consecutive elements of `B`,

```math
b_i<b_{i+1}<\cdots<b_{i+k-1}.
```

Because `B` is a subset of `A`, these are also `k` elements of `A`, although
additional elements of `A` may lie between them. Let `a_j` be the first of
these elements in the increasing ordering of `A`. The `k`th consecutive
element of `A` beginning at `a_j=b_i` occurs no later than `b_{i+k-1}`.
Therefore

```math
\begin{aligned}
b_{i+k-1}-b_i
&\ge a_{j+k-1}-a_j\\
&\ge s_A(k)
\quad\text{[By Definition]}.
\end{aligned}
```

Every consecutive `k`-block of `B` has span at least `s_A(k)`. Taking the
minimum over those blocks gives

```math
s_B(k)\ge s_A(k)
\quad\text{[Q.E.D.]}.
```

## Admissible Diameter

A finite set `H` of integer offsets is **admissible** when it does not cover
every residue class modulo any prime:

```math
H\bmod p\ne\mathbb Z/p\mathbb Z
\qquad
\text{for every prime }p.
```

For fixed `k`, define

```math
D(k)
:=
\min\left\{
\max H-\min H:
|H|=k,\ H\text{ is admissible}
\right\}.
```

This minimum exists. Let

```math
B_k:=\prod_{p\le k}p,
\qquad
H_k:=\{0,B_k,2B_k,\ldots,(k-1)B_k\}.
```

For `p\le k`, every element of `H_k` is `0` modulo `p`, so the pattern occupies
only one residue class. For `p>k`, its `k` elements cannot cover all `p`
residue classes. Thus `H_k` is admissible and

```math
D(k)\le(k-1)B_k.
```

## Eventual Stability and Exact Characterization

Let `P` be a finite set of installed primes containing every prime `p\le k`,
let

```math
M:=\prod_{p\in P}p,
```

and suppose

```math
M>(k-1)B_k.
```

Then the wheel minimum span is exactly

```math
s_P(k)=D(k).
```

### Upper bound

Choose an admissible `k`-point pattern `H` of diameter `D(k)`. For every
installed prime `p\in P`, admissibility supplies a residue `c_p` such that

```math
c_p+h\ne0\pmod p
\qquad
\text{for every }h\in H.
```

By the Chinese remainder theorem, there is a residue `a` modulo `M` satisfying
`a=c_p (mod p)` for every `p\in P`. Hence all points `a+h`, with cyclic
reduction modulo `M`, are accepted by the wheel.

Because

```math
D(k)\le(k-1)B_k<M,
```

the translated points are distinct and lie in one cyclic arc of length
`D(k)`. That arc contains at least `k` accepted residues. Some `k` consecutive
accepted residues inside the arc therefore have span at most `D(k)`, giving

```math
s_P(k)\le D(k).
```

### Lower bound

Choose a cyclic block of `k` consecutive accepted residues attaining
`s_P(k)`, and unwrap its arc. The upper bound already proved gives

```math
s_P(k)\le D(k)<M,
```

so the unwrapped block has `k` distinct integer offsets

```math
H'=\{0=h_0<h_1<\cdots<h_{k-1}=s_P(k)\}.
```

Let `a` be the starting residue of the unwrapped block. For every prime
`p\le k`, the prime is installed, and every `a+h` with `h\in H'` is accepted.
Therefore `h\ne-a (mod p)` for every `h\in H'`, so the residue class `-a` is
absent from `H'\bmod p`. For every prime `p>k`, the `k` offsets cannot cover
all `p` residue classes. Therefore `H'` is globally admissible. By the
definition of `D(k)`,

```math
s_P(k)
=\max H'-\min H'
\ge D(k).
```

Together with the upper bound,

```math
s_P(k)=D(k)
\quad\text{[Q.E.D.]}.
```

## Complete-Period Two-Gap Cluster

The four-point pattern

```math
H=\{0,2,6,8\}
```

is admissible. Modulo `2` it occupies only `{0}`, modulo `3` it occupies only
`{0,2}`, and for every prime `p\ge5` its four points cannot cover all `p`
residue classes.

Therefore, by CRT, every primorial wheel with period `M>8` contains a cyclic
translate

```math
\{a,a+2,a+6,a+8\}\pmod M
```

of accepted residues. Because filter `2` is installed, no accepted integer
lies strictly between either pair at distance `2`. Hence `(a,a+2)` and
`(a+6,a+8)` are two cyclic 2-gaps enclosed by an arc of length `8`.

Every primorial wheel containing `{2,3,5}` has `M\ge30>8`, so the conclusion
holds at every such stage. `[Q.E.D.]`

## Exact Admissible Diameters Through k=14

The first thirteen nontrivial admissible diameters are

```math
\begin{aligned}
D(2)&=2,  &D(3)&=6,  &D(4)&=8,\\
D(5)&=12, &D(6)&=16, &D(7)&=20,\\
D(8)&=26, &D(9)&=30, &D(10)&=32,\\
D(11)&=36, &D(12)&=42, &D(13)&=48,\\
D(14)&=50.
\end{aligned}
```

### Upper bounds

The following admissible patterns prove `D(k)\le d_k`:

| `k` | admissible pattern | `d_k` |
|---:|---|---:|
| 2 | `{0,2}` | 2 |
| 3 | `{0,2,6}` | 6 |
| 4 | `{0,2,6,8}` | 8 |
| 5 | `{0,2,6,8,12}` | 12 |
| 6 | `{0,4,6,10,12,16}` | 16 |
| 7 | `{0,2,6,8,12,18,20}` | 20 |
| 8 | `{0,2,6,8,12,18,20,26}` | 26 |
| 9 | `{0,2,6,8,12,18,20,26,30}` | 30 |
| 10 | `{0,2,6,8,12,18,20,26,30,32}` | 32 |
| 11 | `{0,2,6,8,12,18,20,26,30,32,36}` | 36 |
| 12 | `{0,2,6,8,12,18,20,26,30,32,36,42}` | 42 |
| 13 | `{0,2,6,8,12,18,20,26,30,32,36,42,48}` | 48 |
| 14 | `{0,2,6,8,12,18,20,26,30,32,36,42,48,50}` | 50 |

For each row, direct reduction shows that the pattern misses a residue modulo
every prime `p\le k`. A `k`-point set automatically misses a residue modulo
every prime `p>k`, so every listed pattern is globally admissible.

For completeness, the missing residues of the four new witnesses are:

| `k` | modulo 2 | modulo 3 | modulo 5 | modulo 7 | modulo 11 | modulo 13 |
|---:|---:|---:|---:|---:|---:|---:|
| 11 | 1 | 1 | 4 | 3 | 5 | not needed |
| 12 | 1 | 1 | 4 | 3 | 5 | not needed |
| 13 | 1 | 1 | 4 | 3 | 5 | 1 and 11 |
| 14 | 1 | 1 | 4 | 3 | 5 | 1 |

Thus the new rows give the four upper bounds

```math
D(11)\le36,\quad D(12)\le42,\quad
D(13)\le48,\quad D(14)\le50.
```

### Lower bounds through k=10

Suppose an admissible `k`-point set had diameter less than the proposed `d_k`.
Translate it so that its minimum is `0`. Admissibility modulo `2` then forces
every offset to be even, so its remaining `k-1` points must be chosen from

```math
E_k=\{2,4,\ldots,d_k-2\}.
```

Let `n_j` count the members of `E_k` congruent to `j` modulo `3`. Since `0` is
already present, a set avoids covering all residues modulo `3` only if its
remaining points omit residue `1` or omit residue `2`. The number of cases
surviving this first obstruction is therefore

```math
\binom{n_0+n_1}{k-1}
+
\binom{n_0+n_2}{k-1}
-
\binom{n_0}{k-1}.
```

The complete finite residue-cover certificate is:

| `k` | `d_k` | `(n_0,n_1,n_2)` | after modulo 3 | after modulo 5 | after modulo 7 |
|---:|---:|---:|---:|---:|---:|
| 3 | 6 | `(0,1,1)` | 0 | 0 | 0 |
| 4 | 8 | `(1,1,1)` | 0 | 0 | 0 |
| 5 | 12 | `(1,2,2)` | 0 | 0 | 0 |
| 6 | 16 | `(2,2,3)` | 1 | 0 | 0 |
| 7 | 20 | `(3,3,3)` | 2 | 0 | 0 |
| 8 | 26 | `(4,4,4)` | 16 | 2 | 0 |
| 9 | 30 | `(4,5,5)` | 18 | 0 | 0 |
| 10 | 32 | `(5,5,5)` | 20 | 0 | 0 |

For `k=6,7,9,10`, direct reduction of every case surviving modulo `3` covers
all residue classes modulo `5`. For `k=8`, fourteen of the sixteen cases cover
all residues modulo `5`. The two remaining cases are

```math
\begin{aligned}
H_1&=\{0,2,8,12,14,18,20,24\},\\
H_2&=\{0,4,6,10,12,16,22,24\}.
\end{aligned}
```

Both `H_1` and `H_2` cover all seven residue classes modulo `7`. Thus every
shorter normalized pattern is inadmissible, proving `D(k)\ge d_k`. Together
with the witness upper bounds,

```math
D(k)=d_k
\qquad
(2\le k\le10)
\quad\text{[Q.E.D.]}.
```

### Lower bounds from k=11 through k=14

It remains to exclude shorter patterns for the four new rows. Fix one of

```math
(k,d)\in\{(11,36),(12,42),(13,48),(14,50)\}
```

and suppose that a normalized admissible `k`-point set `H` has diameter less
than `d`. As above, admissibility modulo `2` and `0\in H` force

```math
H\subseteq\{0,2,\ldots,d-2\}.
```

Because `H` is admissible modulo `3`, it misses some residue
`a\in\{1,2\}`; it cannot miss residue `0` because `0\in H`. Similarly, it
misses some residue `b\in\{1,2,3,4\}` modulo `5`. Define

```math
U_d(a,b)=
\left\{
x\in\{0,2,\ldots,d-2\}:
x\not\equiv a\pmod3,\ 
x\not\equiv b\pmod5
\right\}.
```

Then

```math
H\subseteq U_d(a,b).
```

Directly grouping the even offsets by their residues modulo `3` and `5`
gives the following cardinality certificate. Within each cell, the first row
is `a=1`, the second is `a=2`, and the four columns are `b=1,2,3,4`.

| `(k,d)` | `a` | `b=1` | `b=2` | `b=3` | `b=4` |
|---:|---:|---:|---:|---:|---:|
| `(11,36)` | 1 | 10 | 9 | 10 | 10 |
|  | 2 | 10 | 10 | 10 | 9 |
| `(12,42)` | 1 | 11 | 11 | 11 | 12 |
|  | 2 | 11 | 12 | 12 | 11 |
| `(13,48)` | 1 | 13 | 12 | 13 | 13 |
|  | 2 | 12 | 13 | 14 | 13 |
| `(14,50)` | 1 | 14 | 13 | 13 | 14 |
|  | 2 | 13 | 14 | 14 | 14 |

For `(11,36)`, every `U_d(a,b)` has fewer than `k=11` elements, which is
already a contradiction. For the other three rows, discard every cell with
cardinality below `k`. The remaining fourteen ambient sets and their
modulo-7 residue multiplicities are:

| `k` | `(a,b)` | `U_d(a,b)` | counts in residues `(0,1,2,3,4,5,6)` modulo 7 |
|---:|---:|---|---:|
| 12 | `(1,4)` | `{0,2,6,8,12,18,20,26,30,32,36,38}` | `(1,2,2,1,2,2,2)` |
| 12 | `(2,2)` | `{0,4,6,10,16,18,24,28,30,34,36,40}` | `(2,1,2,2,2,1,2)` |
| 12 | `(2,3)` | `{0,4,6,10,12,16,22,24,30,34,36,40}` | `(1,2,2,2,1,2,2)` |
| 13 | `(1,1)` | `{0,2,8,12,14,18,20,24,30,32,38,42,44}` | `(3,1,3,2,2,1,1)` |
| 13 | `(1,3)` | `{0,2,6,12,14,20,24,26,30,32,36,42,44}` | `(3,1,3,1,1,2,2)` |
| 13 | `(1,4)` | `{0,2,6,8,12,18,20,26,30,32,36,38,42}` | `(2,2,2,1,2,2,2)` |
| 13 | `(2,2)` | `{0,4,6,10,16,18,24,28,30,34,36,40,46}` | `(2,1,2,2,3,1,2)` |
| 13 | `(2,3)` | `{0,4,6,10,12,16,22,24,30,34,36,40,42,46}` | `(2,2,2,2,2,2,2)` |
| 13 | `(2,4)` | `{0,6,10,12,16,18,22,28,30,36,40,42,46}` | `(3,2,2,1,2,2,1)` |
| 14 | `(1,1)` | `{0,2,8,12,14,18,20,24,30,32,38,42,44,48}` | `(3,1,3,2,2,1,2)` |
| 14 | `(1,4)` | `{0,2,6,8,12,18,20,26,30,32,36,38,42,48}` | `(2,2,2,1,2,2,3)` |
| 14 | `(2,2)` | `{0,4,6,10,16,18,24,28,30,34,36,40,46,48}` | `(2,1,2,2,3,1,3)` |
| 14 | `(2,3)` | `{0,4,6,10,12,16,22,24,30,34,36,40,42,46}` | `(2,2,2,2,2,2,2)` |
| 14 | `(2,4)` | `{0,6,10,12,16,18,22,28,30,36,40,42,46,48}` | `(3,2,2,1,2,2,2)` |

Thirteen rows have exactly `k` elements. Since `H` is a `k`-element subset,
those rows force `H=U_d(a,b)`. Every displayed multiplicity is positive, so
each forced `H` covers every residue modulo `7` and is inadmissible.

The sole larger row is `(k,a,b)=(13,2,3)`, with `14` elements. Its modulo-7
multiplicity vector is

```math
(2,2,2,2,2,2,2).
```

Because `0\in H`, a `13`-point subset removes one of the thirteen nonzero
members. Removing one member decreases only one entry of that vector from
`2` to `1`; all seven residues remain represented. This `H` also covers
modulo `7` and is inadmissible.

Every possible shorter normalized pattern is therefore rejected by modulo
`2`, `3`, `5`, or `7`. Hence

```math
D(11)\ge36,\quad D(12)\ge42,\quad
D(13)\ge48,\quad D(14)\ge50.
```

Combining these lower bounds with the four explicit admissible witnesses
proves

```math
D(11)=36,\quad D(12)=42,\quad
D(13)=48,\quad D(14)=50
\quad\text{[Q.E.D.]}.
```

## Consequences

- A lower bound computed or proved at an earlier wheel remains a lower bound
  after every additional filter.
- For `k=2`, the cyclic pair `(M-1,1)` supplies a separate persistent witness
  of span `2`, while parity supplies the lower bound `2`. Hence `s(2)=2` and
  `sigma_r(2)=2r` for every odd primorial stage.
- For `k>2`, equality with an earlier finite table requires a persistent
  witness or another upper-bound argument in addition to monotonicity.
- For every fixed `k`, the value does eventually stabilize. At every stage
  satisfying the theorem's explicit conditions, its stable value is `D(k)`.
- At such a stage, an incoming filter `r` has exact fixed-`k` shot span
  `sigma_r(k)=rD(k)`.
- For `2\le k\le14`, the exact stable constants are the values in the proved
  table above.

## Limitation

- Monotonicity alone does not imply stabilization; the admissible-pattern
  upper bound is essential to the theorem.
- The theorem characterizes the stable value as `D(k)` and computes it through
  `k=14`, but it does not give exact numerical values for general `k`. The
  measured table and
  200-stage prefix witnesses are recorded in
  [the empirical #14 note](
  ../../empirical/sieve-sequence/hereditary-shot-spacing.md
  ).
- The result fixes `k` before the wheel grows. `sigma_r(k)` for `k` comparable
  to `T_r` (e.g. `k=T_r`) genuinely requires the full period and is not covered
  by this stability theorem. Note `sigma_r(T_r)=r(M -
  \max_i g_i)` (it sums `T_r-1` of the `T_r` gaps, omitting the largest), not
  `r M`; the full-period span `r M` would require `k=T_r+1`, outside the valid
  range `[2,T_r]`.
- This is a global/wheel property. It constrains shot spacing but does not, by
  itself, locate a surviving 2-gap in any particular window
  `[q,q^2)`; that requires the per-layer interval argument of candidate #14.

## Related

- [exact-global-two-gap-count](exact-global-two-gap-count.md) — the persistent
  `s_2=2` witness is the structural source of that count's positivity.
- [copy-index-filter-frequency](copy-index-filter-frequency.md) — the
  per-filter strike structure that `sigma_r` bounds capacity for.
- [sharp-admissible-shot-spacing-profile](
  ../../candidates/sharp-admissible-shot-spacing-profile.md
  ) — the candidate for exact small-`k` values, recurrence bounds, and
  extremal structure of `D(k)`.
- [hereditary-shot-spacing-capacity](
  ../../candidates/hereditary-shot-spacing-capacity.md
  ) — the candidate that consumes shot-span lower bounds per layer.
