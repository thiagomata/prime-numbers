# Two-Gap Placement Saturation And The Cross-Fiber Coupling Boundary

**Status:** Mathematically proved. Stainless verification is not claimed.

## Meaning

The single-value [Past-Span Saturation property](
past-span-saturation-does-not-determine-placement.md) proves that no
accumulation of complete-period constraints determines which lift each
survivor fiber loses. This property extends that theorem to the article's
actual object — **2-gaps** — where a new subtlety appears: a 2-gap's two
endpoints live in *two different fibers*, so 2-gap statistics can couple
distinct fibers within one layer.

Three results. First, the balanced-companion law of the phase-transition
article (exactly two harmful copy classes per 2-gap parent) is
characterized exactly: it holds iff the value-placement is a **compatible
coloring** of the 2-gap fiber graph. Second, the blind class is pinned
down: every compatible coloring gives the same next-period 2-gap count
`(r-2)G` (with `G` the exact old-period count) and the same marginal
statistics, while producing *different* 2-gap sets. Third, the exact
boundary is located: separation-resolved pair counts are the first
global 2-gap statistics that see placement, through an explicit
exclusion-intersection term; under the real rule this term is rigid
arithmetic (`h = 0, +-2 mod r`). This is the precise home of the
"shared-value effects / CRT correlations between different gaps" named in
the transfer obligation: characterized at the complete-period level,
open exactly at the local level.

## Setup

Let `P` be the installed squarefree period with `6 | P` (post-3 stages),
let `r >= 5` be prime with `gcd(P,r)=1`, and `R=Pr`. Survivor fibers are
the residues `c mod P` with `gcd(c,P)=1`; each has exactly `r` lifts
`c+kP` in `Z/RZ`, and there are `phi(P)` fibers.

A **value-placement** is a map

```math
\varphi:\{\text{survivor fibers}\}\longrightarrow\mathbb Z/r\mathbb Z
```

killing the value `c+varphi(c)P` of fiber `c` (one lift per fiber — the
per-fiber quota of the single-value saturation property). The real rule
is the linear placement

```math
\varphi_{\mathrm{real}}(c)=-cP^{-1}\pmod r,
```

killing exactly the multiples of `r`.

A 2-gap parent is a pair of consecutive old survivors `(n, n+2)`. Write
`n=c_1+k_1P`, `n+2=c_2+k_2P` with fibers `c_2=(c_1+2)\bmod P` and
`k_2-k_1=delta in {0,1}` (`delta=1` only for the wrap pair
`(P-1,1)`). Copy `j` of the parent is the value pair
`(n+jP, n+2+jP)`; it dies exactly when `j` belongs to the **harmful
set**

```math
E(n,n+2)=\{\varphi(c_1)-k_1,\ \varphi(c_2)-k_2\}\pmod r.
```

## Characterization: The Balanced Law Is Compatibility

`|E|=2` (the balanced two-class law) holds iff the two displayed classes
are distinct, i.e. iff

```math
\varphi(c_1)-\varphi(c_2)\neq k_1-k_2=-\delta\pmod r.
```

Since `delta` depends only on the fiber pair, the condition is a
**forbidden-difference constraint per 2-gap fiber pair**:

```math
\boxed{
\begin{aligned}
\varphi(c)&\neq\varphi(c+2)
&&[\text{non-wrap pairs}],\\
\varphi(P-1)-\varphi(1)&\neq-1
&&[\text{wrap pair, if it hosts 2-gaps}].
\end{aligned}}
```

Non-wrap constraints are proper-coloring conditions on the **2-gap fiber
graph** — the subgraph of the step-2 graph on survivor fibers whose edges
host at least one 2-gap. That graph has degree at most `2` (neighbors
`c+-2` only), so it is a union of paths and cycles. The real placement
always satisfies both constraints:

```math
\varphi_{\mathrm{real}}(c)-\varphi_{\mathrm{real}}(c+2)
=(2-\delta P)P^{-1}
=2P^{-1}-\delta
\neq-\delta
\pmod r
```

because `2P^{-1}\neq0` for `r>=5`. Moreover every parent's two harmful
classes differ by the **rigid constant**

```math
\Delta=2P^{-1}\pmod r,
```

independently of the parent — the structural signature distinguishing the
linear placement inside the compatible class.

Consequences, elementarily:

- compatible placement: every parent leaves exactly `r-2` copies — the
  balanced companion family of the article is exactly the set of
  compatible colorings;
- non-compatible placement on some edge: that parent leaves `r-1`
  copies, violating the balanced law;
- greedy coloring gives at least `(r-2)^(phi(P))` compatible placements
  (each fiber has at most two fiber-neighbors, each forbidding at most
  one value), so the real sieve is one point of an exponentially large
  family. `[Q.E.D.]`

## Blind Statistics

**Next-period 2-gap count.** Post-3, no filtering creates a 2-gap: if
`m, m+2` are consecutive survivors of the new filter, then both are
coprime to `P`, and among `m, m+1, m+2` one is `0 mod 3`; since `m, m+2`
are coprime to `P` (hence to 3), it is `m+1`, which was therefore never
an old survivor — so `(m, m+2)` was already an old 2-gap. New 2-gaps are
thus exactly the surviving copies of old parents, and for **every**
compatible placement

```math
\boxed{
\#\{\text{new 2-gaps in one }R\text{-period}\}=(r-2)G,
}
```

with `G` the exact old-period 2-gap count ([Exact Global 2-Gap Count](
exact-global-two-gap-count.md)). The count is placement-blind; the
2-gap **set** is not (see Validation). The period-averaged pair count
`G^2/R` is blind by double counting, which is the averaged form of the
[complete-period pair-correlation average property](
complete-period-two-gap-pair-correlation-average.md). `[Q.E.D.]`

## The Boundary: Where 2-Gap Statistics See Placement

Let `(n, n+2)` and `(n+h, n+h+2)` be two old 2-gap parents with
`0<h<P`. The number of surviving start pairs at exact separation `h` is

```math
\#\{j: j\notin E_1,\ j\notin E_2\}
=r-|E_1\cup E_2|
=r-4+|E_1\cap E_2|.
```

The exclusion-intersection `|E_1\cap E_2| in {0,1,2}` depends on the
placement through the relative position of the two harmful pairs — this
is the first placement-sensitive global 2-gap observable. Under the real
rule, `E_i={alpha_i, alpha_i-Delta}` with `alpha_2-alpha_1=hP^{-1}`,
so

```math
\boxed{
|E_1\cap E_2|
=
\begin{cases}
2,&h\equiv0\pmod r,\\
1,&h\equiv\pm2\pmod r,\\
0,&\text{otherwise},
\end{cases}
}
```

a rigid arithmetic signature: a generic compatible coloring produces its
intersections at placement-dependent separations, while the linear
placement produces them exactly at `h=0, +-2 mod r`. `[Q.E.D.]`

**Saturation corollary.** Past constraints (the per-fiber quota) plus
the balanced-compatibility constraints still leave at least
`(r-2)^(phi(P))` placements that no count, no marginal statistic, and no
period-averaged joint statistic can distinguish. Within-layer
cross-fiber joints — the separation-resolved pair counts above — are the
only complete-period statistics carrying 2-gap placement information,
and they carry it only through the arithmetic exclusion-intersection.
Everything else about 2-gap placement is, as at the single-value level,
invisible to the complete period; the local question remains
structurally necessary.

## Validation

Derivation checks on the toy chain `P=6`, `r=5`, `R=30` (checks of this
file's arithmetic, not empirical evidence about the sieve):

- Real placement `varphi(1)=4, varphi(5)=0` kills `{5,25}`; harmful set
  of the (unique) old-period 2-gap parent is `{0,3}`, difference
  `3-0=-2=2=2P^{-1} mod 5` as required; new-period 2-gaps
  `{(11,13),(17,19),(29,1)}`, count `3=(r-2)G` with `G=1`.
- Compatible non-real placement `varphi(1)=varphi(5)=0` (fiber
  difference `0`, wrap forbids `-1 mod 5=4`) kills `{1,5}`; harmful set
  `{0,4}` — same size, different classes; new-period 2-gaps
  `{(11,13),(17,19),(23,25)}` — same count `3`, **different set**:
  counts blind, positions sensitive.
- Non-compatible placement `varphi(1)=0, varphi(5)=4` (fiber difference
  `4` = forbidden wrap value) kills `{1,29}`; harmful set `{4}` — a
  single class; new-period count `4=(r-1)G`, violating the balanced law.

The toy chain has a single 2-gap fiber pair (the wrap pair), so the
non-wrap proper-coloring branch is validated by derivation rather than
by this enumeration.

## Related

- [Past-span saturation does not determine placement](
  past-span-saturation-does-not-determine-placement.md) — the
  single-value theorem this file extends.
- [Layer Strikes Are Innovations Of The Layer Filtration](
  layer-strike-innovation-orthogonality.md) — the value-level
  orthogonality behind the per-fiber quota.
- [Exact Global 2-Gap Count](exact-global-two-gap-count.md) — the
  blind next-period count input `G`.
- [Complete-period two-gap pair-correlation average](
  complete-period-two-gap-pair-correlation-average.md) — the averaged
  (blind) form of the pair statistics whose resolution carries
  placement.
- [Absence of 2-gaps is stable](absence-of-two-gaps-is-stable.md) —
  the no-creation input, proved here inline for post-3 stages.
- [CRT-coupled real-sieve transfer](
  ../../companions/candidates/crt-coupled-real-sieve-transfer.md) —
  the shared-value-effects item this property characterizes.
- [Sub-CRT strike decoherence](
  ../../candidates/sub-crt-strike-decoherence.md) and
  [window innovation orthogonality](
  ../../candidates/window-innovation-orthogonality.md) — the local
  questions that remain structurally necessary.
- [Survival Frontiers in Balanced 2-Gap Companion Processes, §2–§3](
  ../../articles/draft/draft-adversariality-phase-transition-2-gap-companions.md)
  — the balanced companion family characterized here.
