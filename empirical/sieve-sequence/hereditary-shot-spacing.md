# Empirical Evidence for Hereditary Shot Spacing

**Status:** Finite measurements and conjectural scales. No universal claim in
this note is mathematically proved.

## Scope and Inputs

This note collects the finite evidence related to candidate #14,
[Hereditary Shot-Spacing Capacity](
../../candidates/hereditary-shot-spacing-capacity.md
). The mathematical candidate remains under `candidates/`; deductively proved
facts remain under `properties/`.

The measurements use:

- `data/candidates/lineage-Q17.csv`;
- `data/candidates/lineage-Q101.csv`;
- `data/sieve-sequence/first_gaps_per_seq.csv`;
- `python/src/sieve_sequence/lineage.py`;
- `python/src/sieve_sequence/lineage_cli.py`;
- `python/tests/test_lineage.py`.

The lineage test suite passed before the measurements described here. The
200-stage CSV is accepted as trusted finite input for this research pass by
user direction. Its generator is not currently linked from the repository, so
independent provenance remains to be documented.

## 1. Finite Small-k Gap-Span Table

For a sequence of gaps `g_i`, the prefix experiment measures

```math
s_k^{(100000)}
:=
\min_{0\le i<100000-(k-1)}
\sum_{t=0}^{k-2}g_{i+t}.
```

This is the minimum span found in the first 100,000 gaps, so it is an upper
bound on the full-period minimum `s_k`. The exact stable complete-wheel values
for `2\le k\le10` are now proved independently through admissible diameters;
the prefix remains evidence about where their witnesses occur.

The supplied CSV contains 200 stages and 100,000 gaps per stage. For the 197
stages numbered 4 through 200, where filters `{2,3,5,7}` have been installed,
the observed prefix minima are:

| k | Proved stable `D(k)` | Stages attaining it in the prefix | Other prefix minima |
|---|---:|---:|---|
| 2 | 2 | 197/197 | none |
| 3 | 6 | 197/197 | none |
| 4 | 8 | 197/197 | none |
| 5 | 12 | 197/197 | none |
| 6 | 16 | 197/197 | none |
| 7 | 20 | 197/197 | none |
| 8 | 26 | 197/197 | none |
| 9 | 30 | 197/197 | none |
| 10 | 32 | 42/197 | 34 at 155 stages |

For `k=10`, the first prefix change occurs at stage 46, head 211. From that
stage through stage 200, the minimum found in the recorded prefix is 34 rather
than 32. Since `D(10)=32` is now proved, a diameter-32 translate exists
elsewhere in every such complete wheel. The observation refutes only the
stronger suggestion that a 32-span witness remains visible in this fixed
prefix at every stage.

At stage 200 (head 1229), first witnesses for the observed prefix minima include:

| k | Prefix minimum | First witness gap word | Start survivor |
|---|---:|---|---:|
| 2 | 2 | `(2)` | 1231 |
| 3 | 6 | `(2,4)` | 1279 |
| 4 | 8 | `(2,4,2)` | 1483 |
| 5 | 12 | `(2,4,2,4)` | 1483 |
| 6 | 16 | `(4,2,4,2,4)` | 16061 |
| 7 | 20 | `(2,6,4,2,4,2)` | 5641 |
| 8 | 26 | `(2,4,6,2,6,4,2)` | 1279 |
| 9 | 30 | `(2,4,6,2,6,4,2,4)` | 1279 |
| 10 | 34 | `(4,2,4,6,2,6,4,2,4)` | 113147 |

These recurring words remain useful location data. The fixed-`k` theorem and
finite residue-cover proof now establish the stable values independently; the
same absolute witness need not persist from one wheel or prefix to the next.

## 2. Fixed-Window Lineage Measurements

At `Q=17`, the complete-period quantities are tractable at every relevant
layer. The candidate's interval premise is observed at all 4 layers where
`sigma_r(k)` is defined.

At `Q=101`, the stored lineage output reports the interval premise at all
23 defined layers and 202 final 2-gaps. The population, destruction counts, and
selected `k\le10` spacing values are exact finite computations. Early periods
are directly enumerated; once `{2,3,5,7}` is installed, the proved profile
`D(2)..D(10)` supplies the exact values.

The existential classification can nevertheless be checked independently
without that table. Recomputing the nearest pair of exact window 2-gap starts
gives enclosing length `8` at every one of the 23 defined layers. Since
`sigma_r(2)=2r` is mathematically exact and every such layer has `r>=5`,

```math
8<2r=\sigma_r(2).
```

Thus all 23 Q101 layers have an exact finite `k=2` certificate. The runner's
selected `k=10` witnesses are also exact under the new profile theorem. Neither
finite result proves the premise for every `Q`.

Thus the strict status is:

- `Q=17`: 4/4 defined interval checks use exact finite-period inputs;
- `Q=101`: 23/23 defined interval checks have exact finite `k=2` certificates;
- `Q=101`: all selected `k\le10` witness fields use either direct enumeration
  or the proved exact admissible-diameter profile.

### Expanded exact k=2 sweep (2026-07-27)

An in-memory sweep tested every prime head `17\le Q\le251`, together with

```text
307, 401, 503, 701, 997.
```

This covers 53 heads and 1,837 defined filter layers. At each layer, the sweep
constructed the exact finite window survivors, found the closest two complete
2-gap starts, and compared their enclosing length with the proved capacity
`sigma_r(2)=2r`.

No layer failed. Every closest-pair enclosure had length at most `8`; the
largest observed ratio was

```math
\frac{8}{2\cdot5}=0.8.
```

This substantially strengthens the finite evidence for close-pair placement
inside `[Q,Q^2)`, but it does not prove that every future square window has
such a pair. The sweep was executed as a read-only in-memory analysis using
the lineage survivor definitions; no new CSV or generator was committed
because the unrelated normal code-test baseline remains non-green.

## 3. Recurrence Counterexamples

Let `G` be the pre-filter 2-gap-start count, `D` the destroyed count, and
`S=G-D` the post-filter count. The complete-block frequency suggests

```math
S\ge
\left\lceil G\left(1-\frac2r\right)\right\rceil.
```

The Q=101 data provides finite counterexamples: the inequality fails at 8 of
24 layers, first at `r=13`, with a largest deficit of 5 at `r=31`.

A constant correction calibrated from one chain also fails. Across selected
prime heads

```text
17, 29, 43, 61, 79, 101, 127, 151,
181, 211, 251, 307, 401, 503, 701, 997
```

the maximum positive excess

```math
D-\frac{2G}{r}
```

grows from 0 to approximately 41.740. This refutes the tested constants,
including `C=5`; it does not prove that every fixed constant is impossible.

## 4. Square-Root Discrepancy Signal

For each measured layer, define

```math
\rho(Q,r)
=
\frac{\max(0,D-2G/r)}{\sqrt G}.
```

Across every layer of the 16 selected heads above, the largest observed direct
ratio is approximately `0.3596`, at `Q=997`, `r=277`, `G=12222`.

Candidate #12 uses the more conservative maximum residue-class deviation

```math
E=
\max_a
\left|N_a-\frac Gr\right|.
```

The largest observed `2E/sqrt(G)` in the same sweep is approximately `0.8340`,
at `Q=61`, `r=47`. Consequently, the finite data does not falsify

```math
2E\le\sqrt G.
```

If that inequality held, the two forbidden start classes would give the
conditional recurrence

```math
S
\ge
G\left(1-\frac2r\right)-\sqrt G.
```

Iterating this numerical recurrence remains positive in every measured chain.
This is a viable empirical scale, not a mathematical property. A uniform proof
through the complete chain would force final square-window positivity and is
therefore still twin-prime-strength.

## 5. Falsifiers and Next Empirical Checks

- A full-period span smaller than a proposed `s_k` refutes that proposed lower
  bound at the measured stage.
- Failure to find a witness in a finite prefix does not refute a full-period
  minimum, but it does refute persistence within that prefix.
- Any measured layer with `2E > sqrt(G)` refutes the unit square-root
  conjecture.
- A reproducible generator and checksum for the 200-stage CSV would strengthen
  provenance without changing the mathematical status of the observations.

No amount of additional finite agreement promotes these conjectures into
`properties/`; that requires a deductive proof at the stated universal scope.
