# Short-Window Discrepancy

**Candidate hypothesis:** Unproved and potentially false.

**Conditional implication:** Mathematically proved.

**Empirical status:** INCONCLUSIVE — post-filter `E_q` now computed (lineage, one-sided holds 24/24), but the load-bearing two-sided bound `|E_q| < main_term` is still pending. See "Empirical status (post-filter E_q, lineage experiment)".

## Candidate Hypothesis

Let the exact complete-period density of post-filter 2-gap starts be

```math
\delta_q=
\frac12
\prod_{\substack{3\le r<q\\r\text{ prime}}}
\left(1-\frac2r\right).
```

Write the exact safe-window count as

```math
|S_q\cap W_q|=|W_q|\delta_q+E_q.
```

Suppose, for infinitely many `q`, the discrepancy satisfies

```math
|E_q|<|W_q|\delta_q.
```

The weaker one-sided condition `E_q>-|W_q|delta_q` is already sufficient.

## Why It Is Sufficient

The candidate inequality gives

```math
|S_q\cap W_q|
\ge |W_q|\delta_q-|E_q|>0.
```

The positive integer count yields a square-safe 2-gap and therefore a
twin-prime certificate.

## Big Picture: What "The Filter Behaves As Random" Would Prove

"Why It Is Sufficient" above proves a single window. Chaining it across
transitions proves the actual target: **if the filter behaves as random,
infinitely often, then infinitely many twin primes exist** -- and that
implication itself is fully proved, unconditionally, right now.

**Piece 1: the random prediction diverges.** `main_term(Q)=|W_Q|\delta_Q`
grows because the window `|W_Q|~Q^2` outruns the density decay
`\delta_Q\sim C/(\ln Q)^2` (Mertens-type, elementary -- no conjecture needed
for this *order*). Measured directly, not merely asymptotic:

| `Q` | `delta_Q` | `main_term` |
|---|---|---|
| `101` | `0.019149` | `193.4` |
| `1009` | `0.008656` | `8{,}804.1` |
| `10007` | `0.004894` | `490{,}078.1` |
| `100003` | `0.003138` | `31{,}383{,}666.9` |

**Piece 2: bounded discrepancy forces a certificate.** Already proved above:
`E_Q>-main_term(Q)` gives `|S_Q\cap W_Q|>0`, hence a certified twin-prime pair.

**Chained:** if `E_Q>-main_term(Q)` holds at infinitely many `Q`, `main_term`
diverging forces a survivor at infinitely many `Q`. By the bounded-coverage
argument in
[the adversariality-score file's equivalence section](../properties/sieve-sequence/realized-filter-adversariality-score.md#global-window-and-danger-annulus-recurrence-are-the-same-question)
(a fixed pair only satisfies the window condition for finitely many `Q`, so
infinitely many qualifying `Q` forces infinitely many *distinct* pairs), that
is infinitely many distinct twin primes.

**Extinction is not an open question for any of the three reference
behaviors -- it is decided, three separate times, three separate ways:**

- **Adversarial** (`f=1` up to the proved capacity, `realized-filter-adversariality-score.md`'s
  `N_adversarial`): extinction is a fact. Computed directly at `Q=101`: the
  trajectory reaches exactly `0` at `r=67` and stays there, using only the
  already-proved `worst_case_A` capacity bound at each step -- not
  speculation.
- **Random** (`f=2/r`, this file's `main_term`): extinction never happens.
  Proved above, unconditionally: `main_term(Q)\to\infty` because the window
  `|W_Q|\sim Q^2` outruns the density decay. No conjecture anywhere in that
  argument.
- **Friendly** (`f=0`): never happens, trivially -- the count never
  decreases.

**What remains open is not "could extinction happen" -- it is which of
these three the real filter chain actually tracks.** Does `E_Q` stay bounded
below by `-main_term(Q)` at infinitely many `Q` (behavior at least as good as
random, inheriting the random model's proved non-extinction), or could real
behavior undershoot the random prediction all the way to zero, infinitely
often (behavior converging toward the adversarial model's proved
extinction)? Every measurement so far tracks the random-or-better side (`E_q`
positive at all 24 measured lineage layers), but "so far" is a finite check,
not the infinite claim needed. That one discrepancy bound is the entire
remaining gap -- not because extinction itself is undecided, but because we
do not yet know which decided case the real sequence belongs to.

## Established Inputs

- [Exact global 2-gap count](../properties/sieve-sequence/exact-global-two-gap-count.md)
- [Batched short-window discrepancy boundary](../properties/sieve-sequence/batched-short-window-discrepancy-boundary.md)

## Limitation

The complete-period CRT formula determines the main term but supplies no such
short-window error bound. Proving the candidate requires distributional input
beyond total counts and per-prime residue frequencies.

## Relation To The Collision-Energy Program

This candidate's discrepancy `E_q` compares the final post-filter safe-window
2-gap count with a complete-period density main term. It does not directly
control the accepted-anchor strike-density error

```math
\varepsilon
=
\frac HN-\frac1p
```

that appears in the exact harmful-excess identity

```math
b=H\beta+2L\varepsilon.
```

Therefore candidate #10 is not presently one of the scalar inputs to the
#13/#22/#21 orthogonal energy chain. Candidate #23 is the separate
accepted-strike-density theorem required there. Any future reduction from
`E_q` to `epsilon` must be
proved explicitly rather than inferred from their similar discrepancy
language.

## Empirical status (window scale, p to ~19000)

Source: `python/src/sieve_sequence/window_cli.py`, 186 transitions (dense
p<=991 + sparse to p~19000). The run recorded `main_term = |W| delta_q`, but
computed the reported discrepancy as

```math
E_{\mathrm{measured}}=G_{\mathrm{local}}-|W|\delta_q,
```

where `G_local` is the **pre-filter** 2-gap count. The hypothesis instead
defines

```math
E_q=|S_q\cap W_q|-|W|\delta_q
```

from the **post-filter** count. These are different quantities. Consequently,
the earlier “pass 186/186” label and its discrepancy ratios do not test this
candidate and are withdrawn. The recorded column may remain a pre-filter
window diagnostic, but it cannot be interpreted as `E_q`.

### What must be measured

Recompute `E_q` as `surviving - main_term` and report both the two-sided ratio
`|E_q|/main_term` and the one-sided margin. The one-sided inequality
`E_q>-main_term` is algebraically equivalent to `surviving>0`, so measuring it
only reproduces the outcome. The informative empirical stress test is the
stronger two-sided discrepancy bound and its scaling.

## Strategic assessment after empirical review

The candidate is analytically natural, but its weak one-sided form is a
restatement of local survival. Its value lies in proving a genuinely
non-circular two-sided or relative discrepancy estimate from the arithmetic of
the filters. Until the post-filter discrepancy is computed, this candidate is
**unmeasured as stated** and should not be ranked from the current column.

## Empirical status (post-filter `E_q`, lineage experiment)

The post-filter discrepancy `E_q = surviving - main_term` (using the
POST-filter count, correcting the window pass's pre/post error) is now
computed per layer by the lineage experiment
(`python/src/sieve_sequence/lineage_cli.py`).

**Q=101, 24 layers:** `E_q` ranges over `[+8.60, +1489.60]` — positive at
every layer (the post-filter surviving count exceeds the complete-period main
term). The one-sided sufficient condition `E_q > -main_term` therefore holds
trivially at all 24 layers (as the note's review observed, this is
algebraically equivalent to `surviving > 0`).

The two-sided bound `|E_q| < main_term` — the genuinely informative form that
the review identified as the real test — is **not yet evaluated** end-to-end
at scale: the lineage records `E_q` and `main_term` but does not currently
emit the two-sided ratio. That is a small extension to the runner; flagged
here as the next measurement for this candidate. Honest scope: one window,
one chain; the one-sided form holds everywhere but is a restatement of
survival, and the load-bearing two-sided form is still pending.
