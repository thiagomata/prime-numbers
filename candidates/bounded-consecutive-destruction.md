# Bounded Consecutive Destruction

**Candidate hypothesis:** Unproved and potentially false.

**Conditional implication:** Mathematically proved from the stated ordering.

**Empirical status:** INCONCLUSIVE — window-linear run flat (max 2); cyclic run unmeasurable at scale (period-scale, no shortcut). See "Empirical status (lineage experiment)".

## Candidate Hypothesis

Order the pre-filter 2-gap starts cyclically. Suppose the transition destroys
at most `R_p` consecutive starts in that ordering, and `W_q` contains at least
`R_p+1` consecutive ordered starts whose two endpoints all lie in `W_q`.

Assume this combined condition holds at infinitely many stages.

## Why It Is Sufficient

If every one of the `R_p+1` local starts were destroyed, they would form a run
of more than `R_p` consecutive destroyed 2-gap starts, contradicting the run
bound. Hence at least one remains in `W_q` after filtering.

The run is a run of destroyed 2-gap starts, not a run of arbitrary removed
accepted values. Those are different orderings and cannot be substituted.

## Established Inputs

- [2-gap isolation](../properties/sieve-sequence/two-gap-isolation-after-filter-three.md)
- [Copy-index filter frequency](../properties/sieve-sequence/copy-index-filter-frequency.md)

## Limitation

Neither the destruction-run bound nor the required local block is currently
proved. A global bound on the number of deletions does not bound their longest
consecutive run among 2-gap starts.

## Empirical status (window scale, p to ~19000)

Source: `candidates/analysis/measure_candidates.py`, 186 transitions (dense
p<=991 + sparse to p~19000). Quantity: `max_cons_destroyed_run` = the longest
consecutive run in the **linear order of starts lying inside `W_q`** that the
filter destroys. The implementation does not join the last local start back to
the first, and therefore does not measure the cyclic full-period run stated in
the hypothesis. The candidate requires "there exists a bound `R_p`" — an
existential claim, so no finite run can *confirm* it, only falsify it by
showing unbounded growth.

Distribution over 186 transitions: `{0: 95, 1: 90, 2: 1}`. Min 0, median 0,
**max 2** (single occurrence). Over the sparse large-p sample (p~1000..19000)
the max is 1. Trend (log-log, n=186): exponent k = -0.075, Pearson r = -0.094
against log p — **no detectable trend**; the run is noise around 0/1, not
growing.

### What this does and does not establish

- **Does:** show the destroyed-start run is *flat* and small at window scale to
  p~19000 in the measured linear window. The constant 2 covers every measured
  window-linear run and is a useful conjectural target.
- **Does not:** confirm the bound exists for all p (existential claims can't be
  confirmed by finite data), test the cyclic wrap, or bound runs elsewhere in
  the period. The candidate still requires a proof discharging `R_p`.

## Strategic assessment after empirical review

Among the mechanistic candidates, this is one of the sharpest and most
falsifiable: a third consecutive destroyed start would immediately refute the
conjectural constant `R=2` in the tested setting. Proof priority is high, but
the next experiment must first close the measurement gap by checking cyclic
runs on complete small periods and by tracking runs in a fixed future window
after several consecutive filters.

A proof should characterize the simultaneous congruence requirements for a
run of three destroyed 2-gap starts. If those requirements are impossible, or
force a local configuration incompatible with the prior sieve stages, #4
becomes a concrete non-cherry-picking mechanism rather than an observed bound.

## Empirical status (lineage experiment): cyclic run unmeasurable at scale

The lineage experiment (`candidates/analysis/run_lineage.py`) computes the
cyclic destroyed run for the layers where the period modulus `M_r` is small
enough to materialize. Unlike #14's `sigma_r` (which has a stable-wheel form
making it `O(1)` at any scale), the **cyclic destroyed run genuinely requires
the full period**: it is defined over the cyclic ordering of all `T_r = phi(M_r)`
2-gap starts mod `M_r`, and there is no small-`k` stable shortcut for it. At
Q=101, layers 0-7 (r = 3..23) report the cyclic run exactly; layers 8+
(r = 29..97) report `None` (unmeasured), with `M_r` past tractability.

Across the measured early layers the cyclic run stays small (0-3), consistent
with — but not confirming — the conjectural `R=2`. The window-linear run is
reported alongside and differs (confirming the cyclic and linear orderings are
not interchangeable, as the note states).

**Honest scope:** the cyclic run at scale is the one quantity in this whole
empirical effort that does NOT have a cheap path. Unlike #14, #12, #13 (whose
stated conditions have now been measured at long chains via the lineage
experiment), #4's stated condition remains measurable only for small `M_r`.
Closing it for large `M_r` needs either a structural bound on the run (proof)
or an algorithmic shortcut that has not been found.
