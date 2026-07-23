# Bounded Consecutive Destruction

**Candidate hypothesis:** Unproved and potentially false.

**Conditional implication:** Mathematically proved from the stated ordering.

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
consecutive run (in the cyclic order of 2-gap starts) of starts destroyed by
the filter. The candidate requires "there exists a bound `R_p`" — an
existential claim, so no finite run can *confirm* it, only falsify it by
showing unbounded growth.

Distribution over 186 transitions: `{0: 95, 1: 90, 2: 1}`. Min 0, median 0,
**max 2** (single occurrence). Over the sparse large-p sample (p~1000..19000)
the max is 1. Trend (log-log, n=186): exponent k = -0.075, Pearson r = -0.094
against log p — **no detectable trend**; the run is noise around 0/1, not
growing.

### What this does and does not establish

- **Does:** show the destroyed-start run is *flat* and small at window scale to
  p~19000. Any proof invoking #4 may assume `R_p` is a small constant (2 covers
  every measured transition; the data supports assuming it does not grow) without
  contradicting measurements. A flat trend is exactly the favorable outcome for
  an existential "there exists a bound" claim.
- **Does not:** confirm the bound exists for all p (existential claims can't be
  confirmed by finite data — only falsified, which the data does not do). The
  candidate still requires a proof discharging `R_p`. Window-scale only; does
  not touch infinitude.
