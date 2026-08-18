"""Pure, no-I/O measurement library for the deferred-filter-3 candidate.

Companion to lib.py, reusing its sieve rather than duplicating it. Where
lib.py's #3/#4/#13 columns assume post-filter-3 endpoint-disjointness (see
two-gap-isolation-after-filter-three.md), this module measures the window
[q, q^2) with filter 3 *withheld*, where that assumption does not hold and
2-gaps can share endpoints, forming runs of more than one consecutive 2-gap.

Convention, matching candidates/deferred-filter-three-cluster-survival.md:

  q                 the head (a prime)
  primes_below_q    every prime strictly less than q
  deferred          the set of primes withheld from filtering (default {3})
  pre               survivors of [q, q^2) filtering by every prime below q
                     EXCEPT the deferred set ("the deferred-3 stage")
  post              pre, with the deferred primes then reinstalled -- the
                     ordinary square-safe survivor set, unchanged by the
                     reordering (gcd(n, P(q)) does not depend on filter order)

A "2-run of length L" is L consecutive 2-gaps: L+1 accepted values spaced by
2, maximal in both directions. lib.py has no notion of this because it
assumes 2-gaps are already endpoint-disjoint.
"""

from __future__ import annotations

from typing import Iterable, List

from . import window as lib


def run_lengths(survivors: List[int]) -> List[int]:
    """Length (in 2-gaps) of every maximal run of consecutive spaced-by-2
    values in the sorted survivor list. A run of length L is L+1 values
    y, y+2, ..., y+2L with y-2 and y+2L+2 not present.

    Unlike lib._two_gap_starts, this does not assume 2-gaps are endpoint-
    disjoint: a value can be the shared endpoint of two runs' worth of gaps,
    which is exactly what happens once filter 3 is withheld.
    """
    if len(survivors) < 2:
        return []
    lengths: List[int] = []
    run = 0
    prev = survivors[0]
    for v in survivors[1:]:
        if v - prev == 2:
            run += 1
        else:
            if run > 0:
                lengths.append(run)
            run = 0
        prev = v
    if run > 0:
        lengths.append(run)
    return lengths


def deferred_transition(
    q: int, primes_below_q: List[int], deferred: Iterable[int] = (3,)
) -> dict:
    """Measure one head q with `deferred` withheld from filtering, then
    reinstalled.

    primes_below_q must be every prime strictly less than q. Returns a dict
    with cluster sizes, total 2-gap counts, and head-hitting distance, for
    both the deferred stage and after reinstalling.
    """
    deferred = set(deferred)
    kept = [p for p in primes_below_q if p not in deferred]
    kept_odd = [p for p in kept if p != 2]
    p_min = min(kept_odd) if kept_odd else 0

    pre = lib.survivors_list(q, kept)  # deferred-stage survivors
    runs = run_lengths(pre)
    max_run = max(runs) if runs else 0

    post = pre
    for d in sorted(deferred):
        post = lib.post_filter_survivors(post, d)

    n_two_gaps_deferred = lib.count_two_gaps(pre)
    n_two_gaps_post = lib.count_two_gaps(post)
    d_head_post = lib.head_to_first_start(post, q)

    return {
        "q": q,
        "deferred": ",".join(str(d) for d in sorted(deferred)),
        "window_len": q * q - q,
        "p_min": p_min,
        "predicted_cap": p_min - 2 if p_min else 0,
        "n_survivors_deferred": len(pre),
        "n_two_gaps_deferred": n_two_gaps_deferred,
        "max_run_length": max_run,
        "n_runs_ge3": sum(1 for r in runs if r >= 3),
        "n_runs_total": len(runs),
        "n_two_gaps_post": n_two_gaps_post,
        "d_head_post": d_head_post,
        "lemma_c_predicts_survivor": max_run >= 3,
        "actual_survivor_exists": n_two_gaps_post > 0,
    }
