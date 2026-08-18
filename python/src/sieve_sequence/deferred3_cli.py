"""Thin runner for the deferred-filter-3 candidate stress-test.

  python3 run_deferred3.py [max_prime]   # default 2000

For every prime head q <= max_prime (q >= 7, so at least {2,3,5} lie below
it), withholds filter 3, sieves [q, q^2), measures the 2-run structure, then
reinstalls filter 3 and measures the ordinary square-safe survivor set.
Appends one row per head to data/candidates/deferred3-measurements.csv.

All measurement logic lives in deferred3_lib.py / lib.py (pure, no I/O).
This file only: parses args, generates the prime list, loops heads, writes
CSV, and prints a summary of what candidates/deferred-filter-three-
cluster-survival.md's Lemma A (predicted_cap == max_run_length) and Lemma C
(a run >=3 implies a survivor) predict versus what was actually measured.
"""

from __future__ import annotations

import csv
import os
import sys

from sympy import primerange

from . import deferred3 as dlib

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))
OUT_PATH = os.path.join(REPO, "data", "candidates", "deferred3-measurements.csv")

COLUMNS = [
    "q", "deferred", "window_len", "p_min", "predicted_cap",
    "n_survivors_deferred", "n_two_gaps_deferred",
    "max_run_length", "n_runs_ge3", "n_runs_total",
    "n_two_gaps_post", "d_head_post",
    "lemma_c_predicts_survivor", "actual_survivor_exists",
]


def primes_list(max_prime: int):
    return list(primerange(2, max_prime + 1))


def run(max_prime: int, out_path: str = OUT_PATH, deferred=(3,)) -> int:
    primes = primes_list(max_prime)
    os.makedirs(os.path.dirname(out_path), exist_ok=True)
    rows = 0
    cap_mismatches = 0
    lemma_c_false_negatives = 0  # run>=3 predicted survivor but none found
    with open(out_path, "w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=COLUMNS)
        writer.writeheader()
        for i in range(len(primes)):
            q = int(primes[i])
            if q < 7:
                continue
            below_q = [int(r) for r in primes[:i]]
            res = dlib.deferred_transition(q, below_q, deferred=deferred)
            writer.writerow({k: res[k] for k in COLUMNS})
            rows += 1
            if res["max_run_length"] != res["predicted_cap"]:
                cap_mismatches += 1
            if res["lemma_c_predicts_survivor"] and not res["actual_survivor_exists"]:
                lemma_c_false_negatives += 1
            if rows % 25 == 0 or q <= 50:
                print(
                    f"q={q:6d} win={res['window_len']:>10,} "
                    f"p_min={res['p_min']:3d} cap_pred={res['predicted_cap']:2d} "
                    f"max_run={res['max_run_length']:2d} "
                    f"n_gaps_deferred={res['n_two_gaps_deferred']:6d} "
                    f"n_gaps_post={res['n_two_gaps_post']:5d} "
                    f"d_head_post={res['d_head_post']:8d} "
                    f"runs>=3={res['n_runs_ge3']:3d}"
                )
    print(f"\nWrote {rows} heads to {out_path}")
    print(f"Lemma A (max_run_length == predicted_cap) mismatches: {cap_mismatches} / {rows}")
    print(
        f"Lemma C false negatives (run>=3 present but no post-3 survivor): "
        f"{lemma_c_false_negatives} / {rows}"
    )
    return rows


def main(argv):
    max_prime = int(argv[1]) if len(argv) > 1 else 2000
    out = argv[2] if len(argv) > 2 else OUT_PATH
    print(f"deferred-3 stress-test: max_prime={max_prime} out={out}")
    run(max_prime, out)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
