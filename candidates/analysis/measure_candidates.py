"""Thin runner for the candidate stress-test.

  python3 measure_candidates.py [max_prime]   # default 1000

Sieves the square-safe window W = [q, q^2) for every consecutive-prime
transition (p, q) with p >= 3 and q <= max_prime, and appends one row per
transition to data/candidates/window-measurements.csv.

All measurement logic lives in lib.py (pure, unit-tested by test_measure.py).
This file only: parses args, generates the prime list, loops transitions, and
writes CSV. Run test_measure.py first and keep it green.

Window convention: [q, q^2), article-authoritative (gap-dynamics.md S9).
"""

from __future__ import annotations

import csv
import os
import sys

from sympy import nextprime, primerange

import lib

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))
OUT_PATH = os.path.join(REPO, "data", "candidates", "window-measurements.csv")

# Column order in the CSV. Keep stable; downstream readers depend on it.
COLUMNS = [
    "p", "q", "window_len",
    "G_local", "A_worst", "surplus", "destroyed", "surviving", "waste_ratio",
    "max_cluster_in_width_p", "max_cons_destroyed_run", "d_head",
    "main_term", "E_q",
    "destruction_rate", "gap_2_over_p",
    "residue_max_dev", "endpoint_bias",
]


def primes_list(max_prime: int):
    """Every prime from 2 up to max_prime, ascending."""
    return list(primerange(2, max_prime + 1))


def run(max_prime: int, out_path: str = OUT_PATH) -> int:
    primes = primes_list(max_prime)
    os.makedirs(os.path.dirname(out_path), exist_ok=True)
    rows = 0
    with open(out_path, "w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=COLUMNS)
        writer.writeheader()
        for i in range(len(primes) - 1):
            p = int(primes[i])
            if p < 3:
                continue
            q = int(primes[i + 1])
            # primes below p = the installed filters of the stage headed at p
            below_p = [int(r) for r in primes[:i]]
            res = lib.transition(p, q, below_p)
            writer.writerow({k: res.get(k, "") for k in COLUMNS})
            rows += 1
            if rows % 25 == 0 or p <= 13:
                print(
                    f"p={p:4d} q={q:4d} "
                    f"G_local={res['G_local']:5d} destroyed={res['destroyed']:3d} "
                    f"A_worst={res['A_worst']:3d} waste={res['waste_ratio']:+.3f} "
                    f"surviving={res['surviving']:3d}"
                )
    print(f"\nWrote {rows} transitions to {out_path}")
    return rows


def run_sparse(max_prime: int, stride: int, out_path: str) -> int:
    """Sparse large-prime sample: sieve one transition every `stride` primes.

    Used to check whether the measured properties drift at large p. Sieving
    EVERY transition to a large max_prime is infeasible because the window
    [q,q^2) grows quadratically and late transitions dominate the cost. A sparse
    sample answers "do the properties change at scale?" without that cost.

    Each transition is sieved and its row written immediately, then the window
    array is released, so peak memory is one transition's window (~400MB at
    q~20000).
    """
    primes = primes_list(max_prime)
    os.makedirs(os.path.dirname(out_path), exist_ok=True)
    sampled = []
    for i in range(1, len(primes) - 1):
        if (i - 1) % stride == 0 or i <= 4:
            sampled.append(i)
    rows = 0
    with open(out_path, "w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=COLUMNS)
        writer.writeheader()
        for i in sampled:
            p = int(primes[i])
            q = int(primes[i + 1])
            if p < 3:
                continue
            below_p = [int(r) for r in primes[:i]]
            res = lib.transition(p, q, below_p)
            writer.writerow({k: res.get(k, "") for k in COLUMNS})
            rows += 1
            print(
                f"p={p:6d} q={q:6d} win={q*q-q:>11,} "
                f"G_local={res['G_local']:7d} destroyed={res['destroyed']:3d} "
                f"A_worst={res['A_worst']:3d} waste={res['waste_ratio']:+.3f} "
                f"surv={res['surviving']:6d} dest_rate={res['destruction_rate']:.4g}"
            )
    print(f"\nWrote {rows} sparse transitions to {out_path}")
    return rows


def main(argv):
    # default: dense run to 1000. With --sparse STRIDE [MAX], sample every
    # STRIDE-th prime (up to MAX, default 20000) for a large-p drift check.
    if len(argv) > 1 and argv[1] == "--sparse":
        stride = int(argv[2]) if len(argv) > 2 else 100
        max_prime = int(argv[3]) if len(argv) > 3 else 20000
        out = (
            argv[4] if len(argv) > 4
            else os.path.join(REPO, "data", "candidates", "window-measurements-sparse.csv")
        )
        print(f"candidate stress-test SPARSE: stride={stride} max_prime={max_prime} out={out}")
        run_sparse(max_prime, stride, out)
        return 0
    max_prime = int(argv[1]) if len(argv) > 1 else 1000
    out = argv[2] if len(argv) > 2 else OUT_PATH
    print(f"candidate stress-test: max_prime={max_prime} out={out}")
    run(max_prime, out)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
