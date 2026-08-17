"""Command-line runner for square-window candidate measurements.

Run from the repository root with either:

  python -m sieve_sequence.window_cli [max_prime] [output.csv]
  python -m sieve_sequence.window_cli --sparse [stride] [max_prime] [output.csv]

Defaults are caller-relative paths under ``data/candidates``. Explicit output
paths work from any installation location.
"""

from __future__ import annotations

import csv
import sys
from pathlib import Path

from sympy import primerange

from . import window as lib


DENSE_OUTPUT = Path("data/candidates/window-measurements.csv")
SPARSE_OUTPUT = Path("data/candidates/window-measurements-sparse.csv")

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


def _prepare_output(out_path: str | Path) -> Path:
    path = Path(out_path).expanduser()
    path.parent.mkdir(parents=True, exist_ok=True)
    return path


def run(max_prime: int, out_path: str | Path = DENSE_OUTPUT) -> int:
    """Measure every consecutive-prime transition through ``max_prime``."""
    primes = primes_list(max_prime)
    output = _prepare_output(out_path)
    rows = 0
    with output.open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=COLUMNS)
        writer.writeheader()
        for i in range(len(primes) - 1):
            p = int(primes[i])
            if p < 3:
                continue
            q = int(primes[i + 1])
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
    print(f"\nWrote {rows} transitions to {output}")
    return rows


def run_sparse(max_prime: int, stride: int, out_path: str | Path) -> int:
    """Measure one transition every ``stride`` primes through ``max_prime``."""
    primes = primes_list(max_prime)
    output = _prepare_output(out_path)
    sampled = []
    for i in range(1, len(primes) - 1):
        if (i - 1) % stride == 0 or i <= 4:
            sampled.append(i)
    rows = 0
    with output.open("w", newline="") as f:
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
    print(f"\nWrote {rows} sparse transitions to {output}")
    return rows


def main(argv=None) -> int:
    args = sys.argv if argv is None else argv
    if len(args) > 1 and args[1] == "--sparse":
        stride = int(args[2]) if len(args) > 2 else 100
        max_prime = int(args[3]) if len(args) > 3 else 20000
        out = args[4] if len(args) > 4 else SPARSE_OUTPUT
        print(
            f"candidate stress-test SPARSE: "
            f"stride={stride} max_prime={max_prime} out={out}"
        )
        run_sparse(max_prime, stride, out)
        return 0
    max_prime = int(args[1]) if len(args) > 1 else 1000
    out = args[2] if len(args) > 2 else DENSE_OUTPUT
    print(f"candidate stress-test: max_prime={max_prime} out={out}")
    run(max_prime, out)
    return 0


if __name__ == "__main__":
    sys.exit(main())
