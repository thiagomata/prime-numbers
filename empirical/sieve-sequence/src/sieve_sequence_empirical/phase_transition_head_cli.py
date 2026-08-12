"""Command-line runner for the head-recurrence Borel-Cantelli sweep (draft
article Property IV, section 5.2): does sum_{Q prime} Pr(H_Q) converge or
diverge, for w_r = 1 + c*log(r)?

Unlike the window-occupancy sweep, this genuinely sums over real, enumerated
primes (sympy.primerange) rather than evaluating a closed-form asymptotic at
an arbitrary Q -- Borel-Cantelli's criterion is about an actual sum over
actual primes, not a continuous asymptotic. This bounds the feasible range
to something enumerable (~10^7), which turns out to be enough: this family's
phase transition is polynomial-rate in Q, not double-logarithmic like the
fixed-w family, so the c<1/2 vs c>=1/2 split is already clearly visible well
within that range (see tests/test_phase_transition.py's numeric check).

Writes data/candidates/phase-transition-head.csv for
presentations/sieve-sequence-visualization/figures/phase_transition_head_chart.py
to plot.
"""

from __future__ import annotations

import csv
import sys
from pathlib import Path

from sympy import primerange

from . import phase_transition as lib

C_VALUES = [0.1, 0.3, 0.5, 0.7, 1.0, 1.5]

COLUMNS = ["Q", "prime_index"] + [f"cumsum_c{str(c).replace('.', '_')}" for c in C_VALUES]


def run(out_path: str | Path, Q_max: int = 10_000_000, num_checkpoints: int = 150) -> int:
    import math

    log_min, log_max = math.log10(3), math.log10(Q_max)
    checkpoints = sorted({
        int(round(10 ** (log_min + i * (log_max - log_min) / (num_checkpoints - 1))))
        for i in range(num_checkpoints)
    })

    output = Path(out_path).expanduser()
    output.parent.mkdir(parents=True, exist_ok=True)
    cumsums = {c: 0.0 for c in C_VALUES}
    checkpoint_idx = 0
    rows_written = 0
    with output.open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=COLUMNS)
        writer.writeheader()
        for prime_index, p in enumerate(primerange(3, Q_max + 1), start=1):
            for c in C_VALUES:
                cumsums[c] += lib.head_probability_log_growth(float(p), c)
            if checkpoint_idx < len(checkpoints) and p >= checkpoints[checkpoint_idx]:
                row = {"Q": p, "prime_index": prime_index}
                for c in C_VALUES:
                    row[f"cumsum_c{str(c).replace('.', '_')}"] = cumsums[c]
                writer.writerow(row)
                rows_written += 1
                while checkpoint_idx < len(checkpoints) and p >= checkpoints[checkpoint_idx]:
                    checkpoint_idx += 1
    print(f"Wrote {rows_written} checkpoint rows (Q up to {Q_max}) to {output}")
    return rows_written


def main(argv=None) -> int:
    out = Path("data/candidates") / "phase-transition-head.csv"
    print(f"phase-transition head-recurrence sweep: out={out}")
    run(out)
    return 0


if __name__ == "__main__":
    sys.exit(main())
