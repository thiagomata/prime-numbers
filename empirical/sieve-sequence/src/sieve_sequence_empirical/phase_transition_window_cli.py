"""Command-line runner for the "no finite constant is fatal" window-occupancy
sweep (draft article Property III, section 5.1).

Pure analytic sweep over log10(Q) -- no real data, no prime enumeration, so
Q can be pushed arbitrarily large (needed here: a fixed relative-hazard
factor w=10 does not visibly turn around and start climbing again until
Q is astronomically large, since Q^2 must overtake (ln Q)^(2w)). Writes
data/candidates/phase-transition-window.csv for
presentations/sieve-sequence-visualization/figures/phase_transition_window_chart.py
to plot.

Also includes the log-growth frontier at c=1 (w_r = 1 + log(r)) -- the
article's own exact square-window threshold (Property IV, section 5.2):
c<1 still diverges, c>=1 tends to 0. Unlike the fixed-w curves, this one
sits exactly on the boundary between the two regimes, so it is the natural
line to mark as the frontier on this chart.
"""

from __future__ import annotations

import csv
import sys
from pathlib import Path

from . import phase_transition as lib

FIXED_W_VALUES = [1.0, 3.0, 6.0, 10.0]
CONSTANT_SHARE_ALPHA = 0.01
FRONTIER_C = 1.0

COLUMNS = (
    ["log10_Q"]
    + [f"log10_lambda_fixed_w{int(w)}" for w in FIXED_W_VALUES]
    + ["log10_lambda_constant_share", "log10_lambda_frontier_c1"]
)


def sweep(log10_Q_min: float, log10_Q_max: float, num_points: int) -> list[dict]:
    step = (log10_Q_max - log10_Q_min) / (num_points - 1)
    rows = []
    for i in range(num_points):
        log10_Q = log10_Q_min + i * step
        row = {"log10_Q": log10_Q}
        for w in FIXED_W_VALUES:
            row[f"log10_lambda_fixed_w{int(w)}"] = lib.log10_window_occupancy_fixed_w(log10_Q, w)
        row["log10_lambda_constant_share"] = lib.log10_window_occupancy_constant_share(
            log10_Q, CONSTANT_SHARE_ALPHA
        )
        row["log10_lambda_frontier_c1"] = lib.log10_window_occupancy_log_growth(
            log10_Q, FRONTIER_C
        )
        rows.append(row)
    return rows


def run(out_path: str | Path, log10_Q_min: float = 2.0, log10_Q_max: float = 60.0,
        num_points: int = 300) -> int:
    rows = sweep(log10_Q_min, log10_Q_max, num_points)
    output = Path(out_path).expanduser()
    output.parent.mkdir(parents=True, exist_ok=True)
    with output.open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=COLUMNS)
        writer.writeheader()
        for row in rows:
            writer.writerow(row)
    print(f"Wrote {len(rows)} rows (log10(Q) from {log10_Q_min} to {log10_Q_max}) to {output}")
    return len(rows)


def main(argv=None) -> int:
    out = Path("data/candidates") / "phase-transition-window.csv"
    print(f"phase-transition window-occupancy sweep: out={out}")
    run(out)
    return 0


if __name__ == "__main__":
    sys.exit(main())
