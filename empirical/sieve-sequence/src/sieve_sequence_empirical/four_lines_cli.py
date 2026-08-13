"""Command-line runner for the friendly/random/adversarial/empirical
trajectory comparison.

Reads an existing lineage chain CSV (data/candidates/lineage-Q{Q}.csv,
written by lineage_cli.py -- run that first if it does not exist yet) rather
than recomputing the real trajectory. Anchors the three theoretical
projections (friendly, random, adversarial) at one real measured layer of
that chain, and writes all four side by side for
presentations/sieve-sequence-visualization/figures to plot.

See properties/sieve-sequence/realized-filter-adversariality-score.md,
section "Three Compounding Trajectories," for the derivation, and
articles/learnings/learnings-capacity-argument.md Section 24 for why the very
first layer (r=3, a single huge 2/3 cut) is a poor anchor: the default
anchor layer is 7 (r=23), the point where the per-filter rate 2/r first
drops under 10% -- past the large early deterministic cuts, with enough
population (395) and remaining layers (16) left to show compounding.
"""

from __future__ import annotations

import csv
import sys
from pathlib import Path

from . import four_lines as lib

DEFAULT_ANCHOR_LAYER = 7

COLUMNS = [
    "Q", "anchor_layer", "anchor_r", "anchor_n0",
    "layer", "r",
    "N_friendly", "N_random", "N_adversarial",
    "N_frontier",
    "N_empirical_pre", "N_empirical_post",
]


def _read_lineage_chain(lineage_path: str | Path) -> list[dict]:
    path = Path(lineage_path)
    if not path.exists():
        raise FileNotFoundError(
            f"{path} not found -- run lineage_cli.py for this Q first"
        )
    with path.open(newline="") as f:
        reader = csv.DictReader(f)
        return [
            {
                "layer": int(row["layer"]),
                "r": int(row["r"]),
                "G_r_window": int(row["G_r_window"]),
                "surviving": int(row["surviving"]),
            }
            for row in reader
        ]


def run(
    Q: int,
    lineage_path: str | Path,
    out_path: str | Path,
    anchor_layer: int = DEFAULT_ANCHOR_LAYER,
) -> int:
    chain = _read_lineage_chain(lineage_path)
    chain.sort(key=lambda row: row["layer"])
    if anchor_layer < 0 or anchor_layer >= len(chain):
        raise ValueError(
            f"anchor_layer={anchor_layer} out of range [0, {len(chain) - 1}]"
        )

    anchor = chain[anchor_layer]
    n0 = float(anchor["surviving"])
    future = [row for row in chain if row["layer"] > anchor_layer]
    rs = [row["r"] for row in future]

    friendly = lib.friendly_trajectory(n0, len(rs))
    random_ = lib.random_trajectory(n0, rs)
    adversarial = lib.adversarial_trajectory(n0, Q, rs)
    frontier = lib.log_growth_trajectory(n0, rs)

    output = Path(out_path).expanduser()
    output.parent.mkdir(parents=True, exist_ok=True)
    rows = 0
    with output.open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=COLUMNS)
        writer.writeheader()
        # anchor row: all four lines agree here by construction.
        writer.writerow({
            "Q": Q, "anchor_layer": anchor_layer, "anchor_r": anchor["r"],
            "anchor_n0": n0, "layer": anchor["layer"], "r": anchor["r"],
            "N_friendly": n0, "N_random": n0, "N_adversarial": n0,
            "N_frontier": n0,
            "N_empirical_pre": anchor["G_r_window"],
            "N_empirical_post": anchor["surviving"],
        })
        rows += 1
        for i, row in enumerate(future):
            writer.writerow({
                "Q": Q, "anchor_layer": anchor_layer, "anchor_r": anchor["r"],
                "anchor_n0": n0, "layer": row["layer"], "r": row["r"],
                "N_friendly": friendly[i], "N_random": random_[i],
                "N_adversarial": adversarial[i],
                "N_frontier": frontier[i],
                "N_empirical_pre": row["G_r_window"],
                "N_empirical_post": row["surviving"],
            })
            rows += 1
    print(f"Wrote {rows} rows ({len(future)} projected layers past anchor "
          f"layer {anchor_layer}, r={anchor['r']}, N_0={n0:.0f}) to {output}")
    return rows


def main(argv=None) -> int:
    args = sys.argv if argv is None else argv
    Q = int(args[1]) if len(args) > 1 else 101
    anchor_layer = int(args[2]) if len(args) > 2 else DEFAULT_ANCHOR_LAYER
    lineage_path = Path("data/candidates") / f"lineage-Q{Q}.csv"
    out = Path("data/candidates") / f"four-lines-Q{Q}.csv"
    print(f"four-lines comparison: Q={Q} anchor_layer={anchor_layer} out={out}")
    run(Q, lineage_path, out, anchor_layer)
    return 0


if __name__ == "__main__":
    sys.exit(main())
