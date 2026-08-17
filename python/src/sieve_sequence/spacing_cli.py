"""Command-line runner for the implied-spacing view.

Reads an existing four-lines comparison CSV
(data/candidates/four-lines-Q{Q}.csv, written by
sieve_sequence_empirical.four_lines_cli -- run that first if it does not
exist yet) and transforms its four count columns into implied-spacing
columns, using the anchor's own real density as the reference scale. Writes
data/candidates/spacing-Q{Q}.csv for
presentations/sieve-sequence-visualization/figures/spacing_chart.py to plot.

See empirical/sieve-sequence/src/sieve_sequence_empirical/spacing.py for why
this is a reciprocal-scaling transform of the existing counts, not a new
model, and properties/sieve-sequence/realized-filter-adversariality-score.md
for why a growing-but-finite spacing avoids the extinction illusion that a
shrinking count creates.
"""

from __future__ import annotations

import csv
import sys
from pathlib import Path

from . import spacing as lib

COLUMNS = [
    "Q", "anchor_layer", "anchor_r", "anchor_n0", "ref_spacing",
    "layer", "r",
    "spacing_friendly", "spacing_random", "spacing_adversarial", "spacing_empirical",
]


def _read_four_lines(four_lines_path: str | Path) -> list[dict]:
    path = Path(four_lines_path)
    if not path.exists():
        raise FileNotFoundError(
            f"{path} not found -- run four_lines_cli.py for this Q first"
        )
    with path.open(newline="") as f:
        reader = csv.DictReader(f)
        return [
            {
                "Q": int(row["Q"]),
                "anchor_layer": int(row["anchor_layer"]),
                "anchor_r": int(row["anchor_r"]),
                "anchor_n0": float(row["anchor_n0"]),
                "layer": int(row["layer"]),
                "r": int(row["r"]),
                "N_friendly": float(row["N_friendly"]),
                "N_random": float(row["N_random"]),
                "N_adversarial": float(row["N_adversarial"]),
                "N_empirical_post": float(row["N_empirical_post"]),
            }
            for row in reader
        ]


def run(four_lines_path: str | Path, out_path: str | Path) -> int:
    rows = _read_four_lines(four_lines_path)
    rows.sort(key=lambda row: row["layer"])
    if not rows:
        raise ValueError(f"{four_lines_path} has no rows")

    Q = rows[0]["Q"]
    anchor_layer = rows[0]["anchor_layer"]
    anchor_r = rows[0]["anchor_r"]
    n0 = rows[0]["anchor_n0"]
    ref_spacing = 1.0 / lib.density_at(anchor_r)

    friendly = lib.implied_spacing(n0, [r["N_friendly"] for r in rows], ref_spacing)
    random_ = lib.implied_spacing(n0, [r["N_random"] for r in rows], ref_spacing)
    adversarial = lib.implied_spacing(n0, [r["N_adversarial"] for r in rows], ref_spacing)
    empirical = lib.implied_spacing(n0, [r["N_empirical_post"] for r in rows], ref_spacing)

    output = Path(out_path).expanduser()
    output.parent.mkdir(parents=True, exist_ok=True)
    written = 0
    with output.open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=COLUMNS)
        writer.writeheader()
        for i, row in enumerate(rows):
            writer.writerow({
                "Q": Q, "anchor_layer": anchor_layer, "anchor_r": anchor_r,
                "anchor_n0": n0, "ref_spacing": ref_spacing,
                "layer": row["layer"], "r": row["r"],
                "spacing_friendly": friendly[i],
                "spacing_random": random_[i],
                "spacing_adversarial": adversarial[i],
                "spacing_empirical": empirical[i],
            })
            written += 1
    n_extinct = sum(1 for v in adversarial if v == float("inf"))
    print(
        f"Wrote {written} rows to {output} "
        f"(ref_spacing={ref_spacing:.4f} at anchor r={anchor_r}; "
        f"adversarial hits extinction at {n_extinct} layer(s))"
    )
    return written


def main(argv=None) -> int:
    args = sys.argv if argv is None else argv
    Q = int(args[1]) if len(args) > 1 else 101
    four_lines_path = Path("data/candidates") / f"four-lines-Q{Q}.csv"
    out = Path("data/candidates") / f"spacing-Q{Q}.csv"
    print(f"implied-spacing view: Q={Q} out={out}")
    run(four_lines_path, out)
    return 0


if __name__ == "__main__":
    sys.exit(main())
