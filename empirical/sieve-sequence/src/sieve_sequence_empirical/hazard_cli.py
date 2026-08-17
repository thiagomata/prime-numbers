"""Command-line runner for the fixed-cohort cumulative hazard experiment.

Writes one CSV per Q value with per-layer and cumulative hazard columns.
"""

from __future__ import annotations

import csv
import sys
from pathlib import Path

from . import hazard as lib


COLUMNS = [
    "Q", "layer", "r",
    "L_initial", "L_before", "destroyed", "L_after",
    "f_real", "f_random", "w_real",
    "h_real", "h_random",
    "D_real", "D_random",
    "excess_hazard", "c_eff",
    "survival_real", "survival_random",
]


def _prepare_output(out_path: str | Path) -> Path:
    path = Path(out_path).expanduser()
    path.parent.mkdir(parents=True, exist_ok=True)
    return path


def run(Q: int, out_path: str | Path) -> int:
    rows_list = lib.build_hazard_run(Q)
    output = _prepare_output(out_path)
    L_initial = rows_list[0]["L_before"] if rows_list else 0
    with output.open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=COLUMNS)
        writer.writeheader()
        for idx, row in enumerate(rows_list):
            out_row = {
                "Q": Q,
                "layer": idx,
                "r": row["r"],
                "L_initial": L_initial,
                "L_before": row["L_before"],
                "destroyed": row["destroyed"],
                "L_after": row["L_after"],
                "f_real": row["f_real"],
                "f_random": row["f_random"],
                "w_real": row["w_real"],
                "h_real": row["h_real"],
                "h_random": row["h_random"],
                "D_real": row["D_real"],
                "D_random": row["D_random"],
                "excess_hazard": row["excess_hazard"],
                "c_eff": row["c_eff"],
                "survival_real": row["survival_real"],
                "survival_random": row["survival_random"],
            }
            writer.writerow(out_row)
            print(
                f"layer {idx} r={row['r']:3d} "
                f"L_before={row['L_before']:4d} "
                f"destroyed={row['destroyed']:3d} "
                f"surviving={row['L_after']:4d} "
                f"f_real={row['f_real']:.4f} "
                f"D_real={row['D_real']:.4f} "
                f"excess={row['excess_hazard']:.4f} "
                f"c_eff={row['c_eff']:.4f}"
            )
    print(f"\nWrote {len(rows_list)} layers to {output}")
    return len(rows_list)


def main(argv=None) -> int:
    args = sys.argv if argv is None else argv
    Q = int(args[1]) if len(args) > 1 else 17
    out = (
        args[2] if len(args) > 2
        else Path("data/candidates") / f"fixed-lineage-hazard-Q{Q}.csv"
    )
    print(f"fixed-lineage hazard: Q={Q} out={out}")
    run(Q, out)
    return 0


if __name__ == "__main__":
    sys.exit(main())
