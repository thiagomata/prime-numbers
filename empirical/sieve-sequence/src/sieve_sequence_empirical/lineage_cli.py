"""Command-line runner for the fixed-future-window lineage experiment.

For #14 the per-layer search uses the proved exact stable table for small k
once {2,3,5,7} are installed and exact enumeration at earlier stages. The
small-k premise therefore remains exact beyond the materialization frontier;
only full-period diagnostics may become unmeasured.
"""

from __future__ import annotations

import csv
import sys
from pathlib import Path

from sympy import primerange

from . import lineage as lib


COLUMNS = [
    "Q", "layer", "r", "M_r", "T_r",
    "G_r_window", "destroyed", "surviving",
    "cyclic_run_full_period", "window_linear_run",
    "sigma_r_2", "sigma_r_min_gap_times_r",
    "c14_interval_found", "c14_k_r", "c14_J_len", "c14_G_in_J", "c14_sigma_kr",
    "c14_note",
    "post_E_q", "post_main_term",
    "c12_margin", "c13_margin",
]


def search_c14_interval(
    Q: int, r: int, primes_strictly_below_r: list
) -> dict:
    """Search the exact small-k #14 premise within ``[Q, Q^2)``."""
    out = {"c14_interval_found": False, "c14_k_r": None, "c14_J_len": None,
           "c14_G_in_J": None, "c14_sigma_kr": None, "c14_note": ""}
    pre = lib.window_survivors(Q, primes_strictly_below_r)
    starts = lib.two_gap_starts(pre)
    n = len(starts)
    if n < 2:
        out["c14_note"] = "fewer than 2 window 2-gap starts"
        return out
    has_stable = {2, 3, 5, 7}.issubset(set(primes_strictly_below_r))
    if not has_stable:
        try:
            gaps, _ = lib.full_period_cofactor_gaps(primes_strictly_below_r)
            if len(gaps) < 2:
                out["c14_note"] = "T_r < 2 (first layer; sigma undefined)"
                return out
        except ValueError as exc:
            out["c14_note"] = f"sigma unavailable: {exc}"
            return out

    starts_list = [int(x) for x in starts]
    k_max = 10
    best = None
    for c in range(2, min(k_max, n) + 1):
        try:
            sig, _ = lib.sigma_r_for_layer(c, r, primes_strictly_below_r)
        except ValueError:
            continue
        min_span = None
        for i in range(n - c + 1):
            span = starts_list[i + c - 1] + 2 - starts_list[i]
            if min_span is None or span < min_span:
                min_span = span
        if min_span is not None and min_span < sig:
            surplus = c - 1
            if best is None or surplus > best["surplus"]:
                best = {"c14_interval_found": True, "c14_k_r": c,
                        "c14_J_len": min_span, "c14_G_in_J": c,
                        "c14_sigma_kr": sig, "surplus": surplus}
    if best:
        best.pop("surplus", None)
        return best
    out["c14_note"] = "no interval J_r satisfied the premise at this layer"
    return out


def _prepare_output(out_path: str | Path) -> Path:
    path = Path(out_path).expanduser()
    path.parent.mkdir(parents=True, exist_ok=True)
    return path


def run(Q: int, out_path: str | Path) -> int:
    primes_below_Q = [int(p) for p in primerange(2, Q)]
    output = _prepare_output(out_path)
    rows = 0
    with output.open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=COLUMNS)
        writer.writeheader()
        layers = [r for r in primes_below_Q if r >= 3]
        for layer_idx, r in enumerate(layers):
            below = [p for p in primes_below_Q if p < r]
            res = lib.layer(Q, r, below)
            try:
                gaps, _ = lib.full_period_cofactor_gaps(below)
                T_r = len(gaps)
                sigma_min = r * min(gaps) if gaps else None
            except ValueError:
                T_r = None
                sigma_min = None
            res["layer"] = layer_idx
            res["T_r"] = T_r
            res["sigma_r_min_gap_times_r"] = sigma_min
            res.update(search_c14_interval(Q, r, below))
            writer.writerow({k: res.get(k, "") for k in COLUMNS})
            rows += 1
            print(
                f"layer {layer_idx} r={r:3d} M_r={res.get('M_r')} T_r={T_r} "
                f"G_r={res['G_r_window']:4d} dest={res['destroyed']:3d} "
                f"surv={res['surviving']:4d} "
                f"cyc_run={res.get('cyclic_run_full_period')} "
                f"win_run={res['window_linear_run']} "
                f"c14_found={res['c14_interval_found']} "
                f"c12_margin={res['c12_margin']:+.2f} "
                f"c13_margin={res['c13_margin']:+.2f}"
            )
    print(f"\nWrote {rows} layers to {output}")
    return rows


def main(argv=None) -> int:
    args = sys.argv if argv is None else argv
    Q = int(args[1]) if len(args) > 1 else 17
    out = (
        args[2] if len(args) > 2
        else Path("data/candidates") / f"lineage-Q{Q}.csv"
    )
    print(f"lineage experiment: Q={Q} out={out}")
    run(Q, out)
    return 0


if __name__ == "__main__":
    sys.exit(main())
