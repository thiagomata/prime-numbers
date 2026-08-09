"""Thin runner for the fixed-future-window lineage experiment.

  python3 run_lineage.py [Q]   # default Q=17 (pilot)

Fixes a future square window W_Q = [Q, Q^2). Tracks the window's 2-gap
population through every intermediate prime filter r < Q, layer by layer
(Reading A: actual accepted set per layer). At each layer records the ACTUAL
STATED CONDITION of candidates #4, #10, #12, #13, #14 -- not proxies.

For #14 it performs the required per-layer interval search. Small k uses the
proved exact stable table once {2,3,5,7} are installed, while early stages
enumerate their tractable periods, so the small-k premise remains exact beyond
the materialization frontier. Full-period diagnostics such as T_r, sigma_r_T,
and the cyclic destroyed run remain unmeasured when M_r exceeds the guard; no
proxy is substituted.

All measurement logic is in lib_lineage.py (pure, unit-tested by
test_lineage.py). This file only parses args, sequences layers, and writes CSV.
Run test_lineage.py first and keep it green.
"""

from __future__ import annotations

import csv
import os
import sys

from sympy import primerange

import lib_lineage as lib

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))
OUT_DIR = os.path.join(REPO, "data", "candidates")

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
    """#14 per-layer premise: exists J_r subset [Q,Q^2), k_r in [2,T_r] with
    G_r(J_r) >= k_r and len(J_r) < sigma_r(k_r)?

    O(n * k_max) search, NOT O(n^2). For each cluster size c in [2, k_max], the
    tightest interval containing c consecutive (in value) 2-gap starts is a
    sliding window of width c over the sorted starts; we compute its minimum
    span in O(n). Then test span < sigma_r(c). sigma_r(c) uses the STABLE TABLE
    for small c (O(1), no M-array), so this is fast at any Q.

    k_max is capped at 10 (the tabulated stable range). #14 only needs SOME
    viable (c, J_r); a small cluster suffices, so c beyond 10 is not searched.
    """
    out = {"c14_interval_found": False, "c14_k_r": None, "c14_J_len": None,
           "c14_G_in_J": None, "c14_sigma_kr": None, "c14_note": ""}
    pre = lib.window_survivors(Q, primes_strictly_below_r)
    starts = lib.two_gap_starts(pre)
    n = len(starts)
    if n < 2:
        out["c14_note"] = "fewer than 2 window 2-gap starts"
        return out
    # sigma availability via the stable table (needs {2,3,5,7} installed) or
    # exact for early stages. T<2 -> sigma undefined (first layer).
    has_stable = {2, 3, 5, 7}.issubset(set(primes_strictly_below_r))
    if not has_stable:
        try:
            gaps, _ = lib.full_period_cofactor_gaps(primes_strictly_below_r)
            if len(gaps) < 2:
                out["c14_note"] = "T_r < 2 (first layer; sigma undefined)"
                return out
        except ValueError as e:
            out["c14_note"] = f"sigma unavailable: {e}"
            return out

    starts_list = [int(x) for x in starts]
    k_max = 10
    best = None
    # For each cluster size c, sliding window of c consecutive starts; track
    # the minimum span (starts[i+c-1]+2 - starts[i]). O(n) per c.
    for c in range(2, min(k_max, n) + 1):
        try:
            sig, _ = lib.sigma_r_for_layer(c, r, primes_strictly_below_r)
        except ValueError:
            continue  # c beyond available sigma range
        min_span = None
        for i in range(n - c + 1):
            span = starts_list[i + c - 1] + 2 - starts_list[i]
            if min_span is None or span < min_span:
                min_span = span
        if min_span is not None and min_span < sig:
            surplus = c - 1  # at most c-1 shots fit in J_r; >= c gaps -> >=1 survives
            if best is None or surplus > best["surplus"]:
                best = {"c14_interval_found": True, "c14_k_r": c,
                        "c14_J_len": min_span, "c14_G_in_J": c,
                        "c14_sigma_kr": sig, "surplus": surplus}
    if best:
        best.pop("surplus", None)
        return best
    out["c14_note"] = "no interval J_r satisfied the premise at this layer"
    return out


def run(Q: int, out_path: str) -> int:
    primes_below_Q = [int(p) for p in primerange(2, Q)]  # all primes < Q
    os.makedirs(os.path.dirname(out_path), exist_ok=True)
    rows = 0
    with open(out_path, "w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=COLUMNS)
        writer.writeheader()
        # Layers start at r=3, not r=2. The hereditary candidate is stated
        # "after filter 3": its sigma_r machinery needs T_r >= 2, and the
        # destroyed+surviving==G_r identity needs filter 3 installed (the p>2
        # endpoint-isolation premise). r=2 is out of scope -- it would add a
        # meaningless layer that breaks the identity.
        layers = [r for r in primes_below_Q if r >= 3]
        for layer_idx, r in enumerate(layers):
            below = [p for p in primes_below_Q if p < r]
            res = lib.layer(Q, r, below)
            # T_r and sigma_r_min_gap
            try:
                gaps, M = lib.full_period_cofactor_gaps(below)
                T_r = len(gaps)
                sigma_min = r * min(gaps) if gaps else None
            except ValueError:
                T_r = None
                sigma_min = None
            res["layer"] = layer_idx
            res["T_r"] = T_r
            res["sigma_r_min_gap_times_r"] = sigma_min
            # #14 interval search
            c14 = search_c14_interval(Q, r, below)
            res.update(c14)
            writer.writerow({k: res.get(k, "") for k in COLUMNS})
            rows += 1
            print(
                f"layer {layer_idx} r={r:3d} M_r={res.get('M_r')} T_r={T_r} "
                f"G_r={res['G_r_window']:4d} dest={res['destroyed']:3d} "
                f"surv={res['surviving']:4d} "
                f"cyc_run={res.get('cyclic_run_full_period')} "
                f"win_run={res['window_linear_run']} "
                f"c14_found={res['c14_interval_found']} "
                f"c12_margin={res['c12_margin']:+.2f} c13_margin={res['c13_margin']:+.2f}"
            )
    print(f"\nWrote {rows} layers to {out_path}")
    return rows


def main(argv):
    Q = int(argv[1]) if len(argv) > 1 else 17
    out = argv[2] if len(argv) > 2 else os.path.join(OUT_DIR, f"lineage-Q{Q}.csv")
    print(f"lineage experiment: Q={Q} out={out}")
    run(Q, out)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
