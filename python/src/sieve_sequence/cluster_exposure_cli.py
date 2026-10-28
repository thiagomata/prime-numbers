"""CLI for cluster exposure distribution measurements.

Example:

  python -m sieve_sequence.cluster_exposure_cli --max-stages 20 --prefix-len 10000 --cluster-size 25
"""

from __future__ import annotations

import argparse
import sys

from . import cluster_exposure as lib


def parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(description="Measure cluster exposure distributions from first sieve-sequence prefixes.")
    p.add_argument("--input", default=str(lib.DEFAULT_INPUT), help="first_gaps_per_seq.csv path")
    p.add_argument("--curve-output", default=str(lib.DEFAULT_CURVE_OUTPUT), help="histogram/CDF CSV output path")
    p.add_argument("--summary-output", default=str(lib.DEFAULT_SUMMARY_OUTPUT), help="per-stage summary CSV output path")
    p.add_argument("--svg-output", default=str(lib.DEFAULT_SVG_OUTPUT), help="SVG bar chart output path")
    p.add_argument("--aggression-output", default=str(lib.DEFAULT_AGGRESSION_OUTPUT), help="aggressive filter sweep CSV output path")
    p.add_argument("--aggression-svg-output", default=str(lib.DEFAULT_AGGRESSION_SVG_OUTPUT), help="aggressive filter sweep SVG output path")
    p.add_argument("--aggression-max", type=float, default=20.0, help="maximum aggression multiplier to simulate")
    p.add_argument("--aggression-steps", type=int, default=40, help="number of aggression multipliers to simulate")
    p.add_argument("--max-stages", type=int, default=20, help="number of first stages to read")
    p.add_argument("--prefix-len", type=int, default=10_000, help="gaps per stage to read")
    p.add_argument("--cluster-size", type=int, default=25, help="number of consecutive 2-gap candidates per cluster")
    p.add_argument("--stride", type=int, default=1, help="sliding-window stride over 2-gap candidates")
    p.add_argument("--seed", type=int, default=1, help="random baseline seed")
    return p


def main(argv=None) -> int:
    args = parser().parse_args(sys.argv[1:] if argv is None else argv)
    stages = lib.read_stage_prefixes(
        args.input,
        max_stages=args.max_stages,
        prefix_len=args.prefix_len,
    )
    rows = lib.build_exposures(stages, cluster_size=args.cluster_size, stride=args.stride)
    baseline = lib.random_baseline_exposures(rows, seed=args.seed)
    curve = lib.merged_measured_baseline_curve(rows, baseline)
    summaries = lib.stage_summaries(rows)
    lib.write_curve(args.curve_output, curve)
    lib.write_summary(args.summary_output, summaries)
    lib.write_svg_curve(args.svg_output, curve, rows=rows, baseline_values=baseline)
    factors = [
        1.0 + (args.aggression_max - 1.0) * i / max(1, args.aggression_steps - 1)
        for i in range(args.aggression_steps)
    ]
    sweep = lib.aggression_sweep(rows, factors=factors, seed=args.seed)
    lib.write_aggression_sweep(args.aggression_output, sweep)
    lib.write_aggression_svg(args.aggression_svg_output, sweep)

    exposure_stats = lib.summary_stats([float(row.exposure) for row in rows])
    adversariality_stats = lib.summary_stats([row.adversariality for row in rows])
    direct_survival_stats = lib.summary_stats([row.direct_survival_rate for row in rows])
    effective_survival_stats = lib.summary_stats([row.effective_survival_rate for row in rows])
    baseline_stats = lib.summary_stats([float(value) for value in baseline])
    print(
        "cluster exposure: "
        f"stages={len(stages)} clusters={int(exposure_stats['count'])} "
        f"cluster_size={args.cluster_size} stride={args.stride}"
    )
    print(
        "measured prefix exposure: "
        f"min={exposure_stats['min']:.6g} max={exposure_stats['max']:.6g} "
        f"avg={exposure_stats['avg']:.6g} stddev={exposure_stats['stddev']:.6g}"
    )
    print(
        "adversariality: "
        f"min={adversariality_stats['min']:.6g} max={adversariality_stats['max']:.6g} "
        f"avg={adversariality_stats['avg']:.6g} stddev={adversariality_stats['stddev']:.6g}"
    )
    print(
        "direct survival rate: "
        f"min={direct_survival_stats['min']:.6g} max={direct_survival_stats['max']:.6g} "
        f"avg={direct_survival_stats['avg']:.6g} stddev={direct_survival_stats['stddev']:.6g}"
    )
    print(
        "effective post-filter survival rate: "
        f"min={effective_survival_stats['min']:.6g} max={effective_survival_stats['max']:.6g} "
        f"avg={effective_survival_stats['avg']:.6g} stddev={effective_survival_stats['stddev']:.6g}"
    )
    print(
        "random baseline exposure: "
        f"min={baseline_stats['min']:.6g} max={baseline_stats['max']:.6g} "
        f"avg={baseline_stats['avg']:.6g} stddev={baseline_stats['stddev']:.6g} seed={args.seed}"
    )
    print(f"curve: {args.curve_output}")
    print(f"summary: {args.summary_output}")
    print(f"svg: {args.svg_output}")
    if sweep:
        first_extinct = next((row for row in sweep if row["extinction_rate"] >= 0.5), None)
        if first_extinct:
            print(
                "aggression midpoint: "
                f"extinction_rate>=0.5 at aggression={first_extinct['aggression']:.6g}"
            )
        print(f"aggression: {args.aggression_output}")
        print(f"aggression svg: {args.aggression_svg_output}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
