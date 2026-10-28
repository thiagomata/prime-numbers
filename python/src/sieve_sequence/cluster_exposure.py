"""Cluster exposure measurements over generated sieve-sequence prefixes.

The input is ``data/sieve-sequence/first_gaps_per_seq.csv`` from
``generate_gaps.py``. For each early stage, this module reconstructs the first
prefix of accepted values, extracts consecutive 2-gap candidates, and slides a
fixed-size cluster over those candidates.

For each cluster W of N candidate 2-gaps at stage head p, exposure is the
number of candidates destroyed by installing filter p:

    endpoint left == 0 mod p OR endpoint right == 0 mod p.

This is a first empirical version of the "cluster exposure curve" draft. It
measures direct endpoint-shot exposure and the post-filter effective 2-gap
count inside the same cluster value span.
"""

from __future__ import annotations

import csv
import math
import random
from bisect import bisect_left, bisect_right
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from statistics import fmean, pstdev
from typing import Iterable


REPO_ROOT = Path(__file__).resolve().parents[3]
DEFAULT_INPUT = REPO_ROOT / "data" / "sieve-sequence" / "first_gaps_per_seq.csv"
DEFAULT_CURVE_OUTPUT = REPO_ROOT / "data" / "candidates" / "cluster-exposure-curve.csv"
DEFAULT_SUMMARY_OUTPUT = REPO_ROOT / "data" / "candidates" / "cluster-exposure-summary.csv"
DEFAULT_SVG_OUTPUT = REPO_ROOT / "data" / "candidates" / "cluster-exposure-curve.svg"
DEFAULT_AGGRESSION_OUTPUT = REPO_ROOT / "data" / "candidates" / "cluster-exposure-aggression.csv"
DEFAULT_AGGRESSION_SVG_OUTPUT = REPO_ROOT / "data" / "candidates" / "cluster-exposure-aggression.svg"


@dataclass(frozen=True)
class StagePrefix:
    stage_index: int
    head: int
    survivors: tuple[int, ...]


@dataclass(frozen=True)
class ClusterExposure:
    stage_index: int
    head: int
    cluster_start: int
    cluster_size: int
    exposure: int
    exposure_rate: float
    random_mean: float
    adversariality: float
    direct_survival_rate: float = 0.0
    effective_survivors: int = 0
    effective_survival_rate: float = 0.0


def read_stage_prefixes(
    csv_path: str | Path = DEFAULT_INPUT,
    *,
    max_stages: int | None = 20,
    prefix_len: int | None = 10_000,
) -> list[StagePrefix]:
    """Read generated stage prefixes from the first-gaps CSV.

    ``prefix_len`` limits rows per stage so experiments over the large default
    CSV stay quick. ``None`` means use every available row for each included
    stage.
    """
    path = Path(csv_path)
    stages: list[StagePrefix] = []
    current_stage: int | None = None
    current_head: int | None = None
    current_survivors: list[int] = []

    def flush_current() -> None:
        nonlocal current_stage, current_head, current_survivors
        if current_stage is None or current_head is None:
            return
        stages.append(
            StagePrefix(
                stage_index=current_stage,
                head=current_head,
                survivors=tuple(current_survivors),
            )
        )
        current_stage = None
        current_head = None
        current_survivors = []

    with path.open(newline="") as handle:
        reader = csv.DictReader(handle)
        for row in reader:
            stage_index = int(row["stage_index"])
            head = int(row["head"])
            if current_stage is not None and stage_index != current_stage:
                flush_current()
                if max_stages is not None and len(stages) >= max_stages:
                    break
            if current_stage is None:
                current_stage = stage_index
                current_head = head
                current_survivors = [head]
            if prefix_len is None or len(current_survivors) - 1 < prefix_len:
                current_survivors.append(int(row["survivor"]))

    if max_stages is None or len(stages) < max_stages:
        flush_current()
    return stages


def two_gap_candidates(stage: StagePrefix) -> list[tuple[int, int]]:
    """Adjacent accepted-value pairs of gap 2 in the stage prefix."""
    values = stage.survivors
    return [
        (left, right)
        for left, right in zip(values, values[1:])
        if right - left == 2
    ]


def destroyed_by_head(candidate: tuple[int, int], head: int) -> bool:
    """Whether installing ``head`` destroys the candidate by endpoint deletion."""
    left, right = candidate
    return left % head == 0 or right % head == 0


def count_two_gaps_in_values(values: Iterable[int]) -> int:
    """Count adjacent surviving values whose difference is exactly 2."""
    values_tuple = tuple(values)
    return sum(
        1
        for left, right in zip(values_tuple, values_tuple[1:])
        if right - left == 2
    )


def effective_two_gaps_after_filter(
    stage: StagePrefix,
    *,
    span_left: int,
    span_right: int,
) -> int:
    """Count post-filter 2-gaps inside a cluster's original value span.

    This is the first merge-aware local metric: remove values divisible by the
    stage head, then count adjacent gap-2 pairs among the remaining accepted
    values whose endpoints lie inside the cluster span.
    """
    values = stage.survivors
    start = bisect_left(values, span_left)
    stop = bisect_right(values, span_right)
    post_values = [value for value in values[start:stop] if value % stage.head != 0]
    return count_two_gaps_in_values(post_values)


def stage_cluster_exposures(
    stage: StagePrefix,
    *,
    cluster_size: int = 25,
    stride: int = 1,
) -> list[ClusterExposure]:
    """Slide fixed-size clusters over a stage's 2-gap candidates."""
    if cluster_size <= 0:
        raise ValueError("cluster_size must be positive")
    if stride <= 0:
        raise ValueError("stride must be positive")

    candidates = two_gap_candidates(stage)
    if len(candidates) < cluster_size:
        return []
    destroyed = [destroyed_by_head(candidate, stage.head) for candidate in candidates]
    random_mean = 2.0 * cluster_size / stage.head
    rows: list[ClusterExposure] = []
    for start in range(0, len(candidates) - cluster_size + 1, stride):
        cluster = candidates[start:start + cluster_size]
        exposure = sum(1 for hit in destroyed[start:start + cluster_size] if hit)
        direct_survivors = cluster_size - exposure
        span_left = cluster[0][0]
        span_right = cluster[-1][1]
        effective_survivors = effective_two_gaps_after_filter(
            stage,
            span_left=span_left,
            span_right=span_right,
        )
        adversariality = exposure / random_mean if random_mean > 0 else float("inf")
        rows.append(
            ClusterExposure(
                stage_index=stage.stage_index,
                head=stage.head,
                cluster_start=start,
                cluster_size=cluster_size,
                exposure=exposure,
                exposure_rate=exposure / cluster_size,
                random_mean=random_mean,
                adversariality=adversariality,
                direct_survival_rate=direct_survivors / cluster_size,
                effective_survivors=effective_survivors,
                effective_survival_rate=effective_survivors / cluster_size,
            )
        )
    return rows


def build_exposures(
    stages: Iterable[StagePrefix],
    *,
    cluster_size: int = 25,
    stride: int = 1,
) -> list[ClusterExposure]:
    """Build cluster exposure rows for all stages."""
    rows: list[ClusterExposure] = []
    for stage in stages:
        rows.extend(stage_cluster_exposures(stage, cluster_size=cluster_size, stride=stride))
    return rows


def summary_stats(values: list[float]) -> dict[str, float]:
    """Return count/min/max/average/population-stddev for numeric values."""
    if not values:
        return {"count": 0, "min": math.nan, "max": math.nan, "avg": math.nan, "stddev": math.nan}
    return {
        "count": len(values),
        "min": min(values),
        "max": max(values),
        "avg": fmean(values),
        "stddev": pstdev(values) if len(values) > 1 else 0.0,
    }


def exposure_curve(rows: Iterable[ClusterExposure]) -> list[dict[str, float]]:
    """Histogram/CDF for integer exposure values."""
    rows_list = list(rows)
    counts = Counter(row.exposure for row in rows_list)
    total = sum(counts.values())
    cumulative = 0
    curve = []
    for exposure in sorted(counts):
        count = counts[exposure]
        cumulative += count
        curve.append(
            {
                "exposure": exposure,
                "count": count,
                "probability": count / total if total else math.nan,
                "cdf": cumulative / total if total else math.nan,
            }
        )
    return curve


def random_baseline_exposures(
    rows: Iterable[ClusterExposure],
    *,
    seed: int = 1,
    aggression: float = 1.0,
) -> list[int]:
    """Random companion exposures with the same cluster sizes and stage heads.

    Each candidate in a cluster is independently destroyed with probability
    ``aggression * 2/head`` capped at ``1``. This is deliberately a baseline
    companion, not a claim about the real arithmetic filter.
    """
    if aggression < 0:
        raise ValueError("aggression must be non-negative")
    rng = random.Random(seed)
    out: list[int] = []
    for row in rows:
        probability = min(1.0, aggression * 2.0 / row.head)
        exposure = sum(1 for _ in range(row.cluster_size) if rng.random() < probability)
        out.append(exposure)
    return out


def aggression_sweep(
    rows: Iterable[ClusterExposure],
    *,
    factors: Iterable[float],
    seed: int = 1,
) -> list[dict[str, float]]:
    """Simulate increasingly aggressive random companion filters.

    ``aggression`` multiplies the baseline hit probability ``2/head``. A
    cluster is extinct when the simulated exposure reaches its full cluster
    size.
    """
    row_list = list(rows)
    sweep = []
    for index, factor in enumerate(factors):
        exposures = random_baseline_exposures(row_list, seed=seed + index, aggression=factor)
        survival_rates = [
            (row.cluster_size - exposure) / row.cluster_size
            for row, exposure in zip(row_list, exposures)
        ]
        extinction_flags = [
            1.0 if exposure >= row.cluster_size else 0.0
            for row, exposure in zip(row_list, exposures)
        ]
        exposure_stats = summary_stats([float(exposure) for exposure in exposures])
        survival_stats = summary_stats(survival_rates)
        extinction_stats = summary_stats(extinction_flags)
        sweep.append(
            {
                "aggression": factor,
                "hit_probability_scale": factor,
                "clusters": len(row_list),
                "exposure_avg": exposure_stats["avg"],
                "exposure_stddev": exposure_stats["stddev"],
                "survival_rate_avg": survival_stats["avg"],
                "survival_rate_stddev": survival_stats["stddev"],
                "extinction_rate": extinction_stats["avg"],
            }
        )
    return sweep


def integer_curve(values: Iterable[int], *, prefix: str) -> list[dict[str, float]]:
    """Histogram/CDF for integer values with prefixed column names."""
    values_list = list(values)
    counts = Counter(values_list)
    total = sum(counts.values())
    cumulative = 0
    curve = []
    for value in sorted(counts):
        count = counts[value]
        cumulative += count
        curve.append(
            {
                "exposure": value,
                f"{prefix}_count": count,
                f"{prefix}_probability": count / total if total else math.nan,
                f"{prefix}_cdf": cumulative / total if total else math.nan,
            }
        )
    return curve


def merged_measured_baseline_curve(
    measured_rows: Iterable[ClusterExposure],
    baseline_values: Iterable[int],
) -> list[dict[str, float]]:
    """Merge measured-prefix and random-baseline exposure curves by exposure value."""
    measured = {int(row["exposure"]): row for row in exposure_curve(measured_rows)}
    baseline = {int(row["exposure"]): row for row in integer_curve(baseline_values, prefix="baseline")}
    exposures = sorted(set(measured) | set(baseline))
    merged = []
    last_measured_cdf = 0.0
    last_baseline_cdf = 0.0
    for exposure in exposures:
        measured_row = measured.get(exposure, {})
        base_row = baseline.get(exposure, {})
        if "cdf" in measured_row:
            last_measured_cdf = measured_row["cdf"]
        if "baseline_cdf" in base_row:
            last_baseline_cdf = base_row["baseline_cdf"]
        merged.append(
            {
                "exposure": exposure,
                "measured_count": measured_row.get("count", 0),
                "measured_probability": measured_row.get("probability", 0.0),
                "measured_cdf": last_measured_cdf,
                "baseline_count": base_row.get("baseline_count", 0),
                "baseline_probability": base_row.get("baseline_probability", 0.0),
                "baseline_cdf": last_baseline_cdf,
            }
        )
    return merged


def stage_summaries(rows: Iterable[ClusterExposure]) -> list[dict[str, float]]:
    """Per-stage summary rows over exposure and adversariality."""
    by_stage: dict[tuple[int, int], list[ClusterExposure]] = {}
    for row in rows:
        by_stage.setdefault((row.stage_index, row.head), []).append(row)

    summaries = []
    for (stage_index, head), group in sorted(by_stage.items()):
        exposure_stats = summary_stats([float(row.exposure) for row in group])
        adversariality_stats = summary_stats([row.adversariality for row in group])
        direct_survival_stats = summary_stats([row.direct_survival_rate for row in group])
        effective_survival_stats = summary_stats([row.effective_survival_rate for row in group])
        effective_survivor_stats = summary_stats([float(row.effective_survivors) for row in group])
        summaries.append(
            {
                "stage_index": stage_index,
                "head": head,
                "clusters": exposure_stats["count"],
                "exposure_min": exposure_stats["min"],
                "exposure_max": exposure_stats["max"],
                "exposure_avg": exposure_stats["avg"],
                "exposure_stddev": exposure_stats["stddev"],
                "adversariality_min": adversariality_stats["min"],
                "adversariality_max": adversariality_stats["max"],
                "adversariality_avg": adversariality_stats["avg"],
                "adversariality_stddev": adversariality_stats["stddev"],
                "direct_survival_rate_min": direct_survival_stats["min"],
                "direct_survival_rate_max": direct_survival_stats["max"],
                "direct_survival_rate_avg": direct_survival_stats["avg"],
                "direct_survival_rate_stddev": direct_survival_stats["stddev"],
                "effective_survivors_min": effective_survivor_stats["min"],
                "effective_survivors_max": effective_survivor_stats["max"],
                "effective_survivors_avg": effective_survivor_stats["avg"],
                "effective_survivors_stddev": effective_survivor_stats["stddev"],
                "effective_survival_rate_min": effective_survival_stats["min"],
                "effective_survival_rate_max": effective_survival_stats["max"],
                "effective_survival_rate_avg": effective_survival_stats["avg"],
                "effective_survival_rate_stddev": effective_survival_stats["stddev"],
            }
        )
    return summaries


def write_curve(path: str | Path, curve: list[dict[str, float]]) -> None:
    output = Path(path)
    output.parent.mkdir(parents=True, exist_ok=True)
    with output.open("w", newline="") as handle:
        if curve and "measured_count" in curve[0]:
            fieldnames = [
                "exposure",
                "measured_count",
                "measured_probability",
                "measured_cdf",
                "baseline_count",
                "baseline_probability",
                "baseline_cdf",
            ]
        else:
            fieldnames = ["exposure", "count", "probability", "cdf"]
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(curve)


def write_summary(path: str | Path, summaries: list[dict[str, float]]) -> None:
    output = Path(path)
    output.parent.mkdir(parents=True, exist_ok=True)
    fieldnames = [
        "stage_index",
        "head",
        "clusters",
        "exposure_min",
        "exposure_max",
        "exposure_avg",
        "exposure_stddev",
        "adversariality_min",
        "adversariality_max",
        "adversariality_avg",
        "adversariality_stddev",
        "direct_survival_rate_min",
        "direct_survival_rate_max",
        "direct_survival_rate_avg",
        "direct_survival_rate_stddev",
        "effective_survivors_min",
        "effective_survivors_max",
        "effective_survivors_avg",
        "effective_survivors_stddev",
        "effective_survival_rate_min",
        "effective_survival_rate_max",
        "effective_survival_rate_avg",
        "effective_survival_rate_stddev",
    ]
    with output.open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(summaries)


def write_aggression_sweep(path: str | Path, sweep: list[dict[str, float]]) -> None:
    output = Path(path)
    output.parent.mkdir(parents=True, exist_ok=True)
    fieldnames = [
        "aggression",
        "hit_probability_scale",
        "clusters",
        "exposure_avg",
        "exposure_stddev",
        "survival_rate_avg",
        "survival_rate_stddev",
        "extinction_rate",
    ]
    with output.open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(sweep)


def write_aggression_svg(path: str | Path, sweep: list[dict[str, float]]) -> None:
    """Write survival/extinction-vs-aggression line chart."""
    output = Path(path)
    output.parent.mkdir(parents=True, exist_ok=True)
    width = 920
    height = 520
    margin_left = 72
    margin_right = 155
    margin_top = 44
    margin_bottom = 68
    plot_w = width - margin_left - margin_right
    plot_h = height - margin_top - margin_bottom

    if not sweep:
        output.write_text(
            '<svg xmlns="http://www.w3.org/2000/svg" width="900" height="160">'
            '<text x="24" y="80">No aggression sweep data.</text></svg>\n',
            encoding="utf-8",
        )
        return

    max_factor = max(float(row["aggression"]) for row in sweep)
    if max_factor == 0:
        max_factor = 1.0

    def x_scale(factor: float) -> float:
        return margin_left + (factor / max_factor) * plot_w

    def y_scale(value: float) -> float:
        return margin_top + (1.0 - value) * plot_h

    def path_for(key: str) -> str:
        parts = []
        for i, row in enumerate(sweep):
            x = x_scale(float(row["aggression"]))
            y = y_scale(float(row[key]))
            parts.append(("M" if i == 0 else "L") + f" {x:.2f} {y:.2f}")
        return " ".join(parts)

    parts = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}">',
        '<rect width="100%" height="100%" fill="#ffffff"/>',
        f'<text x="{margin_left}" y="26" font-family="Arial, sans-serif" font-size="18" font-weight="700">Aggressive Filter Sweep</text>',
        f'<line x1="{margin_left}" y1="{margin_top + plot_h}" x2="{margin_left + plot_w}" y2="{margin_top + plot_h}" stroke="#222"/>',
        f'<line x1="{margin_left}" y1="{margin_top}" x2="{margin_left}" y2="{margin_top + plot_h}" stroke="#222"/>',
    ]
    for tick in range(0, 5):
        frac = tick / 4
        y = y_scale(frac)
        parts.append(f'<line x1="{margin_left}" y1="{y:.2f}" x2="{margin_left + plot_w}" y2="{y:.2f}" stroke="#e7e7e7"/>')
        parts.append(
            f'<text x="{margin_left - 10}" y="{y + 4:.2f}" text-anchor="end" '
            f'font-family="Arial, sans-serif" font-size="11">{frac:.2f}</text>'
        )
    for tick in range(0, 6):
        factor = max_factor * tick / 5
        x = x_scale(factor)
        parts.append(f'<line x1="{x:.2f}" y1="{margin_top + plot_h}" x2="{x:.2f}" y2="{margin_top + plot_h + 5}" stroke="#222"/>')
        parts.append(
            f'<text x="{x:.2f}" y="{margin_top + plot_h + 22}" text-anchor="middle" '
            f'font-family="Arial, sans-serif" font-size="11">{factor:.1f}</text>'
        )
    parts.extend([
        f'<path d="{path_for("survival_rate_avg")}" fill="none" stroke="#165a8f" stroke-width="3"/>',
        f'<path d="{path_for("extinction_rate")}" fill="none" stroke="#c85f2b" stroke-width="3" stroke-dasharray="8 5"/>',
        f'<line x1="{margin_left + plot_w + 22}" y1="{margin_top + 18}" x2="{margin_left + plot_w + 56}" y2="{margin_top + 18}" stroke="#165a8f" stroke-width="3"/>',
        f'<text x="{margin_left + plot_w + 64}" y="{margin_top + 22}" font-family="Arial, sans-serif" font-size="12">avg survival</text>',
        f'<line x1="{margin_left + plot_w + 22}" y1="{margin_top + 43}" x2="{margin_left + plot_w + 56}" y2="{margin_top + 43}" stroke="#c85f2b" stroke-width="3" stroke-dasharray="8 5"/>',
        f'<text x="{margin_left + plot_w + 64}" y="{margin_top + 47}" font-family="Arial, sans-serif" font-size="12">extinction rate</text>',
        f'<text x="{margin_left + plot_w / 2}" y="{height - 24}" text-anchor="middle" font-family="Arial, sans-serif" font-size="13">aggression multiplier on baseline hit probability</text>',
        f'<text x="18" y="{margin_top + plot_h / 2}" transform="rotate(-90 18 {margin_top + plot_h / 2})" text-anchor="middle" font-family="Arial, sans-serif" font-size="13">rate</text>',
        "</svg>",
    ])
    output.write_text("\n".join(parts) + "\n", encoding="utf-8")


def _cdf_points(values: Iterable[int], max_exposure: int) -> list[tuple[int, float]]:
    values_list = list(values)
    if not values_list:
        return [(x, 0.0) for x in range(max_exposure + 1)]
    counts = Counter(values_list)
    total = len(values_list)
    cumulative = 0
    points = []
    for exposure in range(max_exposure + 1):
        cumulative += counts.get(exposure, 0)
        points.append((exposure, cumulative / total))
    return points


def write_svg_curve(
    path: str | Path,
    curve: list[dict[str, float]],
    *,
    rows: Iterable[ClusterExposure] | None = None,
    baseline_values: Iterable[int] | None = None,
) -> None:
    """Write a standalone SVG distribution-line chart.

    When ``rows`` are supplied, the chart shows one CDF line per stage plus
    aggregate measured-prefix and random-baseline CDFs. Without ``rows`` it
    falls back to aggregate lines from ``curve``.
    """
    output = Path(path)
    output.parent.mkdir(parents=True, exist_ok=True)

    width = 980
    height = 560
    margin_left = 70
    margin_right = 170
    margin_top = 48
    margin_bottom = 70
    plot_w = width - margin_left - margin_right
    plot_h = height - margin_top - margin_bottom

    if not curve:
        output.write_text(
            '<svg xmlns="http://www.w3.org/2000/svg" width="900" height="160">'
            '<text x="24" y="80">No cluster exposure data.</text></svg>\n',
            encoding="utf-8",
        )
        return

    max_exposure = max(int(row["exposure"]) for row in curve)
    has_baseline = "measured_count" in curve[0]

    row_list = list(rows) if rows is not None else []
    baseline_list = list(baseline_values) if baseline_values is not None else []
    if row_list:
        max_exposure = max(max_exposure, max(row.exposure for row in row_list))
    if baseline_list:
        max_exposure = max(max_exposure, max(baseline_list))

    def x_scale(exposure: int) -> float:
        if max_exposure == 0:
            return margin_left
        return margin_left + (exposure / max_exposure) * plot_w

    def y_scale(cdf: float) -> float:
        return margin_top + (1.0 - cdf) * plot_h

    def path_from_points(points: list[tuple[int, float]]) -> str:
        if not points:
            return ""
        commands = [f"M {x_scale(points[0][0]):.2f} {y_scale(points[0][1]):.2f}"]
        for exposure, cdf in points[1:]:
            commands.append(f"L {x_scale(exposure):.2f} {y_scale(cdf):.2f}")
        return " ".join(commands)

    parts = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}">',
        '<rect width="100%" height="100%" fill="#ffffff"/>',
        f'<text x="{margin_left}" y="28" font-family="Arial, sans-serif" font-size="18" font-weight="700">Cluster Exposure Distribution Lines</text>',
        f'<line x1="{margin_left}" y1="{margin_top + plot_h}" x2="{margin_left + plot_w}" y2="{margin_top + plot_h}" stroke="#222" stroke-width="1"/>',
        f'<line x1="{margin_left}" y1="{margin_top}" x2="{margin_left}" y2="{margin_top + plot_h}" stroke="#222" stroke-width="1"/>',
    ]

    # Grid and axes.
    for tick in range(0, 5):
        frac = tick / 4
        y = y_scale(frac)
        parts.append(f'<line x1="{margin_left}" y1="{y:.2f}" x2="{margin_left + plot_w}" y2="{y:.2f}" stroke="#e7e7e7"/>')
        parts.append(
            f'<text x="{margin_left - 10}" y="{y + 4:.2f}" text-anchor="end" '
            f'font-family="Arial, sans-serif" font-size="11">{frac:.2f}</text>'
        )
    x_ticks = sorted(set([0, max_exposure] + [round(max_exposure * frac / 4) for frac in range(1, 4)]))
    for exposure in x_ticks:
        x = x_scale(exposure)
        parts.append(f'<line x1="{x:.2f}" y1="{margin_top + plot_h}" x2="{x:.2f}" y2="{margin_top + plot_h + 5}" stroke="#222"/>')
        parts.append(
            f'<text x="{x:.2f}" y="{margin_top + plot_h + 22}" text-anchor="middle" '
            f'font-family="Arial, sans-serif" font-size="11">{exposure}</text>'
        )

    # Per-stage lines.
    if row_list:
        by_stage: dict[tuple[int, int], list[int]] = {}
        for row in row_list:
            by_stage.setdefault((row.stage_index, row.head), []).append(row.exposure)
        palette = [
            "#6b8fb3", "#7aa77a", "#b3916b", "#9b7ab8", "#6fb0a8",
            "#b87878", "#8d9a5b", "#8090c8", "#aa82a0", "#6f9d88",
        ]
        for idx, ((stage_index, head), values) in enumerate(sorted(by_stage.items())):
            color = palette[idx % len(palette)]
            points = _cdf_points(values, max_exposure)
            parts.append(
                f'<path d="{path_from_points(points)}" fill="none" stroke="{color}" '
                f'stroke-width="1.2" opacity="0.34"><title>stage {stage_index}, head {head}</title></path>'
            )

        aggregate_points = _cdf_points([row.exposure for row in row_list], max_exposure)
        parts.append(
            f'<path d="{path_from_points(aggregate_points)}" fill="none" stroke="#165a8f" '
            f'stroke-width="3.2" opacity="0.96"/>'
        )
    else:
        if has_baseline:
            aggregate_points = [(int(row["exposure"]), float(row["measured_cdf"])) for row in curve]
        else:
            aggregate_points = [(int(row["exposure"]), float(row["cdf"])) for row in curve]
        parts.append(
            f'<path d="{path_from_points(aggregate_points)}" fill="none" stroke="#165a8f" '
            f'stroke-width="3.2" opacity="0.96"/>'
        )

    if baseline_list:
        baseline_points = _cdf_points(baseline_list, max_exposure)
    elif has_baseline:
        baseline_points = [(int(row["exposure"]), float(row["baseline_cdf"])) for row in curve]
    else:
        baseline_points = []
    if baseline_points:
        parts.append(
            f'<path d="{path_from_points(baseline_points)}" fill="none" stroke="#c85f2b" '
            f'stroke-width="3.2" stroke-dasharray="8 5" opacity="0.95"/>'
        )

    parts.extend([
        f'<line x1="{margin_left + plot_w + 24}" y1="{margin_top + 10}" x2="{margin_left + plot_w + 58}" y2="{margin_top + 10}" stroke="#165a8f" stroke-width="3.2"/>',
        f'<text x="{margin_left + plot_w + 66}" y="{margin_top + 14}" font-family="Arial, sans-serif" font-size="12">prefix aggregate</text>',
        f'<line x1="{margin_left + plot_w + 24}" y1="{margin_top + 34}" x2="{margin_left + plot_w + 58}" y2="{margin_top + 34}" stroke="#c85f2b" stroke-width="3.2" stroke-dasharray="8 5"/>',
        f'<text x="{margin_left + plot_w + 66}" y="{margin_top + 38}" font-family="Arial, sans-serif" font-size="12">random baseline</text>',
        f'<line x1="{margin_left + plot_w + 24}" y1="{margin_top + 58}" x2="{margin_left + plot_w + 58}" y2="{margin_top + 58}" stroke="#6b8fb3" stroke-width="1.2" opacity="0.45"/>',
        f'<text x="{margin_left + plot_w + 66}" y="{margin_top + 62}" font-family="Arial, sans-serif" font-size="12">per-stage prefix</text>',
        f'<text x="{margin_left + plot_w / 2}" y="{height - 24}" text-anchor="middle" font-family="Arial, sans-serif" font-size="13">exposure: destroyed 2-gap candidates per cluster</text>',
        f'<text x="18" y="{margin_top + plot_h / 2}" transform="rotate(-90 18 {margin_top + plot_h / 2})" text-anchor="middle" font-family="Arial, sans-serif" font-size="13">CDF</text>',
        "</svg>",
    ])
    output.write_text("\n".join(parts) + "\n", encoding="utf-8")
