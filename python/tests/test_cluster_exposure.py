from sieve_sequence import cluster_exposure as lib


def test_two_gap_candidates_include_head():
    stage = lib.StagePrefix(stage_index=1, head=3, survivors=(3, 5, 7, 9))
    assert lib.two_gap_candidates(stage) == [(3, 5), (5, 7), (7, 9)]


def test_stage_cluster_exposures_hand_check_stage_5():
    # Stage headed at 5 has filters {2,3}; accepted prefix:
    # 5, 7, 11, 13, 17, 19, 23, 25, 29.
    # 2-gap candidates: (5,7),(11,13),(17,19),(23,25).
    # Installing 5 destroys (5,7) and (23,25).
    stage = lib.StagePrefix(
        stage_index=2,
        head=5,
        survivors=(5, 7, 11, 13, 17, 19, 23, 25, 29),
    )
    rows = lib.stage_cluster_exposures(stage, cluster_size=2, stride=1)
    assert [row.exposure for row in rows] == [1, 0, 1]
    assert [row.exposure_rate for row in rows] == [0.5, 0.0, 0.5]
    assert [row.direct_survival_rate for row in rows] == [0.5, 1.0, 0.5]
    assert [row.effective_survivors for row in rows] == [1, 2, 1]
    assert [row.effective_survival_rate for row in rows] == [0.5, 1.0, 0.5]
    assert rows[0].random_mean == 0.8
    assert rows[0].adversariality == 1.25


def test_effective_survival_can_see_merge_created_two_gap():
    # Removing 9 from 7,9,11 creates the post-filter 2-gap (7,11)? No: its gap
    # is 4, so the original adjacent 2-gaps both die. Removing 11 from
    # 7,9,11,13 leaves (7,9) and (13 outside the local pair span if omitted).
    # This case checks that the metric counts post-filter adjacency, not merely
    # original candidates.
    stage = lib.StagePrefix(
        stage_index=1,
        head=3,
        survivors=(7, 9, 11, 13, 15),
    )
    rows = lib.stage_cluster_exposures(stage, cluster_size=2, stride=1)
    assert rows[0].exposure == 2
    assert rows[0].direct_survival_rate == 0.0
    assert rows[0].effective_survivors == 0


def test_exposure_curve_and_summary_stats():
    rows = [
        lib.ClusterExposure(1, 3, 0, 2, 0, 0.0, 4 / 3, 0.0),
        lib.ClusterExposure(1, 3, 1, 2, 1, 0.5, 4 / 3, 0.75),
        lib.ClusterExposure(1, 3, 2, 2, 1, 0.5, 4 / 3, 0.75),
    ]
    assert lib.exposure_curve(rows) == [
        {"exposure": 0, "count": 1, "probability": 1 / 3, "cdf": 1 / 3},
        {"exposure": 1, "count": 2, "probability": 2 / 3, "cdf": 1.0},
    ]
    stats = lib.summary_stats([0.0, 1.0, 1.0])
    assert stats["count"] == 3
    assert stats["min"] == 0.0
    assert stats["max"] == 1.0
    assert stats["avg"] == 2 / 3


def test_random_baseline_and_merged_curve_are_reproducible():
    rows = [
        lib.ClusterExposure(1, 3, 0, 2, 0, 0.0, 4 / 3, 0.0),
        lib.ClusterExposure(2, 5, 0, 2, 1, 0.5, 4 / 5, 1.25),
    ]
    first = lib.random_baseline_exposures(rows, seed=7)
    second = lib.random_baseline_exposures(rows, seed=7)
    assert first == second
    curve = lib.merged_measured_baseline_curve(rows, first)
    assert {"measured_count", "baseline_count"}.issubset(curve[0])


def test_aggression_sweep_reaches_extinction_limit():
    rows = [
        lib.ClusterExposure(1, 3, 0, 4, 0, 0.0, 8 / 3, 0.0),
        lib.ClusterExposure(2, 5, 0, 4, 0, 0.0, 8 / 5, 0.0),
    ]
    sweep = lib.aggression_sweep(rows, factors=[0.0, 100.0], seed=1)
    assert sweep[0]["survival_rate_avg"] == 1.0
    assert sweep[0]["extinction_rate"] == 0.0
    assert sweep[1]["survival_rate_avg"] == 0.0
    assert sweep[1]["extinction_rate"] == 1.0


def test_merged_curve_cdf_carries_forward():
    rows = [
        lib.ClusterExposure(1, 3, 0, 2, 0, 0.0, 4 / 3, 0.0),
        lib.ClusterExposure(1, 3, 1, 2, 2, 1.0, 4 / 3, 1.5),
    ]
    curve = lib.merged_measured_baseline_curve(rows, [0, 1])
    by_exposure = {row["exposure"]: row for row in curve}
    assert by_exposure[1]["measured_count"] == 0
    assert by_exposure[1]["measured_cdf"] == 0.5


def test_write_svg_curve(tmp_path):
    out = tmp_path / "curve.svg"
    lib.write_svg_curve(
        out,
        [
            {"exposure": 0, "count": 1, "probability": 0.25, "cdf": 0.25},
            {"exposure": 1, "count": 3, "probability": 0.75, "cdf": 1.0},
        ],
    )
    text = out.read_text()
    assert text.startswith("<svg")
    assert "Cluster Exposure Distribution Lines" in text
    assert "prefix aggregate" in text
    assert "<path" in text


def test_write_aggression_svg(tmp_path):
    out = tmp_path / "aggression.svg"
    lib.write_aggression_svg(
        out,
        [
            {
                "aggression": 1.0,
                "survival_rate_avg": 0.8,
                "extinction_rate": 0.1,
            },
            {
                "aggression": 2.0,
                "survival_rate_avg": 0.5,
                "extinction_rate": 0.3,
            },
        ],
    )
    text = out.read_text()
    assert "Aggressive Filter Sweep" in text
    assert "avg survival" in text
