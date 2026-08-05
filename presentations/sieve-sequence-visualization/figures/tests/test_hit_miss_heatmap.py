import os
from fractions import Fraction
from functools import lru_cache

import pytest

import hit_miss_heatmap as hmh
from svg_kit import Canvas

SAMPLE_CSV = hmh.SAMPLE_CSV_PATH


@lru_cache(maxsize=None)
def _load_stages_cached(num_stages):
    """load_stages scans the whole sample CSV regardless of num_stages, so
    cache by num_stages instead of re-parsing it once per test."""
    return hmh.load_stages(SAMPLE_CSV, num_stages)


def test_sample_csv_is_present():
    # This fixture is committed specifically so this module's tests (and the
    # figure itself) don't depend on the large, gitignored full dataset.
    assert os.path.exists(SAMPLE_CSV), f"missing committed sample CSV: {SAMPLE_CSV}"


def test_load_stages_synthesizes_stage_zero_with_no_filter():
    stages = _load_stages_cached(1)
    assert len(stages) == 1
    assert stages[0]["head"] == 2
    assert stages[0]["survivors"][:5] == [2, 3, 4, 5, 6]


def test_load_stages_reads_the_requested_number_of_stages():
    stages = _load_stages_cached(4)
    assert len(stages) == 4
    assert [stage["head"] for stage in stages] == [2, 3, 5, 7]


def test_load_stages_stage_one_survivors_match_odd_numbers_from_head():
    stages = _load_stages_cached(2)
    stage_one = stages[1]
    assert stage_one["head"] == 3
    assert stage_one["survivors"][:5] == [5, 7, 9, 11, 13]


def test_stage_captions_stage_zero_has_flagged_fraction_one():
    stages = _load_stages_cached(2)
    captions = hmh.stage_captions(stages)
    flagged_str, period_str = captions[0]
    assert flagged_str == f"flagged fraction: {Fraction(1, 1)}"
    assert period_str == "gaps repeat: [1]"


def test_stage_captions_stage_one_flagged_fraction_is_one_half():
    stages = _load_stages_cached(2)
    captions = hmh.stage_captions(stages)
    flagged_str, _period_str = captions[1]
    assert flagged_str == f"flagged fraction: {Fraction(1, 2)}"


def test_stage_captions_prints_short_periods_in_full():
    stages = _load_stages_cached(4)
    captions = hmh.stage_captions(stages)
    # stage 2 (head=5): period [2, 4]
    assert captions[2][1] == "gaps repeat: [2,4]"


def test_build_figure_renders_a_well_formed_svg_with_one_panel_per_stage():
    stages = _load_stages_cached(3)
    canvas = hmh.build_figure(stages)
    assert isinstance(canvas, Canvas)
    svg = canvas.render()
    assert svg.startswith("<svg "), svg[:80]
    assert svg.rstrip().endswith("</svg>")
    # One "Stage N (head=..." title per panel.
    assert sum(f"Stage {i} (head=" in svg for i in range(len(stages))) == len(stages)


def test_main_raises_a_clear_error_when_a_stage_is_corrupted(tmp_path, monkeypatch):
    # Regression: main() loaded stages and built the figure straight from
    # them with no structural sanity check at all -- a truncated/misaligned
    # sample CSV would silently draw a wrong picture instead of failing loudly.
    monkeypatch.setattr(hmh, "load_stages", lambda path, n: [{"head": 1, "survivors": [1, 2]}])
    monkeypatch.setattr(hmh, "OUT_DIR", str(tmp_path / "out"))
    with pytest.raises(SystemExit, match="failed validation"):
        hmh.main()
