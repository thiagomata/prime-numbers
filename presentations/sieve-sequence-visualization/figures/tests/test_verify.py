import pytest

import gap_heatmap
import verify
from conftest import walk_stage


def _stages():
    """Real head=3, head=5, head=7 stages -- long enough for
    check_copy_or_merge_theorem_is_exact and check_first_composite_is_head_squared
    to observe at least one real first-composite survivor (head=3's is 9,
    within a 20-gap window)."""
    return [
        walk_stage(3, [2], 20),
        walk_stage(5, [2, 3], 12),
        walk_stage(7, [2, 3, 5], 8),
    ]


def test_check_known_small_stages_passes_on_real_data(capsys):
    assert verify.check_known_small_stages(_stages()) is True
    assert "PASS" in capsys.readouterr().out


def test_check_known_small_stages_fails_when_stage_head_3_is_wrong():
    stages = _stages()
    stages[0]["gaps"][0] = 4  # break the "every gap is 2" claim
    assert verify.check_known_small_stages(stages) is False


def test_check_known_small_stages_fails_when_a_stage_is_missing():
    stages = [stage for stage in _stages() if stage["head"] != 5]
    assert verify.check_known_small_stages(stages) is False


def test_check_first_composite_is_head_squared_passes_on_real_data():
    assert verify.check_first_composite_is_head_squared(_stages()) is True


def test_check_first_composite_is_head_squared_fails_on_a_planted_survivor():
    stages = _stages()
    # Stage head=3's first composite survivor is 9 (= 3^2); corrupt it.
    idx = stages[0]["survivors"].index(9)
    stages[0]["survivors"][idx] = 10
    assert verify.check_first_composite_is_head_squared(stages) is False


def test_check_copy_or_merge_theorem_is_exact_passes_on_a_real_transition():
    assert verify.check_copy_or_merge_theorem_is_exact(_stages()) is True


def test_check_copy_or_merge_theorem_is_exact_fails_on_a_corrupted_gap():
    stages = _stages()
    stages[1]["gaps"][0] += 1  # break the copy-or-merge invariant
    assert verify.check_copy_or_merge_theorem_is_exact(stages) is False


def test_check_schroeder_bound_never_violated_skips_stages_below_head_11():
    # Every stage in _stages() has head < 11, so the bound is None everywhere
    # and there's nothing to check -- this must still report PASS (0 checked
    # stages, no violation found), not fail.
    assert verify.check_schroeder_bound_never_violated(_stages()) is True


def test_report_estimated_bound_fit_does_not_raise(capsys):
    # Informational only -- must never fail the run, just print an INFO line.
    verify.report_estimated_bound_fit(_stages())
    assert "INFO" in capsys.readouterr().out


# --- KNOWN_SMALL_STAGE_GAPS must actually drive the checks -----------------
# Regression: check_known_small_stages used to hardcode the head=3/head=5
# expected values as literals, ignoring KNOWN_SMALL_STAGE_GAPS[3]/[5] even
# though they looked like the source of truth -- editing the dict silently
# changed nothing.

def test_check_known_small_stages_head_3_is_driven_by_the_dict():
    stages = _stages()
    original = verify.KNOWN_SMALL_STAGE_GAPS[3]["all_equal"]
    verify.KNOWN_SMALL_STAGE_GAPS[3]["all_equal"] = original + 100
    try:
        assert verify.check_known_small_stages(stages) is False
    finally:
        verify.KNOWN_SMALL_STAGE_GAPS[3]["all_equal"] = original


def test_check_known_small_stages_head_5_is_driven_by_the_dict():
    stages = _stages()
    original = verify.KNOWN_SMALL_STAGE_GAPS[5]["alternates"]
    verify.KNOWN_SMALL_STAGE_GAPS[5]["alternates"] = [999, 999]
    try:
        assert verify.check_known_small_stages(stages) is False
    finally:
        verify.KNOWN_SMALL_STAGE_GAPS[5]["alternates"] = original


# --- main(): missing/empty-CSV guard ----------------------------------

def test_main_raises_a_clear_error_when_the_csv_is_missing(tmp_path, monkeypatch):
    monkeypatch.setattr(verify, "CSV_PATH", str(tmp_path / "missing.csv"))
    monkeypatch.setattr(gap_heatmap, "CSV_PATH", str(tmp_path / "missing.csv"))
    with pytest.raises(SystemExit, match="not found"):
        verify.main()


def test_main_raises_a_clear_error_when_the_csv_has_no_stage_rows(tmp_path, monkeypatch):
    # Regression: verify.main() called load_stages() with no existence/content
    # guard at all, unlike gap_heatmap.py's own main() -- running verify.py
    # before generate_gaps.py had produced output raised a raw, unguided
    # FileNotFoundError (or IndexError downstream) instead of a clear message.
    csv_path = tmp_path / "empty.csv"
    csv_path.write_text("stage_index,head,gap,survivor\n")
    monkeypatch.setattr(verify, "CSV_PATH", str(csv_path))
    monkeypatch.setattr(gap_heatmap, "CSV_PATH", str(csv_path))
    with pytest.raises(SystemExit, match="no stage rows"):
        verify.main()


def test_main_raises_a_clear_error_when_a_stage_row_is_corrupted(tmp_path, monkeypatch):
    csv_path = tmp_path / "corrupt.csv"
    csv_path.write_text(
        "stage_index,head,gap_index,gap,survivor\n"
        "1,3,0,2,5\n"
        "1,3,1,99,9\n"  # gap 99 does not connect survivor 5 to survivor 9
    )
    monkeypatch.setattr(verify, "CSV_PATH", str(csv_path))
    monkeypatch.setattr(gap_heatmap, "CSV_PATH", str(csv_path))
    with pytest.raises(SystemExit, match="failed validation"):
        verify.main()
