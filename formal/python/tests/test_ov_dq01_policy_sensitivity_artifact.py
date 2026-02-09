from __future__ import annotations

import json

from formal.python.toe.observables.ovdq01_policy_sensitivity_record import (
    default_artifact_path,
    ovdq01_policy_sensitivity_record,
)


def test_ov_dq01_policy_sensitivity_artifact_matches_computed() -> None:
    p = default_artifact_path()
    assert p.exists(), f"Missing canonical artifact: {p.as_posix()}"

    on_disk = json.loads(p.read_text(encoding="utf-8"))
    computed = ovdq01_policy_sensitivity_record().to_jsonable()

    assert on_disk["schema"] == "OV-DQ-01_policy_sensitivity/v2"
    assert isinstance(on_disk.get("fingerprint"), str)
    assert on_disk == computed


def test_ov_dq01_policy_sensitivity_grid_contains_locked_point() -> None:
    rec = ovdq01_policy_sensitivity_record().to_jsonable()

    for key in ("ov01g", "ov04x", "ov03x"):
        obs = rec[key]
        grid = list(obs["grid"])
        assert len(grid) >= 1

        # Ensure canonical threshold is represented.
        locked_t = float(obs["q_threshold_locked"])
        row = next(r for r in grid if abs(float(r["q_threshold"]) - locked_t) <= 1e-12)

        # At the canonical threshold, the what-if decision must match the lock.
        assert bool(row["would_prefer_curved"]) == bool(obs["prefer_curved_locked"])
        assert bool(row["robustness_failed"]) == (not bool(obs["prefer_curved_locked"]))

        # If the lock is non-prefer due to q_ratio, this must be exposed.
        if float(obs["q_ratio_locked"]) > float(obs["q_threshold_locked"]):
            assert "q_ratio_above_threshold" in list(row["blocking_reasons"])


def test_ov_dq01_policy_sensitivity_ov02x_contains_locked_point_and_is_invariant_at_090() -> None:
    rec = ovdq01_policy_sensitivity_record().to_jsonable()
    obs = rec["ov02x"]
    grid = list(obs["grid"])
    assert len(grid) >= 1

    locked_t = float(obs["q_threshold_locked"])
    row = next(r for r in grid if abs(float(r["q_threshold"]) - locked_t) <= 1e-12)

    assert bool(row["baseline_prefer_curved"]) == bool(obs["baseline_prefer_curved_locked"])
    assert bool(row["robustness_failed"]) == bool(obs["robustness_failed_locked"])

    # At the canonical threshold, OV-02x is expected to pass invariance.
    assert abs(locked_t - 0.90) <= 1e-12
    assert bool(row["baseline_prefer_curved"]) is True
    assert bool(row["all_scenarios_match_baseline"]) is True
    assert bool(row["robustness_failed"]) is False
