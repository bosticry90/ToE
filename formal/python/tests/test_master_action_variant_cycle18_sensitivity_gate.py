from __future__ import annotations

import json
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
NOTE_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_TOE_MASTER_ACTION_VARIANT_DISCRIMINATOR_NOTE_v0.md"
RELEASE_NOTE_PATH = REPO_ROOT / "formal" / "docs" / "release" / "MASTER_ACTION_VARIANT_CYCLE18_RELEASE_NOTE_v0.md"
EXECUTION_REPORT_PATH = REPO_ROOT / "formal" / "output" / "master_action_variant_c_pressure_cycle18_execution_report_v0.json"
DRIFT_REPORT_PATH = REPO_ROOT / "formal" / "output" / "master_action_variant_c_pressure_cycle18_drift_report_v0.json"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_cycle18_sensitivity_policy_is_pinned() -> None:
    note_text = _read(NOTE_PATH)
    release_text = _read(RELEASE_NOTE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)

    assert "CYCLE18_PRIORITY_SENSITIVITY_REBALANCE_v0" in note_text
    assert "CYCLE18_PRIORITY_SENSITIVITY_REBALANCE_v0" in release_text

    for ref in (
        "formal/docs/release/MASTER_ACTION_VARIANT_CYCLE18_RELEASE_NOTE_v0.md",
        "formal/output/master_action_variant_c_pressure_cycle18_execution_report_v0.json",
        "formal/output/master_action_variant_c_pressure_cycle18_drift_report_v0.json",
        "formal/python/tests/test_master_action_variant_cycle18_sensitivity_gate.py",
    ):
        assert ref in roadmap_text
        assert ref in state_text


def test_cycle18_reports_require_measurable_drift() -> None:
    execution = _read_json(EXECUTION_REPORT_PATH)
    drift = _read_json(DRIFT_REPORT_PATH)

    assert execution.get("strategy_change_token") == "CYCLE18_PRIORITY_SENSITIVITY_REBALANCE_v0"
    assert drift.get("strategy_change_token") == "CYCLE18_PRIORITY_SENSITIVITY_REBALANCE_v0"

    counts = drift.get("drift", {})
    admissibility_delta = drift.get("priority_lane_admissibility_delta", {})

    count_drift = any(abs(float(counts.get(k, 0))) > 0 for k in ("retain_delta", "prune_delta", "inconclusive_delta"))
    sensitivity_drift = any(abs(float(admissibility_delta.get(k, 0))) > 0 for k in ("qft_score_delta", "sr_score_delta", "threshold_delta"))

    assert count_drift or sensitivity_drift, "Cycle18 requires measurable drift (count or admissibility delta)."
    assert drift.get("success_criteria", {}).get("measurable_drift_observed") is True
    assert drift.get("guard_consistency", {}).get("cycle18_all_guards_true") is True
