from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
PROGRAM_PATH = REPO_ROOT / "formal" / "docs" / "release" / "POST_PLAN_PHYSICS_ADVANCEMENT_PROGRAM_20260418_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_post_plan_phase3_to_phase6_reports_and_mirrors() -> None:
    program_text = _read(PROGRAM_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)

    required_paths = [
        "formal/docs/release/POST_PLAN_QM_FIRST_THEOREM_GAP_TRANCHE_20260418_v0.json",
        "formal/output/reports/post_plan_qm_first_theorem_gap_tranche_20260418_v0.json",
        "formal/python/tools/post_plan_qm_first_theorem_gap_tranche_report.py",
        "formal/docs/release/POST_PLAN_SEAM_REROUTE_REASSESSMENT_20260418_v0.json",
        "formal/output/reports/post_plan_seam_reroute_reassessment_20260418_v0.json",
        "formal/python/tools/post_plan_seam_reroute_reassessment_report.py",
        "formal/docs/release/POST_PLAN_MASTER_ACTION_REEVALUATION_20260418_v0.json",
        "formal/output/reports/post_plan_master_action_reevaluation_20260418_v0.json",
        "formal/python/tools/post_plan_master_action_reevaluation_report.py",
        "formal/docs/release/POST_PLAN_FINAL_INTEGRATION_REVIEW_20260418_v0.json",
        "formal/output/reports/post_plan_final_integration_review_20260418_v0.json",
        "formal/python/tools/post_plan_final_integration_review_report.py",
        "formal/python/tests/test_post_plan_phase3_to_phase6_reports.py",
    ]

    for ref in required_paths:
        assert ref in program_text or ref.endswith("test_post_plan_phase3_to_phase6_reports.py")
        assert ref in roadmap_text or ref in state_text or ref in inventory_text

    qm_report = _read_json(REPO_ROOT / "formal" / "output" / "reports" / "post_plan_qm_first_theorem_gap_tranche_20260418_v0.json")
    reroute_report = _read_json(REPO_ROOT / "formal" / "output" / "reports" / "post_plan_seam_reroute_reassessment_20260418_v0.json")
    master_action_report = _read_json(REPO_ROOT / "formal" / "output" / "reports" / "post_plan_master_action_reevaluation_20260418_v0.json")
    integration_report = _read_json(REPO_ROOT / "formal" / "output" / "reports" / "post_plan_final_integration_review_20260418_v0.json")

    assert qm_report["summary"]["terminal_outcome"] == "POST_PLAN_QM_FIRST_THEOREM_GAP_TRANCHE_EXECUTED_NONPROMOTED"
    assert qm_report["summary"]["target_row_id"] == "ROW-PILLAR-QM-001"
    assert qm_report["summary"]["row_truth_change_detected"] is False

    assert reroute_report["summary"]["terminal_outcome"] == "POST_PLAN_SEAM_REROUTE_REASSESSMENT_NOT_ELIGIBLE_NO_UPSTREAM_MOVEMENT"
    assert reroute_report["summary"]["upstream_movement_detected"] is False

    assert master_action_report["summary"]["terminal_outcome"] == "POST_PLAN_MASTER_ACTION_REEVALUATION_NOT_ELIGIBLE_NO_UPSTREAM_MOVEMENT"
    assert master_action_report["summary"]["upstream_movement_detected"] is False

    assert integration_report["summary"]["terminal_outcome"] == "POST_PLAN_FINAL_INTEGRATION_REVIEW_HELD_PENDING_FURTHER_BLOCKER_MOVEMENT"
    assert integration_report["summary"]["advancement_movement_detected"] is False