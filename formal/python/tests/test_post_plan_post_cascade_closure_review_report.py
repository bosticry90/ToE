from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import post_plan_post_cascade_closure_review_report as tool


REPO_ROOT = find_repo_root(Path(__file__))
PROGRAM_PATH = REPO_ROOT / "formal" / "docs" / "release" / "POST_PLAN_OBJECTIVE_QUALITY_PHYSICS_COMPLETION_PROGRAM_20260418_v0.md"
ADVANCEMENT_PROGRAM_PATH = REPO_ROOT / "formal" / "docs" / "release" / "POST_PLAN_PHYSICS_ADVANCEMENT_PROGRAM_20260418_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "post_plan_recompute_monitoring_path_report": "formal/output/reports/post_plan_recompute_monitoring_path_20260418_v0.json",
                "post_plan_seam_reroute_reassessment_report": "formal/output/reports/post_plan_seam_reroute_reassessment_20260418_v0.json",
                "post_plan_master_action_reevaluation_report": "formal/output/reports/post_plan_master_action_reevaluation_20260418_v0.json",
                "post_plan_final_integration_review_report": "formal/output/reports/post_plan_final_integration_review_20260418_v0.json",
                "post_plan_target_map_report": "formal/output/reports/post_plan_physics_advancement_target_map_20260418_v0.json"
            },
            "closure_policy": {
                "required_monitoring_outcome": "POST_PLAN_RECOMPUTE_MONITORING_PATH_MATERIAL_CASCADE_CONFIRMED",
                "required_monitoring_post_ruling": "MATERIAL_CASCADE_CONFIRMED",
                "required_single_executable_row": "ROW-SEAM-COSMO-SR-001",
                "required_blocked_row": "ROW-SEAM-QM-STAT-001",
                "required_external_hold_row": "ROW-SEAM-QFT-GR-001",
                "required_closed_monitoring_row": "ROW-SEAM-GR-QM-001",
                "required_bounded_hold_rule": "MATERIAL_CASCADE_ALONE_DOES_NOT_RECLASSIFY_DOWNSTREAM_ROUTES_WITHOUT_ROW_OR_ROUTE_MOVEMENT"
            },
            "outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_POST_PLAN_POST_CASCADE_CLOSURE_REVIEW_OUTCOME",
                "no_loop_rule": "ONE_POST_PLAN_POST_CASCADE_CLOSURE_REVIEW_LAYER_ONLY",
                "allowed_outcomes": [
                    "POST_PLAN_POST_CASCADE_CLOSURE_REVIEW_REOPEN_SEAM_REROUTE",
                    "POST_PLAN_POST_CASCADE_CLOSURE_REVIEW_REOPEN_MASTER_ACTION",
                    "POST_PLAN_POST_CASCADE_CLOSURE_REVIEW_ADVANCEMENT_ELIGIBLE",
                    "POST_PLAN_POST_CASCADE_CLOSURE_REVIEW_BOUNDED_HOLD_RECORDED",
                    "POST_PLAN_POST_CASCADE_CLOSURE_REVIEW_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_POST_PLAN_POST_CASCADE_CLOSURE_REPAIR"
                ],
                "default_outcome": "POST_PLAN_POST_CASCADE_CLOSURE_REVIEW_EVIDENCE_INCOMPLETE"
            }
        },
    )


def _seed_target_map(path: Path) -> None:
    _write_json(
        path,
        {
            "routed_rows": [
                {"row_id": "ROW-SEAM-COSMO-SR-001", "route_class": "EXECUTABLE_NOW"},
                {"row_id": "ROW-SEAM-QM-STAT-001", "route_class": "BLOCKED_PENDING_AUTHORITY"},
                {"row_id": "ROW-SEAM-QFT-GR-001", "route_class": "EXTERNAL_HOLD"},
                {"row_id": "ROW-SEAM-GR-QM-001", "route_class": "CLOSED_MONITORING"},
            ]
        },
    )


def _seed_inputs(root: Path, *, integration_outcome: str, seam_outcome: str, master_action_outcome: str) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "post_plan_recompute_monitoring_path_20260418_v0.json",
        {
            "summary": {
                "terminal_outcome": "POST_PLAN_RECOMPUTE_MONITORING_PATH_MATERIAL_CASCADE_CONFIRMED",
                "post_recompute_ruling_id": "MATERIAL_CASCADE_CONFIRMED",
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "post_plan_seam_reroute_reassessment_20260418_v0.json",
        {"summary": {"terminal_outcome": seam_outcome}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "post_plan_master_action_reevaluation_20260418_v0.json",
        {"summary": {"terminal_outcome": master_action_outcome}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "post_plan_final_integration_review_20260418_v0.json",
        {"summary": {"terminal_outcome": integration_outcome}},
    )
    _seed_target_map(root / "formal" / "output" / "reports" / "post_plan_physics_advancement_target_map_20260418_v0.json")


def test_post_cascade_review_records_bounded_hold_when_routes_stay_unchanged(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "POST_PLAN_POST_CASCADE_CLOSURE_REVIEW_20260418_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(
        tmp_path,
        integration_outcome="POST_PLAN_FINAL_INTEGRATION_REVIEW_HELD_PENDING_FURTHER_BLOCKER_MOVEMENT",
        seam_outcome="POST_PLAN_SEAM_REROUTE_REASSESSMENT_NOT_ELIGIBLE_NO_UPSTREAM_MOVEMENT",
        master_action_outcome="POST_PLAN_MASTER_ACTION_REEVALUATION_NOT_ELIGIBLE_NO_UPSTREAM_MOVEMENT",
    )

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "POST_PLAN_POST_CASCADE_CLOSURE_REVIEW_BOUNDED_HOLD_RECORDED"
    assert report["summary"]["next_action"] == "EXECUTE_NEXT_THEOREM_GAP_TRANCHE_OR_EXPLICIT_EXHAUSTION_READ_WITH_POST_CASCADE_HOLD_RECORDED"


def test_post_cascade_review_surfaces_advancement_eligibility_when_integration_moves(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "POST_PLAN_POST_CASCADE_CLOSURE_REVIEW_20260418_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(
        tmp_path,
        integration_outcome="POST_PLAN_FINAL_INTEGRATION_REVIEW_ADVANCEMENT_ELIGIBLE",
        seam_outcome="POST_PLAN_SEAM_REROUTE_REASSESSMENT_NOT_ELIGIBLE_NO_UPSTREAM_MOVEMENT",
        master_action_outcome="POST_PLAN_MASTER_ACTION_REEVALUATION_NOT_ELIGIBLE_NO_UPSTREAM_MOVEMENT",
    )

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "POST_PLAN_POST_CASCADE_CLOSURE_REVIEW_ADVANCEMENT_ELIGIBLE"


def test_live_post_cascade_review_registered_in_mirrors() -> None:
    program_text = _read(PROGRAM_PATH)
    advancement_program_text = _read(ADVANCEMENT_PROGRAM_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)

    required_refs = [
        "formal/docs/release/POST_PLAN_POST_CASCADE_CLOSURE_REVIEW_20260418_v0.json",
        "formal/output/reports/post_plan_post_cascade_closure_review_20260418_v0.json",
        "formal/python/tools/post_plan_post_cascade_closure_review_report.py",
        "formal/python/tests/test_post_plan_post_cascade_closure_review_report.py",
    ]

    for ref in required_refs:
        assert ref in program_text or ref in advancement_program_text
        assert ref in state_text or ref in roadmap_text or ref in inventory_text

    report = _read_json(REPO_ROOT / "formal" / "output" / "reports" / "post_plan_post_cascade_closure_review_20260418_v0.json")
    assert report["summary"]["terminal_outcome"] == "POST_PLAN_POST_CASCADE_CLOSURE_REVIEW_BOUNDED_HOLD_RECORDED"
    assert report["summary"]["next_action"] == "EXECUTE_NEXT_THEOREM_GAP_TRANCHE_OR_EXPLICIT_EXHAUSTION_READ_WITH_POST_CASCADE_HOLD_RECORDED"