from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import post_plan_theorem_gap_fresh_movement_qualification_report as tool


REPO_ROOT = find_repo_root(Path(__file__))
PROGRAM_PATH = REPO_ROOT / "formal" / "docs" / "release" / "POST_PLAN_THEOREM_GAP_REDUCTION_REACTIVATION_PROGRAM_20260419_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"


def _read(path: Path) -> str:
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
                "completion_queue_report": "formal/output/reports/post_plan_objective_quality_physics_completion_queue_20260418_v0.json",
                "post_plan_target_map_report": "formal/output/reports/post_plan_physics_advancement_target_map_20260418_v0.json",
                "blocker_burn_dashboard_report": "formal/output/reports/blocker_burn_dashboard_20260416_v0.json",
                "theorem_gap_row_outcome_trend_report": "formal/output/reports/theorem_gap_row_outcome_trend_20260411_v0.json",
                "post_plan_post_cascade_explicit_exhaustion_decision_report": "formal/output/reports/post_plan_post_cascade_explicit_exhaustion_decision_20260419_v0.json",
                "post_plan_post_cascade_successor_family_eligibility_review_report": "formal/output/reports/post_plan_post_cascade_successor_family_eligibility_review_20260419_v0.json",
                "post_plan_cosmo_sr_selected_continuation_execution_report": "formal/output/reports/post_plan_cosmo_sr_selected_continuation_execution_20260419_v0.json",
            },
            "selection_policy": {
                "required_stop_outcome": "POST_PLAN_POST_CASCADE_SUCCESSOR_FAMILY_ELIGIBILITY_NONE_ELIGIBLE",
                "required_exhaustion_outcome": "POST_PLAN_POST_CASCADE_EXPLICIT_EXHAUSTION_DECISION_EXHAUSTED_UNDER_CURRENT_DECLARED_FAMILY",
                "default_selected_row": "ROW-PILLAR-STAT-001",
                "alternate_selected_row": "ROW-PILLAR-COSMO-001",
                "blocked_row": "ROW-PILLAR-QM-001",
                "dormant_only_row": "ROW-PILLAR-GR-001",
                "reserve_rows": ["ROW-PILLAR-QFT-001", "ROW-PILLAR-EM-001", "ROW-PILLAR-SR-001"],
                "required_primary_executable_seam": "SEAM-COSMO-SR",
                "cosmo_override_row": "ROW-SEAM-COSMO-SR-001",
                "cosmo_override_target_row": "ROW-PILLAR-COSMO-001",
                "stat_execution_surface_declaration": "formal/docs/release/POST_PLAN_STAT_THEOREM_GAP_REACTIVATION_TRANCHE_20260419_v0.json",
                "cosmo_execution_surface_declaration": "formal/docs/release/POST_PLAN_COSMO_THEOREM_GAP_REACTIVATION_TRANCHE_20260419_v0.json",
            },
            "outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_POST_PLAN_THEOREM_GAP_FRESH_MOVEMENT_QUALIFICATION_OUTCOME",
                "no_loop_rule": "ONE_POST_PLAN_THEOREM_GAP_FRESH_MOVEMENT_QUALIFICATION_LAYER_ONLY",
                "allowed_outcomes": [
                    "POST_PLAN_THEOREM_GAP_FRESH_MOVEMENT_QUALIFICATION_STAT_DEFAULT_SELECTED",
                    "POST_PLAN_THEOREM_GAP_FRESH_MOVEMENT_QUALIFICATION_COSMO_OVERRIDE_SELECTED",
                    "POST_PLAN_THEOREM_GAP_FRESH_MOVEMENT_QUALIFICATION_NO_ROW_SELECTED",
                    "POST_PLAN_THEOREM_GAP_FRESH_MOVEMENT_QUALIFICATION_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_POST_PLAN_THEOREM_GAP_FRESH_MOVEMENT_QUALIFICATION_REPAIR",
                ],
                "default_outcome": "POST_PLAN_THEOREM_GAP_FRESH_MOVEMENT_QUALIFICATION_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _seed_inputs(root: Path, *, theorem_gap_delta: int = 0, seam_gap_delta: int = 0, cosmo_row_truth_change: bool = False) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "post_plan_objective_quality_physics_completion_queue_20260418_v0.json",
        {
            "summary": {
                "terminal_outcome": "POST_PLAN_OBJECTIVE_QUALITY_PHYSICS_COMPLETION_QUEUE_MATERIALIZED",
                "second_active_row": "ROW-PILLAR-STAT-001",
                "heavy_structural_row": "ROW-PILLAR-GR-001",
                "excluded_row": "ROW-PILLAR-QM-001",
                "queue_order": [
                    "ROW-PILLAR-COSMO-001",
                    "ROW-PILLAR-STAT-001",
                    "ROW-PILLAR-GR-001",
                    "ROW-PILLAR-QFT-001",
                    "ROW-PILLAR-EM-001",
                    "ROW-PILLAR-SR-001",
                ],
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "post_plan_physics_advancement_target_map_20260418_v0.json",
        {
            "summary": {"executable_now_rows": ["ROW-SEAM-COSMO-SR-001"]},
            "routed_rows": [{"row_id": "ROW-SEAM-COSMO-SR-001", "route_class": "EXECUTABLE_NOW"}],
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "blocker_burn_dashboard_20260416_v0.json",
        {"blocker_scoreboard": {"delta_by_class": {"THEOREM_GAP": theorem_gap_delta, "SEAM_INTEGRATION_GAP": seam_gap_delta}}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "theorem_gap_row_outcome_trend_20260411_v0.json",
        {"objective_quality": {"inputs": {"row_outcome_counts": {"ROW-PILLAR-STAT-001": {"no_change": 0}}}}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "post_plan_post_cascade_explicit_exhaustion_decision_20260419_v0.json",
        {"summary": {"terminal_outcome": "POST_PLAN_POST_CASCADE_EXPLICIT_EXHAUSTION_DECISION_EXHAUSTED_UNDER_CURRENT_DECLARED_FAMILY"}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "post_plan_post_cascade_successor_family_eligibility_review_20260419_v0.json",
        {"summary": {"terminal_outcome": "POST_PLAN_POST_CASCADE_SUCCESSOR_FAMILY_ELIGIBILITY_NONE_ELIGIBLE"}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "post_plan_cosmo_sr_selected_continuation_execution_20260419_v0.json",
        {"summary": {"target_row_id": "ROW-SEAM-COSMO-SR-001", "row_truth_change_detected": cosmo_row_truth_change}},
    )


def test_qualification_selects_stat_by_default_when_theorem_gap_delta_is_negative(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "POST_PLAN_THEOREM_GAP_FRESH_MOVEMENT_QUALIFICATION_20260419_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, theorem_gap_delta=-1, seam_gap_delta=0, cosmo_row_truth_change=False)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "POST_PLAN_THEOREM_GAP_FRESH_MOVEMENT_QUALIFICATION_STAT_DEFAULT_SELECTED"
    assert report["summary"]["selected_row"] == "ROW-PILLAR-STAT-001"


def test_qualification_selects_cosmo_when_seam_override_is_machine_pinned(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "POST_PLAN_THEOREM_GAP_FRESH_MOVEMENT_QUALIFICATION_20260419_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, theorem_gap_delta=0, seam_gap_delta=-1, cosmo_row_truth_change=True)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "POST_PLAN_THEOREM_GAP_FRESH_MOVEMENT_QUALIFICATION_COSMO_OVERRIDE_SELECTED"
    assert report["summary"]["selected_row"] == "ROW-PILLAR-COSMO-001"


def test_live_qualification_report_and_reactivation_mirrors_are_registered() -> None:
    program_text = _read(PROGRAM_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)

    required_refs = [
        "formal/docs/release/POST_PLAN_THEOREM_GAP_REDUCTION_REACTIVATION_PROGRAM_20260419_v0.md",
        "formal/docs/release/POST_PLAN_THEOREM_GAP_FRESH_MOVEMENT_QUALIFICATION_20260419_v0.json",
        "formal/output/reports/post_plan_theorem_gap_fresh_movement_qualification_20260419_v0.json",
        "formal/python/tools/post_plan_theorem_gap_fresh_movement_qualification_report.py",
        "formal/docs/release/POST_PLAN_THEOREM_GAP_SUCCESSOR_FAMILY_AUTHORIZATION_REVIEW_20260419_v0.json",
        "formal/output/reports/post_plan_theorem_gap_successor_family_authorization_review_20260419_v0.json",
        "formal/docs/release/POST_PLAN_THEOREM_GAP_RERANKING_20260419_v0.json",
        "formal/output/reports/post_plan_theorem_gap_reranking_20260419_v0.json",
    ]

    for ref in required_refs:
        assert ref in program_text
        assert ref in state_text or ref in roadmap_text or ref in inventory_text

    report = _read_json(
        REPO_ROOT / "formal" / "output" / "reports" / "post_plan_theorem_gap_fresh_movement_qualification_20260419_v0.json"
    )
    assert report["summary"]["terminal_outcome"] == "POST_PLAN_THEOREM_GAP_FRESH_MOVEMENT_QUALIFICATION_NO_ROW_SELECTED"
    assert report["summary"]["selected_row"] == "NONE"
