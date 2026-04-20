from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import post_plan_remaining_physics_execution_order_report as tool


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


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "post_plan_cosmo_sr_selected_continuation_execution_report": "formal/output/reports/post_plan_cosmo_sr_selected_continuation_execution_20260419_v0.json",
                "post_plan_cosmo_sr_selected_continuation_family_report": "formal/output/reports/post_plan_cosmo_sr_selected_continuation_family_20260419_v0.json",
                "post_plan_cosmo_sr_cycle08_or_later_payload_unlock_surface_report": "formal/output/reports/post_plan_cosmo_sr_cycle08_or_later_payload_unlock_surface_20260419_v0.json",
                "post_plan_objective_quality_physics_completion_queue_report": "formal/output/reports/post_plan_objective_quality_physics_completion_queue_20260418_v0.json",
                "post_plan_post_cascade_explicit_exhaustion_decision_report": "formal/output/reports/post_plan_post_cascade_explicit_exhaustion_decision_20260419_v0.json",
                "post_plan_post_cascade_successor_family_eligibility_review_report": "formal/output/reports/post_plan_post_cascade_successor_family_eligibility_review_20260419_v0.json"
            },
            "ordering_policy": {
                "required_selected_execution_outcome": "POST_PLAN_COSMO_SR_SELECTED_CONTINUATION_EXECUTION_EXECUTED_NONPROMOTED_CLOSEOUT",
                "required_selected_execution_next_action": "PREPARE_POST_PLAN_STAT_THEOREM_GAP_COMPLETION_TRANCHE_AND_RETAIN_CURRENT_SEAM_CLASSES",
                "required_selected_family_outcome": "POST_PLAN_COSMO_SR_SELECTED_CONTINUATION_FAMILY_MATERIALIZED_READY_FOR_SINGLE_EXECUTION",
                "required_selected_family_next_action": "EXECUTE_DECLARED_COSMO_SR_CONTINUATION_PAYLOAD_ONCE",
                "required_unlock_outcome": "POST_PLAN_COSMO_SR_CYCLE08_OR_LATER_PAYLOAD_UNLOCK_SURFACE_ONE_PAYLOAD_UNLOCKED",
                "required_unlock_next_action": "AUTHOR_NEW_COSMO_SR_CONTINUATION_FAMILY_AGAINST_SELECTED_MACHINE_PINNED_PAYLOAD",
                "required_unlock_lane": "COSMO_SR_CYCLE08",
                "required_unlock_target_row": "ROW-SEAM-COSMO-SR-001",
                "required_queue_outcome": "POST_PLAN_OBJECTIVE_QUALITY_PHYSICS_COMPLETION_QUEUE_MATERIALIZED",
                "required_queue_first_row": "ROW-PILLAR-COSMO-001",
                "required_queue_second_row": "ROW-PILLAR-STAT-001",
                "required_queue_heavy_row": "ROW-PILLAR-GR-001",
                "required_queue_primary_executable_seam": "SEAM-COSMO-SR",
                "required_exhaustion_outcome": "POST_PLAN_POST_CASCADE_EXPLICIT_EXHAUSTION_DECISION_EXHAUSTED_UNDER_CURRENT_DECLARED_FAMILY",
                "required_successor_outcome": "POST_PLAN_POST_CASCADE_SUCCESSOR_FAMILY_ELIGIBILITY_NONE_ELIGIBLE",
                "required_successor_next_action": "ACCEPT_TERMINAL_EXHAUSTION_READ_UNTIL_FRESH_BLOCKER_FACING_MOVEMENT_IS_MACHINE_PINNED",
                "ranked_family_order": [
                    "COSMO_SR_SELECTED_CONTINUATION_FAMILY",
                    "OBJECTIVE_QUALITY_QUEUE_DOWNSTREAM",
                    "POST_CASCADE_SUCCESSOR_REOPEN"
                ]
            },
            "ordering_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_POST_PLAN_REMAINING_PHYSICS_EXECUTION_ORDER_OUTCOME",
                "no_loop_rule": "ONE_POST_PLAN_REMAINING_PHYSICS_EXECUTION_ORDER_LAYER_ONLY",
                "allowed_outcomes": [
                    "POST_PLAN_REMAINING_PHYSICS_EXECUTION_ORDER_MATERIALIZED",
                    "POST_PLAN_REMAINING_PHYSICS_EXECUTION_ORDER_EVIDENCE_INCOMPLETE",
                    "POST_PLAN_REMAINING_PHYSICS_EXECUTION_ORDER_CONTRACT_VIOLATION"
                ],
                "default_outcome": "POST_PLAN_REMAINING_PHYSICS_EXECUTION_ORDER_EVIDENCE_INCOMPLETE"
            }
        },
    )


def _seed_inputs(root: Path, *, include_unlock: bool = True) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "post_plan_cosmo_sr_selected_continuation_execution_20260419_v0.json",
        {
            "summary": {
                "terminal_outcome": "POST_PLAN_COSMO_SR_SELECTED_CONTINUATION_EXECUTION_EXECUTED_NONPROMOTED_CLOSEOUT" if include_unlock else "POST_PLAN_COSMO_SR_SELECTED_CONTINUATION_EXECUTION_EVIDENCE_INCOMPLETE",
                "next_action": "PREPARE_POST_PLAN_STAT_THEOREM_GAP_COMPLETION_TRANCHE_AND_RETAIN_CURRENT_SEAM_CLASSES",
                "selected_continuation_lane": "COSMO_SR_CYCLE08",
                "target_row_id": "ROW-SEAM-COSMO-SR-001"
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "post_plan_cosmo_sr_selected_continuation_family_20260419_v0.json",
        {
            "summary": {
                "terminal_outcome": "POST_PLAN_COSMO_SR_SELECTED_CONTINUATION_FAMILY_MATERIALIZED_READY_FOR_SINGLE_EXECUTION" if include_unlock else "POST_PLAN_COSMO_SR_SELECTED_CONTINUATION_FAMILY_EVIDENCE_INCOMPLETE",
                "next_action": "EXECUTE_DECLARED_COSMO_SR_CONTINUATION_PAYLOAD_ONCE",
                "selected_continuation_lane": "COSMO_SR_CYCLE08",
                "selected_continuation_machine_pinned": True,
                "target_row_id": "ROW-SEAM-COSMO-SR-001"
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "post_plan_cosmo_sr_cycle08_or_later_payload_unlock_surface_20260419_v0.json",
        {
            "summary": {
                "terminal_outcome": "POST_PLAN_COSMO_SR_CYCLE08_OR_LATER_PAYLOAD_UNLOCK_SURFACE_ONE_PAYLOAD_UNLOCKED"
                if include_unlock
                else "POST_PLAN_COSMO_SR_CYCLE08_OR_LATER_PAYLOAD_UNLOCK_SURFACE_EVIDENCE_INCOMPLETE",
                "next_action": "AUTHOR_NEW_COSMO_SR_CONTINUATION_FAMILY_AGAINST_SELECTED_MACHINE_PINNED_PAYLOAD",
                "selected_unlock_payload_lane": "COSMO_SR_CYCLE08",
                "selected_unlock_payload_machine_pinned": True,
                "selected_payload_paths_exist": True,
                "target_row_id": "ROW-SEAM-COSMO-SR-001",
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "post_plan_objective_quality_physics_completion_queue_20260418_v0.json",
        {
            "summary": {
                "terminal_outcome": "POST_PLAN_OBJECTIVE_QUALITY_PHYSICS_COMPLETION_QUEUE_MATERIALIZED",
                "first_active_row": "ROW-PILLAR-COSMO-001",
                "second_active_row": "ROW-PILLAR-STAT-001",
                "heavy_structural_row": "ROW-PILLAR-GR-001",
                "primary_executable_seam": "SEAM-COSMO-SR",
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
        root / "formal" / "output" / "reports" / "post_plan_post_cascade_explicit_exhaustion_decision_20260419_v0.json",
        {
            "summary": {
                "terminal_outcome": "POST_PLAN_POST_CASCADE_EXPLICIT_EXHAUSTION_DECISION_EXHAUSTED_UNDER_CURRENT_DECLARED_FAMILY",
                "current_family_scope": "POST_CASCADE_QFT_EM_SR_CONTINUATION_CHAIN_ONLY",
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "post_plan_post_cascade_successor_family_eligibility_review_20260419_v0.json",
        {
            "summary": {
                "terminal_outcome": "POST_PLAN_POST_CASCADE_SUCCESSOR_FAMILY_ELIGIBILITY_NONE_ELIGIBLE",
                "next_action": "ACCEPT_TERMINAL_EXHAUSTION_READ_UNTIL_FRESH_BLOCKER_FACING_MOVEMENT_IS_MACHINE_PINNED",
                "selected_reopen_route": "NONE",
                "target_map_primary_executable_row": "ROW-SEAM-COSMO-SR-001",
            }
        },
    )


def test_remaining_execution_order_materializes_expected_priority(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "POST_PLAN_REMAINING_PHYSICS_EXECUTION_ORDER_20260419_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "POST_PLAN_REMAINING_PHYSICS_EXECUTION_ORDER_MATERIALIZED"
    assert report["summary"]["first_family_id"] == "COSMO_SR_SELECTED_CONTINUATION_FAMILY"
    assert report["summary"]["next_action"] == "PREPARE_POST_PLAN_STAT_THEOREM_GAP_COMPLETION_TRANCHE_AND_RETAIN_CURRENT_SEAM_CLASSES"
    assert report["ranked_families"][1]["queue_order"][:3] == [
        "ROW-PILLAR-COSMO-001",
        "ROW-PILLAR-STAT-001",
        "ROW-PILLAR-GR-001",
    ]


def test_remaining_execution_order_fails_when_unlock_missing(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "POST_PLAN_REMAINING_PHYSICS_EXECUTION_ORDER_20260419_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, include_unlock=False)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "POST_PLAN_REMAINING_PHYSICS_EXECUTION_ORDER_EVIDENCE_INCOMPLETE"


def test_live_remaining_execution_order_registered_in_mirrors() -> None:
    program_text = _read(PROGRAM_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)

    required_refs = [
        "formal/docs/release/POST_PLAN_REMAINING_PHYSICS_EXECUTION_ORDER_20260419_v0.json",
        "formal/output/reports/post_plan_remaining_physics_execution_order_20260419_v0.json",
        "formal/python/tools/post_plan_remaining_physics_execution_order_report.py",
        "formal/python/tests/test_post_plan_remaining_physics_execution_order_report.py",
    ]

    for ref in required_refs:
        assert ref in program_text
        assert ref in state_text or ref in roadmap_text or ref in inventory_text

    report = _read_json(
        REPO_ROOT / "formal" / "output" / "reports" / "post_plan_remaining_physics_execution_order_20260419_v0.json"
    )
    assert report["summary"]["terminal_outcome"] == "POST_PLAN_REMAINING_PHYSICS_EXECUTION_ORDER_MATERIALIZED"
    assert report["summary"]["first_family_id"] == "COSMO_SR_SELECTED_CONTINUATION_FAMILY"
    assert report["summary"]["selected_unlock_payload_lane"] == "COSMO_SR_CYCLE08"
    assert report["summary"]["third_family_id"] == "POST_CASCADE_SUCCESSOR_REOPEN"
    assert report["summary"]["next_action"] == "PREPARE_POST_PLAN_STAT_THEOREM_GAP_COMPLETION_TRANCHE_AND_RETAIN_CURRENT_SEAM_CLASSES"