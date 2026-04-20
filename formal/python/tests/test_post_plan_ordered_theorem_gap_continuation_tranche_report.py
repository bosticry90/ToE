from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import post_plan_ordered_theorem_gap_continuation_tranche_report as tool


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
                "post_plan_remaining_physics_execution_order_report": "formal/output/reports/post_plan_remaining_physics_execution_order_20260419_v0.json",
                "post_plan_objective_quality_physics_completion_queue_report": "formal/output/reports/post_plan_objective_quality_physics_completion_queue_20260418_v0.json",
                "post_plan_stat_theorem_gap_completion_tranche_report": "formal/output/reports/post_plan_stat_theorem_gap_completion_tranche_20260418_v0.json"
            },
            "execution_policy": {
                "required_remaining_order_outcome": "POST_PLAN_REMAINING_PHYSICS_EXECUTION_ORDER_MATERIALIZED",
                "required_first_family": "COSMO_SR_SELECTED_CONTINUATION_FAMILY",
                "required_second_family": "OBJECTIVE_QUALITY_QUEUE_DOWNSTREAM",
                "required_remaining_order_next_action": "PREPARE_POST_PLAN_STAT_THEOREM_GAP_COMPLETION_TRANCHE_AND_RETAIN_CURRENT_SEAM_CLASSES",
                "required_queue_outcome": "POST_PLAN_OBJECTIVE_QUALITY_PHYSICS_COMPLETION_QUEUE_MATERIALIZED",
                "required_queue_first_row": "ROW-PILLAR-COSMO-001",
                "required_queue_second_row": "ROW-PILLAR-STAT-001",
                "required_primary_executable_seam": "SEAM-COSMO-SR",
                "required_stat_tranche_outcome": "POST_PLAN_STAT_THEOREM_GAP_COMPLETION_TRANCHE_EXECUTED_NONPROMOTED",
                "required_stat_tranche_next_action": "PREPARE_GR_DORMANT_NEW_STRUCTURE_COMPLETION_PACKAGE_AND_RETAIN_CURRENT_SEAM_CLASSES",
                "selected_tranche_family": "POST_PLAN_STAT_THEOREM_GAP_COMPLETION_TRANCHE",
                "selected_tranche_target_row": "ROW-PILLAR-STAT-001",
                "selected_tranche_activation_state": "HIGHER_PRIORITY_CLOSEOUT_RECORDED",
                "defer_until_family": "COSMO_SR_SELECTED_CONTINUATION_FAMILY"
            },
            "outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_POST_PLAN_ORDERED_THEOREM_GAP_CONTINUATION_TRANCHE_OUTCOME",
                "no_loop_rule": "ONE_POST_PLAN_ORDERED_THEOREM_GAP_CONTINUATION_TRANCHE_LAYER_ONLY",
                "allowed_outcomes": [
                    "POST_PLAN_ORDERED_THEOREM_GAP_CONTINUATION_TRANCHE_MATERIALIZED",
                    "POST_PLAN_ORDERED_THEOREM_GAP_CONTINUATION_TRANCHE_EVIDENCE_INCOMPLETE",
                    "POST_PLAN_ORDERED_THEOREM_GAP_CONTINUATION_TRANCHE_CONTRACT_VIOLATION"
                ],
                "default_outcome": "POST_PLAN_ORDERED_THEOREM_GAP_CONTINUATION_TRANCHE_EVIDENCE_INCOMPLETE"
            }
        },
    )


def _seed_inputs(root: Path, *, include_order: bool = True) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "post_plan_remaining_physics_execution_order_20260419_v0.json",
        {
            "summary": {
                "terminal_outcome": "POST_PLAN_REMAINING_PHYSICS_EXECUTION_ORDER_MATERIALIZED" if include_order else "POST_PLAN_REMAINING_PHYSICS_EXECUTION_ORDER_EVIDENCE_INCOMPLETE",
                "first_family_id": "COSMO_SR_SELECTED_CONTINUATION_FAMILY",
                "second_family_id": "OBJECTIVE_QUALITY_QUEUE_DOWNSTREAM",
                "queue_primary_executable_seam": "SEAM-COSMO-SR",
                "next_action": "PREPARE_POST_PLAN_STAT_THEOREM_GAP_COMPLETION_TRANCHE_AND_RETAIN_CURRENT_SEAM_CLASSES"
            },
            "ranked_families": [
                {"family_id": "COSMO_SR_SELECTED_CONTINUATION_FAMILY"},
                {"family_id": "OBJECTIVE_QUALITY_QUEUE_DOWNSTREAM"},
                {"family_id": "POST_CASCADE_SUCCESSOR_REOPEN"}
            ]
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "post_plan_objective_quality_physics_completion_queue_20260418_v0.json",
        {
            "summary": {
                "terminal_outcome": "POST_PLAN_OBJECTIVE_QUALITY_PHYSICS_COMPLETION_QUEUE_MATERIALIZED",
                "first_active_row": "ROW-PILLAR-COSMO-001",
                "second_active_row": "ROW-PILLAR-STAT-001",
                "primary_executable_seam": "SEAM-COSMO-SR"
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "post_plan_stat_theorem_gap_completion_tranche_20260418_v0.json",
        {
            "summary": {
                "terminal_outcome": "POST_PLAN_STAT_THEOREM_GAP_COMPLETION_TRANCHE_EXECUTED_NONPROMOTED",
                "target_row_id": "ROW-PILLAR-STAT-001",
                "next_action": "PREPARE_GR_DORMANT_NEW_STRUCTURE_COMPLETION_PACKAGE_AND_RETAIN_CURRENT_SEAM_CLASSES"
            }
        },
    )


def test_ordered_theorem_gap_continuation_materializes(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "POST_PLAN_ORDERED_THEOREM_GAP_CONTINUATION_TRANCHE_20260419_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "POST_PLAN_ORDERED_THEOREM_GAP_CONTINUATION_TRANCHE_MATERIALIZED"
    assert report["summary"]["selected_tranche_family"] == "POST_PLAN_STAT_THEOREM_GAP_COMPLETION_TRANCHE"
    assert report["summary"]["selected_tranche_activation_state"] == "HIGHER_PRIORITY_CLOSEOUT_RECORDED"
    assert report["summary"]["next_action"] == "PREPARE_GR_DORMANT_NEW_STRUCTURE_COMPLETION_PACKAGE_AND_RETAIN_CURRENT_SEAM_CLASSES"


def test_ordered_theorem_gap_continuation_fails_without_remaining_order(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "POST_PLAN_ORDERED_THEOREM_GAP_CONTINUATION_TRANCHE_20260419_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, include_order=False)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "POST_PLAN_ORDERED_THEOREM_GAP_CONTINUATION_TRANCHE_EVIDENCE_INCOMPLETE"


def test_live_ordered_theorem_gap_continuation_registered_in_mirrors() -> None:
    program_text = _read(PROGRAM_PATH)
    advancement_program_text = _read(ADVANCEMENT_PROGRAM_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)

    required_refs = [
        "formal/docs/release/POST_PLAN_ORDERED_THEOREM_GAP_CONTINUATION_TRANCHE_20260419_v0.json",
        "formal/output/reports/post_plan_ordered_theorem_gap_continuation_tranche_20260419_v0.json",
        "formal/python/tools/post_plan_ordered_theorem_gap_continuation_tranche_report.py",
        "formal/python/tests/test_post_plan_ordered_theorem_gap_continuation_tranche_report.py",
    ]

    for ref in required_refs:
        assert ref in program_text or ref in advancement_program_text
        assert ref in state_text or ref in roadmap_text or ref in inventory_text

    report = _read_json(
        REPO_ROOT / "formal" / "output" / "reports" / "post_plan_ordered_theorem_gap_continuation_tranche_20260419_v0.json"
    )
    assert report["summary"]["terminal_outcome"] == "POST_PLAN_ORDERED_THEOREM_GAP_CONTINUATION_TRANCHE_MATERIALIZED"
    assert report["summary"]["selected_tranche_family"] == "POST_PLAN_STAT_THEOREM_GAP_COMPLETION_TRANCHE"
    assert report["summary"]["selected_tranche_target_row"] == "ROW-PILLAR-STAT-001"
