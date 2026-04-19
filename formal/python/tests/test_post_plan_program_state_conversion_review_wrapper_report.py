from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import post_plan_program_state_conversion_review_wrapper_report as tool


REPO_ROOT = find_repo_root(Path(__file__))
PROGRAM_PATH = REPO_ROOT / "formal" / "docs" / "release" / "POST_PLAN_OBJECTIVE_QUALITY_PHYSICS_COMPLETION_PROGRAM_20260418_v0.md"
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
                "post_plan_sr_theorem_gap_completion_tranche_report": "formal/output/reports/post_plan_sr_theorem_gap_completion_tranche_20260418_v0.json",
                "program_state_conversion_review_declaration": "formal/docs/release/PROGRAM_STATE_CONVERSION_REVIEW_20260411_v0.json",
                "program_state_conversion_review_report": "formal/output/reports/program_state_conversion_review_20260411_v0.json",
                "post_plan_deeper_blocker_definition_review_successor_tranche_report": "formal/output/reports/post_plan_deeper_blocker_definition_review_successor_tranche_20260418_v0.json",
            },
            "execution_policy": {
                "required_sr_outcome": "POST_PLAN_SR_THEOREM_GAP_COMPLETION_TRANCHE_EXECUTED_NONPROMOTED",
                "required_sr_next_action": "ROUTE_TO_PROGRAM_STATE_CONVERSION_REVIEW_WITH_QFT_EM_SR_NONMOVING_FAMILIES_RECORDED",
                "required_conversion_review_basis": "THREE_UPSTREAM_EXPLANATIONS_EXHAUSTED_NON_MOVEMENT_PERSISTS",
                "required_conversion_review_outcome": "DEEPER_BLOCKER_DEFINITION_REVIEW_REQUIRED",
                "required_conversion_review_next_action": "EXECUTE_DEEPER_BLOCKER_DEFINITION_REVIEW",
                "required_successor_outcome": "POST_PLAN_DEEPER_BLOCKER_DEFINITION_REVIEW_SUCCESSOR_TRANCHE_MATERIALIZED",
                "required_successor_next_action": "EXECUTE_BOUNDED_BLOCKER_DEFINITION_TEST_PACKET_ONCE",
                "required_wrapper_next_action": "REUSE_EXISTING_PROGRAM_STATE_CONVERSION_REVIEW_DOWNSTREAM_PATH_AND_KEEP_THEOREM_GAP_QUEUE_CLOSED",
            },
            "outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_POST_PLAN_PROGRAM_STATE_CONVERSION_REVIEW_WRAPPER_OUTCOME",
                "no_loop_rule": "ONE_POST_PLAN_PROGRAM_STATE_CONVERSION_REVIEW_WRAPPER_ONLY",
                "allowed_outcomes": [
                    "POST_PLAN_PROGRAM_STATE_CONVERSION_REVIEW_WRAPPER_MATERIALIZED",
                    "POST_PLAN_PROGRAM_STATE_CONVERSION_REVIEW_WRAPPER_BLOCKED",
                    "POST_PLAN_PROGRAM_STATE_CONVERSION_REVIEW_WRAPPER_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_POST_PLAN_PROGRAM_STATE_CONVERSION_REVIEW_WRAPPER_REPAIR",
                ],
                "default_outcome": "POST_PLAN_PROGRAM_STATE_CONVERSION_REVIEW_WRAPPER_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _seed_inputs(root: Path, *, blocked: bool = False) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "post_plan_sr_theorem_gap_completion_tranche_20260418_v0.json",
        {
            "summary": {
                "target_row_id": "ROW-PILLAR-SR-001",
                "terminal_outcome": "POST_PLAN_SR_THEOREM_GAP_COMPLETION_TRANCHE_EXECUTED_NONPROMOTED",
                "next_action": "ROUTE_TO_PROGRAM_STATE_CONVERSION_REVIEW_WITH_QFT_EM_SR_NONMOVING_FAMILIES_RECORDED",
            }
        },
    )
    _write_json(
        root / "formal" / "docs" / "release" / "PROGRAM_STATE_CONVERSION_REVIEW_20260411_v0.json",
        {
            "review_basis": "THREE_UPSTREAM_EXPLANATIONS_EXHAUSTED_NON_MOVEMENT_PERSISTS",
            "review_policy": {"no_loop_rule": "ONE_PROGRAM_STATE_CONVERSION_REVIEW_ONLY"},
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "program_state_conversion_review_20260411_v0.json",
        {
            "summary": {
                "review_outcome": "DEEPER_BLOCKER_DEFINITION_REVIEW_REQUIRED",
                "next_action": "EXECUTE_DEEPER_BLOCKER_DEFINITION_REVIEW",
            }
        },
    )
    successor_outcome = (
        "POST_PLAN_DEEPER_BLOCKER_DEFINITION_REVIEW_SUCCESSOR_TRANCHE_BLOCKED"
        if blocked
        else "POST_PLAN_DEEPER_BLOCKER_DEFINITION_REVIEW_SUCCESSOR_TRANCHE_MATERIALIZED"
    )
    _write_json(
        root
        / "formal"
        / "output"
        / "reports"
        / "post_plan_deeper_blocker_definition_review_successor_tranche_20260418_v0.json",
        {
            "summary": {
                "terminal_outcome": successor_outcome,
                "next_action": "EXECUTE_BOUNDED_BLOCKER_DEFINITION_TEST_PACKET_ONCE",
            }
        },
    )


def test_conversion_review_wrapper_materializes_from_sr_terminal_state(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "POST_PLAN_PROGRAM_STATE_CONVERSION_REVIEW_WRAPPER_20260418_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, blocked=False)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "POST_PLAN_PROGRAM_STATE_CONVERSION_REVIEW_WRAPPER_MATERIALIZED"
    assert report["summary"]["triggering_row"] == "ROW-PILLAR-SR-001"
    assert report["summary"]["next_action"] == "REUSE_EXISTING_PROGRAM_STATE_CONVERSION_REVIEW_DOWNSTREAM_PATH_AND_KEEP_THEOREM_GAP_QUEUE_CLOSED"


def test_conversion_review_wrapper_blocks_without_existing_successor_path(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "POST_PLAN_PROGRAM_STATE_CONVERSION_REVIEW_WRAPPER_20260418_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, blocked=True)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "POST_PLAN_PROGRAM_STATE_CONVERSION_REVIEW_WRAPPER_BLOCKED"


def test_live_conversion_review_wrapper_registered_in_mirrors() -> None:
    program_text = _read(PROGRAM_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)

    required_refs = [
        "formal/docs/release/POST_PLAN_PROGRAM_STATE_CONVERSION_REVIEW_WRAPPER_20260418_v0.json",
        "formal/output/reports/post_plan_program_state_conversion_review_wrapper_20260418_v0.json",
        "formal/python/tools/post_plan_program_state_conversion_review_wrapper_report.py",
        "formal/python/tests/test_post_plan_program_state_conversion_review_wrapper_report.py",
    ]

    for ref in required_refs:
        assert ref in program_text
        assert ref in state_text or ref in roadmap_text or ref in inventory_text

    report = _read_json(
        REPO_ROOT / "formal" / "output" / "reports" / "post_plan_program_state_conversion_review_wrapper_20260418_v0.json"
    )
    assert report["summary"]["terminal_outcome"] == "POST_PLAN_PROGRAM_STATE_CONVERSION_REVIEW_WRAPPER_MATERIALIZED"
    assert report["summary"]["triggering_row"] == "ROW-PILLAR-SR-001"
    assert report["summary"]["next_action"] == "REUSE_EXISTING_PROGRAM_STATE_CONVERSION_REVIEW_DOWNSTREAM_PATH_AND_KEEP_THEOREM_GAP_QUEUE_CLOSED"