from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import post_plan_deeper_blocker_definition_review_successor_tranche_report as tool


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
                "post_plan_gr_tranche_report": "formal/output/reports/post_plan_gr_dormant_new_structure_completion_tranche_20260418_v0.json",
                "deeper_blocker_definition_review_declaration": "formal/docs/release/DEEPER_BLOCKER_DEFINITION_REVIEW_20260411_v0.json",
                "deeper_blocker_definition_review_report": "formal/output/reports/deeper_blocker_definition_review_20260411_v0.json",
                "program_state_conversion_review_report": "formal/output/reports/program_state_conversion_review_20260411_v0.json"
            },
            "execution_policy": {
                "required_gr_outcome": "POST_PLAN_GR_DORMANT_NEW_STRUCTURE_COMPLETION_TRANCHE_EXPLICITLY_EXHAUSTED",
                "required_gr_next_action": "OPEN_DEEPER_BLOCKER_DEFINITION_REVIEW_PATH_WITH_GR_DORMANT_PACKAGE_EXHAUSTION_RECORDED",
                "required_review_basis": "PROGRAM_STATE_CONVERSION_REVIEW_PRESCRIBED_DEEPER_BLOCKER_DEFINITION_REVIEW",
                "required_conversion_review_outcome": "DEEPER_BLOCKER_DEFINITION_REVIEW_REQUIRED",
                "required_deeper_review_outcome": "DEEPER_BLOCKER_DEFINITION_REVIEW_MATERIALIZED",
                "required_successor_next_action": "EXECUTE_BOUNDED_BLOCKER_DEFINITION_TEST_PACKET_ONCE"
            },
            "outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_POST_PLAN_DEEPER_BLOCKER_DEFINITION_REVIEW_SUCCESSOR_TRANCHE_OUTCOME",
                "no_loop_rule": "ONE_POST_PLAN_DEEPER_BLOCKER_DEFINITION_REVIEW_SUCCESSOR_TRANCHE_ONLY",
                "allowed_outcomes": [
                    "POST_PLAN_DEEPER_BLOCKER_DEFINITION_REVIEW_SUCCESSOR_TRANCHE_MATERIALIZED",
                    "POST_PLAN_DEEPER_BLOCKER_DEFINITION_REVIEW_SUCCESSOR_TRANCHE_BLOCKED",
                    "POST_PLAN_DEEPER_BLOCKER_DEFINITION_REVIEW_SUCCESSOR_TRANCHE_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_POST_PLAN_DEEPER_BLOCKER_DEFINITION_REVIEW_SUCCESSOR_TRANCHE_REPAIR"
                ],
                "default_outcome": "POST_PLAN_DEEPER_BLOCKER_DEFINITION_REVIEW_SUCCESSOR_TRANCHE_EVIDENCE_INCOMPLETE"
            }
        }
    )


def _seed_inputs(root: Path, *, blocked: bool = False) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "post_plan_gr_dormant_new_structure_completion_tranche_20260418_v0.json",
        {
            "summary": {
                "target_row_id": "ROW-PILLAR-GR-001",
                "terminal_outcome": "POST_PLAN_GR_DORMANT_NEW_STRUCTURE_COMPLETION_TRANCHE_EXPLICITLY_EXHAUSTED",
                "next_action": "OPEN_DEEPER_BLOCKER_DEFINITION_REVIEW_PATH_WITH_GR_DORMANT_PACKAGE_EXHAUSTION_RECORDED"
            }
        }
    )
    _write_json(
        root / "formal" / "docs" / "release" / "DEEPER_BLOCKER_DEFINITION_REVIEW_20260411_v0.json",
        {"review_basis": "PROGRAM_STATE_CONVERSION_REVIEW_PRESCRIBED_DEEPER_BLOCKER_DEFINITION_REVIEW"}
    )
    _write_json(
        root / "formal" / "output" / "reports" / "program_state_conversion_review_20260411_v0.json",
        {"summary": {"review_outcome": "DEEPER_BLOCKER_DEFINITION_REVIEW_REQUIRED"}}
    )
    deeper_outcome = "REVIEW_BLOCKED_MISSING_PREREQUISITE" if blocked else "DEEPER_BLOCKER_DEFINITION_REVIEW_MATERIALIZED"
    _write_json(
        root / "formal" / "output" / "reports" / "deeper_blocker_definition_review_20260411_v0.json",
        {"summary": {"review_outcome": deeper_outcome, "bounded_follow_on_packet": "ONE_SEAM_ROW_BLOCKER_DEFINITION_TEST_UNDER_REVISED_CRITERIA", "next_action": "EXECUTE_BOUNDED_BLOCKER_DEFINITION_TEST_PACKET_ONCE"}}
    )


def test_successor_tranche_materializes_after_gr_exhaustion(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "POST_PLAN_DEEPER_BLOCKER_DEFINITION_REVIEW_SUCCESSOR_TRANCHE_20260418_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, blocked=False)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "POST_PLAN_DEEPER_BLOCKER_DEFINITION_REVIEW_SUCCESSOR_TRANCHE_MATERIALIZED"
    assert report["summary"]["triggering_row"] == "ROW-PILLAR-GR-001"
    assert report["summary"]["next_action"] == "EXECUTE_BOUNDED_BLOCKER_DEFINITION_TEST_PACKET_ONCE"


def test_successor_tranche_blocks_when_underlying_review_not_materialized(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "POST_PLAN_DEEPER_BLOCKER_DEFINITION_REVIEW_SUCCESSOR_TRANCHE_20260418_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, blocked=True)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "POST_PLAN_DEEPER_BLOCKER_DEFINITION_REVIEW_SUCCESSOR_TRANCHE_BLOCKED"


def test_live_successor_tranche_registered_in_mirrors() -> None:
    program_text = _read(PROGRAM_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)

    required_refs = [
        "formal/docs/release/POST_PLAN_DEEPER_BLOCKER_DEFINITION_REVIEW_SUCCESSOR_TRANCHE_20260418_v0.json",
        "formal/output/reports/post_plan_deeper_blocker_definition_review_successor_tranche_20260418_v0.json",
        "formal/python/tools/post_plan_deeper_blocker_definition_review_successor_tranche_report.py",
        "formal/python/tests/test_post_plan_deeper_blocker_definition_review_successor_tranche_report.py"
    ]

    for ref in required_refs:
        assert ref in program_text
        assert ref in state_text or ref in roadmap_text or ref in inventory_text

    report = _read_json(REPO_ROOT / "formal" / "output" / "reports" / "post_plan_deeper_blocker_definition_review_successor_tranche_20260418_v0.json")
    assert report["summary"]["terminal_outcome"] == "POST_PLAN_DEEPER_BLOCKER_DEFINITION_REVIEW_SUCCESSOR_TRANCHE_MATERIALIZED"
    assert report["summary"]["next_action"] == "EXECUTE_BOUNDED_BLOCKER_DEFINITION_TEST_PACKET_ONCE"
