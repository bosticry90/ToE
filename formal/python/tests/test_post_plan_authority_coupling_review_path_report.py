from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import post_plan_authority_coupling_review_path_report as tool


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
                "post_plan_bounded_blocker_definition_packet_chain_report": "formal/output/reports/post_plan_bounded_blocker_definition_test_packet_chain_20260418_v0.json",
                "authority_coupling_review_declaration": "formal/docs/release/AUTHORITY_COUPLING_REVIEW_20260411_v0.json",
                "authority_coupling_review_report": "formal/output/reports/authority_coupling_review_20260411_v0.json",
                "post_blocker_definition_test_decision_report": "formal/output/reports/post_blocker_definition_test_decision_20260411_v0.json"
            },
            "execution_policy": {
                "required_packet_chain_outcome": "POST_PLAN_BOUNDED_BLOCKER_DEFINITION_TEST_PACKET_CHAIN_VALID_BUT_NONMOVING",
                "required_packet_chain_next_action": "REQUIRE_ONE_BOUNDED_AUTHORITY_COUPLING_REVIEW",
                "required_authority_review_basis": "POST_BLOCKER_DEFINITION_TEST_DECISION_HOLD_SECONDARY_REQUIRE_COUPLING_REVIEW",
                "required_post_decision": "HOLD_REVISED_BLOCKER_DEF_AS_SECONDARY_REQUIRE_AUTHORITY_COUPLING_REVIEW",
                "required_authority_review_outcome": "BOUNDED_COUPLING_REFINEMENT_JUSTIFIED",
                "required_authority_review_next_action": "EXECUTE_BOUNDED_COUPLING_REFINEMENT_PACKET_ONCE"
            },
            "outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_POST_PLAN_AUTHORITY_COUPLING_REVIEW_PATH_OUTCOME",
                "no_loop_rule": "ONE_POST_PLAN_AUTHORITY_COUPLING_REVIEW_PATH_ONLY",
                "allowed_outcomes": [
                    "POST_PLAN_AUTHORITY_COUPLING_REVIEW_PATH_MATERIALIZED",
                    "POST_PLAN_AUTHORITY_COUPLING_REVIEW_PATH_HOLD_AWAITING_THEORY",
                    "POST_PLAN_AUTHORITY_COUPLING_REVIEW_PATH_ESCALATED",
                    "POST_PLAN_AUTHORITY_COUPLING_REVIEW_PATH_BLOCKED",
                    "POST_PLAN_AUTHORITY_COUPLING_REVIEW_PATH_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_POST_PLAN_AUTHORITY_COUPLING_REVIEW_PATH_REPAIR"
                ],
                "default_outcome": "POST_PLAN_AUTHORITY_COUPLING_REVIEW_PATH_EVIDENCE_INCOMPLETE"
            }
        }
    )


def _seed_inputs(root: Path, *, escalated: bool = False) -> None:
    _write_json(root / "formal" / "output" / "reports" / "post_plan_bounded_blocker_definition_test_packet_chain_20260418_v0.json", {"summary": {"terminal_outcome": "POST_PLAN_BOUNDED_BLOCKER_DEFINITION_TEST_PACKET_CHAIN_VALID_BUT_NONMOVING", "next_action": "REQUIRE_ONE_BOUNDED_AUTHORITY_COUPLING_REVIEW"}})
    _write_json(root / "formal" / "output" / "reports" / "post_blocker_definition_test_decision_20260411_v0.json", {"summary": {"post_test_decision": "HOLD_REVISED_BLOCKER_DEF_AS_SECONDARY_REQUIRE_AUTHORITY_COUPLING_REVIEW"}})
    _write_json(root / "formal" / "docs" / "release" / "AUTHORITY_COUPLING_REVIEW_20260411_v0.json", {"review_basis": "POST_BLOCKER_DEFINITION_TEST_DECISION_HOLD_SECONDARY_REQUIRE_COUPLING_REVIEW"})
    review_outcome = "COUPLING_DEFECT_NOT_SUFFICIENTLY_BOUNDED" if escalated else "BOUNDED_COUPLING_REFINEMENT_JUSTIFIED"
    next_action = "ESCALATE_TO_THEORY_POSTURE_OR_PROGRAM_PAUSE_REVIEW" if escalated else "EXECUTE_BOUNDED_COUPLING_REFINEMENT_PACKET_ONCE"
    _write_json(root / "formal" / "output" / "reports" / "authority_coupling_review_20260411_v0.json", {"summary": {"review_outcome": review_outcome, "coupling_disposition": "ESCALATE" if escalated else "REFINE_COUPLING", "next_action": next_action}})


def test_authority_review_path_materializes_with_bounded_refinement_next_step(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "POST_PLAN_AUTHORITY_COUPLING_REVIEW_PATH_20260418_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, escalated=False)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "POST_PLAN_AUTHORITY_COUPLING_REVIEW_PATH_MATERIALIZED"
    assert report["summary"]["next_action"] == "EXECUTE_BOUNDED_COUPLING_REFINEMENT_PACKET_ONCE"


def test_authority_review_path_marks_escalation_when_review_escalates(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "POST_PLAN_AUTHORITY_COUPLING_REVIEW_PATH_20260418_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, escalated=True)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "POST_PLAN_AUTHORITY_COUPLING_REVIEW_PATH_ESCALATED"


def test_live_authority_review_path_registered_in_mirrors() -> None:
    program_text = _read(PROGRAM_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)

    required_refs = [
        "formal/docs/release/POST_PLAN_AUTHORITY_COUPLING_REVIEW_PATH_20260418_v0.json",
        "formal/output/reports/post_plan_authority_coupling_review_path_20260418_v0.json",
        "formal/python/tools/post_plan_authority_coupling_review_path_report.py",
        "formal/python/tests/test_post_plan_authority_coupling_review_path_report.py"
    ]

    for ref in required_refs:
        assert ref in program_text
        assert ref in state_text or ref in roadmap_text or ref in inventory_text

    report = _read_json(REPO_ROOT / "formal" / "output" / "reports" / "post_plan_authority_coupling_review_path_20260418_v0.json")
    assert report["summary"]["terminal_outcome"] == "POST_PLAN_AUTHORITY_COUPLING_REVIEW_PATH_MATERIALIZED"
    assert report["summary"]["next_action"] == "EXECUTE_BOUNDED_COUPLING_REFINEMENT_PACKET_ONCE"
