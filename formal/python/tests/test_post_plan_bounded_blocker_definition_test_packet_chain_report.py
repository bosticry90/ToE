from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import post_plan_bounded_blocker_definition_test_packet_chain_report as tool


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
                "post_plan_successor_tranche_report": "formal/output/reports/post_plan_deeper_blocker_definition_review_successor_tranche_20260418_v0.json",
                "bounded_blocker_definition_test_execution_report": "formal/output/reports/bounded_blocker_definition_test_execution_20260411_v0.json",
                "bounded_blocker_definition_test_ruling_report": "formal/output/reports/bounded_blocker_definition_test_ruling_20260411_v0.json",
                "post_blocker_definition_test_decision_report": "formal/output/reports/post_blocker_definition_test_decision_20260411_v0.json",
                "authority_coupling_review_declaration": "formal/docs/release/AUTHORITY_COUPLING_REVIEW_20260411_v0.json"
            },
            "execution_policy": {
                "required_successor_outcome": "POST_PLAN_DEEPER_BLOCKER_DEFINITION_REVIEW_SUCCESSOR_TRANCHE_MATERIALIZED",
                "required_successor_next_action": "EXECUTE_BOUNDED_BLOCKER_DEFINITION_TEST_PACKET_ONCE",
                "required_execution_classification": "EXECUTION_VALID_REVISED_DEF_FIRES_AUTHORITATIVE_BLOCKED",
                "required_ruling": "REVISED_BLOCKER_DEF_VALID_BUT_NONMOVING",
                "required_post_decision": "HOLD_REVISED_BLOCKER_DEF_AS_SECONDARY_REQUIRE_AUTHORITY_COUPLING_REVIEW",
                "required_post_next_action": "REQUIRE_ONE_BOUNDED_AUTHORITY_COUPLING_REVIEW",
                "required_authority_review_basis": "POST_BLOCKER_DEFINITION_TEST_DECISION_HOLD_SECONDARY_REQUIRE_COUPLING_REVIEW"
            },
            "outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_POST_PLAN_BOUNDED_BLOCKER_DEFINITION_TEST_PACKET_CHAIN_OUTCOME",
                "no_loop_rule": "ONE_POST_PLAN_BOUNDED_BLOCKER_DEFINITION_TEST_PACKET_CHAIN_ONLY",
                "allowed_outcomes": [
                    "POST_PLAN_BOUNDED_BLOCKER_DEFINITION_TEST_PACKET_CHAIN_REVEALS_MEANINGFUL_MOVEMENT",
                    "POST_PLAN_BOUNDED_BLOCKER_DEFINITION_TEST_PACKET_CHAIN_VALID_BUT_NONMOVING",
                    "POST_PLAN_BOUNDED_BLOCKER_DEFINITION_TEST_PACKET_CHAIN_NOT_FIT_FOR_AUTHORITY_USE",
                    "POST_PLAN_BOUNDED_BLOCKER_DEFINITION_TEST_PACKET_CHAIN_BLOCKED",
                    "POST_PLAN_BOUNDED_BLOCKER_DEFINITION_TEST_PACKET_CHAIN_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_POST_PLAN_BOUNDED_BLOCKER_DEFINITION_TEST_PACKET_CHAIN_REPAIR"
                ],
                "default_outcome": "POST_PLAN_BOUNDED_BLOCKER_DEFINITION_TEST_PACKET_CHAIN_EVIDENCE_INCOMPLETE"
            }
        }
    )


def _seed_inputs(root: Path, *, not_fit: bool = False) -> None:
    _write_json(root / "formal" / "output" / "reports" / "post_plan_deeper_blocker_definition_review_successor_tranche_20260418_v0.json", {"summary": {"terminal_outcome": "POST_PLAN_DEEPER_BLOCKER_DEFINITION_REVIEW_SUCCESSOR_TRANCHE_MATERIALIZED", "next_action": "EXECUTE_BOUNDED_BLOCKER_DEFINITION_TEST_PACKET_ONCE", "bounded_follow_on_packet": "ONE_SEAM_ROW_BLOCKER_DEFINITION_TEST_UNDER_REVISED_CRITERIA"}})
    _write_json(root / "formal" / "output" / "reports" / "bounded_blocker_definition_test_execution_20260411_v0.json", {"summary": {"target_row_id": "ROW-SEAM-QM-STAT-001", "candidate_blocker_definition": "REVISED_BLOCKER_DEF_SEAM_ROW_STATE_TRANSITION_WITH_TRANSPORT_COHERENCE_CHECK", "execution_classification": "EXECUTION_VALID_REVISED_DEF_FIRES_AUTHORITATIVE_BLOCKED", "revised_blocker_def_fires": True}})
    ruling = "REVISED_BLOCKER_DEF_NOT_FIT_FOR_AUTHORITY_USE" if not_fit else "REVISED_BLOCKER_DEF_VALID_BUT_NONMOVING"
    decision = "ESCALATE_TO_THEORY_POSTURE_OR_PROGRAM_PAUSE_REVIEW" if not_fit else "HOLD_REVISED_BLOCKER_DEF_AS_SECONDARY_REQUIRE_AUTHORITY_COUPLING_REVIEW"
    decision_next = "ESCALATE_TO_THEORY_POSTURE_OR_PROGRAM_PAUSE_REVIEW" if not_fit else "REQUIRE_ONE_BOUNDED_AUTHORITY_COUPLING_REVIEW"
    _write_json(root / "formal" / "output" / "reports" / "bounded_blocker_definition_test_ruling_20260411_v0.json", {"summary": {"test_ruling": ruling}})
    _write_json(root / "formal" / "output" / "reports" / "post_blocker_definition_test_decision_20260411_v0.json", {"summary": {"post_test_decision": decision, "next_action": decision_next}})
    _write_json(root / "formal" / "docs" / "release" / "AUTHORITY_COUPLING_REVIEW_20260411_v0.json", {"review_basis": "POST_BLOCKER_DEFINITION_TEST_DECISION_HOLD_SECONDARY_REQUIRE_COUPLING_REVIEW"})


def test_packet_chain_reports_valid_but_nonmoving_from_live_shape(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "POST_PLAN_BOUNDED_BLOCKER_DEFINITION_TEST_PACKET_CHAIN_20260418_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, not_fit=False)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "POST_PLAN_BOUNDED_BLOCKER_DEFINITION_TEST_PACKET_CHAIN_VALID_BUT_NONMOVING"
    assert report["summary"]["next_action"] == "REQUIRE_ONE_BOUNDED_AUTHORITY_COUPLING_REVIEW"


def test_packet_chain_reports_not_fit_when_ruling_fails(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "POST_PLAN_BOUNDED_BLOCKER_DEFINITION_TEST_PACKET_CHAIN_20260418_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, not_fit=True)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "POST_PLAN_BOUNDED_BLOCKER_DEFINITION_TEST_PACKET_CHAIN_NOT_FIT_FOR_AUTHORITY_USE"


def test_live_packet_chain_registered_in_mirrors() -> None:
    program_text = _read(PROGRAM_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)

    required_refs = [
        "formal/docs/release/POST_PLAN_BOUNDED_BLOCKER_DEFINITION_TEST_PACKET_CHAIN_20260418_v0.json",
        "formal/output/reports/post_plan_bounded_blocker_definition_test_packet_chain_20260418_v0.json",
        "formal/python/tools/post_plan_bounded_blocker_definition_test_packet_chain_report.py",
        "formal/python/tests/test_post_plan_bounded_blocker_definition_test_packet_chain_report.py"
    ]

    for ref in required_refs:
        assert ref in program_text
        assert ref in state_text or ref in roadmap_text or ref in inventory_text

    report = _read_json(REPO_ROOT / "formal" / "output" / "reports" / "post_plan_bounded_blocker_definition_test_packet_chain_20260418_v0.json")
    assert report["summary"]["terminal_outcome"] == "POST_PLAN_BOUNDED_BLOCKER_DEFINITION_TEST_PACKET_CHAIN_VALID_BUT_NONMOVING"
    assert report["summary"]["next_action"] == "REQUIRE_ONE_BOUNDED_AUTHORITY_COUPLING_REVIEW"
