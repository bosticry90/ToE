from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
DEEPER_REVIEW_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "deeper_blocker_definition_review_20260411_v0.json"
)
EXECUTION_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "bounded_blocker_definition_test_execution_20260411_v0.json"
)
RULING_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "bounded_blocker_definition_test_ruling_20260411_v0.json"
)
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"

BLOCKER_TEST_REFS = (
    "formal/docs/release/BOUNDED_BLOCKER_DEFINITION_TEST_EXECUTION_20260411_v0.json",
    "formal/output/reports/bounded_blocker_definition_test_execution_20260411_v0.json",
    "formal/docs/release/BOUNDED_BLOCKER_DEFINITION_TEST_RULING_20260411_v0.json",
    "formal/output/reports/bounded_blocker_definition_test_ruling_20260411_v0.json",
    "formal/python/tests/test_bounded_blocker_definition_test_live_gate.py",
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_bounded_blocker_definition_test_live_route_is_consistent() -> None:
    deeper_review = _read_json(DEEPER_REVIEW_REPORT_PATH)
    execution = _read_json(EXECUTION_REPORT_PATH)
    ruling = _read_json(RULING_REPORT_PATH)

    deeper_summary = deeper_review.get("summary", {})
    execution_summary = execution.get("summary", {})
    ruling_summary = ruling.get("summary", {})
    execution_inputs = execution.get("objective_quality", {}).get("inputs", {})

    assert deeper_summary.get("review_outcome") == "DEEPER_BLOCKER_DEFINITION_REVIEW_MATERIALIZED"
    assert deeper_summary.get("bounded_follow_on_packet") == "ONE_SEAM_ROW_BLOCKER_DEFINITION_TEST_UNDER_REVISED_CRITERIA"
    assert deeper_summary.get("next_action") == "EXECUTE_BOUNDED_BLOCKER_DEFINITION_TEST_PACKET_ONCE"

    assert execution_summary.get("execution_classification") == "EXECUTION_VALID_REVISED_DEF_FIRES_AUTHORITATIVE_BLOCKED"
    assert execution_summary.get("revised_blocker_def_fires") is True
    assert execution_summary.get("authoritative_fires") is False
    assert execution_summary.get("blocker_signal") == "REVISED_DEF_ONLY"
    assert (
        execution_summary.get("candidate_blocker_definition")
        == "REVISED_BLOCKER_DEF_SEAM_ROW_STATE_TRANSITION_WITH_TRANSPORT_COHERENCE_CHECK"
    )
    assert execution_summary.get("retained_authoritative_signal") == "BLOCKER_TOKEN_CHANGE_REMAINS_AUTHORITATIVE"
    assert execution_summary.get("target_row_id") == "ROW-SEAM-QM-STAT-001"
    assert execution_summary.get("no_loop_rule") == "ONE_BOUNDED_BLOCKER_DEFINITION_TEST_EXECUTION_ONLY"
    assert execution_summary.get("next_action") == "EMIT_BOUNDED_BLOCKER_DEFINITION_TEST_RULING"

    assert ruling_summary.get("test_ruling") == "REVISED_BLOCKER_DEF_VALID_BUT_NONMOVING"
    assert ruling_summary.get("revised_blocker_def_fires") is True
    assert ruling_summary.get("authoritative_fires") is False
    assert ruling_summary.get("blocker_signal") == "REVISED_DEF_ONLY"
    assert (
        ruling_summary.get("candidate_blocker_definition")
        == "REVISED_BLOCKER_DEF_SEAM_ROW_STATE_TRANSITION_WITH_TRANSPORT_COHERENCE_CHECK"
    )
    assert ruling_summary.get("no_loop_rule") == "ONE_BOUNDED_BLOCKER_DEFINITION_TEST_RULING_ONLY"
    assert ruling_summary.get("next_action") == "ASSESS_BLOCKER_DEFINITION_TEST_RULING_AND_DECIDE_PROMOTION_OR_HOLD"

    assert execution_inputs.get("review_outcome") == "DEEPER_BLOCKER_DEFINITION_REVIEW_MATERIALIZED"
    assert execution_inputs.get("revised_blocker_def_fires") is True
    assert execution_inputs.get("authoritative_fires") is False

    assert execution.get("source_bundle", {}).get("deeper_blocker_definition_review_report") == (
        "formal/output/reports/deeper_blocker_definition_review_20260411_v0.json"
    )
    assert ruling.get("source_bundle", {}).get("bounded_blocker_definition_test_execution_report") == (
        "formal/output/reports/bounded_blocker_definition_test_execution_20260411_v0.json"
    )


def test_bounded_blocker_definition_test_authority_pointers_are_pinned() -> None:
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)

    for ref in BLOCKER_TEST_REFS:
        assert ref in roadmap_text, f"Roadmap must pin {ref}."
        assert ref in state_text or ref in inventory_text, (
            f"Compact-State or central inventory must pin {ref}."
        )