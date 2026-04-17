from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
CONVERSION_REVIEW_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "program_state_conversion_review_20260411_v0.json"
)
DEEPER_REVIEW_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "deeper_blocker_definition_review_20260411_v0.json"
)
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"

DEEPER_REVIEW_REFS = (
    "formal/docs/release/DEEPER_BLOCKER_DEFINITION_REVIEW_20260411_v0.json",
    "formal/output/reports/deeper_blocker_definition_review_20260411_v0.json",
    "formal/python/tests/test_deeper_blocker_definition_review_live_gate.py",
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_deeper_blocker_definition_review_live_route_is_consistent() -> None:
    conversion_review = _read_json(CONVERSION_REVIEW_REPORT_PATH)
    deeper_review = _read_json(DEEPER_REVIEW_REPORT_PATH)

    conversion_summary = conversion_review.get("summary", {})
    deeper_summary = deeper_review.get("summary", {})
    deeper_inputs = deeper_review.get("objective_quality", {}).get("inputs", {})

    assert conversion_summary.get("review_outcome") == "DEEPER_BLOCKER_DEFINITION_REVIEW_REQUIRED"
    assert conversion_summary.get("next_action") == "EXECUTE_DEEPER_BLOCKER_DEFINITION_REVIEW"

    assert deeper_summary.get("review_outcome") == "DEEPER_BLOCKER_DEFINITION_REVIEW_MATERIALIZED"
    assert (
        deeper_summary.get("q1")
        == "BLOCKER_TOKEN_CHANGE_DEFINITION_TOO_STRICT_OR_MONITORING_WRONG_ARTIFACT"
    )
    assert (
        deeper_summary.get("q2")
        == "REVISED_BLOCKER_DEF_SEAM_ROW_STATE_TRANSITION_WITH_TRANSPORT_COHERENCE_CHECK"
    )
    assert (
        deeper_summary.get("q3")
        == "ONE_SEAM_ROW_BLOCKER_DEFINITION_TEST_UNDER_REVISED_CRITERIA"
    )
    assert deeper_summary.get("current_authoritative_signal") == "BLOCKER_TOKEN_CHANGE_REMAINS_AUTHORITATIVE"
    assert deeper_summary.get("authoritative_signal_status") == "NEVER_FIRED_IN_ANY_EXECUTION"
    assert (
        deeper_summary.get("revised_blocker_definition_candidate")
        == "REVISED_BLOCKER_DEF_SEAM_ROW_STATE_TRANSITION_WITH_TRANSPORT_COHERENCE_CHECK"
    )
    assert deeper_summary.get("bounded_follow_on_packet") == "ONE_SEAM_ROW_BLOCKER_DEFINITION_TEST_UNDER_REVISED_CRITERIA"
    assert deeper_summary.get("no_loop_rule") == "ONE_DEEPER_BLOCKER_DEFINITION_REVIEW_ONLY"
    assert deeper_summary.get("next_action") == "EXECUTE_BOUNDED_BLOCKER_DEFINITION_TEST_PACKET_ONCE"

    assert deeper_inputs.get("conversion_review_outcome") == "DEEPER_BLOCKER_DEFINITION_REVIEW_REQUIRED"
    assert deeper_inputs.get("current_authoritative_signal") == "BLOCKER_TOKEN_CHANGE_REMAINS_AUTHORITATIVE"
    assert deeper_inputs.get("diagnostic_signal") == "SEAM_INTEGRATION_COVERAGE_DELTA_GT_0"
    assert deeper_inputs.get("diagnostic_signal_status") == "FIRED_IN_BOUNDED_PILOT"
    assert deeper_inputs.get("signal_status") == "NEVER_FIRED_IN_ANY_EXECUTION"

    assert deeper_review.get("source_bundle", {}).get("program_state_conversion_review_report") == (
        "formal/output/reports/program_state_conversion_review_20260411_v0.json"
    )


def test_deeper_blocker_definition_review_authority_pointers_are_pinned() -> None:
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)

    for ref in DEEPER_REVIEW_REFS:
        assert ref in roadmap_text, f"Roadmap must pin {ref}."
        assert ref in state_text or ref in inventory_text, (
            f"Compact-State or central inventory must pin {ref}."
        )