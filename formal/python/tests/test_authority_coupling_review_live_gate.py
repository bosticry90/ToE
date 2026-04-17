from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
POST_TEST_DECISION_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "post_blocker_definition_test_decision_20260411_v0.json"
)
COUPLING_REVIEW_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "authority_coupling_review_20260411_v0.json"
)
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"

COUPLING_REVIEW_REFS = (
    "formal/docs/release/AUTHORITY_COUPLING_REVIEW_20260411_v0.json",
    "formal/output/reports/authority_coupling_review_20260411_v0.json",
    "formal/python/tests/test_authority_coupling_review_live_gate.py",
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_authority_coupling_review_live_route_is_consistent() -> None:
    post_test_decision = _read_json(POST_TEST_DECISION_REPORT_PATH)
    coupling_review = _read_json(COUPLING_REVIEW_REPORT_PATH)

    decision_summary = post_test_decision.get("summary", {})
    review_summary = coupling_review.get("summary", {})
    review_inputs = coupling_review.get("objective_quality", {}).get("inputs", {})

    assert (
        decision_summary.get("post_test_decision")
        == "HOLD_REVISED_BLOCKER_DEF_AS_SECONDARY_REQUIRE_AUTHORITY_COUPLING_REVIEW"
    )
    assert decision_summary.get("revised_signal_disposition") == "HOLD_SECONDARY"
    assert decision_summary.get("next_action") == "REQUIRE_ONE_BOUNDED_AUTHORITY_COUPLING_REVIEW"

    assert review_summary.get("review_outcome") == "BOUNDED_COUPLING_REFINEMENT_JUSTIFIED"
    assert (
        review_summary.get("coupling_defect")
        == "REVISED_DEF_FIRES_WITHOUT_CORRESPONDING_BLOCKER_ARTIFACT_FLUX_IN_LEDGER"
    )
    assert (
        review_summary.get("coupling_boundedness")
        == "COUPLING_DEFECT_IS_SPECIFIC_AND_BOUNDED_BETWEEN_SEAM_AND_BLOCKER_ARTIFACT"
    )
    assert (
        review_summary.get("routing_decision")
        == "BOUNDED_COUPLING_REFINEMENT_JUSTIFIED_SEAM_ARTIFACT_BINDING_REVIEW"
    )
    assert review_summary.get("coupling_disposition") == "REFINE_COUPLING"
    assert (
        review_summary.get("revised_blocker_definition")
        == "REVISED_BLOCKER_DEF_SEAM_ROW_STATE_TRANSITION_WITH_TRANSPORT_COHERENCE_CHECK"
    )
    assert review_summary.get("authoritative_signal_status") == "NEVER_FIRES_IN_ANY_EXECUTION"
    assert review_summary.get("no_loop_rule") == "ONE_AUTHORITY_COUPLING_REVIEW_ONLY"
    assert review_summary.get("next_action") == "EXECUTE_BOUNDED_COUPLING_REFINEMENT_PACKET_ONCE"

    assert (
        review_inputs.get("decision_outcome")
        == "HOLD_REVISED_BLOCKER_DEF_AS_SECONDARY_REQUIRE_AUTHORITY_COUPLING_REVIEW"
    )
    assert review_inputs.get("coupling_is_bounded") is True
    assert review_inputs.get("coupling_escalate") is False

    assert coupling_review.get("source_bundle", {}).get("post_blocker_definition_test_decision_report") == (
        "formal/output/reports/post_blocker_definition_test_decision_20260411_v0.json"
    )


def test_authority_coupling_review_authority_pointers_are_pinned() -> None:
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)

    for ref in COUPLING_REVIEW_REFS:
        assert ref in roadmap_text, f"Roadmap must pin {ref}."
        assert ref in state_text or ref in inventory_text, (
            f"Compact-State or central inventory must pin {ref}."
        )