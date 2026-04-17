from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
RULING_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "bounded_blocker_definition_test_ruling_20260411_v0.json"
)
DECISION_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "post_blocker_definition_test_decision_20260411_v0.json"
)
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"

POST_TEST_DECISION_REFS = (
    "formal/docs/release/POST_BLOCKER_DEFINITION_TEST_DECISION_20260411_v0.json",
    "formal/output/reports/post_blocker_definition_test_decision_20260411_v0.json",
    "formal/python/tests/test_post_blocker_definition_test_decision_live_gate.py",
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_post_blocker_definition_test_decision_live_route_is_consistent() -> None:
    ruling = _read_json(RULING_REPORT_PATH)
    decision = _read_json(DECISION_REPORT_PATH)

    ruling_summary = ruling.get("summary", {})
    decision_summary = decision.get("summary", {})
    decision_inputs = decision.get("objective_quality", {}).get("inputs", {})

    assert ruling_summary.get("test_ruling") == "REVISED_BLOCKER_DEF_VALID_BUT_NONMOVING"
    assert ruling_summary.get("revised_blocker_def_fires") is True
    assert ruling_summary.get("authoritative_fires") is False
    assert ruling_summary.get("next_action") == "ASSESS_BLOCKER_DEFINITION_TEST_RULING_AND_DECIDE_PROMOTION_OR_HOLD"

    assert (
        decision_summary.get("post_test_decision")
        == "HOLD_REVISED_BLOCKER_DEF_AS_SECONDARY_REQUIRE_AUTHORITY_COUPLING_REVIEW"
    )
    assert decision_summary.get("revised_signal_disposition") == "HOLD_SECONDARY"
    assert decision_summary.get("test_ruling") == "REVISED_BLOCKER_DEF_VALID_BUT_NONMOVING"
    assert decision_summary.get("revised_blocker_def_fires") is True
    assert decision_summary.get("authoritative_fires") is False
    assert decision_summary.get("no_loop_rule") == "ONE_POST_BLOCKER_DEFINITION_TEST_DECISION_ONLY"
    assert decision_summary.get("no_further_blocker_testing_until_routing_resolved") is True
    assert decision_summary.get("next_action") == "REQUIRE_ONE_BOUNDED_AUTHORITY_COUPLING_REVIEW"

    route_assessment = decision_inputs.get("candidate_route_assessment", [])
    assert any(
        route.get("route_id") == "HOLD_ROUTE" and route.get("supported") is True
        for route in route_assessment
    )
    assert any(
        route.get("route_id") == "COUPLING_REFINEMENT_ROUTE" and route.get("supported") is False
        for route in route_assessment
    )
    assert any(
        route.get("route_id") == "ESCALATE_ROUTE" and route.get("supported") is False
        for route in route_assessment
    )

    assert decision.get("source_bundle", {}).get("bounded_blocker_definition_test_ruling_report") == (
        "formal/output/reports/bounded_blocker_definition_test_ruling_20260411_v0.json"
    )


def test_post_blocker_definition_test_decision_authority_pointers_are_pinned() -> None:
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)

    for ref in POST_TEST_DECISION_REFS:
        assert ref in roadmap_text, f"Roadmap must pin {ref}."
        assert ref in state_text or ref in inventory_text, (
            f"Compact-State or central inventory must pin {ref}."
        )