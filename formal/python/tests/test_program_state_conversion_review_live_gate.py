from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
REGISTRATION_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "revised_signal_diagnostic_registration_20260411_v0.json"
)
CONVERSION_REVIEW_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "program_state_conversion_review_20260411_v0.json"
)
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"

CONVERSION_REFS = (
    "formal/docs/release/PROGRAM_STATE_CONVERSION_REVIEW_20260411_v0.json",
    "formal/output/reports/program_state_conversion_review_20260411_v0.json",
    "formal/python/tests/test_program_state_conversion_review_live_gate.py",
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_program_state_conversion_review_live_route_is_consistent() -> None:
    registration = _read_json(REGISTRATION_REPORT_PATH)
    conversion_review = _read_json(CONVERSION_REVIEW_REPORT_PATH)

    registration_summary = registration.get("summary", {})
    review_summary = conversion_review.get("summary", {})
    review_inputs = conversion_review.get("objective_quality", {}).get("inputs", {})

    assert registration_summary.get("registration_outcome") == "REVISED_SIGNAL_REGISTERED_AS_DIAGNOSTIC_ONLY"
    assert registration_summary.get("signal_disposition") == "DIAGNOSTIC_ONLY"
    assert registration_summary.get("promotion_to_authoritative_blocked") is True
    assert registration_summary.get("next_action") == "EXECUTE_PROGRAM_STATE_CONVERSION_REVIEW"

    assert review_summary.get("review_outcome") == "DEEPER_BLOCKER_DEFINITION_REVIEW_REQUIRED"
    assert review_summary.get("q1") == "DEEPER_BLOCKER_DEFINITION_REVIEW_REQUIRED"
    assert review_summary.get("q2") == "THEORY_POSTURE_REVIEW_NOT_YET_REQUIRED"
    assert review_summary.get("q3") == "PAUSE_REFRAME_NOT_YET_REQUIRED"
    assert review_summary.get("no_loop_rule") == "ONE_PROGRAM_STATE_CONVERSION_REVIEW_ONLY"
    assert review_summary.get("no_further_pilot_loops_honored") is True
    assert review_summary.get("next_action") == "EXECUTE_DEEPER_BLOCKER_DEFINITION_REVIEW"

    assert review_inputs.get("registration_outcome") == "REVISED_SIGNAL_REGISTERED_AS_DIAGNOSTIC_ONLY"
    assert review_inputs.get("exhausted_explanations") == [
        "LOCAL_PACKET_SELECTION",
        "ARCHITECTURE_AND_UNIT_SELECTION",
        "MOVEMENT_SIGNAL_BLINDNESS",
    ]

    assert conversion_review.get("source_bundle", {}).get("revised_signal_diagnostic_registration_report") == (
        "formal/output/reports/revised_signal_diagnostic_registration_20260411_v0.json"
    )


def test_program_state_conversion_review_authority_pointers_are_pinned() -> None:
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)

    for ref in CONVERSION_REFS:
        assert ref in roadmap_text, f"Roadmap must pin {ref}."
        assert ref in state_text or ref in inventory_text, (
            f"Compact-State or central inventory must pin {ref}."
        )