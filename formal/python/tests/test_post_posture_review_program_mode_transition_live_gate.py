from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
POSTURE_REVIEW_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "program_posture_review_packet_20260411_v0.json"
)
TRANSITION_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "post_posture_review_program_mode_transition_20260411_v0.json"
)
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"

TRANSITION_REFS = (
    "formal/docs/release/POST_POSTURE_REVIEW_PROGRAM_MODE_TRANSITION_20260411_v0.json",
    "formal/output/reports/post_posture_review_program_mode_transition_20260411_v0.json",
    "formal/python/tests/test_post_posture_review_program_mode_transition_live_gate.py",
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_post_posture_review_program_mode_transition_live_route_is_consistent() -> None:
    posture_review = _read_json(POSTURE_REVIEW_REPORT_PATH)
    transition = _read_json(TRANSITION_REPORT_PATH)

    posture_summary = posture_review.get("summary", {})
    transition_summary = transition.get("summary", {})
    transition_inputs = transition.get("objective_quality", {}).get("inputs", {})

    assert posture_summary.get("packet_outcome") == "PROGRAM_POSTURE_REVIEW_PACKET_MATERIALIZED"
    assert posture_summary.get("selected_next_program_mode") == "REORIENT_MEASUREMENT_REGIME"
    assert posture_summary.get("next_action") == "EXECUTE_POST_POSTURE_REVIEW_PROGRAM_MODE_TRANSITION"

    assert transition_summary.get("transition_outcome") == "MEASUREMENT_REGIME_TRANSITION_MATERIALIZED"
    assert (
        transition_summary.get("measurement_defect")
        == "BLOCKER_MOVEMENT_SIGNALS_NEVER_TRIGGERED_UNDER_ANY_ATTACK_CLASS"
    )
    assert (
        transition_summary.get("new_blocker_movement_signal")
        == "SEAM_INTEGRATION_COVERAGE_DELTA_GT_0"
    )
    assert (
        transition_summary.get("retained_blocker_movement_signal")
        == "BLOCKER_TOKEN_CHANGE_REMAINS_AUTHORITATIVE"
    )
    assert (
        transition_summary.get("pilot_tranche")
        == "ONE_SEAM_ROW_RECOMPUTE_UNDER_REVISED_SIGNALS"
    )
    assert transition_summary.get("no_loop_rule") == "ONE_BOUNDED_MEASUREMENT_REGIME_PILOT_ONLY"
    assert transition_summary.get("next_action") == "EXECUTE_BOUNDED_MEASUREMENT_REGIME_PILOT_ONCE"

    assert transition_inputs.get("posture_review_outcome") == "PROGRAM_POSTURE_REVIEW_PACKET_MATERIALIZED"
    assert transition_inputs.get("posture_review_selected_mode") == "REORIENT_MEASUREMENT_REGIME"
    assert (
        transition_inputs.get("measurement_defect")
        == "BLOCKER_MOVEMENT_SIGNALS_NEVER_TRIGGERED_UNDER_ANY_ATTACK_CLASS"
    )
    assert transition_inputs.get("new_blocker_movement_signal") == "SEAM_INTEGRATION_COVERAGE_DELTA_GT_0"
    assert (
        transition_inputs.get("retained_blocker_movement_signal")
        == "BLOCKER_TOKEN_CHANGE_REMAINS_AUTHORITATIVE"
    )
    assert transition_inputs.get("pilot_tranche") == "ONE_SEAM_ROW_RECOMPUTE_UNDER_REVISED_SIGNALS"

    assert transition.get("source_bundle", {}).get("program_posture_review_packet_report") == (
        "formal/output/reports/program_posture_review_packet_20260411_v0.json"
    )


def test_post_posture_review_program_mode_transition_authority_pointers_are_pinned() -> None:
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)

    for ref in TRANSITION_REFS:
        assert ref in roadmap_text, f"Roadmap must pin {ref}."
        assert ref in state_text or ref in inventory_text, (
            f"Compact-State or central inventory must pin {ref}."
        )