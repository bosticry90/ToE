from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
POST_ALIGNMENT_DECISION_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "science_post_architecture_alignment_decision_20260411_v0.json"
)
POSTURE_REVIEW_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "program_posture_review_packet_20260411_v0.json"
)
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"

POSTURE_REVIEW_REFS = (
    "formal/docs/release/PROGRAM_POSTURE_REVIEW_PACKET_20260411_v0.json",
    "formal/output/reports/program_posture_review_packet_20260411_v0.json",
    "formal/python/tests/test_program_posture_review_live_gate.py",
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_program_posture_review_live_route_is_consistent() -> None:
    post_alignment_decision = _read_json(POST_ALIGNMENT_DECISION_REPORT_PATH)
    posture_review = _read_json(POSTURE_REVIEW_REPORT_PATH)

    decision_summary = post_alignment_decision.get("summary", {})
    posture_summary = posture_review.get("summary", {})
    posture_inputs = posture_review.get("objective_quality", {}).get("inputs", {})

    assert decision_summary.get("post_architecture_decision") == "PROGRAM_POSTURE_REVIEW_REQUIRED"
    assert decision_summary.get("selected_next_program_mode") == "PROGRAM_POSTURE_REVIEW"
    assert decision_summary.get("next_action") == "MATERIALIZE_PROGRAM_POSTURE_REVIEW_PACKET"

    assert posture_summary.get("packet_outcome") == "PROGRAM_POSTURE_REVIEW_PACKET_MATERIALIZED"
    assert posture_summary.get("measurement_regime_fit_for_purpose") is False
    assert posture_summary.get("formal_organization_outpacing_conversion") is True
    assert posture_summary.get("selected_next_program_mode") == "REORIENT_MEASUREMENT_REGIME"
    assert posture_summary.get("no_loop_rule") == "ONE_POSTURE_REVIEW_ONLY"
    assert posture_summary.get("next_action") == "EXECUTE_POST_POSTURE_REVIEW_PROGRAM_MODE_TRANSITION"

    assert posture_inputs.get("post_architecture_decision") == "PROGRAM_POSTURE_REVIEW_REQUIRED"
    assert posture_inputs.get("alignment_ruling") == "EXHAUSTED_UNDER_CURRENT_FILTER"
    assert posture_inputs.get("blocker_conversion_failure_location") == "MASTER_ACTION_RESIDUAL_EXTRACTION"
    assert posture_inputs.get("nonmoving_attack_class_count") == 4
    assert posture_inputs.get("nonmoving_count_threshold") == 4
    assert posture_inputs.get("blocker_movement_ever_observed") is False

    review_answers = posture_inputs.get("review_answers", [])
    assert {item.get("question_id"): item.get("answer") for item in review_answers} == {
        "Q1": "MEASUREMENT_REGIME_REQUIRES_REVISION",
        "Q2": "FORMAL_ORGANIZATION_OUTPACING_SCIENTIFIC_CONVERSION",
        "Q3": "REORIENT_MEASUREMENT_REGIME",
    }

    assert posture_review.get("source_bundle", {}).get("science_post_architecture_alignment_decision_report") == (
        "formal/output/reports/science_post_architecture_alignment_decision_20260411_v0.json"
    )


def test_program_posture_review_authority_pointers_are_pinned() -> None:
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)

    for ref in POSTURE_REVIEW_REFS:
        assert ref in roadmap_text, f"Roadmap must pin {ref}."
        assert ref in state_text or ref in inventory_text, (
            f"Compact-State or central inventory must pin {ref}."
        )