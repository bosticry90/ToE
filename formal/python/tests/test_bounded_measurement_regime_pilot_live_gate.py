from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
TRANSITION_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "post_posture_review_program_mode_transition_20260411_v0.json"
)
EXECUTION_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "bounded_measurement_regime_pilot_execution_20260411_v0.json"
)
RULING_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "bounded_measurement_regime_pilot_ruling_20260411_v0.json"
)
POST_DECISION_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "post_measurement_regime_pilot_decision_20260411_v0.json"
)
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"

PILOT_STACK_REFS = (
    "formal/docs/release/BOUNDED_MEASUREMENT_REGIME_PILOT_EXECUTION_20260411_v0.json",
    "formal/output/reports/bounded_measurement_regime_pilot_execution_20260411_v0.json",
    "formal/docs/release/BOUNDED_MEASUREMENT_REGIME_PILOT_RULING_20260411_v0.json",
    "formal/output/reports/bounded_measurement_regime_pilot_ruling_20260411_v0.json",
    "formal/docs/release/POST_MEASUREMENT_REGIME_PILOT_DECISION_20260411_v0.json",
    "formal/output/reports/post_measurement_regime_pilot_decision_20260411_v0.json",
    "formal/python/tests/test_bounded_measurement_regime_pilot_live_gate.py",
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_bounded_measurement_regime_pilot_live_route_is_consistent() -> None:
    transition = _read_json(TRANSITION_REPORT_PATH)
    execution = _read_json(EXECUTION_REPORT_PATH)
    ruling = _read_json(RULING_REPORT_PATH)
    post_decision = _read_json(POST_DECISION_REPORT_PATH)

    transition_summary = transition.get("summary", {})
    execution_summary = execution.get("summary", {})
    ruling_summary = ruling.get("summary", {})
    post_decision_summary = post_decision.get("summary", {})

    assert transition_summary.get("transition_outcome") == "MEASUREMENT_REGIME_TRANSITION_MATERIALIZED"
    assert transition_summary.get("pilot_tranche") == "ONE_SEAM_ROW_RECOMPUTE_UNDER_REVISED_SIGNALS"
    assert transition_summary.get("next_action") == "EXECUTE_BOUNDED_MEASUREMENT_REGIME_PILOT_ONCE"

    assert execution_summary.get("execution_classification") == "PILOT_VALID_BUT_NONMOVING"
    assert execution_summary.get("new_signal_fired") is True
    assert execution_summary.get("retained_signal_fired") is False
    assert execution_summary.get("blocker_movement_signal") == "NEW_SIGNAL_ONLY"
    assert execution_summary.get("no_loop_rule") == "ONE_BOUNDED_MEASUREMENT_REGIME_PILOT_ONLY"
    assert execution_summary.get("next_action") == "EMIT_BOUNDED_MEASUREMENT_REGIME_PILOT_RULING"

    assert ruling_summary.get("pilot_ruling") == "REVISED_SIGNAL_VALID_BUT_NONMOVING"
    assert ruling_summary.get("execution_classification") == "PILOT_VALID_BUT_NONMOVING"
    assert ruling_summary.get("new_signal_fired") is True
    assert ruling_summary.get("retained_signal_fired") is False
    assert ruling_summary.get("next_action") == "ASSESS_PILOT_RESULT_AND_DECIDE_ROLLBACK_OR_HOLD"

    assert post_decision_summary.get("post_pilot_decision") == "RETAIN_REVISED_SIGNAL_AS_DIAGNOSTIC_ONLY"
    assert post_decision_summary.get("revised_signal_disposition") == "RETAIN_DIAGNOSTIC"
    assert post_decision_summary.get("new_signal_fired") is True
    assert post_decision_summary.get("retained_signal_fired") is False
    assert post_decision_summary.get("no_loop_rule") == "ONE_POST_PILOT_DECISION_ONLY"
    assert post_decision_summary.get("next_action") == "REGISTER_REVISED_SIGNAL_AS_DIAGNOSTIC_ONLY_AND_HOLD"

    assert execution.get("source_bundle", {}).get("post_posture_review_program_mode_transition_report") == (
        "formal/output/reports/post_posture_review_program_mode_transition_20260411_v0.json"
    )
    assert ruling.get("source_bundle", {}).get("bounded_measurement_regime_pilot_execution_report") == (
        "formal/output/reports/bounded_measurement_regime_pilot_execution_20260411_v0.json"
    )
    assert post_decision.get("source_bundle", {}).get("bounded_measurement_regime_pilot_ruling_report") == (
        "formal/output/reports/bounded_measurement_regime_pilot_ruling_20260411_v0.json"
    )


def test_bounded_measurement_regime_pilot_authority_pointers_are_pinned() -> None:
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)

    for ref in PILOT_STACK_REFS:
        assert ref in roadmap_text, f"Roadmap must pin {ref}."
        assert ref in state_text or ref in inventory_text, (
            f"Compact-State or central inventory must pin {ref}."
        )