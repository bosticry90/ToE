from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
POST_PILOT_DECISION_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "post_measurement_regime_pilot_decision_20260411_v0.json"
)
REGISTRATION_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "revised_signal_diagnostic_registration_20260411_v0.json"
)
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"

REGISTRATION_REFS = (
    "formal/docs/release/REVISED_SIGNAL_DIAGNOSTIC_REGISTRATION_20260411_v0.json",
    "formal/output/reports/revised_signal_diagnostic_registration_20260411_v0.json",
    "formal/python/tests/test_revised_signal_diagnostic_registration_live_gate.py",
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_revised_signal_diagnostic_registration_live_route_is_consistent() -> None:
    post_pilot_decision = _read_json(POST_PILOT_DECISION_REPORT_PATH)
    registration = _read_json(REGISTRATION_REPORT_PATH)

    decision_summary = post_pilot_decision.get("summary", {})
    registration_summary = registration.get("summary", {})
    registration_inputs = registration.get("objective_quality", {}).get("inputs", {})

    assert decision_summary.get("post_pilot_decision") == "RETAIN_REVISED_SIGNAL_AS_DIAGNOSTIC_ONLY"
    assert decision_summary.get("revised_signal_disposition") == "RETAIN_DIAGNOSTIC"
    assert decision_summary.get("new_signal_fired") is True
    assert decision_summary.get("retained_signal_fired") is False
    assert decision_summary.get("next_action") == "REGISTER_REVISED_SIGNAL_AS_DIAGNOSTIC_ONLY_AND_HOLD"

    assert registration_summary.get("registration_outcome") == "REVISED_SIGNAL_REGISTERED_AS_DIAGNOSTIC_ONLY"
    assert registration_summary.get("signal_id") == "SEAM_INTEGRATION_COVERAGE_DELTA_GT_0"
    assert registration_summary.get("signal_disposition") == "DIAGNOSTIC_ONLY"
    assert registration_summary.get("promotion_to_authoritative_blocked") is True
    assert (
        registration_summary.get("authoritative_signal_unchanged")
        == "BLOCKER_TOKEN_CHANGE_REMAINS_AUTHORITATIVE"
    )
    assert (
        registration_summary.get("diagnostic_use_scope")
        == "SEAM_INTEGRATION_COVERAGE_TRACKING_ONLY"
    )
    assert registration_summary.get("no_loop_rule") == "ONE_DIAGNOSTIC_SIGNAL_REGISTRATION_ONLY"
    assert registration_summary.get("no_further_pilot_loops_honored") is True
    assert registration_summary.get("next_action") == "EXECUTE_PROGRAM_STATE_CONVERSION_REVIEW"

    assert registration_inputs.get("post_pilot_decision") == "RETAIN_REVISED_SIGNAL_AS_DIAGNOSTIC_ONLY"
    assert registration_inputs.get("revised_signal_disposition") == "RETAIN_DIAGNOSTIC"
    assert registration_inputs.get("signal_id") == "SEAM_INTEGRATION_COVERAGE_DELTA_GT_0"
    assert registration_inputs.get("signal_disposition") == "DIAGNOSTIC_ONLY"
    assert registration_inputs.get("promotion_to_authoritative_blocked") is True
    assert registration_inputs.get("no_further_pilot_loops_honored") is True

    assert registration.get("source_bundle", {}).get("post_measurement_regime_pilot_decision_report") == (
        "formal/output/reports/post_measurement_regime_pilot_decision_20260411_v0.json"
    )


def test_revised_signal_diagnostic_registration_authority_pointers_are_pinned() -> None:
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)

    for ref in REGISTRATION_REFS:
        assert ref in roadmap_text, f"Roadmap must pin {ref}."
        assert ref in state_text or ref in inventory_text, (
            f"Compact-State or central inventory must pin {ref}."
        )