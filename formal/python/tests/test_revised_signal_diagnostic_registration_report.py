from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import revised_signal_diagnostic_registration_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _seed(
    tmp_path: Path,
    *,
    post_pilot_decision: str = "RETAIN_REVISED_SIGNAL_AS_DIAGNOSTIC_ONLY",
    revised_signal_disposition: str = "RETAIN_DIAGNOSTIC",
) -> tuple[Path, object]:
    """Return (declaration_path, original_repo_root)."""
    reports_dir = tmp_path / "formal" / "output" / "reports"
    reports_dir.mkdir(parents=True, exist_ok=True)

    pilot_decision_path = reports_dir / "post_measurement_regime_pilot_decision_20260411_v0.json"
    _write_json(
        pilot_decision_path,
        {
            "summary": {
                "post_pilot_decision": post_pilot_decision,
                "revised_signal_disposition": revised_signal_disposition,
                "new_signal_fired": True,
                "retained_signal_fired": False,
                "no_loop_rule": "ONE_POST_PILOT_DECISION_ONLY",
                "no_further_pilot_loops_policy": "NO_FURTHER_MEASUREMENT_REGIME_PILOT_LOOPS_UNTIL_DECISION_RESOLVED",
                "next_action": "REGISTER_REVISED_SIGNAL_AS_DIAGNOSTIC_ONLY_AND_HOLD",
            }
        },
    )

    declaration_path = (
        tmp_path / "formal" / "docs" / "release"
        / "REVISED_SIGNAL_DIAGNOSTIC_REGISTRATION_20260411_v0.json"
    )
    declaration_path.parent.mkdir(parents=True, exist_ok=True)
    _write_json(
        declaration_path,
        {
            "schema_id": "REVISED_SIGNAL_DIAGNOSTIC_REGISTRATION_20260411_v0",
            "required_inputs": {
                "post_measurement_regime_pilot_decision_report": "formal/output/reports/post_measurement_regime_pilot_decision_20260411_v0.json",
            },
            "signal_to_register": {
                "signal_id": "SEAM_INTEGRATION_COVERAGE_DELTA_GT_0",
                "signal_origin": "BOUNDED_MEASUREMENT_REGIME_PILOT_20260411",
                "signal_description": "Transport witness bound AND bridge object materialized for target seam row.",
                "pilot_outcome": "FIRED_IN_PILOT_FOR_ROW_SEAM_QM_STAT_001",
            },
            "registration_policy": {
                "signal_disposition": "DIAGNOSTIC_ONLY",
                "promotion_to_authoritative_blocked": True,
                "promotion_block_reason": "BLOCKER_TOKEN_CHANGE_DID_NOT_FIRE_IN_PILOT_PROMOTION_REQUIRES_BOTH_SIGNALS",
                "authoritative_signal_unchanged": "BLOCKER_TOKEN_CHANGE_REMAINS_AUTHORITATIVE",
                "diagnostic_use_authorized": True,
                "diagnostic_use_scope": "SEAM_INTEGRATION_COVERAGE_TRACKING_ONLY",
                "no_loop_rule": "ONE_DIAGNOSTIC_SIGNAL_REGISTRATION_ONLY",
                "no_further_pilot_loops_honored": True,
            },
            "next_program_step": {
                "next_action": "EXECUTE_PROGRAM_STATE_CONVERSION_REVIEW",
                "rationale": "Three upstream explanations for non-movement have been tested and exhausted.",
            },
        },
    )

    original = tool.REPO_ROOT
    tool.REPO_ROOT = tmp_path
    return declaration_path, original


def _run(tmp_path: Path, **seed_kwargs) -> dict:
    declaration_path, original = _seed(tmp_path, **seed_kwargs)
    try:
        return tool.build_report(
            declaration_path=declaration_path,
            captured_at_utc="2026-04-11T00:00:00Z",
        )
    finally:
        tool.REPO_ROOT = original


def test_registration_outcome_retain_diagnostic(tmp_path: Path) -> None:
    """When post-pilot decision is RETAIN_REVISED_SIGNAL_AS_DIAGNOSTIC_ONLY, signal must be registered as diagnostic-only."""
    report = _run(tmp_path)
    summary = report["summary"]

    assert summary["registration_outcome"] == "REVISED_SIGNAL_REGISTERED_AS_DIAGNOSTIC_ONLY"
    assert summary["signal_id"] == "SEAM_INTEGRATION_COVERAGE_DELTA_GT_0"
    assert summary["signal_disposition"] == "DIAGNOSTIC_ONLY"
    assert summary["promotion_to_authoritative_blocked"] is True
    assert summary["authoritative_signal_unchanged"] == "BLOCKER_TOKEN_CHANGE_REMAINS_AUTHORITATIVE"
    assert summary["no_loop_rule"] == "ONE_DIAGNOSTIC_SIGNAL_REGISTRATION_ONLY"
    assert summary["no_further_pilot_loops_honored"] is True
    assert summary["next_action"] == "EXECUTE_PROGRAM_STATE_CONVERSION_REVIEW"


def test_registration_blocked_when_prerequisite_missing(tmp_path: Path) -> None:
    """When post-pilot decision is not RETAIN, registration outcome must be BLOCKED."""
    report = _run(
        tmp_path,
        post_pilot_decision="ROLL_BACK_REVISED_SIGNAL_FOR_PROMOTION_USE",
        revised_signal_disposition="ROLL_BACK",
    )
    summary = report["summary"]

    assert summary["registration_outcome"] == "REGISTRATION_BLOCKED_MISSING_PREREQUISITE"
