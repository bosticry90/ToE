from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import bounded_blocker_definition_test_execution_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _seed(
    tmp_path: Path,
    *,
    review_outcome: str = "DEEPER_BLOCKER_DEFINITION_REVIEW_MATERIALIZED",
    transport_witness_bound: bool = True,
    bridge_object_materialized: bool = True,
) -> tuple[Path, object]:
    """Return (declaration_path, original_repo_root)."""
    reports_dir = tmp_path / "formal" / "output" / "reports"
    reports_dir.mkdir(parents=True, exist_ok=True)

    review_path = reports_dir / "deeper_blocker_definition_review_20260411_v0.json"
    _write_json(
        review_path,
        {
            "summary": {
                "review_outcome": review_outcome,
                "q1": "BLOCKER_TOKEN_CHANGE_DEFINITION_TOO_STRICT_OR_MONITORING_WRONG_ARTIFACT",
                "q2": "REVISED_BLOCKER_DEF_SEAM_ROW_STATE_TRANSITION_WITH_TRANSPORT_COHERENCE_CHECK",
                "q3": "ONE_SEAM_ROW_BLOCKER_DEFINITION_TEST_UNDER_REVISED_CRITERIA",
                "current_authoritative_signal": "BLOCKER_TOKEN_CHANGE_REMAINS_AUTHORITATIVE",
                "authoritative_signal_status": "NEVER_FIRED_IN_ANY_EXECUTION",
                "no_loop_rule": "ONE_DEEPER_BLOCKER_DEFINITION_REVIEW_ONLY",
                "next_action": "EXECUTE_BOUNDED_BLOCKER_DEFINITION_TEST_PACKET_ONCE",
            }
        },
    )

    # Create test artifact files
    arch_dir = tmp_path / "formal" / "output" / "architecture"
    arch_dir.mkdir(parents=True, exist_ok=True)

    if transport_witness_bound:
        _write_json(
            arch_dir / "SEAM_QM_STAT_TRANSPORT_WITNESS_BINDING_v0.json",
            {"bound": True, "coherence_check": "PASSED"},
        )

    if bridge_object_materialized:
        _write_json(
            arch_dir / "SEAM_TO_MASTER_ACTION_RESIDUAL_BRIDGE_OBJECT_v0.json",
            {"materialized": True, "state": "COHERENT"},
        )

    declaration_path = (
        tmp_path / "formal" / "docs" / "release"
        / "BOUNDED_BLOCKER_DEFINITION_TEST_EXECUTION_20260411_v0.json"
    )
    declaration_path.parent.mkdir(parents=True, exist_ok=True)

    _write_json(
        declaration_path,
        {
            "schema_id": "BOUNDED_BLOCKER_DEFINITION_TEST_EXECUTION_20260411_v0",
            "required_inputs": {
                "deeper_blocker_definition_review_report": "formal/output/reports/deeper_blocker_definition_review_20260411_v0.json",
            },
            "test_target": {
                "target_row_id": "ROW-SEAM-QM-STAT-001",
                "target_package_id": "QM_STAT_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE_v0",
                "transport_witness_artifact": "formal/output/architecture/SEAM_QM_STAT_TRANSPORT_WITNESS_BINDING_v0.json",
                "bridge_object_artifact": "formal/output/architecture/SEAM_TO_MASTER_ACTION_RESIDUAL_BRIDGE_OBJECT_v0.json",
            },
            "blocker_definition_under_test": {
                "candidate_blocker_definition": "REVISED_BLOCKER_DEF_SEAM_ROW_STATE_TRANSITION_WITH_TRANSPORT_COHERENCE_CHECK",
                "definition_description": "Blocker movement when: (1) transport witness bound AND bridge object materialized AND (2) coherent state transition under QM-stat.",
                "definition_scope": "SEAM_ROW_SPECIFIC_STATE_TRANSITION",
                "strictness_relative_to_diagnostic": "STRICTER_THAN_DIAGNOSTIC_SEAM_COVERAGE",
            },
            "retained_authoritative_guard": {
                "retained_authoritative_signal": "BLOCKER_TOKEN_CHANGE_REMAINS_AUTHORITATIVE",
                "tracking_policy": "BLOCKER_TOKEN_CHANGE_TRACKED_IN_PARALLEL_BUT_NOT_PROMOTION_BEARING_IN_THIS_TEST",
                "monitoring_note": "Authoritative signal still never fires.",
            },
            "execution_policy": {
                "test_scope": "SINGLE_ROW_SINGLE_DEFINITION_ONCE",
                "promotion_requires_explicit_revised_def_movement": True,
                "authoritative_blocker_token_not_required_for_success": True,
                "no_loop_rule": "ONE_BOUNDED_BLOCKER_DEFINITION_TEST_EXECUTION_ONLY",
                "reversibility_rule": "TEST_RESULTS_MUST_BE_ASSESSED_BEFORE_PROMOTION_OR_ROLLBACK",
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


def test_execution_revised_def_fires_artifacts_present(tmp_path: Path) -> None:
    """When review materialized and artifacts present, revised blocker def fires; authoritative blocked."""
    report = _run(tmp_path, transport_witness_bound=True, bridge_object_materialized=True)
    summary = report["summary"]

    assert summary["execution_classification"] == "EXECUTION_VALID_REVISED_DEF_FIRES_AUTHORITATIVE_BLOCKED"
    assert summary["revised_blocker_def_fires"] is True
    assert summary["authoritative_fires"] is False
    assert summary["blocker_signal"] == "REVISED_DEF_ONLY"
    assert summary["candidate_blocker_definition"] == "REVISED_BLOCKER_DEF_SEAM_ROW_STATE_TRANSITION_WITH_TRANSPORT_COHERENCE_CHECK"
    assert summary["retained_authoritative_signal"] == "BLOCKER_TOKEN_CHANGE_REMAINS_AUTHORITATIVE"
    assert summary["no_loop_rule"] == "ONE_BOUNDED_BLOCKER_DEFINITION_TEST_EXECUTION_ONLY"
    assert summary["next_action"] == "EMIT_BOUNDED_BLOCKER_DEFINITION_TEST_RULING"


def test_execution_blocked_when_prerequisite_missing(tmp_path: Path) -> None:
    """When review outcome is not materialized, execution must not proceed."""
    report = _run(
        tmp_path,
        review_outcome="THEORY_POSTURE_REVIEW_REQUIRED",
    )
    criteria = report["criteria"]

    assert criteria["review_prerequisite_satisfied"] is False
