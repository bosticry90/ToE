from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import bounded_measurement_regime_pilot_execution_report as exec_tool
from formal.python.tools import bounded_measurement_regime_pilot_ruling_report as ruling_tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_execution_declaration(
    path: Path,
    *,
    target_row_id: str,
    target_package_id: str,
) -> None:
    _write_json(
        path,
        {
            "pilot_tranche": "ONE_SEAM_ROW_RECOMPUTE_UNDER_REVISED_SIGNALS",
            "required_inputs": {
                "post_posture_review_program_mode_transition_report": "formal/output/reports/post_posture_review_program_mode_transition_20260411_v0.json",
            },
            "pilot_targets": {
                "target_row_id": target_row_id,
                "target_package_id": target_package_id,
                "transport_witness_artifact": "formal/output/architecture/SEAM_QM_STAT_TRANSPORT_WITNESS_BINDING_v0.json",
                "bridge_object_artifact": "formal/output/architecture/SEAM_TO_MASTER_ACTION_RESIDUAL_BRIDGE_OBJECT_v0.json",
            },
            "revised_signal_spec": {
                "new_signal": "SEAM_INTEGRATION_COVERAGE_DELTA_GT_0",
                "retained_signal": "BLOCKER_TOKEN_CHANGE_REMAINS_AUTHORITATIVE",
                "new_signal_pass_rule": "TRANSPORT_WITNESS_BOUND_AND_BRIDGE_OBJECT_MATERIALIZED_FOR_TARGET_ROW",
                "retained_signal_pass_rule": "BLOCKER_TOKEN_CHANGE_OBSERVED_IN_LEDGER",
            },
            "execution_policy": {
                "no_loop_rule": "ONE_BOUNDED_MEASUREMENT_REGIME_PILOT_ONLY",
                "promotion_requires_both_signals": True,
                "reversibility_rule": "PILOT_RESULTS_MUST_BE_ASSESSED_BEFORE_PROMOTION_OR_ROLLBACK",
            },
        },
    )


def _write_transition_report(reports_dir: Path, *, transition_outcome: str) -> None:
    _write_json(
        reports_dir / "post_posture_review_program_mode_transition_20260411_v0.json",
        {
            "summary": {
                "transition_outcome": transition_outcome,
                "measurement_defect": "BLOCKER_MOVEMENT_SIGNALS_NEVER_TRIGGERED_UNDER_ANY_ATTACK_CLASS",
                "new_blocker_movement_signal": "SEAM_INTEGRATION_COVERAGE_DELTA_GT_0",
                "retained_blocker_movement_signal": "BLOCKER_TOKEN_CHANGE_REMAINS_AUTHORITATIVE",
                "pilot_tranche": "ONE_SEAM_ROW_RECOMPUTE_UNDER_REVISED_SIGNALS",
                "no_loop_rule": "ONE_BOUNDED_MEASUREMENT_REGIME_PILOT_ONLY",
                "next_action": "EXECUTE_BOUNDED_MEASUREMENT_REGIME_PILOT_ONCE",
            }
        },
    )


def _write_architecture_artifacts(arch_dir: Path, *, row_id: str, package_id: str) -> None:
    _write_json(
        arch_dir / "SEAM_QM_STAT_TRANSPORT_WITNESS_BINDING_v0.json",
        {
            "witness_id": "SEAM_QM_STAT_TRANSPORT_WITNESS_BINDING_v0",
            "status": "BOUND",
            "row_id": row_id,
            "target_package_id": package_id,
        },
    )
    _write_json(
        arch_dir / "SEAM_TO_MASTER_ACTION_RESIDUAL_BRIDGE_OBJECT_v0.json",
        {
            "object_id": "SEAM_TO_MASTER_ACTION_RESIDUAL_BRIDGE_OBJECT_v0",
            "status": "MATERIALIZED",
            "row_id": row_id,
            "target_package_id": package_id,
        },
    )


# ── Execution tests ─────────────────────────────────────────────────────────


def test_pilot_execution_classifies_valid_but_nonmoving_when_new_signal_fires_but_retained_does_not(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(exec_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "BOUNDED_MEASUREMENT_REGIME_PILOT_EXECUTION_20260411_v0.json"
    )
    row_id = "ROW-SEAM-QM-STAT-001"
    package_id = "QM_STAT_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE_v0"

    _write_execution_declaration(
        declaration_path,
        target_row_id=row_id,
        target_package_id=package_id,
    )
    _write_transition_report(
        tmp_path / "formal" / "output" / "reports",
        transition_outcome="MEASUREMENT_REGIME_TRANSITION_MATERIALIZED",
    )
    _write_architecture_artifacts(
        tmp_path / "formal" / "output" / "architecture",
        row_id=row_id,
        package_id=package_id,
    )

    report = exec_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["execution_classification"] == "PILOT_VALID_BUT_NONMOVING"
    assert report["summary"]["new_signal_fired"] is True
    assert report["summary"]["retained_signal_fired"] is False
    assert report["summary"]["blocker_movement_signal"] == "NEW_SIGNAL_ONLY"
    assert report["summary"]["next_action"] == "EMIT_BOUNDED_MEASUREMENT_REGIME_PILOT_RULING"
    assert report["criteria"]["no_loop_rule_declared"] is True


def test_pilot_execution_incomplete_when_transition_not_materialized(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(exec_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "BOUNDED_MEASUREMENT_REGIME_PILOT_EXECUTION_20260411_v0.json"
    )
    row_id = "ROW-SEAM-QM-STAT-001"
    package_id = "QM_STAT_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE_v0"

    _write_execution_declaration(
        declaration_path,
        target_row_id=row_id,
        target_package_id=package_id,
    )
    _write_transition_report(
        tmp_path / "formal" / "output" / "reports",
        transition_outcome="MEASUREMENT_REGIME_TRANSITION_INCOMPLETE",
    )
    _write_architecture_artifacts(
        tmp_path / "formal" / "output" / "architecture",
        row_id=row_id,
        package_id=package_id,
    )

    report = exec_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["execution_classification"] == "PILOT_EXECUTION_INCOMPLETE"
    assert report["summary"]["next_action"] == "RESTORE_PILOT_EXECUTION_PRECONDITIONS"


# ── Ruling tests ─────────────────────────────────────────────────────────────


def _write_ruling_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "bounded_measurement_regime_pilot_execution_report": "formal/output/reports/bounded_measurement_regime_pilot_execution_20260411_v0.json",
            },
            "ruling_policy": {
                "moved_rule": "EXECUTION_CLASSIFICATION_EQ_PILOT_MOVED",
                "valid_but_nonmoving_rule": "EXECUTION_CLASSIFICATION_EQ_PILOT_VALID_BUT_NONMOVING",
                "not_fit_rule": "EXECUTION_CLASSIFICATION_EQ_PILOT_SIGNAL_NOT_FIT",
                "promotion_requires_both_signals": True,
                "no_loop_rule": "ONE_BOUNDED_MEASUREMENT_REGIME_PILOT_ONLY",
                "next_action_if_moved": "PROMOTE_REVISED_MEASUREMENT_REGIME_AND_EXECUTE_NEXT_SEAM_TRANCHE",
                "next_action_if_nonmoving": "ASSESS_PILOT_RESULT_AND_DECIDE_ROLLBACK_OR_HOLD",
                "next_action_if_not_fit": "ROLLBACK_REVISED_MEASUREMENT_REGIME_AND_HOLD",
            },
        },
    )


def _write_execution_report(
    reports_dir: Path,
    *,
    execution_classification: str,
    new_signal_fired: bool,
    retained_signal_fired: bool,
    blocker_movement_signal: str,
) -> None:
    _write_json(
        reports_dir / "bounded_measurement_regime_pilot_execution_20260411_v0.json",
        {
            "summary": {
                "execution_classification": execution_classification,
                "new_signal_fired": new_signal_fired,
                "retained_signal_fired": retained_signal_fired,
                "blocker_movement_signal": blocker_movement_signal,
                "no_loop_rule": "ONE_BOUNDED_MEASUREMENT_REGIME_PILOT_ONLY",
                "next_action": "EMIT_BOUNDED_MEASUREMENT_REGIME_PILOT_RULING",
            }
        },
    )


def test_ruling_is_valid_but_nonmoving_when_new_signal_fires_but_not_retained(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(ruling_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "BOUNDED_MEASUREMENT_REGIME_PILOT_RULING_20260411_v0.json"
    )
    _write_ruling_declaration(declaration_path)
    _write_execution_report(
        tmp_path / "formal" / "output" / "reports",
        execution_classification="PILOT_VALID_BUT_NONMOVING",
        new_signal_fired=True,
        retained_signal_fired=False,
        blocker_movement_signal="NEW_SIGNAL_ONLY",
    )

    report = ruling_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["pilot_ruling"] == "REVISED_SIGNAL_VALID_BUT_NONMOVING"
    assert report["summary"]["next_action"] == "ASSESS_PILOT_RESULT_AND_DECIDE_ROLLBACK_OR_HOLD"
    assert report["criteria"]["ruling_materialized"] is True


def test_ruling_is_not_fit_when_new_signal_does_not_fire(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(ruling_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "BOUNDED_MEASUREMENT_REGIME_PILOT_RULING_20260411_v0.json"
    )
    _write_ruling_declaration(declaration_path)
    _write_execution_report(
        tmp_path / "formal" / "output" / "reports",
        execution_classification="PILOT_SIGNAL_NOT_FIT",
        new_signal_fired=False,
        retained_signal_fired=False,
        blocker_movement_signal="NONE_TRIGGERED",
    )

    report = ruling_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["pilot_ruling"] == "REVISED_SIGNAL_NOT_FIT_FOR_PROMOTION_USE"
    assert report["summary"]["next_action"] == "ROLLBACK_REVISED_MEASUREMENT_REGIME_AND_HOLD"
