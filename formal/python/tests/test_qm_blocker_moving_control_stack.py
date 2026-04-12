from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import qm_blocker_moving_ruling_report as ruling_tool
from formal.python.tools import qm_blocker_moving_tranche_report as tranche_tool
from formal.python.tools import science_next_attack_class_selection_report as selection_tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def test_qm_blocker_moving_tranche_report_classifies_valid_but_nonmoving(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(tranche_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "QM_BLOCKER_MOVING_TRANCHE_PACKET_20260411_v0.json"
    )
    reports_dir = tmp_path / "formal" / "output" / "reports"

    _write_json(
        declaration_path,
        {
            "tranche_id": "QM-BLOCKER-MOVING-001",
            "row_id": "ROW-PILLAR-QM-001",
            "subtarget_id": "QM_PACKET04_THRESHOLD_ALIGNMENT_SUBPROBLEM_v0",
            "required_inputs": {
                "execution_checkpoint": "formal/output/ws10_tgc77_qm_theorem_gap_closure_increment_execution_checkpoint_20260409_v0.json",
                "qm_rework_report": "formal/output/reports/theorem_gap_qm_rework_tranche_20260411_v0.json",
                "qm_subtarget_report": "formal/output/reports/theorem_gap_qm_subtarget_tranche_20260411_v0.json",
                "trend_report": "formal/output/reports/governance_blocker_trend_window_20260410_v0.json",
                "row_outcome_trend_report": "formal/output/reports/theorem_gap_row_outcome_trend_20260411_v0.json",
                "ledger_report": "formal/output/reports/physics_progress_ledger_v0.json",
                "linkage_registry": "formal/docs/release/THEOREM_GAP_TRANCHE_LINKAGE_REGISTRY_20260411_v0.json",
            },
            "movement_policy": {
                "success_rule": "THEOREM_GAP_DELTA_LT_0_OR_TARGET_ROW_SUCCESS_INCREMENT_GT_0",
                "failure_rule": "ALL_MOVEMENT_SIGNALS_FALSE",
                "no_loop_rule": "ONE_BOUNDED_EXECUTION_ONLY",
            },
        },
    )
    _write_json(
        tmp_path / "formal" / "output" / "ws10_tgc77_qm_theorem_gap_closure_increment_execution_checkpoint_20260409_v0.json",
        {
            "acceptance_posture": "TGC77_EXECUTION_AND_VALIDATION_COMPLETE_PENDING_BOUNDED_COMMIT",
            "verification": {
                "focused_gate": {"result": "1 passed in 0.99s"},
                "full_governance": {"governance_gate_ok": True},
                "checkpoint_ladder": {"governance_gate_ok": True},
            },
        },
    )
    _write_json(
        reports_dir / "theorem_gap_qm_rework_tranche_20260411_v0.json",
        {
            "objective_quality": {
                "inputs": {
                    "target_row_success_count": 0,
                    "target_row_no_change_count": 2,
                    "target_row_failure_count": 0,
                }
            }
        },
    )
    _write_json(
        reports_dir / "theorem_gap_qm_subtarget_tranche_20260411_v0.json",
        {"objective_quality": {"inputs": {"target_row": "ROW-PILLAR-QM-001"}}},
    )
    _write_json(
        reports_dir / "governance_blocker_trend_window_20260410_v0.json",
        {"blocker_counts": {"prior": {"THEOREM_GAP": 7}, "current": {"THEOREM_GAP": 7}}},
    )
    _write_json(
        reports_dir / "theorem_gap_row_outcome_trend_20260411_v0.json",
        {
            "objective_quality": {
                "inputs": {
                    "row_outcome_counts": {
                        "ROW-PILLAR-QM-001": {
                            "success": 0,
                            "no_change": 3,
                            "failure": 0,
                            "total": 3,
                        }
                    }
                }
            }
        },
    )
    _write_json(
        reports_dir / "physics_progress_ledger_v0.json",
        {"actual_blocker_state_change": "NO_DELTA_DETECTED_ROUTE_TO_REWORK"},
    )
    _write_json(
        tmp_path / "formal" / "docs" / "release" / "THEOREM_GAP_TRANCHE_LINKAGE_REGISTRY_20260411_v0.json",
        {"entries": [{"tranche_id": "R6-QM-SUBTARGET-001", "target_row": "ROW-PILLAR-QM-001"}]},
    )

    report = tranche_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["tranche_classification"] == "QM_VALID_BUT_NONMOVING"
    assert report["summary"]["theorem_gap_delta"] == 0
    assert report["summary"]["target_row_outcome_delta"] == {
        "success": 0,
        "no_change": 1,
        "failure": 0,
        "total": 1,
    }
    assert report["summary"]["blocker_state_token_delta"] == 0


def test_qm_blocker_moving_ruling_exhausts_nonmoving_single_execution_packet(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(ruling_tool, "REPO_ROOT", tmp_path)

    declaration_path = tmp_path / "formal" / "docs" / "release" / "QM_BLOCKER_MOVING_RULING_20260411_v0.json"
    reports_dir = tmp_path / "formal" / "output" / "reports"

    _write_json(
        declaration_path,
        {
            "required_inputs": {
                "qm_blocker_moving_packet": "formal/docs/release/QM_BLOCKER_MOVING_TRANCHE_PACKET_20260411_v0.json",
                "qm_blocker_moving_tranche_report": "formal/output/reports/qm_blocker_moving_tranche_20260411_v0.json",
            },
            "ruling_policy": {
                "next_action_if_exhausted": "REFRESH_ATTACK_CLASS_SELECTION_AND_DO_NOT_LOOP_QM",
            },
        },
    )
    _write_json(
        tmp_path / "formal" / "docs" / "release" / "QM_BLOCKER_MOVING_TRANCHE_PACKET_20260411_v0.json",
        {"row_id": "ROW-PILLAR-QM-001", "subtarget_id": "QM_PACKET04_THRESHOLD_ALIGNMENT_SUBPROBLEM_v0"},
    )
    _write_json(
        reports_dir / "qm_blocker_moving_tranche_20260411_v0.json",
        {
            "summary": {
                "row_id": "ROW-PILLAR-QM-001",
                "subtarget_id": "QM_PACKET04_THRESHOLD_ALIGNMENT_SUBPROBLEM_v0",
                "tranche_classification": "QM_VALID_BUT_NONMOVING",
                "no_loop_rule": "ONE_BOUNDED_EXECUTION_ONLY",
            }
        },
    )

    report = ruling_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["qm_ruling"] == "EXHAUSTED_UNDER_CURRENT_FILTER"
    assert report["summary"]["exclude_from_immediate_reselection"] is True
    assert report["summary"]["next_action"] == "REFRESH_ATTACK_CLASS_SELECTION_AND_DO_NOT_LOOP_QM"


def test_science_next_attack_class_selection_escalates_when_qm_and_proof_debt_are_exhausted(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(selection_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "SCIENCE_NEXT_ATTACK_CLASS_SELECTION_20260411_v0.json"
    )
    reports_dir = tmp_path / "formal" / "output" / "reports"

    _write_json(
        declaration_path,
        {
            "required_inputs": {
                "science_global_completion_baseline_report": "formal/output/reports/science_global_completion_baseline_20260411_v0.json",
                "proof_debt_program_exhaustion_decision_report": "formal/output/reports/proof_debt_program_exhaustion_decision_20260411_v0.json",
                "qm_blocker_moving_ruling_report": "formal/output/reports/qm_blocker_moving_ruling_20260411_v0.json",
            },
            "selection_policy": {
                "retain_qm_when_ruling": "MOVING",
                "default_next_attack_class": "DIRECT_MASTER_ACTION_RESIDUAL_TRANSPORT_ATTACK_CLASS",
                "default_next_action": "MATERIALIZE_DIRECT_MASTER_ACTION_RESIDUAL_TRANSPORT_ATTACK_CLASS_PACKET",
                "do_not_reopen_proof_debt_in_parallel": True,
            },
        },
    )
    _write_json(
        reports_dir / "science_global_completion_baseline_20260411_v0.json",
        {"completion_assessment": {"science_global_complete": False, "global_objective_complete": False}},
    )
    _write_json(
        reports_dir / "proof_debt_program_exhaustion_decision_20260411_v0.json",
        {
            "summary": {
                "program_state": "PROOF_DEBT_PROGRAM_EXHAUSTED_UNDER_CURRENT_FILTER",
                "decision": "ESCALATE_TO_NEXT_ATTACK_CLASS",
            }
        },
    )
    _write_json(
        reports_dir / "qm_blocker_moving_ruling_20260411_v0.json",
        {"summary": {"qm_ruling": "EXHAUSTED_UNDER_CURRENT_FILTER"}},
    )

    report = selection_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["decision"] == "ESCALATE_TO_DECLARED_NEXT_ATTACK_CLASS"
    assert report["summary"]["selected_next_attack_class"] == "DIRECT_MASTER_ACTION_RESIDUAL_TRANSPORT_ATTACK_CLASS"
    assert report["summary"]["next_action"] == "MATERIALIZE_DIRECT_MASTER_ACTION_RESIDUAL_TRANSPORT_ATTACK_CLASS_PACKET"
    assert report["summary"]["proof_debt_parallel_reopen_allowed"] is False


def test_science_next_attack_class_selection_retains_qm_when_qm_is_moving(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(selection_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "SCIENCE_NEXT_ATTACK_CLASS_SELECTION_20260411_v0.json"
    )
    reports_dir = tmp_path / "formal" / "output" / "reports"

    _write_json(
        declaration_path,
        {
            "required_inputs": {
                "science_global_completion_baseline_report": "formal/output/reports/science_global_completion_baseline_20260411_v0.json",
                "proof_debt_program_exhaustion_decision_report": "formal/output/reports/proof_debt_program_exhaustion_decision_20260411_v0.json",
                "qm_blocker_moving_ruling_report": "formal/output/reports/qm_blocker_moving_ruling_20260411_v0.json",
            },
            "selection_policy": {
                "retain_qm_when_ruling": "MOVING",
                "default_next_attack_class": "DIRECT_MASTER_ACTION_RESIDUAL_TRANSPORT_ATTACK_CLASS",
                "default_next_action": "MATERIALIZE_DIRECT_MASTER_ACTION_RESIDUAL_TRANSPORT_ATTACK_CLASS_PACKET",
                "do_not_reopen_proof_debt_in_parallel": True,
            },
        },
    )
    _write_json(
        reports_dir / "science_global_completion_baseline_20260411_v0.json",
        {"completion_assessment": {"science_global_complete": False, "global_objective_complete": False}},
    )
    _write_json(
        reports_dir / "proof_debt_program_exhaustion_decision_20260411_v0.json",
        {
            "summary": {
                "program_state": "PROOF_DEBT_PROGRAM_EXHAUSTED_UNDER_CURRENT_FILTER",
                "decision": "ESCALATE_TO_NEXT_ATTACK_CLASS",
            }
        },
    )
    _write_json(
        reports_dir / "qm_blocker_moving_ruling_20260411_v0.json",
        {"summary": {"qm_ruling": "MOVING"}},
    )

    report = selection_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["decision"] == "RETAIN_QM_AS_ACTIVE_BLOCKER_ROW"
    assert report["summary"]["selected_next_attack_class"] is None
    assert report["summary"]["next_action"] == "CONTINUE_QM_BLOCKER_MOVING_PROGRAM"
