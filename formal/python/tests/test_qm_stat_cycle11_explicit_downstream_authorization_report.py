from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import qm_stat_cycle11_explicit_downstream_authorization_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "target_seam": {
                "row_id": "ROW-SEAM-QM-STAT-001",
                "lane": "QM_STAT_CYCLE11",
                "blocker_class": "SEAM_INTEGRATION_GAP",
                "domain": "seam",
            },
            "required_inputs": {
                "qm_stat_cycle11_pre_screening_step_report": "formal/output/reports/qm_stat_cycle11_pre_screening_step_20260419_v0.json",
                "qm_stat_seam_authorization_readiness_dossier_report": "formal/output/reports/qm_stat_seam_authorization_readiness_dossier_20260414_v0.json",
                "qm_stat_cycle11_lane_status_report": "formal/output/reports/qm_stat_cycle11_lane_status_20260411_v0.json",
                "physics_progress_ledger_report": "formal/output/reports/physics_progress_ledger_v0.json",
                "seam_resolution_sla_ledger_report": "formal/output/reports/seam_resolution_sla_ledger_20260416_v0.json",
                "cycle12_candidate_doc": "formal/docs/release/WS_10_T20_QM_STAT_CYCLE12_ADDITIVE_CANDIDATE_v0.md",
                "cycle12_target_doc": "formal/docs/paper/DERIVATION_TARGET_QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE12_v0.md",
                "cycle12_artifact": "formal/output/qm_stat_class_b_seam_physics_pilot_cycle12_v0.json",
                "cycle12_gate": "formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle12_gate.py",
            },
            "downstream_authorization_contract": {
                "required_pre_screening_outcome": "QM_STAT_CYCLE11_PRE_SCREENING_STEP_EXECUTED_NONLIVE",
                "required_pre_screening_next_action": "STOP_AT_QM_STAT_CYCLE11_PRE_SCREENING_TOKEN_PENDING_EXPLICIT_DOWNSTREAM_AUTHORIZATION",
                "required_readiness_outcome": "QM_STAT_SEAM_AUTHORIZATION_DOSSIER_READY_FOR_BOUNDED_PRE_SCREENING",
                "required_lane_internal_status": "RETAINED",
                "required_lane_externalization_status": "OUT_OF_SCOPE_UNDER_CYCLE11",
                "required_progress_classification": "PROGRESS",
                "required_sla_decision_state": "ACTIVE_TRACK_PENDING_BRANCH_EXCEPTION_DECISION",
                "required_sla_gate_runtime_status": "PATH_PINNED_RUNTIME_AWAITING_AUTHORITY_DECISION",
                "required_candidate_tokens": [
                    "WS10_T20_QM_STAT_CYCLE12_STATUS_v0: DECLARED_BOUNDED_NONCLAIM",
                    "WS10_T20_QM_STAT_CYCLE12_LANE_v0: QM_STAT",
                    "WS10_T20_QM_STAT_CYCLE12_TARGET_v0: CYCLE12",
                    "WS10_T20_QM_STAT_CYCLE12_ARTIFACT_v0: formal/output/qm_stat_class_b_seam_physics_pilot_cycle12_v0.json",
                    "WS10_T20_QM_STAT_CYCLE12_GATE_v0: formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle12_gate.py",
                ],
                "required_target_doc_tokens": [
                    "QM_STAT_CYCLE12_STATUS_v0: TWENTIETH_CENTRAL_MOMENT_PARITY_AND_EXCLUSION_PINNED_NONCLAIM",
                    "QM_STAT_CYCLE12_BLOCKER_DISCHARGE_CRITERIA_v0: MASS_MEAN_VARIANCE_THIRD_FOURTH_SIXTH_EIGHTH_TENTH_TWELFTH_FOURTEENTH_SIXTEENTH_EIGHTEENTH_AND_TWENTIETH_MOMENT_PARITY_REQUIRED",
                    "QM_STAT_CYCLE12_SCOPE_v0: FINITE_STATE_DISCRETE_HIGHER_MOMENT_AUDIT_ONLY_NONCLAIM",
                    "QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE12_STATUS_v0: CRITERIA_AND_TWENTIETH_MOMENT_EXCLUSION_PINNED_NONCLAIM",
                ],
                "required_artifact_status": "CRITERIA_AND_TWENTIETH_MOMENT_EXCLUSION_PINNED_NONCLAIM",
                "required_adjudication": "NOT_YET_DISCHARGED",
                "authorization_scope_token": "CONTROL_SURFACE_QM_STAT_CYCLE12_BOUNDED_AUTHORIZATION_NONLIVE",
                "authorization_result_token": "QM_STAT_CYCLE12_SINGLE_LANE_AUTHORIZED_NONLIVE_v0",
                "branch_chain_status": "UNAMBIGUOUS_SINGLE_ACTIVE_LANE",
                "execution_live_token_count": 0,
                "single_layer_only": True,
                "single_outcome_only": True,
                "minimum_bounded_downstream_tranche": {
                    "target_row_id": "ROW-SEAM-QM-STAT-001",
                    "source_lane": "QM_STAT_CYCLE11",
                    "authorized_candidate_target": "CYCLE12",
                    "current_status": "PATH_PINNED_RUNTIME_AWAITING_AUTHORITY_DECISION",
                    "required_evidence_surface": "formal/docs/paper/DERIVATION_TARGET_QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE12_v0.md",
                    "required_closure_artifact": "formal/output/qm_stat_class_b_seam_physics_pilot_cycle12_v0.json",
                    "required_closure_gate": "formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle12_gate.py",
                    "required_exit_criterion": "CYCLE_GATE_AND_SYNTHESIS_GATE_PASS",
                    "bounded_scope": "SINGLE_ROW_SINGLE_SEAM_QM_STAT_CYCLE12_CONTINUATION_AUTHORIZATION_ONLY",
                },
            },
            "downstream_authorization_outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_QM_STAT_CYCLE11_EXPLICIT_DOWNSTREAM_AUTHORIZATION_OUTCOME",
                "no_loop_rule": "ONE_QM_STAT_CYCLE11_EXPLICIT_DOWNSTREAM_AUTHORIZATION_LAYER_ONLY",
                "allowed_outcomes": [
                    "QM_STAT_CYCLE12_SINGLE_LANE_AUTHORIZED_NONLIVE_v0",
                    "QM_STAT_EXPLICIT_DOWNSTREAM_AUTHORIZATION_BLOCKED",
                    "QM_STAT_EXPLICIT_DOWNSTREAM_AUTHORIZATION_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_QM_STAT_EXPLICIT_DOWNSTREAM_AUTHORIZATION_REPAIR",
                ],
                "default_outcome": "QM_STAT_EXPLICIT_DOWNSTREAM_AUTHORIZATION_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _seed_inputs(root: Path, *, pre_screening_outcome: str = "QM_STAT_CYCLE11_PRE_SCREENING_STEP_EXECUTED_NONLIVE") -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_cycle11_pre_screening_step_20260419_v0.json",
        {
            "summary": {
                "terminal_outcome": pre_screening_outcome,
                "target_row_id": "ROW-SEAM-QM-STAT-001",
                "target_lane": "QM_STAT_CYCLE11",
                "next_action": "STOP_AT_QM_STAT_CYCLE11_PRE_SCREENING_TOKEN_PENDING_EXPLICIT_DOWNSTREAM_AUTHORIZATION",
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_seam_authorization_readiness_dossier_20260414_v0.json",
        {
            "summary": {
                "terminal_outcome": "QM_STAT_SEAM_AUTHORIZATION_DOSSIER_READY_FOR_BOUNDED_PRE_SCREENING",
                "target_row_id": "ROW-SEAM-QM-STAT-001",
                "target_lane": "QM_STAT_CYCLE11",
            },
            "target_row_dossier": {
                "minimum_post_authorization_tranche": {
                    "required_evidence_surface": "formal/docs/paper/DERIVATION_TARGET_QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE11_v0.md"
                }
            },
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_cycle11_lane_status_20260411_v0.json",
        {
            "summary": {
                "internal_lane_status": "RETAINED",
                "externalization_status": "OUT_OF_SCOPE_UNDER_CYCLE11",
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "physics_progress_ledger_v0.json",
        {"progress_classification": "PROGRESS"},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "seam_resolution_sla_ledger_20260416_v0.json",
        {
            "entries": [
                {
                    "row_id": "ROW-SEAM-QM-STAT-001",
                    "decision_state": "ACTIVE_TRACK_PENDING_BRANCH_EXCEPTION_DECISION",
                    "gate_runtime_status": "PATH_PINNED_RUNTIME_AWAITING_AUTHORITY_DECISION",
                    "target_surface": "formal/docs/paper/DERIVATION_TARGET_QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE11_v0.md",
                }
            ]
        },
    )
    _write_text(
        root / "formal" / "docs" / "release" / "WS_10_T20_QM_STAT_CYCLE12_ADDITIVE_CANDIDATE_v0.md",
        "\n".join(
            [
                "# Candidate",
                "- WS10_T20_QM_STAT_CYCLE12_STATUS_v0: DECLARED_BOUNDED_NONCLAIM",
                "- WS10_T20_QM_STAT_CYCLE12_LANE_v0: QM_STAT",
                "- WS10_T20_QM_STAT_CYCLE12_TARGET_v0: CYCLE12",
                "- WS10_T20_QM_STAT_CYCLE12_ARTIFACT_v0: formal/output/qm_stat_class_b_seam_physics_pilot_cycle12_v0.json",
                "- WS10_T20_QM_STAT_CYCLE12_GATE_v0: formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle12_gate.py",
            ]
        ),
    )
    _write_text(
        root / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE12_v0.md",
        "\n".join(
            [
                "# Target",
                "- QM_STAT_CYCLE12_STATUS_v0: TWENTIETH_CENTRAL_MOMENT_PARITY_AND_EXCLUSION_PINNED_NONCLAIM",
                "- QM_STAT_CYCLE12_BLOCKER_DISCHARGE_CRITERIA_v0: MASS_MEAN_VARIANCE_THIRD_FOURTH_SIXTH_EIGHTH_TENTH_TWELFTH_FOURTEENTH_SIXTEENTH_EIGHTEENTH_AND_TWENTIETH_MOMENT_PARITY_REQUIRED",
                "- QM_STAT_CYCLE12_SCOPE_v0: FINITE_STATE_DISCRETE_HIGHER_MOMENT_AUDIT_ONLY_NONCLAIM",
                "- QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE12_STATUS_v0: CRITERIA_AND_TWENTIETH_MOMENT_EXCLUSION_PINNED_NONCLAIM",
            ]
        ),
    )
    _write_json(
        root / "formal" / "output" / "qm_stat_class_b_seam_physics_pilot_cycle12_v0.json",
        {
            "artifact_id": "qm_stat_class_b_seam_physics_pilot_cycle12_v0",
            "status": "CRITERIA_AND_TWENTIETH_MOMENT_EXCLUSION_PINNED_NONCLAIM",
            "adjudication": {"value": "NOT_YET_DISCHARGED"},
        },
    )
    _write_text(root / "formal" / "python" / "tests" / "test_qm_stat_class_b_seam_physics_pilot_cycle12_gate.py", "def test_placeholder():\n    assert True\n")


def test_reports_qm_stat_explicit_downstream_authorization(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "QM_STAT_CYCLE11_EXPLICIT_DOWNSTREAM_AUTHORIZATION_20260419_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "QM_STAT_CYCLE12_SINGLE_LANE_AUTHORIZED_NONLIVE_v0"
    assert report["summary"]["authorization_scope_token"] == "CONTROL_SURFACE_QM_STAT_CYCLE12_BOUNDED_AUTHORIZATION_NONLIVE"


def test_reports_qm_stat_explicit_downstream_authorization_blocked_without_pre_screening(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "QM_STAT_CYCLE11_EXPLICIT_DOWNSTREAM_AUTHORIZATION_20260419_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, pre_screening_outcome="QM_STAT_CYCLE11_PRE_SCREENING_STEP_BLOCKED")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "QM_STAT_EXPLICIT_DOWNSTREAM_AUTHORIZATION_BLOCKED"


def test_live_repo_qm_stat_explicit_downstream_authorization() -> None:
    report = tool.build_report(declaration_path=tool.DEFAULT_DECLARATION_PATH, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "QM_STAT_CYCLE12_SINGLE_LANE_AUTHORIZED_NONLIVE_v0"
    assert report["summary"]["next_action"] == "EXECUTE_ONE_BOUNDED_QM_STAT_CYCLE12_CONTINUATION_ONLY"