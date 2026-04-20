from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import qm_stat_cycle11_pre_screening_step_report as tool


REPO_ROOT = find_repo_root(Path(__file__))
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "target_lane": {
                "row_id": "ROW-SEAM-QM-STAT-001",
                "lane": "QM_STAT_CYCLE11",
                "blocker_class": "SEAM_INTEGRATION_GAP",
                "domain": "seam",
            },
            "required_inputs": {
                "qm_stat_seam_authorization_readiness_dossier_report": "formal/output/reports/qm_stat_seam_authorization_readiness_dossier_20260414_v0.json",
                "qm_stat_cycle11_lane_status_report": "formal/output/reports/qm_stat_cycle11_lane_status_20260411_v0.json",
                "cycle11_artifact": "formal/output/qm_stat_class_b_seam_physics_pilot_cycle11_v0.json",
                "cycle11_target_doc": "formal/docs/paper/DERIVATION_TARGET_QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE11_v0.md",
            },
            "pre_screening_execution_contract": {
                "required_readiness_outcome": "QM_STAT_SEAM_AUTHORIZATION_DOSSIER_READY_FOR_BOUNDED_PRE_SCREENING",
                "required_readiness_next_action": "EXECUTE_ONE_BOUNDED_QM_STAT_CYCLE11_PRE_SCREENING_STEP_WITH_NO_DIRECT_EXECUTION_AUTHORIZATION",
                "required_current_restart_blocker": "",
                "required_lane_internal_status": "RETAINED",
                "required_lane_externalization_status": "OUT_OF_SCOPE_UNDER_CYCLE11",
                "required_lane_routing_implication": "DO_NOT_COUNT_QM_STAT_AS_CURRENT_EXTERNAL_PATH_SIGNAL",
                "required_artifact_status": "CRITERIA_AND_EIGHTEENTH_MOMENT_EXCLUSION_PINNED_NONCLAIM",
                "required_adjudication": "NOT_YET_DISCHARGED",
                "required_target_doc_tokens": [
                    "QM_STAT_CYCLE11_STATUS_v0: EIGHTEENTH_CENTRAL_MOMENT_PARITY_AND_EXCLUSION_PINNED_NONCLAIM",
                    "QM_STAT_CYCLE11_BLOCKER_DISCHARGE_CRITERIA_v0: MASS_MEAN_VARIANCE_THIRD_FOURTH_SIXTH_EIGHTH_TENTH_TWELFTH_FOURTEENTH_SIXTEENTH_AND_EIGHTEENTH_MOMENT_PARITY_REQUIRED",
                    "QM_STAT_CYCLE11_SCOPE_v0: FINITE_STATE_DISCRETE_HIGHER_MOMENT_AUDIT_ONLY_NONCLAIM",
                ],
                "execution_scope_token": "QM_STAT_CYCLE11_SINGLE_PRE_SCREENING_STEP_ONLY_NONLIVE",
                "execution_live_token_count": 0,
                "single_layer_only": True,
                "single_outcome_only": True,
            },
            "pre_screening_execution_outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_QM_STAT_CYCLE11_PRE_SCREENING_STEP_OUTCOME",
                "no_loop_rule": "ONE_QM_STAT_CYCLE11_PRE_SCREENING_STEP_LAYER_ONLY",
                "allowed_outcomes": [
                    "QM_STAT_CYCLE11_PRE_SCREENING_STEP_EXECUTED_NONLIVE",
                    "QM_STAT_CYCLE11_PRE_SCREENING_STEP_BLOCKED",
                    "QM_STAT_CYCLE11_PRE_SCREENING_STEP_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_QM_STAT_CYCLE11_PRE_SCREENING_STEP_REPAIR",
                ],
                "default_outcome": "QM_STAT_CYCLE11_PRE_SCREENING_STEP_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _seed_inputs(root: Path, *, readiness_outcome: str = "QM_STAT_SEAM_AUTHORIZATION_DOSSIER_READY_FOR_BOUNDED_PRE_SCREENING") -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_seam_authorization_readiness_dossier_20260414_v0.json",
        {
            "summary": {
                "terminal_outcome": readiness_outcome,
                "target_row_id": "ROW-SEAM-QM-STAT-001",
                "target_lane": "QM_STAT_CYCLE11",
                "current_restart_blocker": "",
                "next_action": "EXECUTE_ONE_BOUNDED_QM_STAT_CYCLE11_PRE_SCREENING_STEP_WITH_NO_DIRECT_EXECUTION_AUTHORIZATION",
            },
            "target_row_dossier": {
                "minimum_post_authorization_tranche": {
                    "target_row_id": "ROW-SEAM-QM-STAT-001",
                    "target_lane": "QM_STAT_CYCLE11",
                    "required_closure_artifact": "formal/output/qm_stat_class_b_seam_physics_pilot_cycle11_v0.json",
                    "required_closure_gate": "formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycle11_gate.py",
                    "required_evidence_surface": "formal/docs/paper/DERIVATION_TARGET_QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE11_v0.md",
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
                "routing_implication": "DO_NOT_COUNT_QM_STAT_AS_CURRENT_EXTERNAL_PATH_SIGNAL",
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "qm_stat_class_b_seam_physics_pilot_cycle11_v0.json",
        {
            "artifact_id": "qm_stat_class_b_seam_physics_pilot_cycle11_v0",
            "status": "CRITERIA_AND_EIGHTEENTH_MOMENT_EXCLUSION_PINNED_NONCLAIM",
            "adjudication": {"value": "NOT_YET_DISCHARGED"},
        },
    )
    _write_text(
        root / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE11_v0.md",
        "\n".join(
            [
                "- `QM_STAT_CYCLE11_STATUS_v0: EIGHTEENTH_CENTRAL_MOMENT_PARITY_AND_EXCLUSION_PINNED_NONCLAIM`",
                "- `QM_STAT_CYCLE11_BLOCKER_DISCHARGE_CRITERIA_v0: MASS_MEAN_VARIANCE_THIRD_FOURTH_SIXTH_EIGHTH_TENTH_TWELFTH_FOURTEENTH_SIXTEENTH_AND_EIGHTEENTH_MOMENT_PARITY_REQUIRED`",
                "- `QM_STAT_CYCLE11_SCOPE_v0: FINITE_STATE_DISCRETE_HIGHER_MOMENT_AUDIT_ONLY_NONCLAIM`",
            ]
        ),
    )


def test_reports_pre_screening_step_executed_nonlive(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "QM_STAT_CYCLE11_PRE_SCREENING_STEP_20260419_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "QM_STAT_CYCLE11_PRE_SCREENING_STEP_EXECUTED_NONLIVE"
    assert report["summary"]["execution_scope_token"] == "QM_STAT_CYCLE11_SINGLE_PRE_SCREENING_STEP_ONLY_NONLIVE"


def test_reports_pre_screening_step_blocked_when_readiness_falls_out(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "QM_STAT_CYCLE11_PRE_SCREENING_STEP_20260419_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, readiness_outcome="QM_STAT_SEAM_AUTHORIZATION_DOSSIER_EVIDENCE_INCOMPLETE")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "QM_STAT_CYCLE11_PRE_SCREENING_STEP_BLOCKED"


def test_live_pre_screening_step_report_matches_current_repo_state() -> None:
    state_text = _read(STATE_PATH)
    assert "QM_STAT_SEAM_AUTHORIZATION_READINESS_DOSSIER_NEXT_ACTION_v0: EXECUTE_ONE_BOUNDED_QM_STAT_CYCLE11_PRE_SCREENING_STEP_WITH_NO_DIRECT_EXECUTION_AUTHORIZATION" in state_text

    report = _read_json(
        REPO_ROOT / "formal" / "output" / "reports" / "qm_stat_cycle11_pre_screening_step_20260419_v0.json"
    )
    assert report["summary"]["terminal_outcome"] == "QM_STAT_CYCLE11_PRE_SCREENING_STEP_EXECUTED_NONLIVE"
    assert report["summary"]["next_action"] == "STOP_AT_QM_STAT_CYCLE11_PRE_SCREENING_TOKEN_PENDING_EXPLICIT_DOWNSTREAM_AUTHORIZATION"