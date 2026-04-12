from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import qm_stat_rl10_observable_mapping_review_report as review_tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "target_seam": {
                "row_id": "ROW-SEAM-QM-STAT-001",
                "lane": "QM_STAT_CYCLE11",
                "source_signature_artifact": "formal/output/qm_stat_class_b_seam_physics_pilot_cycle11_v0.json",
            },
            "required_inputs": {
                "qm_stat_single_baseline_comparator_report": "formal/output/reports/qm_stat_single_baseline_comparator_20260411_v0.json",
                "qm_stat_external_path_signal_execution_report": "formal/output/reports/qm_stat_external_path_signal_execution_20260411_v0.json",
            },
            "mapping_target": {
                "baseline_id": "OV-RL-10",
                "baseline_name": "RL10_ENTROPY_BALANCE",
                "exact_rl10_observable_quantity": "RL10_STATIONARY_PI_PLUS_ENTROPY_BALANCE_DIAGNOSTICS_INTERFACE",
                "required_candidate_fields": ["stationary_pi", "sigma_proxy", "db_residual"],
                "proposed_transform_question": "Can the QM-STAT finite-support mass and higher-moment parity signature be transformed?",
            },
            "review_contract": {
                "allowed_outcomes": [
                    "RL10_MAPPING_ESTABLISHED",
                    "RL10_MAPPING_NOT_YET_DEFINED",
                    "QM_STAT_EXTERNALIZATION_PATH_FALSIFIED",
                ],
                "rerun_policy": "NO_QM_STAT_EXTERNAL_PATH_RERUN_UNLESS_RL10_MAPPING_ESTABLISHED",
                "no_loop_rule": "ONE_QM_STAT_RL10_OBSERVABLE_MAPPING_REVIEW_ONLY",
            },
        },
    )


def test_qm_stat_rl10_mapping_review_reports_not_yet_defined_when_fields_are_missing(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(review_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "QM_STAT_RL10_OBSERVABLE_MAPPING_REVIEW_20260411_v0.json"
    )
    _write_declaration(declaration_path)
    _write_json(
        tmp_path / "formal" / "output" / "qm_stat_class_b_seam_physics_pilot_cycle11_v0.json",
        {"blocker_discharge_criteria": {"shared_support": [0, 1, 2]}},
    )
    _write_json(
        tmp_path / "formal" / "output" / "reports" / "qm_stat_single_baseline_comparator_20260411_v0.json",
        {
            "summary": {
                "comparator_status": "DECLARED_COMPLETE_SINGLE_BASELINE_ONLY",
                "candidate_mapping_status": "MOMENT_PARITY_SIGNATURE_ONLY_NOT_YET_RL10_OBSERVABLE_READY",
            }
        },
    )
    _write_json(
        tmp_path / "formal" / "output" / "reports" / "qm_stat_external_path_signal_execution_20260411_v0.json",
        {"summary": {"execution_outcome": "INTERNAL_ONLY_REMAINS"}},
    )

    report = review_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["mapping_review_outcome"] == "RL10_MAPPING_NOT_YET_DEFINED"
    assert report["summary"]["external_rerun_justified"] is False
    assert report["summary"]["missing_required_fields"] == ["stationary_pi", "sigma_proxy", "db_residual"]


def test_qm_stat_rl10_mapping_review_reports_established_when_fields_and_mapping_are_ready(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(review_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "QM_STAT_RL10_OBSERVABLE_MAPPING_REVIEW_20260411_v0.json"
    )
    _write_declaration(declaration_path)
    _write_json(
        tmp_path / "formal" / "output" / "qm_stat_class_b_seam_physics_pilot_cycle11_v0.json",
        {"stationary_pi": [0.2, 0.6, 0.2], "sigma_proxy": 0.0, "db_residual": 0.0},
    )
    _write_json(
        tmp_path / "formal" / "output" / "reports" / "qm_stat_single_baseline_comparator_20260411_v0.json",
        {
            "summary": {
                "comparator_status": "DECLARED_COMPLETE_SINGLE_BASELINE_ONLY",
                "candidate_mapping_status": "BASELINE_COMPARATOR_EVALUABLE",
            }
        },
    )
    _write_json(
        tmp_path / "formal" / "output" / "reports" / "qm_stat_external_path_signal_execution_20260411_v0.json",
        {"summary": {"execution_outcome": "INTERNAL_ONLY_REMAINS"}},
    )

    report = review_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["mapping_review_outcome"] == "RL10_MAPPING_ESTABLISHED"
    assert report["summary"]["external_rerun_justified"] is True
    assert report["summary"]["next_action"] == "AUTHORIZE_ONE_ADDITIONAL_QM_STAT_EXTERNAL_PATH_EXECUTION_ONLY"


def test_qm_stat_rl10_mapping_review_reports_path_falsified_when_prior_execution_falsified(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(review_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "QM_STAT_RL10_OBSERVABLE_MAPPING_REVIEW_20260411_v0.json"
    )
    _write_declaration(declaration_path)
    _write_json(tmp_path / "formal" / "output" / "qm_stat_class_b_seam_physics_pilot_cycle11_v0.json", {})
    _write_json(
        tmp_path / "formal" / "output" / "reports" / "qm_stat_single_baseline_comparator_20260411_v0.json",
        {
            "summary": {
                "comparator_status": "DECLARED_COMPLETE_SINGLE_BASELINE_ONLY",
                "candidate_mapping_status": "MOMENT_PARITY_SIGNATURE_ONLY_NOT_YET_RL10_OBSERVABLE_READY",
            }
        },
    )
    _write_json(
        tmp_path / "formal" / "output" / "reports" / "qm_stat_external_path_signal_execution_20260411_v0.json",
        {"summary": {"execution_outcome": "PATH_FALSIFIED"}},
    )

    report = review_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["mapping_review_outcome"] == "QM_STAT_EXTERNALIZATION_PATH_FALSIFIED"
    assert report["summary"]["next_action"] == "DO_NOT_RERUN_QM_STAT_EXTERNAL_PATH_AND_RECLASSIFY_RL10_ROUTE"
