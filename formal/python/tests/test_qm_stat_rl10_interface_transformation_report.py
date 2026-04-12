from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import qm_stat_rl10_interface_transformation_report as transform_tool


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
                "qm_stat_rl10_observable_mapping_review_report": "formal/output/reports/qm_stat_rl10_observable_mapping_review_20260411_v0.json",
                "qm_stat_single_baseline_comparator_report": "formal/output/reports/qm_stat_single_baseline_comparator_20260411_v0.json",
                "qm_stat_external_path_signal_execution_report": "formal/output/reports/qm_stat_external_path_signal_execution_20260411_v0.json",
            },
            "interface_target": {
                "baseline_id": "OV-RL-10",
                "required_observables": ["stationary_pi", "sigma_proxy", "db_residual"],
                "stationary_pi_rule": "MAP_BLOCKER_DISCHARGE_CRITERIA.stat_probability_mass_TO_DISCRETE_STATIONARY_PI_CANDIDATE_ON_SHARED_SUPPORT",
                "sigma_proxy_rule": "REQUIRES_DECLARED_TRANSITION_DYNAMICS_OR_GENERATOR_NOT_PRESENT_IN_CURRENT_QM_STAT_SURFACES",
                "db_residual_rule": "REQUIRES_DECLARED_BIDIRECTIONAL_TRANSITION_MATRIX_OR_FLOW_RATES_NOT_PRESENT_IN_CURRENT_QM_STAT_SURFACES",
            },
            "execution_contract": {
                "allowed_outcomes": [
                    "RL10_INTERFACE_DEFINED",
                    "RL10_INTERFACE_PARTIAL_HOLD",
                    "QM_STAT_EXTERNALIZATION_PATH_FALSIFIED",
                ],
                "no_loop_rule": "ONE_QM_STAT_RL10_INTERFACE_TRANSFORMATION_PACKET_ONLY",
                "rerun_policy": "NO_QM_STAT_EXTERNAL_PATH_RERUN_UNLESS_FULL_RL10_INTERFACE_DEFINED",
            },
        },
    )


def _write_common_inputs(root: Path) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_rl10_observable_mapping_review_20260411_v0.json",
        {"summary": {"mapping_review_outcome": "RL10_MAPPING_NOT_YET_DEFINED"}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_single_baseline_comparator_20260411_v0.json",
        {"summary": {"comparator_status": "DECLARED_COMPLETE_SINGLE_BASELINE_ONLY"}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_external_path_signal_execution_20260411_v0.json",
        {"summary": {"execution_outcome": "INTERNAL_ONLY_REMAINS"}},
    )


def test_qm_stat_rl10_interface_transformation_reports_partial_hold_from_current_surface(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(transform_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "QM_STAT_RL10_INTERFACE_TRANSFORMATION_PACKET_20260411_v0.json"
    )
    _write_declaration(declaration_path)
    _write_common_inputs(tmp_path)
    _write_json(
        tmp_path / "formal" / "output" / "qm_stat_class_b_seam_physics_pilot_cycle11_v0.json",
        {"blocker_discharge_criteria": {"stat_probability_mass": ["1/4", "1/2", "1/4"]}},
    )

    report = transform_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["transformation_outcome"] == "RL10_INTERFACE_PARTIAL_HOLD"
    assert report["summary"]["stationary_pi_status"] == "DEFINED_FROM_STAT_PROBABILITY_MASS"
    assert report["summary"]["sigma_proxy_status"] == "NOT_DEFINED_REQUIRES_DECLARED_TRANSITION_DYNAMICS"
    assert report["summary"]["db_residual_status"] == "NOT_DEFINED_REQUIRES_DECLARED_BIDIRECTIONAL_TRANSITION_RATES"


def test_qm_stat_rl10_interface_transformation_reports_defined_when_all_fields_exist(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(transform_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "QM_STAT_RL10_INTERFACE_TRANSFORMATION_PACKET_20260411_v0.json"
    )
    _write_declaration(declaration_path)
    _write_common_inputs(tmp_path)
    _write_json(
        tmp_path / "formal" / "output" / "qm_stat_class_b_seam_physics_pilot_cycle11_v0.json",
        {
            "blocker_discharge_criteria": {"stat_probability_mass": ["1/4", "1/2", "1/4"]},
            "sigma_proxy": 0.0,
            "db_residual": 0.0,
        },
    )

    report = transform_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["transformation_outcome"] == "RL10_INTERFACE_DEFINED"
    assert report["summary"]["full_interface_defined"] is True


def test_qm_stat_rl10_interface_transformation_reports_path_falsified_when_prior_execution_falsified(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(transform_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "QM_STAT_RL10_INTERFACE_TRANSFORMATION_PACKET_20260411_v0.json"
    )
    _write_declaration(declaration_path)
    _write_common_inputs(tmp_path)
    _write_json(
        tmp_path / "formal" / "output" / "reports" / "qm_stat_external_path_signal_execution_20260411_v0.json",
        {"summary": {"execution_outcome": "PATH_FALSIFIED"}},
    )
    _write_json(
        tmp_path / "formal" / "output" / "qm_stat_class_b_seam_physics_pilot_cycle11_v0.json",
        {},
    )

    report = transform_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["transformation_outcome"] == "QM_STAT_EXTERNALIZATION_PATH_FALSIFIED"
    assert report["summary"]["next_action"] == "DO_NOT_RERUN_QM_STAT_EXTERNAL_PATH_AND_RECLASSIFY_QM_STAT_RL10_ROUTE"
