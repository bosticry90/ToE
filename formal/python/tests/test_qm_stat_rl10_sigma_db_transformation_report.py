from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import qm_stat_rl10_sigma_db_transformation_report as transform_tool


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
                "qm_stat_rl10_interface_transformation_report": "formal/output/reports/qm_stat_rl10_interface_transformation_20260411_v0.json",
                "qm_stat_external_path_signal_execution_report": "formal/output/reports/qm_stat_external_path_signal_execution_20260411_v0.json",
            },
            "transformation_targets": {
                "sigma_proxy_target": "RL10_ENTROPY_PRODUCTION_PROXY_SIGMA",
                "db_residual_target": "RL10_DETAILED_BALANCE_RESIDUAL",
                "stationary_pi_source_rule": "USE_BLOCKER_DISCHARGE_CRITERIA.stat_probability_mass_AS_DISCRETE_STATIONARY_PI_INPUT",
                "sigma_proxy_dependency_rule": "REQUIRES_DECLARED_TRANSITION_DYNAMICS_OPERATOR_OR_TRANSITION_MATRIX_TO_COMPUTE_DIRECTIONAL_FLOWS",
                "db_residual_dependency_rule": "REQUIRES_DECLARED_BIDIRECTIONAL_TRANSITION_RATES_OR_TRANSITION_MATRIX_TO_COMPUTE_FLOW_IMBALANCE",
            },
            "assumption_contract": {
                "required_transition_assumptions": [
                    "DECLARED_DISCRETE_TRANSITION_DYNAMICS_OPERATOR_OR_MARKOV_KERNEL",
                    "DECLARED_BIDIRECTIONAL_TRANSITION_RATES_OR_EQUIVALENT_TRANSITION_MATRIX",
                    "DECLARED_FLOW_CONSTRUCTION_LINKING_STATIONARY_PI_TO_TRANSITION_STRUCTURE",
                ],
            },
            "execution_contract": {
                "allowed_outcomes": [
                    "SIGMA_DB_INTERFACE_DEFINED",
                    "SIGMA_DB_INTERFACE_PARTIAL_HOLD",
                    "QM_STAT_EXTERNALIZATION_PATH_FALSIFIED",
                ],
                "no_loop_rule": "ONE_QM_STAT_RL10_SIGMA_DB_TRANSFORMATION_PACKET_ONLY",
                "rerun_policy": "NO_QM_STAT_EXTERNAL_PATH_RERUN_UNLESS_SIGMA_DB_INTERFACE_DEFINED",
            },
        },
    )


def _write_common_inputs(root: Path) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_rl10_interface_transformation_20260411_v0.json",
        {"summary": {"transformation_outcome": "RL10_INTERFACE_PARTIAL_HOLD"}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_external_path_signal_execution_20260411_v0.json",
        {"summary": {"execution_outcome": "INTERNAL_ONLY_REMAINS"}},
    )


def test_qm_stat_rl10_sigma_db_transformation_reports_partial_hold_when_transition_structure_is_missing(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(transform_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "QM_STAT_RL10_SIGMA_DB_TRANSFORMATION_PACKET_20260411_v0.json"
    )
    _write_declaration(declaration_path)
    _write_common_inputs(tmp_path)
    _write_json(
        tmp_path / "formal" / "output" / "qm_stat_class_b_seam_physics_pilot_cycle11_v0.json",
        {"blocker_discharge_criteria": {"stat_probability_mass": ["1/4", "1/2", "1/4"]}},
    )

    report = transform_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["transformation_outcome"] == "SIGMA_DB_INTERFACE_PARTIAL_HOLD"
    assert report["summary"]["sigma_proxy_definable_from_current_qm_stat_surfaces"] is False
    assert report["summary"]["db_residual_definable_from_current_qm_stat_surfaces"] is False


def test_qm_stat_rl10_sigma_db_transformation_reports_defined_when_transition_matrix_exists(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(transform_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "QM_STAT_RL10_SIGMA_DB_TRANSFORMATION_PACKET_20260411_v0.json"
    )
    _write_declaration(declaration_path)
    _write_common_inputs(tmp_path)
    _write_json(
        tmp_path / "formal" / "output" / "qm_stat_class_b_seam_physics_pilot_cycle11_v0.json",
        {
            "blocker_discharge_criteria": {"stat_probability_mass": ["1/4", "1/2", "1/4"]},
            "transition_matrix": [[0.7, 0.2, 0.1], [0.2, 0.6, 0.2], [0.1, 0.2, 0.7]],
        },
    )

    report = transform_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["transformation_outcome"] == "SIGMA_DB_INTERFACE_DEFINED"
    assert report["summary"]["sigma_proxy_definable_from_current_qm_stat_surfaces"] is True
    assert report["summary"]["db_residual_definable_from_current_qm_stat_surfaces"] is True


def test_qm_stat_rl10_sigma_db_transformation_reports_path_falsified_when_prior_execution_falsified(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(transform_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "QM_STAT_RL10_SIGMA_DB_TRANSFORMATION_PACKET_20260411_v0.json"
    )
    _write_declaration(declaration_path)
    _write_common_inputs(tmp_path)
    _write_json(
        tmp_path / "formal" / "output" / "reports" / "qm_stat_external_path_signal_execution_20260411_v0.json",
        {"summary": {"execution_outcome": "PATH_FALSIFIED"}},
    )
    _write_json(tmp_path / "formal" / "output" / "qm_stat_class_b_seam_physics_pilot_cycle11_v0.json", {})

    report = transform_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["transformation_outcome"] == "QM_STAT_EXTERNALIZATION_PATH_FALSIFIED"
    assert report["summary"]["next_action"] == "DO_NOT_RERUN_QM_STAT_EXTERNAL_PATH_AND_RECLASSIFY_SIGMA_DB_ROUTE"
