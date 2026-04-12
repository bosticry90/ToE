from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import qm_stat_rl10_discrete_transition_bridge_first_test_packet_report as packet_tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "new_external_path_seam_model_proposal_declaration": "formal/docs/release/NEW_EXTERNAL_PATH_SEAM_MODEL_PROPOSAL_20260411_v0.json",
                "new_external_path_seam_model_proposal_report": "formal/output/reports/new_external_path_seam_model_proposal_20260411_v0.json",
                "qm_stat_transition_dynamics_feasibility_review_report": "formal/output/reports/qm_stat_transition_dynamics_feasibility_review_20260411_v0.json",
                "qm_stat_rl10_sigma_db_transformation_report": "formal/output/reports/qm_stat_rl10_sigma_db_transformation_20260411_v0.json",
                "qm_stat_single_baseline_comparator_report": "formal/output/reports/qm_stat_single_baseline_comparator_20260411_v0.json",
            },
            "test_scope": {
                "proposed_seam_model_class_id": "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_SEAM_v0",
                "bounded_first_test_id": "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_FIRST_TEST_v0",
                "governance_boundary": "DO_NOT_REOPEN_EXISTING_QM_STAT_OR_OTHER_CYCLE11_LANES",
                "single_baseline_id": "OV-RL-10",
                "discrete_support_only": True,
            },
            "declared_transition_structure": {
                "discrete_transition_kernel": {
                    "kernel_id": "RL10_BRIDGE_KERNEL_v0",
                    "state_space": ["S0", "S1", "S2"],
                    "row_stochastic": True,
                },
                "bidirectional_transition_rate_matrix": {
                    "matrix_id": "RL10_BRIDGE_RATE_MATRIX_v0",
                    "shape": [3, 3],
                    "bidirectional": True,
                    "nonnegative_off_diagonal": True,
                },
                "stationary_flow_sigma_db_interface": {
                    "interface_id": "RL10_BRIDGE_SIGMA_DB_INTERFACE_v0",
                    "sigma_proxy_mapping_declared": True,
                    "db_residual_mapping_declared": True,
                    "baseline_id": "OV-RL-10",
                },
            },
            "undeclared_structure_policy": {
                "allowed_new_assumptions": [
                    "DECLARE_DISCRETE_TRANSITION_DYNAMICS_OPERATOR_OR_MARKOV_KERNEL",
                    "DECLARE_BIDIRECTIONAL_TRANSITION_RATES_OR_EQUIVALENT_TRANSITION_MATRIX",
                    "DECLARE_STATIONARY_FLOW_TO_SIGMA_DB_OBSERVABLE_INTERFACE",
                ],
                "forbidden_extra_assumptions": [],
            },
            "terminal_contract": {
                "allowed_outcomes": [
                    "BRIDGE_SEAM_FIRST_TEST_EXECUTABLE",
                    "BRIDGE_SEAM_FIRST_TEST_INCOHERENT",
                    "BRIDGE_SEAM_FIRST_TEST_OUT_OF_SCOPE",
                    "BRIDGE_SEAM_FIRST_TEST_REQUIRES_UNDECLARED_STRUCTURE",
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_TERMINAL_OUTCOME",
                "no_loop_rule": "ONE_BOUNDED_FIRST_TEST_PACKET_ONLY",
            },
        },
    )


def _seed_common_inputs(root: Path) -> None:
    _write_json(
        root / "formal" / "docs" / "release" / "NEW_EXTERNAL_PATH_SEAM_MODEL_PROPOSAL_20260411_v0.json",
        {
            "proposal_scope": {
                "proposed_seam_model_class_id": "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_SEAM_v0",
                "bounded_first_test_id": "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_FIRST_TEST_v0",
            },
            "proposal_contract": {
                "no_existing_lane_reopen_rule": "DO_NOT_REOPEN_EXISTING_QM_STAT_OR_OTHER_CYCLE11_LANES_FROM_THIS_PROPOSAL"
            },
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "new_external_path_seam_model_proposal_20260411_v0.json",
        {
            "summary": {
                "proposal_outcome": "NEW_SEAM_MODEL_PROPOSAL_JUSTIFIED",
                "proposed_seam_model_class_id": "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_SEAM_v0",
                "bounded_first_test_id": "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_FIRST_TEST_v0",
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_transition_dynamics_feasibility_review_20260411_v0.json",
        {"summary": {"review_outcome": "TRANSITION_DYNAMICS_EXTENSION_OUT_OF_SCOPE"}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_rl10_sigma_db_transformation_20260411_v0.json",
        {
            "summary": {
                "sigma_proxy_definable_from_current_qm_stat_surfaces": False,
                "db_residual_definable_from_current_qm_stat_surfaces": False,
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_single_baseline_comparator_20260411_v0.json",
        {
            "summary": {
                "comparator_status": "DECLARED_COMPLETE_SINGLE_BASELINE_ONLY",
                "baseline_id": "OV-RL-10",
            }
        },
    )


def test_first_test_packet_reports_executable_when_all_criteria_pass(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(packet_tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_FIRST_TEST_PACKET_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_common_inputs(tmp_path)

    report = packet_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "BRIDGE_SEAM_FIRST_TEST_EXECUTABLE"


def test_first_test_packet_reports_incoherent_for_bad_transition_shape(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(packet_tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_FIRST_TEST_PACKET_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_common_inputs(tmp_path)
    declaration = json.loads(declaration_path.read_text(encoding="utf-8"))
    declaration["declared_transition_structure"]["bidirectional_transition_rate_matrix"]["shape"] = [2, 3]
    declaration_path.write_text(json.dumps(declaration, indent=2) + "\n", encoding="utf-8")

    report = packet_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "BRIDGE_SEAM_FIRST_TEST_INCOHERENT"


def test_first_test_packet_reports_out_of_scope_if_proposal_not_justified(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(packet_tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_FIRST_TEST_PACKET_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_common_inputs(tmp_path)
    _write_json(
        tmp_path / "formal" / "output" / "reports" / "new_external_path_seam_model_proposal_20260411_v0.json",
        {
            "summary": {
                "proposal_outcome": "PROPOSAL_UNDERDEFINED",
                "proposed_seam_model_class_id": "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_SEAM_v0",
                "bounded_first_test_id": "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_FIRST_TEST_v0",
            }
        },
    )

    report = packet_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "BRIDGE_SEAM_FIRST_TEST_OUT_OF_SCOPE"


def test_first_test_packet_reports_requires_undeclared_structure_when_policy_violated(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(packet_tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_RL10_DISCRETE_TRANSITION_BRIDGE_FIRST_TEST_PACKET_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_common_inputs(tmp_path)
    declaration = json.loads(declaration_path.read_text(encoding="utf-8"))
    declaration["undeclared_structure_policy"]["forbidden_extra_assumptions"] = ["UNDECLARED_EXTRA_STRUCTURE"]
    declaration_path.write_text(json.dumps(declaration, indent=2) + "\n", encoding="utf-8")

    report = packet_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert (
        report["summary"]["terminal_outcome"]
        == "BRIDGE_SEAM_FIRST_TEST_REQUIRES_UNDECLARED_STRUCTURE"
    )