from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import qm_stat_transition_dynamics_feasibility_review_report as review_tool


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
                "source_signature_artifact": "formal/output/qm_stat_class_b_seam_physics_pilot_cycle11_v0.json",
                "derivation_target_artifact": "formal/docs/paper/DERIVATION_TARGET_QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE11_v0.md",
            },
            "required_inputs": {
                "qm_stat_rl10_sigma_db_transformation_report": "formal/output/reports/qm_stat_rl10_sigma_db_transformation_20260411_v0.json",
            },
            "feasibility_questions": {
                "transition_operator_question": "CAN_A_DISCRETE_TRANSITION_OPERATOR_OR_MARKOV_KERNEL_BE_DECLARED_WITHOUT_VIOLATING_CURRENT_QM_STAT_SCOPE",
                "bidirectional_rate_question": "CAN_BIDIRECTIONAL_TRANSITION_RATES_BE_INTRODUCED_WITHOUT_COLLAPSING_THE_CURRENT_INTERPRETATION_BOUNDARY",
                "model_class_question": "WOULD_ADDING_TRANSITION_STRUCTURE_REMAIN_WITHIN_QM_STAT_OR_REQUIRE_A_NEW_SEAM_OR_MODEL_CLASS",
            },
            "assumption_targets": {
                "sigma_proxy_required_assumptions": [
                    "DECLARE_DISCRETE_TRANSITION_DYNAMICS_OPERATOR_OR_MARKOV_KERNEL",
                    "DECLARE_DIRECTIONAL_STATE_TO_STATE_FLOW_CONSTRUCTION",
                ],
                "db_residual_required_assumptions": [
                    "DECLARE_BIDIRECTIONAL_TRANSITION_RATES_OR_EQUIVALENT_TRANSITION_MATRIX",
                    "DECLARE_DETAILED_BALANCE_RESIDUAL_CONSTRUCTION_FROM_STATIONARY_FLOW_DIFFERENCE",
                ],
            },
            "review_contract": {
                "allowed_outcomes": [
                    "TRANSITION_DYNAMICS_EXTENSION_JUSTIFIED",
                    "TRANSITION_DYNAMICS_EXTENSION_OUT_OF_SCOPE",
                    "QM_STAT_RL10_EXTERNALIZATION_PATH_FALSIFIED",
                ],
                "no_loop_rule": "ONE_QM_STAT_TRANSITION_DYNAMICS_FEASIBILITY_REVIEW_ONLY",
                "rerun_policy": "NO_QM_STAT_EXTERNAL_PATH_OR_SIGMA_DB_RERUN_UNLESS_TRANSITION_DYNAMICS_EXTENSION_JUSTIFIED",
            },
        },
    )


def test_transition_dynamics_review_reports_out_of_scope_for_cycle11_audit_only_lane(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(review_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_TRANSITION_DYNAMICS_FEASIBILITY_REVIEW_20260411_v0.json"
    )
    _write_declaration(declaration_path)
    _write_json(
        tmp_path / "formal" / "output" / "reports" / "qm_stat_rl10_sigma_db_transformation_20260411_v0.json",
        {"summary": {"transformation_outcome": "SIGMA_DB_INTERFACE_PARTIAL_HOLD"}},
    )
    _write_json(
        tmp_path / "formal" / "output" / "qm_stat_class_b_seam_physics_pilot_cycle11_v0.json",
        {
            "status": "CRITERIA_AND_EIGHTEENTH_MOMENT_EXCLUSION_PINNED_NONCLAIM",
            "bounded_scope": {
                "class_flip_claimed": False,
                "full_theorem_discharge_claimed": False,
                "continuum_statistical_closure_claimed": False,
                "external_truth_claimed": False,
            },
        },
    )
    _write_text(
        tmp_path / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE11_v0.md",
        "\n".join(
            [
                "QM_STAT_CYCLE11_SCOPE_v0: FINITE_STATE_DISCRETE_HIGHER_MOMENT_AUDIT_ONLY_NONCLAIM",
                "Non-claim boundary:",
                "- no continuum statistical closure claim,",
                "- no external truth claim,",
                "- no full theorem discharge claim.",
            ]
        ),
    )

    report = review_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["review_outcome"] == "TRANSITION_DYNAMICS_EXTENSION_OUT_OF_SCOPE"
    assert report["summary"]["can_declare_transition_operator_without_scope_violation"] is False
    assert report["summary"]["can_introduce_bidirectional_rates_without_boundary_collapse"] is False
    assert report["summary"]["resulting_model_class"] == "NEW_SEAM_OR_MODEL_CLASS_REQUIRED"


def test_transition_dynamics_review_reports_justified_when_transition_scope_is_explicitly_available(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(review_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_TRANSITION_DYNAMICS_FEASIBILITY_REVIEW_20260411_v0.json"
    )
    _write_declaration(declaration_path)
    _write_json(
        tmp_path / "formal" / "output" / "reports" / "qm_stat_rl10_sigma_db_transformation_20260411_v0.json",
        {"summary": {"transformation_outcome": "SIGMA_DB_INTERFACE_PARTIAL_HOLD"}},
    )
    _write_json(
        tmp_path / "formal" / "output" / "qm_stat_class_b_seam_physics_pilot_cycle11_v0.json",
        {
            "status": "TRANSITION_STRUCTURE_AUTHORIZED_WITHIN_QM_STAT_SCOPE",
            "bounded_scope": {
                "class_flip_claimed": False,
                "full_theorem_discharge_claimed": False,
                "continuum_statistical_closure_claimed": True,
                "external_truth_claimed": False,
            },
            "transition_kernel": {"type": "declared"},
        },
    )
    _write_text(
        tmp_path / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE11_v0.md",
        "QM_STAT_CYCLE11_SCOPE_v0: TRANSITION_DYNAMICS_EXTENSION_AUTHORIZED_NONCLAIM\n",
    )

    report = review_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["review_outcome"] == "TRANSITION_DYNAMICS_EXTENSION_JUSTIFIED"
    assert report["summary"]["can_declare_transition_operator_without_scope_violation"] is True
    assert report["summary"]["can_introduce_bidirectional_rates_without_boundary_collapse"] is True
    assert report["summary"]["resulting_model_class"] == "QM_STAT_SCOPE_EXTENSION_STILL_WITHIN_CURRENT_LANE"


def test_transition_dynamics_review_reports_falsified_when_sigma_db_route_is_already_falsified(
    tmp_path: Path,
    monkeypatch,
) -> None:
    monkeypatch.setattr(review_tool, "REPO_ROOT", tmp_path)

    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "QM_STAT_TRANSITION_DYNAMICS_FEASIBILITY_REVIEW_20260411_v0.json"
    )
    _write_declaration(declaration_path)
    _write_json(
        tmp_path / "formal" / "output" / "reports" / "qm_stat_rl10_sigma_db_transformation_20260411_v0.json",
        {"summary": {"transformation_outcome": "QM_STAT_EXTERNALIZATION_PATH_FALSIFIED"}},
    )
    _write_json(
        tmp_path / "formal" / "output" / "qm_stat_class_b_seam_physics_pilot_cycle11_v0.json",
        {"bounded_scope": {}},
    )
    _write_text(
        tmp_path / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_CYCLE11_v0.md",
        "QM_STAT_CYCLE11_SCOPE_v0: FINITE_STATE_DISCRETE_HIGHER_MOMENT_AUDIT_ONLY_NONCLAIM\n",
    )

    report = review_tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["review_outcome"] == "QM_STAT_RL10_EXTERNALIZATION_PATH_FALSIFIED"
    assert (
        report["summary"]["next_action"]
        == "DO_NOT_RERUN_QM_STAT_EXTERNAL_PATH_AND_RECLASSIFY_TRANSITION_DYNAMICS_ROUTE"
    )
