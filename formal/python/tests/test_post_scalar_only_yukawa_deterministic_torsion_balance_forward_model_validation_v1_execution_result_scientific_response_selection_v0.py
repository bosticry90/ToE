from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from formal.python.tools import (
    post_scalar_only_yukawa_deterministic_torsion_balance_forward_model_validation_v1_execution_result_scientific_response_selection_v0
    as selection,
)


ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = ROOT / selection.REPORT_RELATIVE_PATH


def _report() -> dict[str, Any]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_selector_regenerates_and_consumes_exact_review_authority() -> None:
    assert selection.artifact_bytes() == REPORT_PATH.read_bytes()
    report = _report()
    assert report["target"] == selection.TARGET
    assert report["verdict"] == selection.VERDICT
    assert report["selected_route"] == selection.SELECTED_ROUTE
    assert report["selected_candidate_id"] == selection.SELECTED_CANDIDATE_ID
    assert report["selected_next_target"] == selection.SELECTED_NEXT_TARGET
    assert {
        row["relative_path"]: row["sha256"]
        for row in report["authority"]["frozen_result_review_artifacts"]
    } == selection.AUTHORITY_HASHES


def test_exactly_four_routes_and_eight_weighted_criteria_are_compared() -> None:
    policy = _report()["selection_policy"]
    assert policy["candidate_count"] == 4
    assert policy["criterion_count"] == 8
    assert policy["criteria_weights"] == selection.CRITERIA
    assert len(_report()["ranking"]["rows"]) == 4


def test_bounded_diagnosis_is_the_stable_first_ranked_route() -> None:
    ranking = _report()["ranking"]
    assert ranking["selected_candidate_id"] == selection.SELECTED_CANDIDATE_ID
    assert ranking["selected_score"] == 172
    assert ranking["runner_up_candidate_id"] == "REPLACE_PRODUCTION_INTEGRATION_METHOD"
    assert ranking["runner_up_score"] == 116
    assert ranking["winning_margin"] == 56
    sensitivity = _report()["sensitivity_analysis"]
    assert sensitivity["variant_count"] == 24
    assert sensitivity["selected_candidate_stable_in_all_variants"] is True
    assert sensitivity["minimum_winning_margin"] > 0


def test_accepted_block_is_not_misreported_as_physical_unidentifiability() -> None:
    row = _report()["accepted_result_interpretation"]
    assert row["principal_result"] == "BLOCKED_PRODUCTION_KERNEL_VALIDATION"
    assert row["deterministic_apparatus_model"] == "NOT_VALIDATED"
    assert row["apparatus_physically_unidentifiable"] is False
    assert row["physical_identifiability"] == "NOT_TESTED"
    assert row["jacobian"] == "NOT_COMPUTED"
    assert row["stage_b"] == "NOT_AUTHORIZED"
    assert row["rerun"] == "NOT_AUTHORIZED"


def test_diagnosis_requires_separate_newtonian_and_yukawa_records() -> None:
    row = _report()["diagnosis_packet_preparation_requirements"]["component_separation"]
    assert row["required_components"] == ["NEWTONIAN", "YUKAWA"]
    assert row["required_records"] == [
        "ABSOLUTE_RESULT",
        "RELATIVE_ERROR",
        "CONVERGENCE_RECORD",
        "DIMENSIONAL_CHECK",
        "LIMITING_BEHAVIOR",
    ]
    assert row["combined_total_cannot_substitute"] is True


def test_independent_oracle_must_self_converge() -> None:
    row = _report()["diagnosis_packet_preparation_requirements"]["reference_oracle"]
    assert row["nearby_order_same_cubature_sufficient"] is False
    assert row["independent_route_required"] is True
    assert len(row["permitted_families"]) == 5
    assert row["oracle_self_convergence_required"] is True
    assert row["oracle_tolerances_must_be_frozen_before_execution"] is True


def test_gap_range_near_contact_and_precision_probes_are_required() -> None:
    requirements = _report()["diagnosis_packet_preparation_requirements"]
    strata = requirements["gap_and_range_strata"]
    assert strata["lambda_regimes"] == [
        "LAMBDA_MUCH_LESS_THAN_GAP",
        "LAMBDA_COMPARABLE_TO_GAP",
        "LAMBDA_MUCH_GREATER_THAN_GAP",
    ]
    assert strata["exact_grid_must_be_frozen_in_packet"] is True
    assert strata["post_result_point_selection_forbidden"] is True
    assert all(requirements["near_contact_diagnosis"].values())
    assert all(requirements["precision_and_cancellation"].values())


def test_angular_dft_isolated_with_analytic_signal_first() -> None:
    row = _report()["diagnosis_packet_preparation_requirements"]["angular_dft_isolation"]
    assert row["analytic_synthetic_torque_first"] is True
    assert row["known_harmonics"] == [2, 4, 6]
    assert row["production_torque_test_after_kernel_accuracy_only"] is True
    assert row["distinguish_grid_resolution_from_kernel_noise"] is True


def test_outputs_are_diagnostic_only_and_root_causes_are_frozen() -> None:
    requirements = _report()["diagnosis_packet_preparation_requirements"]
    assert len(requirements["required_outputs"]) == 9
    assert requirements["forbidden_outputs"] == [
        "FINAL_REAL_150_APPARATUS_VECTOR",
        "JACOBIAN",
        "SVD",
        "ETA_LAMBDA",
        "IDENTIFIABILITY_RESULT",
        "SYNTHETIC_NOISE",
        "SENSITIVITY_FORECAST",
    ]
    assert requirements["root_cause_outcomes"] == list(selection.ROOT_CAUSE_OUTCOMES)


def test_all_twenty_selector_gates_pass() -> None:
    gates = _report()["selection_gates"]
    assert gates["gate_count"] == gates["pass_count"] == 20
    assert gates["failure_count"] == 0
    assert all(row["status"] == "PASS" for row in gates["rows"])


def test_scope_authorizes_packet_preparation_only() -> None:
    scope = _report()["scope"]
    allowed_true = {
        "scientific_response_selection_executed",
        "accepted_execution_result_frozen",
        "four_bounded_options_compared",
        "kernel_diagnosis_packet_preparation_authorized",
        "independent_reference_oracle_packet_preparation_authorized",
    }
    for key, value in scope.items():
        assert value is (key in allowed_true), key


def test_anti_rabbit_hole_boundary_forbids_rerun_and_method_tuning() -> None:
    boundary = _report()["anti_rabbit_hole_boundary"]
    assert all(boundary.values())
    assert boundary["full_stage_a_rerun_prohibited"] is True
    assert boundary["tolerance_relaxation_prohibited"] is True
    assert boundary["result_dependent_method_selection_prohibited"] is True
    assert boundary["automatic_v2_prohibited"] is True


def test_human_selector_records_exact_route_scope_and_next_target() -> None:
    text = (ROOT / selection.HUMAN_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        selection.VERDICT,
        selection.SELECTED_ROUTE,
        "172",
        "116",
        "24 frozen",
        "not truth probabilities",
        "diagnosis packet prepared now:       NO",
        selection.SELECTED_NEXT_TARGET,
    ):
        assert token in text
