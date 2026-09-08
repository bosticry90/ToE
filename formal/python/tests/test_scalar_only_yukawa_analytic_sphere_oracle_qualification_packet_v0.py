from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from formal.python.tools import (
    scalar_only_yukawa_analytic_sphere_oracle_qualification_packet_v0 as packet,
)


ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = ROOT / packet.REPORT_RELATIVE_PATH


def _report() -> dict[str, Any]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_packet_regenerates_and_consumes_exact_selector_authority() -> None:
    assert packet.artifact_bytes() == REPORT_PATH.read_bytes()
    report = _report()
    assert report["target"] == packet.TARGET
    assert report["verdict"] == packet.VERDICT
    assert report["status"] == "PREPARED_PENDING_INDEPENDENT_REVIEW"
    assert report["selected_next_target"] == packet.SELECTED_NEXT_TARGET
    assert {
        row["relative_path"]: row["sha256"]
        for row in report["authority"]["frozen_selector_artifacts"]
    } == packet.SELECTOR_HASHES


def test_newtonian_and_yukawa_derivation_contract_is_exact() -> None:
    report = _report()
    conventions = report["physical_conventions"]
    assert conventions["yukawa_amplitude_exact"] == "1/3"
    assert conventions["surface_gap_definition"] == "g=D-R1-R2"
    assert conventions["strict_nonoverlap_rule"].startswith("D>R1+R2")
    derivation = report["derivation_contract"]
    assert derivation["newtonian_oracle"] == "U_N(D)=-G*M1*M2/D"
    assert derivation["sphere_form_factor"] == "F(x)=3*(x*cosh(x)-sinh(x))/x^3"
    assert "F(x1)*F(x2)*exp(-D/lambda)" in derivation["yukawa_oracle"]
    assert len(derivation["obligations"]) == 8
    assert derivation["derivation_may_be_replaced_by_standard_formula_citation"] is False


def test_three_stable_evaluator_regimes_and_pair_identity_are_frozen() -> None:
    evaluator = _report()["stable_evaluator_contract"]
    assert evaluator["common_scaled_output"] == "H(x)=exp(-x)*F(x)"
    assert evaluator["small_x"]["primary_domain"] == "0<x<=0.1"
    assert "x^8/1330560" in evaluator["small_x"]["formula"]
    assert evaluator["moderate_x"]["primary_domain"] == "0.1<x<=40"
    assert evaluator["large_x"]["primary_domain"] == "40<x<=1000"
    assert evaluator["large_x"]["direct_sinh_or_cosh_forbidden"] is True
    assert "exp(-g/lambda)*H(x1)*H(x2)" in evaluator["stable_pair_factor"]
    assert evaluator["log_domain_energy_required"] is True
    assert evaluator["silent_overflow_or_underflow_forbidden"] is True


def test_overlap_grids_bound_both_regime_transitions() -> None:
    overlaps = _report()["stable_evaluator_contract"]["overlap_checks"]
    assert overlaps == [
        {
            "overlap_id": "SMALL_DIRECT",
            "x_values": [0.05, 0.1, 0.2],
            "absolute_tolerance_H": 5e-14,
            "relative_tolerance_H": 5e-11,
        },
        {
            "overlap_id": "DIRECT_SCALED",
            "x_values": [20.0, 32.0, 40.0],
            "absolute_tolerance_H": 5e-15,
            "relative_tolerance_H": 5e-13,
        },
    ]


def test_eight_case_grid_is_nonoverlapping_bounded_and_role_complete() -> None:
    domain = _report()["representative_domain"]
    assert domain["case_count"] == 8
    assert domain["minimum_case_count"] == 6
    assert domain["maximum_case_count"] == 9
    assert domain["maximum_x"] == 1000.0
    assert domain["failed_stage_a_case_count"] == 3
    assert all(row["strictly_nonoverlapping"] for row in domain["rows"])
    assert all(row["center_distance_m"] > row["radius_1_m"] + row["radius_2_m"] for row in domain["rows"])
    roles = {role for row in domain["rows"] for role in row["roles"]}
    assert {
        "SMALL_X", "X_NEAR_ONE", "LARGE_X", "X_MAX_1000", "EQUAL_RADII",
        "UNEQUAL_RADII", "WIDE_SEPARATION", "SMALL_POSITIVE_GAP",
    } <= roles
    assert domain["post_result_case_addition_removal_or_shift"] == "FORBIDDEN"


def test_single_independent_radial_cross_check_is_production_free() -> None:
    cross = _report()["independent_cross_check_contract"]
    assert cross["path_count"] == 1
    assert cross["dimension"] == 1
    assert "expm1" in cross["scaled_integral"]
    assert cross["decimal_precision_ladder"] == [50, 80, 120]
    assert cross["plateau_levels"] == [80, 120]
    assert cross["all_eight_cases"] is True
    assert cross["analytic_form_factor_call_forbidden"] is True
    assert cross["closed_form_scaled_factor_call_forbidden"] is True
    assert cross["production_kernel_or_cubature_import_forbidden"] is True
    assert cross["self_convergence"]["absolute_tolerance_H"] == 1e-30
    assert cross["cross_agreement"]["energy_absolute_tolerance_J"] == 1e-38


def test_resource_and_process_custody_is_strict_and_stage_atomic() -> None:
    custody = _report()["resource_and_custody_contract"]
    assert custody["total_wall_clock_seconds_max"] == 600
    assert custody["memory_mib_max"] == 2048
    assert sum(row["wall_clock_seconds_max"] for row in custody["stage_rows"]) == 600
    assert custody["process_group_termination"] == "MANDATORY"
    assert custody["raw_launcher_transcript"] == "PRESERVED"
    assert custody["timeout_initiation_timestamp"] == "PRESERVED"
    assert custody["child_process_tree_and_termination_timestamps"] == "PRESERVED"
    assert custody["zero_surviving_process_check"] == "MANDATORY"
    assert custody["stage_level_atomic_status"] == "REQUIRED"
    assert custody["packet_wide_qualified_outcome_requires_all_stages_complete"] is True
    assert custody["result_dependent_budget_change"] == "FORBIDDEN"


def test_all_eight_mutations_traverse_live_future_path() -> None:
    mutations = _report()["mutation_controls"]
    assert mutations["mutation_count"] == 8
    assert len(mutations["rows"]) == 8
    assert mutations["same_live_oracle_evaluator_and_adjudicator_required"] is True
    assert mutations["metadata_only_rejection_forbidden"] is True
    assert {row["mutation_id"] for row in mutations["rows"]} == {
        "INTERPRET_RADIUS_AS_DIAMETER",
        "USE_SURFACE_GAP_AS_CENTER_DISTANCE",
        "OMIT_FOUR_PI_OVER_THREE_MASS_FACTOR",
        "OMIT_A_Y_ONE_THIRD",
        "OMIT_SECOND_SPHERE_FORM_FACTOR",
        "FLIP_YUKAWA_EXPONENTIAL_SIGN",
        "FORCE_DIRECT_LARGE_X_SINH_COSH_PATH",
        "FORCE_DIRECT_SMALL_X_CANCELLATION_PATH",
    }
    assert all(row["required_result"] == "FAIL" for row in mutations["rows"])


def test_terminal_outcomes_and_success_eligibility_are_exact() -> None:
    output = _report()["execution_output_contract"]
    assert output["terminal_outcomes"] == list(packet.TERMINAL_OUTCOMES)
    assert output["only_success_eligibility"].startswith(
        "Only ANALYTIC_SPHERE_ORACLE_QUALIFIED"
    )
    assert len(output["authorized_only_after_accepted_review"]) == 9
    assert output["forbidden_outputs"] == [
        "PRODUCTION_CUBATURE_JUDGMENT",
        "PRODUCTION_INTEGRATION_REPLACEMENT",
        "TORQUE",
        "ANGULAR_DFT",
        "APPARATUS_HARMONICS",
        "FINAL_REAL_150_VECTOR",
        "JACOBIAN_OR_SVD",
        "IDENTIFIABILITY",
        "SENSITIVITY_FORECAST_OR_STAGE_B",
    ]


def test_packet_review_authorizes_at_most_one_future_oracle_execution() -> None:
    review = _report()["packet_review_contract"]
    assert review["review_outcomes"] == list(packet.PACKET_REVIEW_OUTCOMES)
    assert review["ready_outcome_authorizes"] == (
        "ONE_SMALL_ANALYTIC_ORACLE_QUALIFICATION_EXECUTION_ONLY"
    )
    assert review["authorized_execution_count"] == 1
    assert review["executions_consumed"] == 0
    assert len(review["ready_outcome_does_not_authorize"]) == 6
    assert review["post_execution_independent_result_review_required"] is True
    assert review["post_result_fresh_scientific_response_selector_required"] is True


def test_all_preparation_gates_pass_without_scientific_execution() -> None:
    gates = _report()["preparation_gates"]
    assert gates["gate_count"] == gates["pass_count"] == 42
    assert gates["failure_count"] == 0
    assert all(row["status"] == "PASS" for row in gates["rows"])


def test_scope_is_packet_preparation_only() -> None:
    scope = _report()["scope"]
    allowed_true = {
        "analytic_oracle_packet_prepared",
        "selector_authority_consumed",
        "case_grid_constructed_as_contract_metadata",
        "independent_packet_review_required",
    }
    for key, value in scope.items():
        assert value is (key in allowed_true), key


def test_human_packet_records_formulas_grid_custody_and_stop() -> None:
    text = (ROOT / packet.HUMAN_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        packet.VERDICT,
        "H_radial(x)",
        "EXTREME_X_1000_UNEQUAL",
        "600 seconds and 2048 MiB",
        "Process-group termination is mandatory",
        "ANALYTIC_SPHERE_ORACLE_QUALIFIED",
        packet.SELECTED_NEXT_TARGET,
        "NOT AUTHORIZED / NOT PERFORMED",
    ):
        assert token in text
