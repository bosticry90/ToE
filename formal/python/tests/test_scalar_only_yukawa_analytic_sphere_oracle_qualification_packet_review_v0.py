from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from formal.python.tools import (
    scalar_only_yukawa_analytic_sphere_oracle_qualification_packet_review_v0 as review,
)


ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = ROOT / review.REPORT_RELATIVE_PATH


def _report() -> dict[str, Any]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_review_regenerates_and_consumes_exact_packet_authority() -> None:
    assert review.artifact_bytes() == REPORT_PATH.read_bytes()
    report = _report()
    assert report["target"] == review.TARGET
    assert report["verdict"] == review.VERDICT
    assert report["status"] == "INDEPENDENT_PACKET_REVIEW_COMPLETE"
    assert report["selected_next_target"] == review.SELECTED_NEXT_TARGET
    assert {
        row["relative_path"]: row["sha256"]
        for row in report["authority"]["frozen_packet_artifacts"]
    } == review.PACKET_HASHES


def test_eight_cases_reproduce_nonoverlap_roles_and_x_endpoint() -> None:
    domain = _report()["independent_domain_reproduction"]
    assert domain["case_count"] == 8
    assert domain["all_strictly_nonoverlapping"] is True
    assert domain["maximum_gap_reconstruction_absolute_error_m"] <= 2e-17
    assert domain["failed_stage_a_case_count"] == 3
    assert domain["role_coverage_complete"] is True
    assert domain["minimum_x"] == 0.001
    assert domain["maximum_x"] == 1000.0
    assert domain["continuous_domain_numerical_qualification_claimed"] is False


def test_newtonian_and_yukawa_formulas_are_convention_complete() -> None:
    formula = _report()["independent_formula_reproduction"]
    assert formula["newtonian"]["passed"] is True
    assert formula["newtonian"]["energy_formula"] == "U_N(D)=-G*M1*M2/D"
    assert formula["yukawa"]["passed"] is True
    assert formula["yukawa"]["amplitude_exact"] == "1/3"
    assert formula["yukawa"]["both_form_factors"] is True
    assert formula["yukawa"]["center_distance_exponential"] is True
    assert formula["yukawa"]["point_limit_obligation"] is True
    assert formula["yukawa"]["sphere_exchange_symmetry_obligation"] is True


def test_small_x_coefficients_are_independently_reproduced() -> None:
    small = _report()["independent_formula_reproduction"]["small_x"]
    assert small["coefficient_formula"] == "a_k=6*(k+1)/(2*k+3)! for k=0..4"
    assert small["independently_reproduced_coefficients"] == [
        "1", "1/10", "1/280", "1/15120", "1/1330560"
    ]
    assert small["independently_reproduced_coefficients"] == small["frozen_coefficients"]
    assert small["coefficients_match"] is True


def test_large_x_pair_scaling_and_overlap_contracts_are_complete() -> None:
    formula = _report()["independent_formula_reproduction"]
    large = formula["large_x"]
    assert large["primary_domain"] == "40<x<=1000"
    assert large["direct_hyperbolic_forbidden"] is True
    assert "exp(-2*x)" in large["formula"]
    assert "exp(-g/lambda)*H(x1)*H(x2)" in large["scaled_identity"]
    assert large["log_domain_required"] is True
    overlaps = formula["overlaps"]
    assert overlaps["grid_count"] == 2
    assert overlaps["small_direct_x"] == [0.05, 0.1, 0.2]
    assert overlaps["direct_scaled_x"] == [20.0, 32.0, 40.0]
    assert overlaps["absolute_and_relative_tolerances_present"] is True


def test_radial_path_is_numerically_independent_with_claim_qualification() -> None:
    cross = _report()["independent_cross_check_reproduction"]
    assert cross["path_count"] == 1
    assert cross["dimension"] == 1
    assert "expm1" in cross["scaled_integral"]
    assert cross["numerically_independent_of_closed_form_evaluator"] is True
    assert cross["pair_factorization_may_be_accepted_from_cross_check_alone"] is False
    assert cross["derivation_gate_must_pass_first"] is True
    qualification = _report()["review_qualification"]
    assert qualification["accepted"] is True
    assert qualification["qualification_id"] == (
        "RADIAL_NUMERICAL_INDEPENDENCE_AFTER_ANALYTIC_ANGULAR_REDUCTION"
    )
    assert "cannot repair or override a failed derivation" in qualification["consequence"]


def test_self_convergence_and_agreement_are_separate_decisions() -> None:
    cross = _report()["independent_cross_check_reproduction"]
    execution = _report()["independent_execution_contract_reproduction"]
    assert cross["precision_ladder"] == [50, 80, 120]
    assert cross["plateau_levels"] == [80, 120]
    assert "1e-30" in cross["self_convergence_rule"]
    assert "abs_tol+rel_tol" in cross["agreement_rule"]
    assert execution["nonconverged_radial_value_may_confirm_or_reject_formula"] is False
    assert [row["record"] for row in execution["scientific_stage_records"]] == [
        "ANALYTIC_DERIVATION",
        "STABLE_EVALUATOR",
        "RADIAL_SELF_CONVERGENCE",
        "ANALYTIC_RADIAL_AGREEMENT",
    ]


def test_mutations_use_live_path_and_custody_is_complete() -> None:
    execution = _report()["independent_execution_contract_reproduction"]
    assert execution["mutation_count"] == 8
    assert len(execution["mutation_ids"]) == 8
    assert execution["live_path_required"] is True
    assert execution["metadata_only_rejection_forbidden"] is True
    assert execution["resource_envelope"] == {
        "total_seconds": 600,
        "memory_mib": 2048,
        "stage_seconds_sum": 600,
        "stage_count": 6,
    }
    custody = execution["custody"]
    assert custody["process_group_termination"] == "MANDATORY"
    assert custody["raw_launcher_transcript"] == "PRESERVED"
    assert custody["timeout_timestamp"] == "PRESERVED"
    assert custody["child_termination_records"] == "PRESERVED"
    assert custody["zero_survivors"] == "MANDATORY"
    assert custody["stage_atomic"] == "REQUIRED"
    assert custody["all_stages_required"] is True


def test_outcomes_authority_and_required_stop_are_exact() -> None:
    report = _report()
    execution = report["independent_execution_contract_reproduction"]
    assert len(execution["terminal_outcomes"]) == 5
    assert execution["only_success_eligibility"].startswith(
        "Only ANALYTIC_SPHERE_ORACLE_QUALIFIED"
    )
    assert execution["authorized_execution_count"] == 1
    assert execution["executions_consumed"] == 0
    accepted = report["accepted_contract"]
    assert accepted["oracle_execution_authorized"] == 1
    assert accepted["oracle_execution_performed"] == 0
    assert accepted["required_stop"] == "INDEPENDENT_ANALYTIC_ORACLE_EXECUTION_RESULT_REVIEW"


def test_all_forty_review_gates_pass() -> None:
    gates = _report()["review_gates"]
    assert gates["gate_count"] == gates["pass_count"] == 40
    assert gates["failure_count"] == 0
    assert all(row["status"] == "PASS" for row in gates["rows"])


def test_scope_authorizes_only_one_unexecuted_oracle_run() -> None:
    scope = _report()["scope"]
    allowed_true = {
        "independent_packet_review_executed",
        "packet_custody_verified",
        "analytic_oracle_qualification_contract_ready",
        "one_small_oracle_execution_authorized",
    }
    for key, value in scope.items():
        assert value is (key in allowed_true), key


def test_human_review_records_qualification_custody_and_stop() -> None:
    text = (ROOT / review.HUMAN_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        review.VERDICT,
        "40 / 40 PASSED",
        "x=1000",
        "a_k = 6*(k+1)/(2*k+3)!",
        "does not independently prove two-sphere",
        "A nonconverged radial value may neither confirm nor reject",
        "600-second and 2048-MiB",
        review.SELECTED_NEXT_TARGET,
    ):
        assert token in text
