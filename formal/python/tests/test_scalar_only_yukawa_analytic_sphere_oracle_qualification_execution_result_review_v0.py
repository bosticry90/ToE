from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any

from formal.python.tools import (
    scalar_only_yukawa_analytic_sphere_oracle_qualification_execution_result_review_v0
    as review,
)


ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = ROOT / review.REPORT_RELATIVE_PATH
HUMAN_PATH = ROOT / review.HUMAN_RELATIVE_PATH


def _report() -> dict[str, Any]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_review_regenerates_and_rotates_only_to_fresh_selector() -> None:
    report = review.build_report()
    assert report["target"] == review.TARGET
    assert report["verdict"] == review.VERDICT
    assert report["selected_next_target"] == review.SELECTED_NEXT_TARGET
    assert report["selected_next_target_kind"] == review.SELECTED_NEXT_TARGET_KIND
    assert report["status"] == "INDEPENDENT_EXECUTION_RESULT_REVIEW_COMPLETE"


def test_all_five_execution_surfaces_remain_hash_exact() -> None:
    report = _report()
    observed = {
        row["relative_path"]: row["sha256"]
        for row in report["authority"]["frozen_execution_artifacts"]
    }
    assert observed == review.EXECUTION_HASHES
    for relative_path, expected in review.EXECUTION_HASHES.items():
        assert _sha256(ROOT / relative_path) == expected


def test_custody_reconstructs_one_normal_zero_survivor_launch() -> None:
    custody = _report()["independent_custody_audit"]
    assert custody["release_equals_canonical_result"] is True
    assert custody["reported_custody_equals_atomic_file"] is True
    assert custody["reported_payload_equals_atomic_file"] is True
    assert custody["launch_count"] == 1
    assert custody["launch_flag_run_id"] == custody["run_id"]
    assert custody["worker_exit_code"] == 0
    assert custody["timeout_initiated_at_utc"] is None
    assert custody["zero_surviving_processes"] is True
    assert custody["peak_job_memory_within_limit"] is True
    assert custody["raw_launcher_log_sha256_reported"] == custody[
        "raw_launcher_log_sha256_observed"
    ]


def test_six_atomic_stages_are_complete_and_pointer_qualification_is_explicit() -> None:
    custody = _report()["independent_custody_audit"]
    assert custody["stage_count"] == 6
    assert custody["all_stage_files_match_report"] is True
    assert custody["all_stages_complete"] is True
    assert custody["all_stages_within_budget"] is True
    assert custody["raw_log_stage_start_count"] == 6
    assert custody["raw_log_stage_end_count"] == 6
    assert custody["raw_log_outcome_count"] == 1
    assert custody["raw_log_stage_order_exact"] is True
    assert custody["current_stage_pointer_terminalized"] is False
    assert custody["current_stage_pointer_decision_bearing"] is False
    assert "IN_PROGRESS monitor pointer" in custody["custody_qualification"]


def test_derivation_and_exact_series_coefficients_are_independently_reproduced() -> None:
    audit = _report()["independent_derivation_audit"]
    assert audit["passed"] is True
    assert audit["strict_nonoverlap_all_cases"] is True
    assert audit["newtonian_shell_derivation_present"] is True
    assert audit["yukawa_angular_kernel_identity_present"] is True
    assert audit["radial_antiderivative_present"] is True
    assert audit["both_form_factors_present"] is True
    assert audit["center_distance_exponential_present"] is True
    assert audit["yukawa_amplitude_exact"] == "1/3"
    assert audit["independently_reproduced_series_coefficients"] == [
        "1", "1/10", "1/280", "1/15120", "1/1330560"
    ]
    assert audit["point_particle_limit_reproduced"] is True
    assert audit["scaled_pair_identity_present"] is True


def test_evaluator_routing_overlaps_and_extreme_x_are_reproduced() -> None:
    audit = _report()["independent_evaluator_audit"]
    assert audit["reported_status"] == "PASS"
    assert len(audit["case_rows"]) == 8
    assert audit["all_case_regimes_exact"] is True
    assert audit["all_scaled_factors_finite_positive"] is True
    assert len(audit["overlap_rows"]) == 6
    assert audit["all_six_overlap_decisions_reproduced"] is True
    assert audit["x_1000_used_scaled_branch"] is True
    assert audit["direct_hyperbolic_at_x_1000"] is False
    assert audit["silent_overflow_or_underflow"] is False


def test_radial_convergence_and_all_case_agreements_are_recomputed() -> None:
    audit = _report()["independent_radial_and_agreement_audit"]
    assert audit["reported_self_convergence"] == "PASS"
    assert audit["unique_x_count"] == 11
    assert len(audit["convergence_rows"]) == 11
    assert audit["all_eleven_convergence_decisions_reproduced"] is True
    assert audit["reported_agreement"] == "PASS"
    assert len(audit["case_rows"]) == 8
    assert audit["all_eight_agreement_decisions_reproduced"] is True
    assert audit["maximum_reported_relative_difference"].startswith(
        "9.1935311209820829"
    )
    assert audit["maximum_relative_difference_below_1e_13"] is True
    assert audit["three_failed_stage_a_cases_present"] is True


def test_all_eight_mutations_have_live_numeric_failure_reasons() -> None:
    audit = _report()["independent_mutation_audit"]
    assert audit["reported_status"] == "PASS"
    assert audit["mutation_ids_exact"] is True
    assert audit["reported_count"] == audit["reported_detected_count"] == 8
    assert audit["live_path_attested"] is True
    assert audit["all_eight_numerically_detected"] is True
    assert all(row["reported_detected"] for row in audit["rows"])
    assert all(row["numerical_failure_reason_present"] for row in audit["rows"])


def test_review_gate_tally_has_one_non_decision_bearing_qualification() -> None:
    gates = _report()["review_gates"]
    assert gates["gate_count"] == 40
    assert gates["pass_count"] == 39
    assert gates["qualified_pass_count"] == 1
    assert gates["admissible_count"] == 40
    assert gates["failure_count"] == 0
    qualified = [row for row in gates["rows"] if row["status"] == "PASS_WITH_QUALIFICATION"]
    assert [row["gate_id"] for row in qualified] == [
        "R14_CURRENT_STAGE_POINTER_QUALIFIED_NON_DECISION_BEARING"
    ]


def test_accepted_result_is_bounded_and_production_remains_unadjudicated() -> None:
    accepted = _report()["accepted_result"]
    assert accepted["analytic_sphere_oracle"] == (
        "QUALIFIED_ON_EIGHT_FROZEN_CASES_AND_OVERLAP_PROBES"
    )
    assert accepted["radial_self_convergence"] == "ACCEPTED_11_OF_11"
    assert accepted["analytic_radial_agreement"] == "ACCEPTED_8_OF_8"
    assert accepted["mutations"] == "ACCEPTED_8_OF_8"
    assert accepted["production_cubature"] == "UNADJUDICATED"
    assert accepted["continuous_uniform_error_claim"] == "NOT_ESTABLISHED"
    assert accepted["execution_rerun"] == "NOT_AUTHORIZED"
    assert accepted["required_next_action"] == "FRESH_SCIENTIFIC_RESPONSE_SELECTOR"


def test_scope_authorizes_only_review_acceptance_and_fresh_selector() -> None:
    scope = _report()["scope"]
    true_keys = {key for key, value in scope.items() if value is True}
    assert true_keys == {
        "independent_execution_result_review_performed",
        "execution_custody_accepted",
        "analytic_sphere_oracle_qualified_result_accepted",
        "fresh_scientific_response_selector_authorized",
    }
    assert scope["oracle_execution_rerun_authorized"] is False
    assert scope["production_cubature_comparison_authorized"] is False
    assert scope["production_kernel_replacement_authorized"] is False
    assert scope["stage_a_rerun_authorized"] is False
    assert scope["torque_or_dft_authorized"] is False
    assert scope["jacobian_or_identifiability_authorized"] is False
    assert scope["stage_b_eligible"] is False
    assert scope["stage_b_authorized"] is False


def test_human_review_records_verdict_qualification_and_authority_ceiling() -> None:
    text = HUMAN_PATH.read_text(encoding="utf-8")
    for token in (
        review.VERDICT,
        "39 PASS",
        "1 PASS WITH CUSTODY QUALIFICATION",
        "9.1935311209820829",
        "UNADJUDICATED",
        "fresh scientific-response selector only",
        review.SELECTED_NEXT_TARGET,
    ):
        assert token in text
