from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import scalar_only_yukawa_analytic_sphere_kernel_exploratory_sandbox_execution_result_review_v1 as review


ROOT = Path(__file__).resolve().parents[3]
REPORT = ROOT / review.REPORT_RELATIVE_PATH


def _report() -> dict[str, object]:
    value = json.loads(REPORT.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_review_regenerates_without_importing_or_rerunning_sandbox() -> None:
    assert review.artifact_bytes() == REPORT.read_bytes()
    report = _report()
    assert report["target"] == review.TARGET
    assert report["verdict"] == review.VERDICT
    assert report["principal_review_outcome"] == review.PRINCIPAL_OUTCOME


def test_exact_one_shot_custody_is_accepted() -> None:
    report = _report()
    frozen = {
        row["relative_path"]: row["sha256"]
        for row in report["authority"]["frozen_execution_artifacts"]
    }
    assert frozen == review.FROZEN_ARTIFACT_HASHES
    custody = report["custody_review"]
    assert custody["authorized_execution_count"] == 1
    assert custody["consumed_execution_count"] == 1
    assert custody["surviving_process_count"] == 0
    assert custody["completed_stage_boundary_count"] == 8
    assert custody["canonical_result_written_and_verified"] is True


def test_positive_rows_are_bounded_nonqualifying_observations() -> None:
    observations = _report()["preserved_exploratory_observations"]
    assert observations["status"] == "BOUNDED_NONQUALIFYING_POSITIVE_OBSERVATIONS"
    assert all(observations["surfaces"].values())
    assert observations["regression_case_count"] == 8
    assert observations["derivative_reference_case_count"] == 8
    assert observations["boundary_probe_count"] == 13
    assert observations["evaluator_overlap_count"] == 6
    assert observations["runtime_trial_count"] == 5
    assert observations["qualifies_kernel"] is False


def test_all_twenty_mutation_children_failed_before_adjudication() -> None:
    failure = _report()["mutation_failure_review"]
    assert failure["synthetic_route_count"] == 8
    assert failure["kernel_mutation_count"] == 12
    assert failure["total_child_failure_count"] == 20
    assert failure["common_error_type"] == "builtins.OSError"
    assert failure["common_error_message"] == "[Errno 9] Bad file descriptor"
    assert failure["common_failure_boundary"] == "FIRST_CHILD_CAPABILITY_PIPE_READ"
    for key in (
        "validation_session_constructed",
        "fixture_loaded",
        "mutation_injected",
        "candidate_called",
        "predicate_executed",
        "adjudication_executed",
    ):
        assert failure[key] is False
    assert len(failure["rows"]) == 20
    assert all(row["candidate_or_predicate_entered"] is False for row in failure["rows"])


def test_defect_is_validation_plumbing_not_candidate_science() -> None:
    attribution = _report()["defect_attribution"]
    assert attribution["principal_classification"] == "VALIDATION_INFRASTRUCTURE_IMPLEMENTATION_FAILURE"
    assert attribution["secondary_classification"] == (
        "MUTATION_HARNESS_WINDOWS_PLATFORM_PORTABILITY_DEFECT"
    )
    assert attribution["further_mechanism_adjudicated"] is False
    assert attribution["candidate_kernel_defect_established"] is False
    assert attribution["scientific_mutation_disagreement_established"] is False


def test_scientific_fail_closed_boundary_is_exact() -> None:
    admissibility = _report()["scientific_admissibility"]
    assert admissibility["canonical_preservation"] == "PASSED"
    assert admissibility["mandatory_mutation_controls"] == "FAILED_BEFORE_ADJUDICATION"
    assert admissibility["kernel_pass_or_fail"] == "UNRESOLVED"
    assert admissibility["validation_infrastructure"] == "NOT_QUALIFIED"
    assert admissibility["historical_cubature"] == "UNADJUDICATED"
    assert admissibility["scientific_claim"] == "NONE"


def test_all_forty_review_gates_pass() -> None:
    gates = _report()["review_gates"]
    assert gates["gate_count"] == 40
    assert gates["pass_count"] == 40
    assert gates["failure_count"] == 0
    assert len({row["gate_id"] for row in gates["rows"]}) == 40


def test_scope_permits_only_fresh_selector() -> None:
    scope = _report()["scope"]
    true_keys = {key for key, value in scope.items() if value is True}
    assert true_keys == {
        "independent_execution_result_review_performed",
        "one_shot_custody_accepted",
        "canonical_preservation_pass_accepted",
        "bounded_positive_exploratory_observations_accepted",
        "validation_infrastructure_child_pipe_failure_accepted",
        "windows_mutation_harness_portability_defect_localized",
        "fresh_scientific_response_selector_authorized",
    }
    assert scope["analytic_kernel_qualified"] is False
    assert scope["analytic_kernel_refuted"] is False
    assert scope["pipe_repair_authorized"] is False
    assert scope["sandbox_rerun_authorized"] is False
    assert scope["sandbox_v2_authorized"] is False
    assert scope["stage_b_authorized"] is False


def test_terminal_boundary_forbids_repair_rerun_and_automatic_advance() -> None:
    boundary = _report()["next_response_boundary"]
    assert boundary["automatic_rerun"] == "PROHIBITED"
    assert boundary["direct_pipe_repair_and_rerun"] == "PROHIBITED"
    assert boundary["sandbox_v2"] == "PROHIBITED"
    assert boundary["additional_prerequisite"] == "PROHIBITED"
    assert boundary["production_or_scientific_advance"] == "PROHIBITED"
    assert boundary["fresh_selector_required"] is True
    assert _report()["selected_next_target"] == review.SELECTED_NEXT_TARGET


def test_human_review_records_exact_outcome_and_authority() -> None:
    text = (ROOT / review.HUMAN_REVIEW_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        review.VERDICT,
        review.PRINCIPAL_OUTCOME,
        "40 / 40 PASS",
        "Windows portability",
        "KERNEL_QUALIFICATION_REMAINS_UNRESOLVED",
        review.SELECTED_NEXT_TARGET,
    ):
        assert token in text
