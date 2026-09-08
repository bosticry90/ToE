from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import scalar_only_yukawa_analytic_sphere_kernel_exploratory_sandbox_execution_result_review_v0 as review


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


def test_exact_execution_custody_is_frozen() -> None:
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


def test_failure_is_implementation_plus_control_integration_not_contract_ambiguity() -> None:
    attribution = _report()["defect_attribution"]
    assert attribution["principal_classification"] == "IMPLEMENTATION_FAILURE"
    assert attribution["secondary_classification"] == (
        "SYNTHETIC_CONTROL_INTEGRATION_COVERAGE_GAP"
    )
    assert attribution["contract_coverage_failure_established"] is False
    assert attribution["ambiguity_in_decimal_conversion_obligation_established"] is False
    assert attribution["contract_rule"] == "UPPERCASE_NORMALIZED_DECIMAL_STRINGS_ONLY"
    assert len(attribution["static_trace"]) == 5


def test_stage_completion_does_not_restore_scientific_values() -> None:
    admissibility = _report()["scientific_admissibility"]
    assert admissibility["stage_completion_is_decision_bearing"] is False
    for key in (
        "regression_values_admissible",
        "derivative_values_admissible",
        "boundary_probe_results_admissible",
        "mutation_results_admissible",
        "runtime_results_admissible",
    ):
        assert admissibility[key] is False
    assert admissibility["kernel_pass_or_fail"] == "UNRESOLVED"
    assert admissibility["infrastructure_pass_or_fail"] == (
        "FAILED_QUALIFICATION_BY_SERIALIZATION"
    )


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
        "serialization_failure_accepted",
        "implementation_defect_localized",
        "synthetic_control_integration_gap_localized",
        "fresh_scientific_response_selector_authorized",
    }
    assert scope["sandbox_rerun_authorized"] is False
    assert scope["implementation_edit_authorized"] is False
    assert scope["missing_value_reconstruction_authorized"] is False
    assert scope["analytic_kernel_qualified"] is False


def test_next_boundary_forbids_automatic_recovery() -> None:
    boundary = _report()["next_response_boundary"]
    assert boundary["automatic_rerun"] == "PROHIBITED"
    assert boundary["silent_implementation_edit"] == "PROHIBITED"
    assert boundary["missing_value_reconstruction"] == "PROHIBITED"
    assert boundary["fresh_selector_required"] is True
    assert _report()["selected_next_target"] == review.SELECTED_NEXT_TARGET


def test_human_review_records_attribution_and_authority() -> None:
    text = (ROOT / review.HUMAN_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        review.VERDICT,
        review.PRINCIPAL_OUTCOME,
        "IMPLEMENTATION FAILURE",
        "SYNTHETIC-CONTROL INTEGRATION GAP",
        "not a contract ambiguity",
        "40 / 40 PASS",
        review.SELECTED_NEXT_TARGET,
    ):
        assert token in text
