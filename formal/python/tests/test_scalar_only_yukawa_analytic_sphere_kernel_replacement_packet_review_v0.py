from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import scalar_only_yukawa_analytic_sphere_kernel_replacement_packet_review_v0 as review


ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = ROOT / review.REPORT_RELATIVE_PATH


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_review_regenerates_and_freezes_exact_packet() -> None:
    assert review.artifact_bytes() == REPORT_PATH.read_bytes()
    report = _report()
    assert report["target"] == review.TARGET
    assert report["verdict"] == review.VERDICT
    assert {
        row["relative_path"]: row["sha256"]
        for row in report["authority"]["frozen_packet_artifacts"]
    } == review.PACKET_HASHES


def test_principal_and_secondary_blocks_are_exact() -> None:
    report = _report()
    assert report["principal_review_outcome"] == "BLOCKED_REPLACEMENT_VALIDATION_INDEPENDENCE"
    assert report["secondary_review_outcomes"] == [
        "BLOCKED_REPLACEMENT_INTERFACE_IDENTITY",
        "BLOCKED_REPLACEMENT_DOMAIN_COVERAGE",
    ]
    assert report["selected_next_target"] == review.SELECTED_NEXT_TARGET


def test_formula_and_architecture_surfaces_are_accepted() -> None:
    accepted = _report()["accepted_surfaces"]
    assert accepted["newtonian_and_yukawa_formulas"] == "ACCEPTED_AS_ALGEBRAICALLY_COMPLETE"
    assert accepted["stable_x_regimes_and_overlap_contract"] == "ACCEPTED"
    assert accepted["live_entrypoint_vs_cubature_helper_distinction"] == "ACCEPTED"
    assert accepted["overall_replacement_contract"] == "NOT_READY"


def test_interface_identity_omissions_are_reproduced() -> None:
    audit = _report()["independent_interface_audit"]
    assert audit["public_entrypoint"] == "pair_energy_and_radial_derivative"
    assert audit["internal_replacement_targets_exact"] is False
    assert audit["lambda_component_compatibility_matrix_complete"] is False
    assert audit["array_invalid_element_behavior_complete"] is False
    assert audit["validation_hook_authorization_mechanism_complete"] is False


def test_regression_rows_have_values_but_not_executable_inputs() -> None:
    audit = _report()["independent_domain_and_regression_audit"]
    assert audit["regression_case_count"] == 8
    assert audit["regression_reference_values_present"] is True
    assert audit["regression_inputs_complete"] is False
    assert "lambda_m" in audit["regression_required_input_keys"]
    assert "lambda_m" not in audit["regression_observed_common_keys"]


def test_limits_runtime_and_serialization_are_descriptive() -> None:
    audit = _report()["independent_domain_and_regression_audit"]
    assert audit["limit_and_boundary_probe_rows_present"] is False
    assert audit["limit_and_boundary_probes_numeric"] is False
    assert audit["runtime_probe_inputs_exact"] is False
    assert audit["canonical_serialization_schema_exact"] is False


def test_derivative_and_mutation_validation_are_incomplete() -> None:
    audit = _report()["independent_validation_audit"]
    assert audit["energy_references_complete"] is True
    assert audit["radial_derivative_references_complete"] is False
    assert audit["mutation_count"] == 12
    assert audit["mutation_routes_complete"] is False
    assert audit["mutation_detection_predicates_numeric"] is False
    assert audit["candidate_oracle_import_forbidden"] is True
    assert audit["candidate_cubature_import_forbidden"] is True


def test_exact_eleven_failed_gates_and_counts() -> None:
    gates = _report()["review_gates"]
    assert gates["gate_count"] == 62
    assert gates["pass_count"] == 51
    assert gates["failure_count"] == 11
    assert gates["failed_gate_ids"] == list(review.FAILED_GATE_IDS)


def test_no_implementation_or_downstream_authority() -> None:
    scope = _report()["scope"]
    assert scope["independent_packet_review_performed"] is True
    assert scope["fresh_scientific_response_selector_authorized"] is True
    for key in (
        "replacement_contract_ready",
        "shadow_kernel_implementation_authorized",
        "shadow_kernel_implementation_performed",
        "production_kernel_replacement_authorized",
        "production_kernel_replacement_performed",
        "old_cubature_called",
        "old_cubature_adjudicated",
        "automatic_packet_repair_authorized",
        "comparison_v2_authorized",
        "torque_or_dft_authorized",
        "stage_a_rerun_authorized",
        "jacobian_or_identifiability_authorized",
        "stage_b_authorized",
    ):
        assert scope[key] is False


def test_block_requires_fresh_selector_not_silent_repair() -> None:
    next_action = _report()["required_next_action"]
    assert next_action["fresh_selector_required"] is True
    assert next_action["silent_packet_repair"] == "PROHIBITED"
    assert next_action["automatic_packet_v1"] == "PROHIBITED"
    assert next_action["shadow_implementation"] == "NOT_AUTHORIZED"


def test_human_review_records_findings_and_authority() -> None:
    text = (ROOT / review.HUMAN_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        review.VERDICT,
        "BLOCKED_REPLACEMENT_VALIDATION_INDEPENDENCE",
        "eight regression rows preserve outputs but not their executable inputs",
        "radial derivative has no independent frozen reference",
        "twelve mutations are identities, not executable routes",
        "No candidate implementation is authorized",
        review.SELECTED_NEXT_TARGET,
    ):
        assert token in text
