from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import scalar_only_yukawa_analytic_sphere_kernel_replacement_packet_v1 as packet


ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = ROOT / packet.REPORT_RELATIVE_PATH


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_packet_regenerates_and_consumes_exact_selector() -> None:
    assert packet.artifact_bytes() == REPORT_PATH.read_bytes()
    report = _report()
    assert report["target"] == packet.TARGET
    assert report["verdict"] == packet.VERDICT
    assert report["selected_next_target"] == packet.SELECTED_NEXT_TARGET
    assert report["authority"]["consumed_selector_route"] == (
        "REPAIR_ANALYTIC_KERNEL_REPLACEMENT_EXECUTION_CONTRACT"
    )


def test_exact_eleven_repairs_and_fifty_one_frozen_gates() -> None:
    repair = _report()["v1_repair_scope"]
    assert repair["accepted_review_gate_count"] == 51
    assert repair["repaired_review_gate_count"] == 11
    assert repair["repaired_review_gate_ids"] == list(packet.FAILED_REVIEW_GATES)
    assert repair["all_other_v0_surfaces"].startswith("FROZEN")
    assert repair["automatic_v2"] == "PROHIBITED"


def test_internal_replacement_and_unchanged_callers_are_exact() -> None:
    identity = _report()["replacement_interface_identity_v1"]
    assert identity["candidate_replaces_internal_functions"] == [
        "uniform_sphere_form_factor",
        "scaled_uniform_sphere_form_factor",
        "pair_energy_and_radial_derivative",
    ]
    assert identity["future_dispatch_seam_symbol"] == "SPHERE_PAIR_KERNEL_ID"
    assert len(identity["unchanged_callers"]) == 4
    assert identity["excluded_read_only_helper"] == (
        "reduced_four_dimensional_density_integral_yukawa_energy"
    )


def test_component_lambda_matrix_and_array_failure_are_complete() -> None:
    identity = _report()["replacement_interface_identity_v1"]
    matrix = identity["lambda_component_compatibility_matrix"]
    assert len(matrix) == 12
    assert {(row["component"], row["lambda_class"]) for row in matrix} == {
        (component, cls)
        for component in ("newtonian", "yukawa", "total")
        for cls in ("POSITIVE_FINITE", "ZERO", "NEGATIVE_FINITE", "NONFINITE")
    }
    array = identity["array_invalid_element_behavior"]
    assert array["atomic"] is True
    assert array["partial_output"] == "FORBIDDEN"
    assert "ASCENDING_C_ORDER" in array["invalid_index_order"]


def test_validation_hooks_have_an_enforceable_private_route() -> None:
    hooks = _report()["replacement_interface_identity_v1"]["validation_hook_authorization_mechanism"]
    assert hooks["private_entrypoint"] == "_qualification_mutation_entrypoint"
    assert hooks["capability_type"] == "_QualificationCapability"
    assert hooks["ambient_environment_or_global_mode"] == "FORBIDDEN"
    assert all(
        hooks[key].startswith("PermissionError")
        for key in (
            "public_nondefault_yukawa_amplitude",
            "public_nondefault_yukawa_sign",
            "public_remove_attractor_form_factor_true",
        )
    )


def test_all_eight_regression_rows_have_inputs_energy_and_derivatives() -> None:
    contract = _report()["regression_and_derivative_reference_v1"]
    assert contract["row_count"] == 8
    required = {
        "radius_1_m_hex", "radius_2_m_hex", "mass_1_kg_hex", "mass_2_kg_hex",
        "surface_gap_m_hex", "center_distance_m_hex", "lambda_m_hex",
        "yukawa_amplitude_hex", "newtonian_energy_reference_J_decimal",
        "yukawa_energy_reference_J_decimal", "newtonian_dU_dD_reference_N_decimal",
        "yukawa_dU_dD_reference_N_decimal", "energy_acceptance",
        "derivative_acceptance", "derivative_reference_provenance",
    }
    assert all(required <= set(row) for row in contract["rows"])
    assert contract["independence"]["candidate_energy_or_derivative_call"] == "FORBIDDEN"


def test_thirteen_limit_and_boundary_probes_are_numeric() -> None:
    probes = _report()["limit_and_boundary_probe_contract_v1"]
    assert probes["probe_count"] == 13
    assert [row["probe_id"] for row in probes["rows"]] == [f"P{i:02d}_{suffix}" for i, suffix in (
        (1, "POINT_PARTICLE"), (2, "POINT_NEWTONIAN_LAMBDA_ZERO_SENTINEL"),
        (3, "NEAR_CONTACT_RESOLVED"), (4, "TOUCHING_REJECTED"),
        (5, "OVERLAP_REJECTED"), (6, "X_1000_ACCEPTED"),
        (7, "X_ABOVE_1000_REJECTED"), (8, "ZERO_COUPLING"),
        (9, "HALF_COUPLING_LINEARITY"), (10, "LONG_RANGE"),
        (11, "LARGE_SEPARATION_REPRESENTABLE"),
        (12, "LARGE_SEPARATION_UNDERFLOW"), (13, "EMPTY_ARRAY_REJECTED"),
    )]
    assert all("expected" in row and "absolute_tolerance" in row and "relative_tolerance" in row for row in probes["rows"])


def test_all_twelve_mutations_have_complete_routes_and_predicates() -> None:
    mutations = _report()["mutation_routing_v1"]
    assert mutations["mutation_count"] == 12
    required = {
        "mutation_id", "case_ids", "components", "injection_point",
        "execution_order", "acceptance_rule", "failure_consequence",
    }
    assert all(required <= set(row) for row in mutations["rows"])
    assert all(
        "absolute_tolerance" in row or "relative_tolerance" in row or "required_exception" in row
        for row in mutations["rows"]
    )
    assert mutations["any_missing_or_failed_detection"].startswith("BLOCKED")


def test_runtime_workload_is_exact_and_bounded() -> None:
    runtime = _report()["runtime_workload_v1"]
    assert runtime["timed_call_count_per_trial"] == 10000
    assert runtime["warmup_call_count"] == 24
    assert runtime["trial_count"] == 5
    assert len(runtime["runtime_probe_case_rows"]) == 8
    assert runtime["runtime_probe_component_order"] == ["newtonian", "yukawa", "total"]
    assert runtime["maximum_median_seconds"] == 5.0
    assert runtime["parallelism"].startswith("FORBIDDEN")


def test_serialization_and_comparison_are_canonical() -> None:
    serialization = _report()["canonical_serialization_and_comparison_v1"]
    assert len(serialization["root_keys_exact"]) == 11
    assert "sort_keys=True" in serialization["canonical_encoder"]
    assert serialization["float_serialization_rule"].startswith("ALL_BINARY64")
    assert serialization["duration_serialization_rule"] == "INTEGER_NANOSECONDS"
    assert serialization["comparison_requires_both_energy_and_derivative"] is True
    assert serialization["duplicate_missing_or_unknown_id"].startswith("BLOCKED")


def test_precedence_and_review_boundary_fail_closed() -> None:
    report = _report()
    precedence = report["qualification_precedence_v1"]
    assert [row["priority"] for row in precedence["priority_rows"]] == [1, 2, 3, 4, 5, 6]
    assert precedence["partial_or_lower_priority_scientific_classification"] == "FORBIDDEN"
    assert report["packet_review_outcomes"] == list(packet.PACKET_REVIEW_OUTCOMES)
    assert report["review_consequence"]["automatic_v2"] == "PROHIBITED"
    assert report["review_consequence"]["production_adoption"] == "NOT_AUTHORIZED_BY_PACKET_REVIEW"


def test_packet_scope_authorizes_review_only() -> None:
    report = _report()
    scope = report["scope"]
    true_keys = {key for key, value in scope.items() if value is True}
    assert true_keys == {
        "v1_packet_prepared", "selector_authority_verified", "v0_packet_and_review_frozen",
        "fifty_one_accepted_review_gates_frozen", "eleven_failed_gates_repaired_in_contract",
        "independent_v1_packet_review_authorized",
        "derivative_reference_values_derived_as_contract_metadata",
    }
    assert scope["candidate_kernel_created"] is False
    assert scope["candidate_kernel_executed"] is False
    assert scope["production_kernel_replaced"] is False
    assert scope["old_cubature_adjudicated"] is False
    assert scope["automatic_v2_authorized"] is False


def test_packet_gate_count_and_human_boundary() -> None:
    report = _report()
    assert report["packet_gates"]["gate_count"] == 54
    assert report["packet_gates"]["pass_count"] == 54
    text = (ROOT / packet.HUMAN_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        packet.VERDICT,
        "51 accepted gates remain frozen",
        "11 failed gates",
        "independent derivative reference",
        "10,000-call runtime workload",
        "canonical serialization",
        "No candidate kernel was created",
        packet.SELECTED_NEXT_TARGET,
    ):
        assert token in text
