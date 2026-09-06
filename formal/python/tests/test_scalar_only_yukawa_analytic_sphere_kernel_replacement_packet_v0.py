from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import scalar_only_yukawa_analytic_sphere_kernel_replacement_packet_v0 as packet


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
        "RETIRE_OLD_CUBATURE_COMPARISON_AND_PREPARE_ANALYTIC_KERNEL_REPLACEMENT"
    )


def test_oracle_and_historical_surfaces_are_hash_pinned() -> None:
    report = _report()
    oracle = {
        row["relative_path"]: row["sha256"]
        for row in report["authority"]["frozen_accepted_oracle_artifacts"]
    }
    historical = {
        row["relative_path"]: row["sha256"]
        for row in report["authority"]["frozen_historical_interface_artifacts"]
    }
    assert oracle == packet.ORACLE_HASHES
    assert historical == packet.HISTORICAL_INTERFACE_HASHES


def test_history_distinguishes_live_entrypoint_from_cubature_helper() -> None:
    identity = _report()["historical_path_identity"]
    assert identity["live_stage_a_energy_entrypoint"] == "pair_energy_and_radial_derivative"
    assert identity["fixed_tensor_cubature_helper"] == (
        "reduced_four_dimensional_density_integral_yukawa_energy"
    )
    assert identity["paths_are_distinct"] is True
    assert identity["live_entrypoint_already_contains_a_related_form_factor_implementation"] is True
    assert identity["old_cubature_source_disposition"].startswith("READ_ONLY")


def test_exact_energy_and_radial_derivative_contract() -> None:
    kernel = _report()["analytic_kernel_contract"]
    assert kernel["newtonian_energy"] == "U_N=-G*M1*M2/D"
    assert kernel["newtonian_radial_derivative"] == "dU_N/dD=G*M1*M2/D^2"
    assert "F(x1)*F(x2)*exp(-D/lambda)" in kernel["yukawa_energy"]
    assert kernel["yukawa_amplitude_production_exact"] == "1/3"
    assert kernel["sphere_exchange_symmetry_required"] is True
    assert kernel["equal_and_unequal_radii_supported"] is True


def test_numeric_regimes_and_guarded_domain_are_exact() -> None:
    evaluator = _report()["numerical_evaluator_contract"]
    domain = _report()["domain_and_limit_contract"]
    assert evaluator["qualified_x_interval"] == "0<=x<=1000"
    assert evaluator["H_at_zero_exact"] == 1.0
    assert evaluator["large_x"]["direct_sinh_or_cosh_forbidden"] is True
    assert evaluator["silent_overflow_or_underflow"] == "FORBIDDEN"
    assert domain["touching_or_overlap"] == "REJECT"
    assert domain["nonpositive_lambda_for_yukawa_or_total"] == "REJECT"
    assert "16*ulp" in domain["machine_resolvable_gap_rule"]
    assert "LINEAR_IN_A_Y" in domain["small_coupling_limit"]


def test_caller_schema_preserves_shape_dtype_and_components() -> None:
    interface = _report()["caller_interface_contract"]
    assert interface["public_compatibility_entrypoint"] == "pair_energy_and_radial_derivative"
    assert interface["components"] == ["newtonian", "yukawa", "total"]
    assert interface["return_schema"].startswith("tuple(numpy_float64_array")
    assert "ZERO_DIMENSIONAL_SCALAR_ARRAY" in interface["return_shape"]
    assert interface["torque_or_angular_semantics"].startswith("NOT_PART")


def test_all_eight_accepted_reference_rows_are_copied_not_recomputed() -> None:
    regression = _report()["accepted_oracle_regression_contract"]
    assert regression["case_count"] == 8
    assert regression["case_order"] == list(packet.REQUIRED_CASE_IDS)
    assert [row["case_id"] for row in regression["rows"]] == list(packet.REQUIRED_CASE_IDS)
    assert regression["reference_values_copied_not_recomputed_during_packet_preparation"] is True
    assert regression["accepted_binary64_values_are_custody_witnesses_not_the_independent_reference"] is True
    assert regression["candidate_result_bitwise_identity_required"] is False


def test_validation_is_independent_and_mutations_are_live_path() -> None:
    validation = _report()["validation_independence_contract"]
    assert validation["candidate_may_import_accepted_oracle_evaluator"] is False
    assert validation["candidate_may_import_old_cubature_helper"] is False
    assert validation["candidate_may_call_old_cubature"] is False
    assert [row["mutation_id"] for row in validation["validation_mutations"]] == list(
        packet.MUTATION_IDS
    )
    assert validation["metadata_only_mutation_detection"] == "FORBIDDEN"


def test_review_ready_authorizes_shadow_qualification_not_adoption() -> None:
    future = _report()["future_shadow_qualification_contract"]
    review = _report()["review_consequence"]
    assert future["authorized_by_this_preparation"] is False
    assert future["production_import_or_dispatch_change"] == "FORBIDDEN"
    assert future["total_wall_clock_seconds_max"] == 300
    assert future["memory_mib_max"] == 1024
    assert review["ready_outcome"].endswith("ONLY")
    assert review["production_adoption_on_ready_review"] == "NOT_AUTHORIZED"
    assert review["automatic_packet_v1_or_comparison_v2"] == "PROHIBITED"


def test_rollback_never_becomes_scientific_validation() -> None:
    adoption = _report()["implementation_adoption_and_rollback_contract"]
    assert adoption["historical_source_in_place_edit_during_shadow_qualification"] == "FORBIDDEN"
    assert "OPERATIONAL_RESTORATION_ONLY" in adoption["rollback_result"]
    assert adoption["mixed_kernel_outputs_in_one_scientific_record"] == "FORBIDDEN"
    assert adoption["automatic_fallback_after_candidate_failure"] == "FORBIDDEN"


def test_packet_review_outcomes_and_scope_are_fail_closed() -> None:
    report = _report()
    assert report["packet_review_outcomes"] == list(packet.PACKET_REVIEW_OUTCOMES)
    assert report["packet_gates"]["gate_count"] == 50
    assert report["packet_gates"]["pass_count"] == 50
    assert report["packet_gates"]["failure_count"] == 0
    scope = report["scope"]
    true_keys = {key for key, value in scope.items() if value is True}
    assert true_keys == {
        "replacement_packet_prepared",
        "selector_authority_consumed",
        "accepted_oracle_custody_frozen",
        "historical_interface_inspected_read_only",
        "independent_packet_review_authorized",
    }
    assert scope["analytic_kernel_implemented"] is False
    assert scope["production_kernel_replaced"] is False
    assert scope["old_cubature_adjudicated"] is False


def test_human_packet_records_the_exact_preimplementation_boundary() -> None:
    text = (ROOT / packet.HUMAN_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        packet.VERDICT,
        "pre-implementation",
        "neither validated nor invalidated",
        "pair_energy_and_radial_derivative",
        "reduced_four_dimensional_density_integral_yukawa_energy",
        "No candidate kernel was created",
        "operational rollback is not scientific validation",
        packet.SELECTED_NEXT_TARGET,
    ):
        assert token in text
