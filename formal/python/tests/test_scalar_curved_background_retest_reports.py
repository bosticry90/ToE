from __future__ import annotations

import math

import pytest

from formal.python.tests.strict_physics_state_helpers import (
    active_workstream,
    current_target_state,
    loop_registry,
    workstream,
)
from formal.python.tools.scalar_curved_background_retest_reports import (
    EXECUTION_OUTCOME,
    EXECUTION_STRICT_OUTCOME,
    EXECUTION_TARGET,
    GUARDRAIL_OUTCOME,
    GUARDRAIL_STRICT_OUTCOME,
    NONZERO_CURVATURE_GUARDRAIL_TARGET,
    PROPOSED_EQUATION_ID,
    THRESHOLD_REPAIR_TARGET,
    build_guardrail_payload,
    build_execution_report,
    build_qm_representation_pressure,
    canonical_json_bytes,
    validate_guardrail_payload,
    validate_qm_representation_pressure,
)


def test_guardrail_freezes_required_interface_and_level_three_scope() -> None:
    payload = build_guardrail_payload()
    validate_guardrail_payload(payload)
    assert payload["packet_result"] == GUARDRAIL_OUTCOME
    assert payload["strict_packet_result"] == GUARDRAIL_STRICT_OUTCOME
    assert payload["selected_next_target"] == EXECUTION_TARGET
    assert payload["claim_ceiling"]["claim_ladder_level"] == 3
    assert payload["claim_ceiling"]["not_gravity_dynamics"] is True
    assert payload["claim_ceiling"]["not_source_admissibility"] is True
    assert payload["claim_ceiling"]["not_bianchi_compatibility"] is True
    assert payload["claim_ceiling"]["not_seam_admissibility"] is True


def test_guardrail_freezes_metric_connection_and_curvature_conventions() -> None:
    payload = build_guardrail_payload()
    equations = payload["equation_surfaces"]
    connection = payload["connection_and_curvature_conventions"]
    assert equations["metric"] == "g_mu_nu = a(eta)^2 * diag(-1,+1)"
    assert equations["metric_signature"] == "(-,+)"
    assert equations["field_residual"] == (
        "E_phi = Box_g phi - V'(phi) = Box_g phi"
    )
    assert equations["identity"] == (
        "nabla_mu T^{mu nu} = E_phi nabla^nu phi"
    )
    assert equations["proposed_equation_id_pending_review"] == PROPOSED_EQUATION_ID
    assert set(connection["nonzero_christoffels"].values()) == {"H"}
    assert connection["curvature_used_as_dynamic_equation"] is False


def test_guardrail_freezes_exact_controls_and_thresholds() -> None:
    payload = build_guardrail_payload()
    inputs = payload["inputs"]
    thresholds = payload["success_criteria"]
    controls = payload["required_controls"]
    assert inputs["scale_factor"] == "a(eta) = exp(H * eta)"
    assert inputs["conformal_rate_H"] == 0.2
    assert inputs["mass_m"] == 0.0
    assert inputs["omega_on"] == inputs["wave_number_k"] == 2.0
    assert inputs["omega_off"] == 2.2
    assert inputs["omega_off"] ** 2 - inputs["wave_number_k"] ** 2 == pytest.approx(
        0.84
    )
    assert thresholds["minimum_convergence_order_two_finest_pairs"] == 1.8
    assert thresholds["maximum_finest_combined_off_shell_relative_error"] == 0.02
    assert thresholds["maximum_metric_compatibility_absolute_error"] == 1e-12
    assert thresholds["maximum_flat_limit_absolute_discrepancy"] == 1e-12
    assert all(controls.values())


def test_failure_route_is_versioned_and_preserves_artifacts() -> None:
    failure = build_guardrail_payload()["failure_criteria"]
    assert failure["primary_claim_label"] == "B-BLOCKED"
    assert failure["selected_repair_target"] == THRESHOLD_REPAIR_TARGET
    assert failure["failed_artifacts_preserved"] is True
    assert failure["threshold_changes_require_new_versioned_guardrail"] is True


def test_qm_representation_pressure_is_deferred_without_claim_upgrade() -> None:
    pressure = build_qm_representation_pressure()
    validate_qm_representation_pressure(pressure)
    assert pressure["pressure_id"] == (
        "quantum_representation_number_field_nonuniqueness"
    )
    assert pressure["claim_upgrade"] is False
    assert pressure["active_lane_interrupted"] is False
    assert pressure["selected_as_current_target"] is False
    assert len(pressure["representation_neutral_requirements"]) == 8
    assert len(pressure["future_sprint_sequence"]) == 3
    assert pressure["monthly_watch_created"] is False


def test_canonical_contract_rejects_nonfinite_numbers() -> None:
    payload = build_guardrail_payload()
    assert canonical_json_bytes(payload).endswith(b"\n")
    payload["inputs"]["conformal_rate_H"] = math.inf
    with pytest.raises(ValueError):
        canonical_json_bytes(payload)


def test_guardrail_does_not_execute_or_promote_equations() -> None:
    payload = build_guardrail_payload()
    assert payload["calculation_executed"] is False
    assert payload["e_repro_claimed"] is False
    assert payload["equation_compendium_row_added"] is False
    assert payload["equation_surfaces"]["equation_compendium_edited"] is False
    assert payload["ccft_lane_status"] == "paused_upstream_prerequisites"


def test_prior_guardrail_execution_and_review_are_preserved_after_rotation() -> None:
    registry = loop_registry()
    state = current_target_state(registry)
    active = active_workstream(registry)
    guardrail = workstream(
        "prepare_bounded_curved_space_scalar_qft_gr_source_contract_retest_"
        "guardrail_packet",
        registry,
    )
    execution = workstream(EXECUTION_TARGET, registry)
    review = workstream(
        "review_calc_scalar_stress_energy_covariant_divergence_identity_"
        "conformal_background_v0_result",
        registry,
    )
    assert guardrail["status"] == "paused"
    assert guardrail["selected_next_target"] == EXECUTION_TARGET
    assert execution["status"] == "paused"
    assert execution["selected_next_target"] == (
        "review_calc_scalar_stress_energy_covariant_divergence_identity_"
        "conformal_background_v0_result"
    )
    assert review["status"] == "paused"
    assert review["selected_next_target"] == NONZERO_CURVATURE_GUARDRAIL_TARGET
    assert state["previous_live_next_target"] == (
        "execute_calc_scalar_stress_energy_covariant_divergence_identity_multi_"
        "background_robustness_v0"
    )
    assert state["live_next_target"] == (
        "review_calc_scalar_stress_energy_covariant_divergence_identity_multi_"
        "background_robustness_v0_result"
    )
    assert active["workstream_id"] == state["live_next_target"]
    assert active["claim_ceiling_level"] == 3
    assert active["claim_status"] == "candidate_pending_independent_result_review"


def test_execution_report_preserves_locally_flat_interpretation() -> None:
    payload = build_execution_report()
    assert payload["packet_result"] == EXECUTION_OUTCOME
    assert payload["strict_packet_result"] == EXECUTION_STRICT_OUTCOME
    assert payload["selected_next_target"] == (
        "review_calc_scalar_stress_energy_covariant_divergence_identity_"
        "conformal_background_v0_result"
    )
    assert payload["background_geometry_classification"] == (
        "locally_flat_nontrivial_conformal_connection"
    )
    assert payload["scalar_curvature"] == 0.0
    assert payload["curvature_test_claimed"] is False
    assert payload["covariant_connection_test_claimed"] is True
    assert payload["all_thresholds_passed"] is True
    assert payload["claim"]["claim_status"] == "generated_pending_result_review"
    assert payload["equation_compendium_edited"] is False
