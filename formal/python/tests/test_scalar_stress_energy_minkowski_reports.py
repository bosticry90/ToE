from __future__ import annotations

import math

import pytest

from formal.python.tests.strict_physics_state_helpers import (
    active_workstream,
    current_target_state,
    loop_registry,
    workstream,
)
from formal.python.tools.scalar_stress_energy_minkowski_reports import (
    EXECUTION_OUTCOME,
    EXECUTION_STRICT_OUTCOME,
    EXECUTION_TARGET,
    GUARDRAIL_OUTCOME,
    GUARDRAIL_STRICT_OUTCOME,
    THRESHOLD_REPAIR_TARGET,
    build_guardrail_payload,
    build_execution_report,
    canonical_json_bytes,
    validate_guardrail_payload,
)


def test_guardrail_freezes_required_sprint_interface_and_scope() -> None:
    payload = build_guardrail_payload()
    validate_guardrail_payload(payload)
    assert payload["packet_result"] == GUARDRAIL_OUTCOME
    assert payload["strict_packet_result"] == GUARDRAIL_STRICT_OUTCOME
    assert payload["selected_next_target"] == EXECUTION_TARGET
    assert payload["claim_ceiling"]["claim_ladder_level"] == 3
    assert payload["claim_ceiling"]["not_gravity_dynamics"] is True
    assert payload["claim_ceiling"]["not_source_admissibility"] is True
    assert payload["claim_ceiling"]["not_seam_admissibility"] is True


def test_guardrail_freezes_exact_conventions_and_controls() -> None:
    payload = build_guardrail_payload()
    equations = payload["equation_surfaces"]
    inputs = payload["inputs"]
    assert equations["metric_signature"] == "eta_mu_nu = diag(-1,+1)"
    assert equations["field_residual"] == "E_phi = box phi - m^2 phi"
    assert equations["divergence_identity"] == (
        "partial_mu T^{mu nu} = E_phi partial^nu phi"
    )
    assert inputs["time_slices"] == [0.0, 0.37, 0.91]
    assert inputs["spatial_resolutions_N"] == [64, 128, 256, 512]
    assert inputs["off_shell_exact_coefficient"] == pytest.approx(1.05)
    assert (1.1 * math.sqrt(5.0)) ** 2 - 2.0**2 - 1.0**2 == pytest.approx(
        1.05
    )


def test_guardrail_freezes_numerical_method_thresholds_and_failure_route() -> None:
    payload = build_guardrail_payload()
    method = payload["numerical_method"]
    thresholds = payload["success_criteria"]
    failure = payload["failure_criteria"]
    assert method["temporal_derivatives"] == "analytic"
    assert "second-order centered periodic" in method["spatial_derivatives"]
    assert thresholds["minimum_convergence_order_two_finest_pairs"] == 1.8
    assert thresholds["maximum_finest_combined_off_shell_relative_error"] == 0.02
    assert thresholds["maximum_exact_coefficient_absolute_error"] == 1e-12
    assert thresholds["minimum_finest_off_to_on_divergence_norm_ratio"] == 100.0
    assert failure["primary_claim_label"] == "B-BLOCKED"
    assert failure["selected_repair_target"] == THRESHOLD_REPAIR_TARGET
    assert failure["threshold_changes_require_new_versioned_guardrail"] is True


def test_guardrail_canonical_contract_rejects_nonfinite_numbers() -> None:
    payload = build_guardrail_payload()
    assert canonical_json_bytes(payload).endswith(b"\n")
    payload["inputs"]["amplitude_A"] = math.nan
    with pytest.raises(ValueError):
        canonical_json_bytes(payload)


def test_guardrail_does_not_execute_or_activate_equations() -> None:
    payload = build_guardrail_payload()
    assert payload["calculation_executed"] is False
    assert payload["e_repro_claimed"] is False
    assert payload["equation_compendium_row_added"] is False
    assert payload["equation_surfaces"]["equation_compendium_edited"] is False
    assert payload["ccft_lane_status"] == "paused_upstream_prerequisites"


def test_guardrail_and_execution_are_preserved_after_result_review() -> None:
    registry = loop_registry()
    state = current_target_state(registry)
    active = active_workstream(registry)
    guardrail = workstream(
        "prepare_scalar_qft_gr_source_contract_flat_limit_pretest_guardrail_packet",
        registry,
    )
    execution = workstream(EXECUTION_TARGET, registry)
    assert guardrail["status"] == "paused"
    assert guardrail["selected_next_target"] == EXECUTION_TARGET
    assert execution["status"] == "paused"
    assert execution["selected_next_target"] == (
        "review_calc_scalar_stress_energy_divergence_identity_minkowski_v0_result"
    )
    assert state["live_next_target"] == (
        "prepare_bounded_curved_space_scalar_qft_gr_source_contract_retest_"
        "guardrail_packet"
    )
    assert state["previous_live_next_target"] == (
        "review_calc_scalar_stress_energy_divergence_identity_minkowski_v0_result"
    )
    assert active["workstream_id"] == state["live_next_target"]
    assert active["authorized_next_strict_target"] == state["live_next_target"]
    assert active["claim_ceiling_level"] == 3


def test_execution_report_records_passed_scoped_result_pending_review() -> None:
    payload = build_execution_report()
    assert payload["packet_result"] == EXECUTION_OUTCOME
    assert payload["strict_packet_result"] == EXECUTION_STRICT_OUTCOME
    assert payload["selected_next_target"] == (
        "review_calc_scalar_stress_energy_divergence_identity_minkowski_v0_result"
    )
    assert payload["control_counts"] == {
        "on_shell_time_resolution_rows": 12,
        "off_shell_time_resolution_rows": 12,
        "time_slice_count": 3,
        "resolution_count": 4,
        "divergence_component_count": 2,
    }
    assert payload["all_thresholds_passed"] is True
    assert all(payload["threshold_checks"].values())
    assert payload["claim"]["primary_label"] == "E-REPRO"
    assert payload["claim"]["claim_status"] == "generated_pending_result_review"
    assert payload["equation_compendium_edited"] is False
