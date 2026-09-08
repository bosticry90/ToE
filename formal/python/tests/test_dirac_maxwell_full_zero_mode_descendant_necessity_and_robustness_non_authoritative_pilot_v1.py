from __future__ import annotations

import pytest

from formal.python.tools import dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_non_authoritative_pilot_v1 as pilot


@pytest.fixture(scope="module")
def artifacts() -> tuple[dict, dict, dict, dict]:
    return pilot.build_artifacts()


def test_pilot_artifacts_are_current(artifacts: tuple[dict, dict, dict, dict]) -> None:
    packet, arrays, manifest, report = artifacts
    assert pilot.PACKET_PATH.read_bytes() == pilot.canonical_json_bytes(packet)
    assert pilot.ARRAYS_PATH.read_bytes() == pilot.canonical_json_bytes(arrays)
    assert pilot.MANIFEST_PATH.read_bytes() == pilot.canonical_json_bytes(manifest)
    assert pilot.REPORT_PATH.read_bytes() == pilot.canonical_json_bytes(report)


def test_accepted_guardrail_authorizes_exactly_this_pilot() -> None:
    binding = pilot.validate_authority()
    assert binding["review_commit"] == pilot.REVIEW_COMMIT
    assert binding["review_parent"] == pilot.REVIEW_PARENT
    assert len(binding["bound_inputs"]) == 5
    assert pilot.PROMPT_DEPENDENCY_ROLE == "DEMOTE_TO_NONBLOCKING_PROVENANCE"


def test_fixed_five_row_subset_and_run_inventory_are_exact(
    artifacts: tuple[dict, dict, dict, dict],
) -> None:
    packet, arrays, _, _ = artifacts
    summary = packet["summary"]
    assert [item["row_id"] for item in summary["row_results"]] == [
        "R00_CANONICAL",
        "R03_F_ZERO",
        "R05_F_HIGH",
        "R10_MU_HIGH",
        "R11_CORNER_WEAK_HIGH",
    ]
    assert summary["registered_run_count"] == len(arrays["runs"]) == 50
    assert summary["full_run_count"] == 45
    assert summary["forced_comparator_run_count"] == 5
    assert len({item["run_record_id"] for item in arrays["runs"]}) == 50


def test_every_initial_state_reconstructs_all_axes_with_runtime_mass_and_charge(
    artifacts: tuple[dict, dict, dict, dict],
) -> None:
    packet, _, _, _ = artifacts
    for row in packet["summary"]["row_results"]:
        reconstruction = row["base_initial_state_reconstruction"]
        assert reconstruction["round_trip_passed"] is True
        assert max(reconstruction["round_trip_absolute_errors"].values()) <= pilot.ROUND_TRIP_TOLERANCE
        assert reconstruction["positive_base_strictly_positive"] is True
        assert reconstruction["charge_identity_error"] == 0.0
        assert reconstruction["mass_runtime_parameter"] == row["requested_axis_values"]["MU_MASS_DOMAIN"]
        assert reconstruction["sector_multiplicity"] == 4
        assert reconstruction["charge_neutrality_error"] <= 1e-14


def test_each_row_has_controlled_refinement_solver_and_energy_evidence(
    artifacts: tuple[dict, dict, dict, dict],
) -> None:
    packet, _, _, _ = artifacts
    summary = packet["summary"]
    assert all(summary["numerical_criteria"].values())
    for row in summary["row_results"]:
        assert row["temporal_refinement"]["observed_descendant_order"] > 1.5
        assert row["solver_hierarchy"]["observed_ratio"] <= 0.01
        assert row["energy_behavior"]["observed_maximum_error_order"] > 1.5
        drifts = row["energy_behavior"]["maximum_drift_by_temporal_refinement"]
        assert drifts[-1] <= drifts[0]
        assert row["energy_behavior"]["accepted_error_class_under_test"] == "BOUNDED_CONVERGENT_ENERGY_ERROR"


def test_energy_shape_is_recorded_separately_from_refinement_acceptance(
    artifacts: tuple[dict, dict, dict, dict],
) -> None:
    packet, _, _, _ = artifacts
    for row in packet["summary"]["row_results"]:
        assert row["energy_behavior"]["drift_shape_by_temporal_refinement"] == [
            "MONOTONE_AT_FIXED_RESOLUTION",
            "MONOTONE_AT_FIXED_RESOLUTION",
            "MONOTONE_AT_FIXED_RESOLUTION",
        ]


def test_forced_comparators_keep_parent_provenance_and_fail_for_source_reason(
    artifacts: tuple[dict, dict, dict, dict],
) -> None:
    packet, _, _, _ = artifacts
    evidence = packet["summary"]["comparator_evidence"]
    assert len(evidence) == 5
    assert all(item["comparator_realized_loading"] is None for item in evidence)
    assert all(item["comparator_realized_loading_status"] == "NOT_PHYSICALLY_ELIGIBLE" for item in evidence)
    assert all(item["forced_R_TRUNC_equation_residual"] > 0.0 for item in evidence)
    assert all(item["scientific_materiality_evaluated_for_claim"] is False for item in evidence)


def test_all_frozen_controls_discriminate(artifacts: tuple[dict, dict, dict, dict]) -> None:
    packet, _, _, report = artifacts
    summary = packet["summary"]
    assert [item["control_id"] for item in summary["positive_controls"]] == pilot.POSITIVE_CONTROL_IDS
    assert len(summary["positive_controls"]) == report["positive_controls_passed"] == 8
    assert all(item["passed"] for item in summary["positive_controls"])
    assert [(item["control_id"], item["expected_diagnostic"]) for item in summary["negative_controls"]] == pilot.NEGATIVE_CONTROL_SPECS
    assert len(summary["negative_controls"]) == report["negative_controls_passed"] == 13
    assert all(item["actual_diagnostics"] == [item["expected_diagnostic"]] for item in summary["negative_controls"])
    assert all(item["passed"] for item in summary["negative_controls"])


def test_candidate_thresholds_are_mechanical_unreviewed_and_not_frozen(
    artifacts: tuple[dict, dict, dict, dict],
) -> None:
    packet, _, _, report = artifacts
    summary = packet["summary"]
    assert all(summary["threshold_generation_criteria"].values())
    for key, value in summary["maximum_numerical_metrics"].items():
        assert summary["candidate_thresholds_unreviewed"][key] == pilot.round_up_one_significant(2.0 * value)
    assert summary["scientific_materiality_thresholds_unchanged"] == {
        "material_gate": 0.1,
        "dominated_gate": 0.5,
        "threshold_sensitivity_values": [0.05, 0.1, 0.2],
    }
    assert packet["candidate_numerical_thresholds_frozen"] is False
    assert packet["candidate_parameters_frozen"] is False
    assert packet["calibration_freeze_authorized"] is False
    assert report["candidate_thresholds_frozen"] is False


def test_pilot_outcome_is_engineering_ready_pending_independent_review(
    artifacts: tuple[dict, dict, dict, dict],
) -> None:
    packet, _, _, report = artifacts
    assert packet["outcome"] == "ACCEPT_ENGINEERING_READY"
    assert packet["selected_next_target"] == pilot.REVIEW_TARGET
    assert report["verdict"] == "ACCEPT_ENGINEERING_READY_PENDING_INDEPENDENT_REVIEW"
    assert packet["summary"]["scientific_significance_class_assigned"] is False
    assert packet["summary"]["robustness_status_assigned"] is False
    assert packet["canonical_robustness_execution_authorized"] is False
    assert packet["new_scientific_claim_authorized"] is False


def test_two_clean_pilot_executions_are_byte_identical(
    artifacts: tuple[dict, dict, dict, dict],
) -> None:
    packet, _, _, _ = artifacts
    determinism = packet["determinism"]
    assert determinism["execution_count"] == 2
    assert determinism["byte_identical"] is True
    assert len(set(determinism["execution_sha256"])) == 1
