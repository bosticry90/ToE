from __future__ import annotations

from collections import Counter

import pytest

from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_calibration_and_parameter_freeze_packet_v1
    as freeze,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_canonical_result_classifier_v1
    as classifier,
)


@pytest.fixture(scope="module")
def artifacts() -> tuple[dict, dict, dict, dict]:
    return freeze.build_artifacts()


def test_generated_artifacts_are_current(artifacts: tuple[dict, dict, dict, dict]) -> None:
    packet, matrix, manifest, report = artifacts
    assert freeze.PACKET_PATH.read_bytes() == freeze.canonical_json_bytes(packet)
    assert freeze.RUN_MATRIX_PATH.read_bytes() == freeze.canonical_json_bytes(matrix)
    assert freeze.MANIFEST_PATH.read_bytes() == freeze.canonical_json_bytes(manifest)
    assert freeze.REPORT_PATH.read_bytes() == freeze.canonical_json_bytes(report)


def test_exact_accepted_authority_and_inputs_are_bound(artifacts: tuple[dict, dict, dict, dict]) -> None:
    packet, _, _, _ = artifacts
    authority = packet["authority_basis"]
    assert authority["pilot_review_commit"] == freeze.PILOT_REVIEW_COMMIT
    assert authority["pilot_review_parent"] == freeze.PILOT_REVIEW_PARENT
    assert authority["pilot_review_verdict"] == "ACCEPT_ENGINEERING_READY"
    assert {item["path"]: item["sha256"] for item in authority["input_artifacts"]} == freeze.INPUT_HASHES
    assert freeze.sha256_path(freeze.REPO_ROOT / freeze.PROMPT_RELATIVE_PATH) == freeze.PROMPT_SHA256


def test_fourteen_accepted_scientific_rows_are_immutable(artifacts: tuple[dict, dict, dict, dict]) -> None:
    packet, _, _, _ = artifacts
    design = packet["scientific_design_freeze"]
    assert design["row_count"] == len(design["scientific_rows"]) == 14
    assert len(design["scientific_row_ids"]) == len(set(design["scientific_row_ids"])) == 14
    assert design["scientific_row_ids"][0] == "R00_CANONICAL"
    assert design["scientific_row_ids"][-1] == "R13_CORNER_STRONG_LOW"
    assert design["axis_levels_changed"] is False
    assert design["observable_definitions_changed"] is False
    assert design["control_inventory_changed"] is False
    assert design["materiality_definitions_changed"] is False


def test_full_run_matrix_is_literal_complete_and_unique(artifacts: tuple[dict, dict, dict, dict]) -> None:
    _, matrix, _, _ = artifacts
    assert matrix["scientific_row_count"] == 14
    assert matrix["scientific_records_per_row"] == 13
    assert matrix["scientific_record_count"] == 182
    assert matrix["control_record_count"] == 21
    assert matrix["record_count"] == matrix["unique_run_id_count"] == 203
    assert matrix["role_counts"] == {
        "DETERMINISTIC_DUPLICATE": 28,
        "FORCED_COMPARATOR": 14,
        "NEGATIVE_CONTROL": 13,
        "POSITIVE_CONTROL": 8,
        "PRIMARY_FULL_MODEL": 14,
        "SOLVER_VERIFICATION": 42,
        "SPATIAL_REFINEMENT": 42,
        "TEMPORAL_REFINEMENT": 42,
    }
    required_fields = {
        "run_id", "scientific_row_id", "run_role", "model_or_comparator_class", "grid_size",
        "time_step", "duration", "solver_tolerance", "iteration_cap", "initial_condition_identity",
        "expected_diagnostic", "output_path",
    }
    assert all(required_fields <= set(record) for record in matrix["records"])
    assert len({record["output_path"] for record in matrix["records"]}) == 203
    assert all(":" not in record["output_path"].rsplit("/", 1)[-1] for record in matrix["records"])


def test_every_scientific_row_has_the_same_closed_role_expansion(artifacts: tuple[dict, dict, dict, dict]) -> None:
    packet, matrix, _, _ = artifacts
    for row_id in packet["scientific_design_freeze"]["scientific_row_ids"]:
        roles = Counter(
            record["run_role"]
            for record in matrix["records"]
            if record["scientific_row_id"] == row_id
            and record["run_role"] not in {"POSITIVE_CONTROL", "NEGATIVE_CONTROL"}
        )
        assert roles == {
            "PRIMARY_FULL_MODEL": 1,
            "SPATIAL_REFINEMENT": 3,
            "TEMPORAL_REFINEMENT": 3,
            "SOLVER_VERIFICATION": 3,
            "DETERMINISTIC_DUPLICATE": 2,
            "FORCED_COMPARATOR": 1,
        }
    parameters = packet["proposed_numerical_parameter_freeze"]
    assert parameters["primary_full_model"] == freeze.PRIMARY_PARAMETERS
    assert parameters["row_specific_rescue_parameters_forbidden"] is True
    assert parameters["primary_is_declared_cross_product_not_a_claim_that_exact_tuple_was_piloted"] is True


def test_comparators_and_control_inventory_remain_exact(artifacts: tuple[dict, dict, dict, dict]) -> None:
    packet, matrix, _, _ = artifacts
    forced = [record for record in matrix["records"] if record["run_role"] == "FORCED_COMPARATOR"]
    assert len(forced) == 14
    assert all(record["model_or_comparator_class"] == "INTENTIONALLY_NONINVARIANT_COMPARATOR" for record in forced)
    assert all(record["parent_scientific_row_id"] == record["scientific_row_id"] for record in forced)
    assert matrix["invariant_descendant_free_comparator_record_count"] == 0
    assert matrix["invariant_descendant_free_comparator_reason"] == "NOT_AVAILABLE_WITHOUT_SEPARATE_ACCEPTED_INVARIANCE_PROOF"
    controls = [record for record in matrix["records"] if record["run_role"] in {"POSITIVE_CONTROL", "NEGATIVE_CONTROL"}]
    assert Counter(record["run_role"] for record in controls) == {"POSITIVE_CONTROL": 8, "NEGATIVE_CONTROL": 13}
    invariant = next(record for record in controls if record["run_id"].endswith("P_ANALYTIC_INVARIANT_DESCENDANT_FREE"))
    assert invariant["execution_kind"] == "ELIGIBILITY_CHECK"
    assert invariant["expected_diagnostic"] == "CONDITIONAL_NOT_EXECUTED_WITHOUT_SEPARATE_ACCEPTED_INVARIANT_SUBDOMAIN_PROOF"
    assert packet["comparator_freeze"]["forced_comparator_positive_robustness_eligible"] is False


def test_all_residual_and_floor_thresholds_reconstruct_mechanically(artifacts: tuple[dict, dict, dict, dict]) -> None:
    packet, _, _, _ = artifacts
    thresholds = packet["numerical_threshold_provenance"]
    assert len(thresholds) == 22
    assert all(item["candidate_frozen_threshold"] == item["recomputed_threshold"] for item in thresholds)
    assert all(item["candidate_frozen_threshold"] > 0.0 for item in thresholds)
    by_id = {item["threshold_id"]: item for item in thresholds}
    assert len(by_id["epsilon_observable_floor"]["pilot_source_run_ids"]) == 10
    assert len(by_id["epsilon_exchange_floor"]["pilot_source_run_ids"]) == 10
    assert all(
        len(item["pilot_source_run_ids"]) == 50
        for threshold_id, item in by_id.items()
        if threshold_id not in {"epsilon_observable_floor", "epsilon_exchange_floor"}
    )
    assert by_id["maximum_solver_residual"]["candidate_frozen_threshold"] == 2e-8
    assert by_id["maximum_energy_drift"]["candidate_frozen_threshold"] == 8e-10
    assert by_id["epsilon_observable_floor"]["candidate_frozen_threshold"] == pytest.approx(5e-11)
    assert by_id["epsilon_exchange_floor"]["candidate_frozen_threshold"] == 3e-16


def test_convergence_and_structural_gates_are_frozen_without_fit_selection(artifacts: tuple[dict, dict, dict, dict]) -> None:
    packet, _, _, _ = artifacts
    convergence = packet["convergence_threshold_provenance"]
    assert [item["threshold_id"] for item in convergence] == [
        "minimum_spatial_descendant_order",
        "minimum_temporal_descendant_order",
        "minimum_energy_error_order",
    ]
    assert all(item["candidate_frozen_threshold"] == 1.5 for item in convergence)
    assert all(len(item["pilot_source_run_ids"]) == 15 for item in convergence)
    gates = packet["fixed_structural_numerical_gates"]
    assert gates["maximum_solver_to_truncation_ratio"] == 0.01
    assert gates["maximum_iterations"] == 80
    assert gates["axis_round_trip_absolute_tolerance"] == 2e-15
    assert gates["fit_members_may_be_excluded"] is False
    assert gates["fit_ranges_may_change_after_execution"] is False


def test_materiality_outcomes_and_classifier_provenance_stay_separate(artifacts: tuple[dict, dict, dict, dict]) -> None:
    packet, _, _, _ = artifacts
    materiality = packet["scientific_materiality_freeze"]
    assert materiality["material_R_perp_gate"] == materiality["material_F_exchange_perp_gate"] == 0.1
    assert materiality["descendant_dominated_R_perp_gate"] == materiality["descendant_dominated_F_exchange_perp_gate"] == 0.5
    assert materiality["threshold_sensitivity_values"] == [0.05, 0.1, 0.2]
    logic = packet["deterministic_outcome_logic"]
    assert logic["robustness_classification_order"] == [
        "NUMERICALLY_BLOCKED", "MODEL_DOMAIN_LIMITED", "THRESHOLD_SENSITIVE", "BROADLY_ROBUST", "CONDITIONALLY_ROBUST"
    ]
    assert logic["separation_rule"].startswith("robustness status and descendant-significance status are independent")
    provenance = packet["classifier_versioning_and_provenance"]
    assert provenance["pre_correction_source_blob_bound"] is False
    assert provenance["classifier_implementation_must_be_committed_before_first_evaluation"] is True
    assert provenance["execution_must_refuse_uncommitted_or_hash_mismatched_classifier"] is True
    assert provenance["classifier_implementation"] == {"path": freeze.CLASSIFIER_RELATIVE_PATH, "sha256": freeze.CLASSIFIER_SHA256}
    assert "No separate pre-correction source blob" in provenance["permanent_limitation"]


def test_frozen_classifier_applies_precedence_and_separate_significance() -> None:
    rows = [{"row_id": f"R{index:02d}", "robustness_pass": True} for index in range(14)]
    base = {
        "custody_ok": True,
        "controls_ok": True,
        "evidence_complete": True,
        "model_domain_limited": False,
        "threshold_sensitive": False,
        "necessity_resolved": True,
        "numerical_floor_resolved": True,
        "row_results": rows,
        "r_perp_maxima": [0.2],
        "f_exchange_perp": [0.05],
    }
    broad = classifier.classify_registered_result(base)
    assert broad["robustness_status"] == "BROADLY_ROBUST"
    assert broad["descendant_significance_status"] == "INTERMEDIATE_DESCENDANT_CONTRIBUTION"
    custody = classifier.classify_registered_result({**base, "custody_ok": False})
    assert custody["execution_status"] == "B-BLOCKED_CUSTODY"
    assert custody["robustness_status"] is None
    blocked = classifier.classify_registered_result({**base, "evidence_complete": False})
    assert blocked["robustness_status"] == "NUMERICALLY_BLOCKED"
    assert blocked["descendant_significance_status"] is None
    conditional_rows = [*rows]
    conditional_rows[-1] = {"row_id": "R13", "robustness_pass": False}
    conditional = classifier.classify_registered_result({**base, "row_results": conditional_rows, "r_perp_maxima": [0.6]})
    assert conditional["robustness_status"] == "CONDITIONALLY_ROBUST"
    assert conditional["descendant_significance_status"] == "DESCENDANT_DOMINATED_REGIME"


def test_preparation_rotates_only_to_independent_freeze_review(artifacts: tuple[dict, dict, dict, dict]) -> None:
    packet, _, _, report = artifacts
    assert report["verdict"] == "PREPARED_PENDING_INDEPENDENT_REVIEW"
    assert report["selected_next_target"] == freeze.REVIEW_TARGET
    assert packet["post_acceptance_target"] == freeze.POST_ACCEPTANCE_TARGET
    boundary = packet["authority_boundary"]
    assert boundary["packet_prepared"] is True
    assert boundary["packet_independently_accepted"] is False
    assert boundary["numerical_parameters_authoritatively_frozen"] is False
    assert boundary["numerical_thresholds_authoritatively_frozen"] is False
    assert boundary["canonical_fourteen_row_execution_authorized"] is False
    assert boundary["robustness_classification_assigned"] is False
    assert boundary["descendant_significance_assigned"] is False
    assert boundary["new_E_REPRO_claim"] is False
    assert boundary["previous_canonical_E_REPRO_unchanged"] is True
