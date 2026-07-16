from __future__ import annotations

import pytest

from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_design_packet_v0
    as design,
)


@pytest.fixture(scope="module")
def artifacts() -> tuple[dict, dict, dict]:
    return design.build_artifacts()


@pytest.fixture(scope="module")
def packet(artifacts: tuple[dict, dict, dict]) -> dict:
    return artifacts[0]


def test_generated_design_artifacts_are_current(artifacts: tuple[dict, dict, dict]) -> None:
    packet, manifest, report = artifacts
    assert design.PACKET_PATH.read_bytes() == design.canonical_json_bytes(packet)
    assert design.MANIFEST_PATH.read_bytes() == design.canonical_json_bytes(manifest)
    assert design.REPORT_PATH.read_bytes() == design.canonical_json_bytes(report)


def test_accepted_route_A_authority_and_all_canonical_outputs_have_exact_custody(
    packet: dict,
) -> None:
    custody = packet["source_custody"]
    assert custody["passed"] is True
    assert custody["source_artifact_hashes"] == design.EXPECTED_SOURCE_HASHES
    assert custody["accepted_route_A_design_preparation_authority_exact"] is True
    assert custody["canonical_run_output_count_checked"] == 203
    assert custody["canonical_run_output_hash_failures"] == []
    assert custody["canonical_root_file_count"] == 205
    assert custody["canonical_root_digest"] == design.EXPECTED_CANONICAL_ROOT_DIGEST
    assert custody["execution_count_performed"] == 1


def test_design_preparation_is_read_only_and_does_not_import_simulator(packet: dict) -> None:
    before = design.canonical_root_digest()
    design.build_artifacts()
    after = design.canonical_root_digest()
    source = (design.REPO_ROOT / design.GENERATOR_RELATIVE_PATH).read_text(encoding="utf-8")
    assert before == after == design.EXPECTED_CANONICAL_ROOT_DIGEST
    assert " as simulator" not in source
    assert packet["source_custody"]["new_simulation_run_count"] == 0
    assert packet["source_custody"]["canonical_output_mutation_count"] == 0


def test_three_scientific_questions_map_to_all_unresolved_mechanisms(packet: dict) -> None:
    questions = packet["scientific_questions"]
    assert len(questions) == 3
    assert [item["mechanism_id"] for item in questions] == design.MECHANISM_IDS
    assert packet["inherited_authority"]["root_numerical_mechanism_status"] == "UNRESOLVED"


def test_core_roles_require_loose_tight_neighbor_and_paired_self_controls(packet: dict) -> None:
    roles = {item["role_class"]: item for item in packet["required_run_classes"]}
    assert set(roles) == {
        "CORE_R13_LOOSE_MECHANISM",
        "CORE_R13_TIGHT_REFERENCE",
        "CORE_MATCHED_PASSING_NEIGHBOR_LOOSE",
        "INSTRUMENTATION_NONPERTURBATION_REFERENCE",
    }
    assert "1e-8" in roles["CORE_R13_LOOSE_MECHANISM"]["solver_tolerance_rule"]
    assert "1e-10 and 1e-12" in roles["CORE_R13_TIGHT_REFERENCE"][
        "solver_tolerance_rule"
    ]
    assert roles["INSTRUMENTATION_NONPERTURBATION_REFERENCE"]["instrumented"] is False
    assert "every distinct core" in packet["instrumentation_nonperturbation_contract"][
        "paired_self_control_scope"
    ]


def test_neighbor_rule_is_deterministic_but_exact_neighbor_is_not_frozen(packet: dict) -> None:
    neighbor = packet["matched_neighbor_selection_design"]
    assert neighbor["eligible_axis_sharing_candidate_count"] == 11
    assert neighbor["provisional_top_candidate_for_freeze_confirmation"] == "R10_MU_HIGH"
    assert neighbor["exact_neighbor_frozen_now"] is False
    assert neighbor["post_result_visual_choice_allowed"] is False
    assert neighbor["ranking_rule"] == [
        "maximize number of shared R13 axis values",
        "minimize Euclidean distance after per-axis min-max normalization over the frozen matrix",
        "break remaining ties by lexicographically ascending scientific_row_id",
    ]
    ranked = neighbor["ranked_candidate_audit"]
    assert all(item["all_four_loose_solver_residual_ceilings_pass"] for item in ranked)


def test_nonperturbation_contract_prefers_byte_identity_and_blocks_posthoc_fallback(
    packet: dict,
) -> None:
    contract = packet["instrumentation_nonperturbation_contract"]
    assert contract["primary_equivalence_rule"] == (
        "byte-identical registered physical trajectory payload"
    )
    assert contract["fallback_equivalence_rule_status"] == (
        "NOT_DEFINED_OR_AUTHORIZED_IN_DESIGN_v0"
    )
    assert contract["nonperturbation_floor_frozen_now"] is False
    assert contract["nonperturbation_ceiling_frozen_now"] is False
    assert contract["failure_disposition"] == "B-BLOCKED_INSTRUMENTATION_PERTURBATION"
    assert len(contract["forbidden_effects"]) == 7


def test_exchange_and_solver_instrumentation_preserve_raw_and_normalized_evidence(
    packet: dict,
) -> None:
    observables = {item["observable_id"]: item for item in packet["mechanism_observable_registry"]}
    assert set(observables).issuperset(
        {
            "EXCHANGE_FIELD_LONGITUDINAL_RAW",
            "EXCHANGE_MATTER_LONGITUDINAL_RAW",
            "EXCHANGE_LONGITUDINAL_REMAINDER_RAW",
            "EXCHANGE_CANCELLATION_KAPPA",
            "SOLVER_BLOCK_RESIDUAL_RAW",
            "SOLVER_BLOCK_RESIDUAL_NORMALIZED",
            "SOLVER_BLOCK_DOMINANCE_FRACTION",
            "SOLVER_ITERATION_METADATA",
        }
    )
    assert "epsilon_exchange" in observables["EXCHANGE_CANCELLATION_KAPPA"][
        "semantic_requirement"
    ]
    assert observables["SOLVER_BLOCK_RESIDUAL_RAW"]["unit_requirement"].startswith(
        "native block unit"
    )
    assert observables["SOLVER_BLOCK_DOMINANCE_FRACTION"]["unit_requirement"] == (
        "dimensionless"
    )


def test_spatial_fields_and_actual_discrete_closure_are_mandatory(packet: dict) -> None:
    observable_ids = {item["observable_id"] for item in packet["mechanism_observable_registry"]}
    assert observable_ids.issuperset(
        {
            "GAUSS_RESIDUAL_FIELD",
            "CONTINUITY_RESIDUAL_FIELD",
            "LONGITUDINAL_MAXWELL_RESIDUAL_COMPONENTS",
            "DISCRETE_OPERATOR_OUTPUTS",
            "MAXWELL_TO_CONTINUITY_CLOSURE_RESIDUAL",
        }
    )
    closure = packet["discrete_Maxwell_continuity_closure_contract"]
    assert closure["continuum_formula_is_not_the_audit_definition"] is True
    assert closure["posthoc_continuum_derivative_substitution_allowed"] is False
    assert closure["closure_formula_frozen_now"] is False
    assert closure["closure_threshold_frozen_now"] is False


def test_all_implemented_blocks_require_complete_semantics_and_missing_data_blocks(
    packet: dict,
) -> None:
    contract = packet["aggregation_block_registry_and_missing_data_contract"]
    assert len(contract["per_block_freeze_fields"]) == 9
    assert "every implemented solver block" in contract["block_registry_requirement"]
    assert contract["required_missing_data_behavior"] == (
        "B-BLOCKED_REQUIRED_MECHANISM_OBSERVABLE_MISSING"
    )
    assert "never silent zero" in contract["optional_not_applicable_behavior"]


def test_hypotheses_classifier_allows_multiple_distributed_and_unresolved_outcomes(
    packet: dict,
) -> None:
    design_logic = packet["hypotheses_and_classifier_design"]
    assert [item["hypothesis_id"] for item in design_logic["hypotheses"]] == [
        "H_A_CANCELLATION_CONDITIONING",
        "H_B_LONGITUDINAL_EQUATION_BLOCK_DOMINANCE",
        "H_C_DISCRETE_CLOSURE_MISMATCH",
        "H_D_DISTRIBUTED_ACCUMULATED_SOLVER_ERROR",
        "H_E_UNRESOLVED_MECHANISM",
    ]
    assert design_logic["multiple_H_A_to_H_C_support_allowed"] is True
    assert design_logic["forced_single_winner_allowed"] is False
    assert design_logic["unresolved_outcome_mandatory"] is True
    assert design_logic["outcome_classes"] == [
        "EVIDENCE_BLOCKED_CUSTODY_OR_INSTRUMENTATION",
        "EVIDENCE_BLOCKED_NUMERICAL_OR_DEFINITION",
        "SINGLE_SUPPORTED_MECHANISM",
        "MULTIPLE_SUPPORTED_MECHANISMS",
        "DISTRIBUTED_ACCUMULATED_SOLVER_ERROR",
        "UNRESOLVED_MECHANISM",
    ]


def test_supporting_tolerance_and_duration_modules_remain_secondary(packet: dict) -> None:
    modules = packet["supporting_modules"]
    assert [item["module_id"] for item in modules] == [
        "SUPPORT_B_EXPANDED_TOLERANCE_LADDER",
        "SUPPORT_C_DURATION_SCALING",
    ]
    assert all(item["status"].startswith("SECONDARY_OPTION") for item in modules)
    assert all(item["freeze_requirements_if_included"] for item in modules)


def test_output_family_is_separate_and_custody_volume_failures_are_blocking(packet: dict) -> None:
    output = packet["output_separation_and_custody_design"]
    assert output["new_output_family_required"] is True
    assert output["canonical_output_root_write_allowed"] is False
    assert output["canonical_digest_required_before_and_after_every_future_stage"] is True
    assert len(output["payload_identity_fields_required"]) == 13
    assert output["new_output_root_created_now"] is False
    assert output["new_mechanism_output_created_now"] is False
    assert "disk or serialization failure is B-BLOCKED" in output["output_volume_contract"]


def test_exact_values_and_execution_authority_remain_deferred_to_freeze(packet: dict) -> None:
    assert len(packet["freeze_deferred_registry"]) == 16
    assert packet["verdict"] == "PREPARED_PENDING_INDEPENDENT_REVIEW"
    assert packet["passed_decision_count"] == packet["decision_count"] == 27
    assert packet["failed_decision_ids"] == []
    assert packet["selected_next_target"] == design.SELECTED_NEXT_TARGET
    assert packet["downstream_target_if_independent_review_accepts"] == (
        design.DOWNSTREAM_TARGET_IF_ACCEPTED
    )
    authority = packet["authority_boundary"]
    assert authority["design_packet_prepared"] is True
    assert authority["design_independently_accepted"] is False
    assert authority["numerical_freeze_packet_authorized"] is False
    assert authority["experiment_frozen"] is False
    assert authority["new_simulation_authorized"] is False
    assert authority["exact_run_count_or_values_selected"] is False
    assert authority["threshold_or_fit_change_authorized"] is False
    assert authority["robustness_reclassification_authorized"] is False
    assert authority["materiality_classification_authorized"] is False
    assert authority["new_E_REPRO_authorized"] is False
