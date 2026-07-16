from __future__ import annotations

import copy
import importlib
from functools import lru_cache
from pathlib import Path
from typing import Any

import pytest

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_classifier_v0
    as classifier,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_implementation_v0
    as instrumentation,
)


ROOT = find_repo_root(Path(__file__))
FREEZE_MODULE = (
    "formal.python.tools.dirac_maxwell_full_zero_mode_descendant_necessity_and_"
    "robustness_instrumented_r13_mechanism_experiment_numerical_freeze_packet_v0"
)
BLOCK_IDS = [
    "THETA_KINEMATIC",
    "P_LONGITUDINAL_MAXWELL",
    "PHI2_KINEMATIC",
    "P2_DYNAMIC",
    "PHI3_KINEMATIC",
    "P3_DYNAMIC",
    "DIRAC_PLUS",
    "DIRAC_MINUS",
]


def _freeze() -> Any:
    try:
        module = importlib.import_module(FREEZE_MODULE)
    except ModuleNotFoundError:
        pytest.skip("numerical-freeze generator has not landed yet")
    if not all(hasattr(module, name) for name in ("artifact_bytes", "build_packet")):
        pytest.skip("numerical-freeze generator is not complete yet")
    return module


@lru_cache(maxsize=1)
def _built_artifacts() -> tuple[
    Any,
    dict[str, Any],
    dict[str, Any],
    dict[str, Any],
    dict[str, Any],
    dict[str, Any],
]:
    freeze = _freeze()
    packet, matrix, identity, manifest, report = freeze.build_artifacts()
    return freeze, packet, matrix, identity, manifest, report


def _role_metrics() -> dict[str, dict[str, Any]]:
    return {
        role: {
            "median_kappa": 10.0,
            "severe_step_fraction": 0.0,
            "sample_count": 16,
        }
        for role in classifier.ROLE_KEYS
    }


def _block_metrics() -> dict[str, dict[str, Any]]:
    shares = {block_id: 0.125 for block_id in BLOCK_IDS}
    return {
        role: {
            "dominant_block_id": "THETA_KINEMATIC",
            "median_dominance_share": 0.125,
            "dominant_step_fraction": 0.0,
            "median_share_by_block": copy.deepcopy(shares),
        }
        for role in classifier.ROLE_KEYS
    }


def _closure_metrics() -> dict[str, dict[str, Any]]:
    return {
        role: {
            "max_roundoff_bound_ratio": 0.5,
            "maximum_consecutive_violation_steps": 0,
            "sample_count": 16,
        }
        for role in classifier.ROLE_KEYS
    }


def _distributed_metrics() -> dict[str, dict[str, Any]]:
    return {
        role: {
            "distributed_step_fraction": 0.0,
            "linked_series_maxima_at_final_count": 4,
            "minimum_nondecreasing_increment_count": 14,
        }
        for role in classifier.ROLE_KEYS
    }


def _admissible_fixture() -> dict[str, Any]:
    return {
        "custody_passed": True,
        "observed_run_ids": list(classifier.EXPECTED_RUN_IDS),
        "required_payloads_complete": True,
        "required_observables_complete": True,
        "separate_output_custody_passed": True,
        "instrumentation_nonperturbation_passed": True,
        "observable_semantics_passed": True,
        "discrete_operator_binding_passed": True,
        "metrics": {
            "exchange_conditioning": _role_metrics(),
            "block_dominance": _block_metrics(),
            "discrete_closure": _closure_metrics(),
            "distributed_accumulation": _distributed_metrics(),
        },
    }


def _support_H_A(evidence: dict[str, Any]) -> None:
    metrics = evidence["metrics"]["exchange_conditioning"]
    metrics["R13_LOOSE"].update(
        median_kappa=1.0e8,
        severe_step_fraction=0.75,
    )
    metrics["R13_TIGHT"]["median_kappa"] = 1.0e6
    metrics["R10_LOOSE_NEIGHBOR"]["median_kappa"] = 1.0e6


def _support_H_B(evidence: dict[str, Any]) -> None:
    metrics = evidence["metrics"]["block_dominance"]
    loose = metrics["R13_LOOSE"]
    loose["dominant_block_id"] = "P_LONGITUDINAL_MAXWELL"
    loose["median_dominance_share"] = 0.60
    loose["dominant_step_fraction"] = 0.75
    loose["median_share_by_block"]["P_LONGITUDINAL_MAXWELL"] = 0.60
    metrics["R13_TIGHT"]["median_share_by_block"][
        "P_LONGITUDINAL_MAXWELL"
    ] = 0.20
    metrics["R10_LOOSE_NEIGHBOR"]["median_share_by_block"][
        "P_LONGITUDINAL_MAXWELL"
    ] = 0.20


def _support_H_C(evidence: dict[str, Any]) -> None:
    metrics = evidence["metrics"]["discrete_closure"]
    metrics["R13_LOOSE"].update(
        max_roundoff_bound_ratio=20.0,
        maximum_consecutive_violation_steps=2,
    )
    metrics["R13_TIGHT"]["max_roundoff_bound_ratio"] = 2.0
    metrics["R10_LOOSE_NEIGHBOR"]["max_roundoff_bound_ratio"] = 10.0


def _support_H_D(evidence: dict[str, Any]) -> None:
    metrics = evidence["metrics"]["distributed_accumulation"]
    metrics["R13_LOOSE"]["distributed_step_fraction"] = 0.75
    metrics["R13_TIGHT"]["distributed_step_fraction"] = 0.25
    metrics["R10_LOOSE_NEIGHBOR"]["distributed_step_fraction"] = 0.25


def test_classifier_public_contract_has_exact_frozen_domains() -> None:
    assert classifier.EXPECTED_RUN_IDS == [
        "MECHv0:R13_LOOSE:INSTRUMENTED",
        "MECHv0:R13_LOOSE:NONINSTRUMENTED_CONTROL",
        "MECHv0:R13_TIGHT:INSTRUMENTED",
        "MECHv0:R13_TIGHT:NONINSTRUMENTED_CONTROL",
        "MECHv0:R10_LOOSE:INSTRUMENTED",
        "MECHv0:R10_LOOSE:NONINSTRUMENTED_CONTROL",
    ]
    assert len(classifier.HYPOTHESES_A_TO_D) == 4
    assert len(classifier.EVIDENCE_OUTCOMES) == 7
    assert len(classifier.AGGREGATE_OUTCOMES) == 4
    assert classifier.ROLE_KEYS == [
        "R13_LOOSE",
        "R13_TIGHT",
        "R10_LOOSE_NEIGHBOR",
    ]


def test_instrumentation_registry_self_validation_and_source_bindings() -> None:
    assert instrumentation.EXACT_MATRIX_RUN_IDS == classifier.EXPECTED_RUN_IDS
    assert list(instrumentation.PACKED_RESIDUAL_BLOCK_IDS) == BLOCK_IDS
    assert len(instrumentation.BLOCK_REGISTRY) == 8
    assert len(instrumentation.OBSERVABLE_IDS) == 14
    assert instrumentation.DISCRETE_CLOSURE_CONTRACT["gamma_operation_count"] == 32
    assert (
        instrumentation.DISCRETE_CLOSURE_CONTRACT[
            "continuum_substitution_allowed"
        ]
        is False
    )
    assert all(instrumentation.self_validate().values())
    source_report = instrumentation.source_binding_report(ROOT)
    assert source_report["all_passed"] is True
    assert len(source_report["bindings"]) == 2


def test_complete_nondiscriminating_evidence_supports_only_H_E() -> None:
    result = classifier.classify(_admissible_fixture())
    assert result["evidence_result"] == "EVIDENCE_ADMISSIBLE"
    assert result["supported_mechanism_ids"] == []
    assert result["aggregate_mechanism_result"] == (
        "MECHANISM_UNRESOLVED_COMPLETE_EVIDENCE"
    )
    assert result["hypothesis_decisions"][classifier.H_E]["status"] == "SUPPORTED"
    assert classifier.validate_result(result) == []


@pytest.mark.parametrize(
    ("support", "expected"),
    [
        (_support_H_A, "H_A_CANCELLATION_CONDITIONING"),
        (_support_H_B, "H_B_LONGITUDINAL_EQUATION_BLOCK_DOMINANCE"),
        (_support_H_C, "H_C_DISCRETE_CLOSURE_MISMATCH"),
        (_support_H_D, "H_D_DISTRIBUTED_ACCUMULATED_SOLVER_ERROR"),
    ],
)
def test_each_positive_mechanism_is_independently_supported(
    support: Any, expected: str
) -> None:
    evidence = _admissible_fixture()
    support(evidence)
    result = classifier.classify(evidence)
    assert result["supported_mechanism_ids"] == [expected]
    assert result["aggregate_mechanism_result"] == "SINGLE_SUPPORTED_MECHANISM"
    assert result["hypothesis_decisions"][expected]["necessary_condition_decisions"]
    assert classifier.validate_result(result) == []


def test_H_D_is_positive_and_not_a_fallback_for_H_A_through_H_C() -> None:
    evidence = _admissible_fixture()
    _support_H_A(evidence)
    _support_H_D(evidence)
    result = classifier.classify(evidence)
    assert result["supported_mechanism_ids"] == [
        "H_A_CANCELLATION_CONDITIONING",
        "H_D_DISTRIBUTED_ACCUMULATED_SOLVER_ERROR",
    ]
    assert result["aggregate_mechanism_result"] == "MULTIPLE_SUPPORTED_MECHANISMS"
    assert classifier.validate_result(result) == []


def test_multiple_support_preserves_the_exact_ordered_identity_set() -> None:
    evidence = _admissible_fixture()
    _support_H_A(evidence)
    _support_H_C(evidence)
    result = classifier.classify(evidence)
    assert result["supported_mechanism_ids"] == [
        "H_A_CANCELLATION_CONDITIONING",
        "H_C_DISCRETE_CLOSURE_MISMATCH",
    ]
    defective = copy.deepcopy(result)
    defective.pop("supported_mechanism_ids")
    assert classifier.validate_result(defective) == [
        "MULTIPLE_MECHANISM_IDENTITY_SET_MISSING"
    ]


@pytest.mark.parametrize(
    ("mutation", "outcome", "diagnostic"),
    [
        ({"custody_passed": False}, "BLOCKED_CUSTODY", "CUSTODY_OR_IMPLEMENTATION_IDENTITY_FAILED"),
        ({"separate_output_custody_passed": False}, "BLOCKED_CUSTODY", "INSTRUMENTED_OUTPUT_ROOT_COLLIDES_CANONICAL"),
        ({"observed_run_ids": []}, "BLOCKED_RUN_IDENTITY", "EXPECTED_RUN_ID_CLOSURE_MISMATCH"),
        ({"required_payloads_complete": False}, "BLOCKED_REQUIRED_EVIDENCE_INCOMPLETE", "REQUIRED_OUTPUT_MISSING"),
        ({"required_observables_complete": False}, "BLOCKED_REQUIRED_EVIDENCE_INCOMPLETE", "REQUIRED_OBSERVABLE_MISSING"),
        ({"instrumentation_nonperturbation_passed": False}, "BLOCKED_INSTRUMENTATION_PERTURBATION", "INSTRUMENTED_TRAJECTORY_NOT_BYTE_IDENTICAL"),
        ({"observable_semantics_passed": False}, "BLOCKED_OBSERVABLE_SEMANTICS", "OBSERVABLE_UNIT_OR_NORMALIZATION_INVALID"),
        ({"discrete_operator_binding_passed": False}, "BLOCKED_OPERATOR_BINDING", "ACTUAL_DISCRETE_OPERATOR_BINDING_FAILED"),
    ],
)
def test_fail_closed_gates_precede_every_hypothesis(
    mutation: dict[str, Any], outcome: str, diagnostic: str
) -> None:
    evidence = _admissible_fixture()
    evidence.update(copy.deepcopy(mutation))
    result = classifier.classify(evidence)
    assert result["evidence_result"] == outcome
    assert result["evidence_diagnostic"] == diagnostic
    assert result["aggregate_mechanism_result"] == "BLOCKED"
    assert {item["status"] for item in result["hypothesis_decisions"].values()} == {
        "NOT_EVALUATED"
    }
    assert classifier.validate_result(result) == []


def test_missing_evidence_cannot_be_reclassified_as_H_E() -> None:
    evidence = _admissible_fixture()
    evidence["required_observables_complete"] = False
    result = classifier.classify(evidence)
    assert result["hypothesis_decisions"][classifier.H_E]["status"] == "NOT_EVALUATED"
    defective = copy.deepcopy(result)
    defective["hypothesis_decisions"][classifier.H_E]["status"] = "SUPPORTED"
    assert classifier.validate_result(defective) == [
        "INCOMPLETE_EVIDENCE_MISCLASSIFIED_AS_UNRESOLVED"
    ]


def test_generic_mechanism_classification_is_forbidden_after_perturbation_block() -> None:
    evidence = _admissible_fixture()
    evidence["instrumentation_nonperturbation_passed"] = False
    result = classifier.classify(evidence)
    defective = copy.deepcopy(result)
    supported_evidence = _admissible_fixture()
    _support_H_A(supported_evidence)
    supported_result = classifier.classify(supported_evidence)
    h_a = classifier.HYPOTHESES_A_TO_D[0]
    defective["hypothesis_decisions"][h_a] = copy.deepcopy(
        supported_result["hypothesis_decisions"][h_a]
    )
    defective["supported_mechanism_ids"] = [h_a]
    assert classifier.validate_result(defective) == [
        "CLASSIFICATION_PERFORMED_AFTER_EVIDENCE_BLOCK"
    ]


def test_registered_adversarial_mutations_are_executable_and_exact() -> None:
    controls = classifier.mutation_controls(_admissible_fixture())
    assert len(controls) == 6
    assert all(item["passed"] for item in controls)
    assert {item["mutation_id"] for item in controls} == {
        "MISSING_REQUIRED_OBSERVABLE",
        "INSTRUMENTED_TRAJECTORY_CHANGED",
        "CONTINUUM_OPERATOR_SUBSTITUTED",
        "INSTRUMENTED_OUTPUT_ROOT_COLLIDES_CANONICAL",
        "DUPLICATE_RUN_ID",
        "UNKNOWN_RUN_ID",
    }


def test_claim_ceiling_forbids_execution_result_promotions() -> None:
    result = classifier.classify(_admissible_fixture())
    ceiling = result["claim_ceiling"]
    for token in [
        "no robustness reclassification",
        "materiality",
        "E-REPRO",
        "pillar",
        "seam",
        "CCFT",
        "master-action promotion",
    ]:
        assert token in ceiling


def test_generated_freeze_artifacts_are_current_when_generator_lands() -> None:
    freeze = _freeze()
    expected = freeze.artifact_bytes()
    assert set(expected) == {
        freeze.PACKET_RELATIVE_PATH,
        freeze.RUN_MATRIX_RELATIVE_PATH,
        freeze.IDENTITY_RELATIVE_PATH,
        freeze.MANIFEST_RELATIVE_PATH,
        freeze.REPORT_RELATIVE_PATH,
    }
    assert all((ROOT / path).read_bytes() == raw for path, raw in expected.items())
    assert freeze.main(["--check"]) == 0


def test_environment_configuration_uses_committed_blob_bytes(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    freeze, packet, _, _, _, _ = _built_artifacts()

    def reject_working_tree_hash(_: Path) -> str:
        raise AssertionError("working-tree hashes are not freeze regeneration inputs")

    monkeypatch.setattr(freeze, "sha256_path", reject_working_tree_hash)
    regenerated = freeze._environment_identity()
    custody = regenerated["committed_configuration_custody"]
    assert custody["source_commit"] == freeze.CONFIGURATION_SOURCE_COMMIT
    assert custody["source_commit_parent"] == freeze.CONFIGURATION_SOURCE_PARENT
    assert custody["all_authoritative_hashes_use_committed_bytes"] is True
    assert custody["working_tree_line_endings_cannot_change_artifact_bytes"] is True
    assert regenerated == packet["environment_identity"]

    records = {record["path"]: record for record in custody["records"]}
    assert set(records) == set(freeze.COMMITTED_CONFIGURATION)
    for path, expected in freeze.COMMITTED_CONFIGURATION.items():
        record = records[path]
        assert record["git_blob_oid"] == expected["git_blob_oid"]
        assert record["sha256"] == expected["sha256_of_committed_bytes"]
        assert record["working_tree_hash_is_regeneration_input"] is False
        assert record["normalization_mode"] == (
            "committed Git blob bytes; no working-tree conversion"
        )


def test_exact_six_run_matrix_pairing_and_inherited_parameters() -> None:
    freeze, _, matrix, _, _, _ = _built_artifacts()
    records = matrix["records"]
    assert matrix["record_count"] == len(records) == 6
    assert matrix["physical_configuration_count"] == 3
    assert matrix["instrumented_record_count"] == 3
    assert matrix["noninstrumented_control_record_count"] == 3
    assert [record["run_id"] for record in records] == classifier.EXPECTED_RUN_IDS
    assert [record["execution_ordinal_zero_based"] for record in records] == list(
        range(6)
    )

    by_id = {record["run_id"]: record for record in records}
    assert len(by_id) == 6
    for record in records:
        paired = by_id[record["paired_run_id"]]
        assert paired["paired_run_id"] == record["run_id"]
        assert paired["instrumentation_enabled"] is not record["instrumentation_enabled"]
        for field in [
            "mechanism_configuration_role",
            "scientific_row_id",
            "parent_canonical_run_id",
            "parent_canonical_input_hash",
            "requested_axis_values",
            "row",
            "model_class",
            "grid_size",
            "time_step",
            "duration",
            "solver_tolerance",
            "iteration_cap",
            "implementation_id",
            "implementation_sha256",
        ]:
            assert paired[field] == record[field]
        assert record["grid_size"] == record["n"] == 16
        assert record["time_step"] == record["dt"] == 0.003125
        assert record["duration"] == 0.05
        assert record["accepted_step_count"] == 16
        assert record["checkpoint_count_including_initial"] == 17
        assert record["iteration_cap"] == record["max_iterations"] == 80

    records_by_role = {
        role: [
            record
            for record in records
            if record["mechanism_configuration_role"] == role
        ]
        for role in classifier.ROLE_KEYS
    }
    assert {role: len(items) for role, items in records_by_role.items()} == {
        "R13_LOOSE": 2,
        "R13_TIGHT": 2,
        "R10_LOOSE_NEIGHBOR": 2,
    }
    assert {
        role: items[0]["solver_tolerance"]
        for role, items in records_by_role.items()
    } == {
        "R13_LOOSE": 1.0e-8,
        "R13_TIGHT": 1.0e-12,
        "R10_LOOSE_NEIGHBOR": 1.0e-8,
    }
    assert {
        role: items[0]["scientific_row_id"]
        for role, items in records_by_role.items()
    } == {
        "R13_LOOSE": "R13_CORNER_STRONG_LOW",
        "R13_TIGHT": "R13_CORNER_STRONG_LOW",
        "R10_LOOSE_NEIGHBOR": "R10_MU_HIGH",
    }
    assert {
        role: items[0]["parent_canonical_run_id"]
        for role, items in records_by_role.items()
    } == freeze.PARENT_CANONICAL_RUN_IDS
    assert all(
        record["instrumented_observable_ids"] == freeze.OBSERVABLE_IDS
        if record["instrumentation_enabled"]
        else record["instrumented_observable_ids"] == []
        for record in records
    )
    assert "R10_MU_HIGH" in matrix["selection_rules_closed"]["matched_neighbor"]


def test_exact_observable_and_solver_block_registries_are_bound_to_source() -> None:
    freeze, packet, _, _, _, _ = _built_artifacts()
    observables = packet["mechanism_observable_registry"]
    blocks = packet["equation_block_registry"]
    assert packet["mechanism_observable_count"] == len(observables) == 14
    assert [item["observable_id"] for item in observables] == freeze.OBSERVABLE_IDS
    assert freeze.OBSERVABLE_IDS == instrumentation.OBSERVABLE_IDS
    assert packet["equation_block_count"] == len(blocks) == 8
    assert [item["block_id"] for item in blocks] == freeze.BLOCK_IDS
    assert freeze.BLOCK_IDS == list(instrumentation.PACKED_RESIDUAL_BLOCK_IDS)
    assert packet["implementation_closure"]["literal_observable_ids"] == (
        instrumentation.OBSERVABLE_IDS
    )
    assert [
        item["block_id"]
        for item in packet["implementation_closure"]["literal_block_registry"]
    ] == freeze.BLOCK_IDS
    assert all(
        item["missing_nonfinite_or_shape_mismatch_behavior"]
        == "BLOCKED_REQUIRED_EVIDENCE_INCOMPLETE"
        for item in observables
    )
    assert all(
        item["missing_data_behavior"] == "BLOCKED_REQUIRED_EVIDENCE_INCOMPLETE"
        for item in blocks
    )


def test_discrete_closure_and_nonperturbation_are_exact_and_fail_closed() -> None:
    _, packet, _, _, _, _ = _built_artifacts()
    closure = packet["discrete_Maxwell_continuity_closure_freeze"]
    assert closure["step_integrated_closure_formula"] == (
        "Q=(G1-G0)-(roll(Rp,1)-Rp)-a*dt*C"
    )
    assert closure["implementation_literal_contract"] == (
        instrumentation.DISCRETE_CLOSURE_CONTRACT
    )
    assert closure["gamma_operation_count"] == 32
    assert closure["posthoc_continuum_substitution_allowed"] is False
    assert closure["operator_implementation_sha256"] == packet[
        "implementation_closure"
    ]["sha256"]
    assert closure["binding_failure"] == "BLOCKED_OPERATOR_BINDING"

    nonperturbation = packet["instrumentation_nonperturbation_freeze"]
    assert nonperturbation["pair_count"] == 3
    assert "byte" in nonperturbation["required_rule"]
    assert nonperturbation["equivalence_ceiling"] == 0.0
    assert nonperturbation["bounded_equivalence_fallback_authorized"] is False
    assert nonperturbation["any_pair_failure"] == (
        "BLOCKED_INSTRUMENTATION_PERTURBATION"
    )
    assert (
        nonperturbation[
            "instrumentation_may_modify_state_solver_order_stopping_or_parameters"
        ]
        is False
    )


def test_classifier_freeze_preserves_precedence_hypotheses_and_controls() -> None:
    _, packet, _, _, _, _ = _built_artifacts()
    contract = packet["classifier_freeze"]
    assert contract["expected_run_ids"] == classifier.EXPECTED_RUN_IDS
    assert contract["hypotheses_A_to_D"] == classifier.HYPOTHESES_A_TO_D
    assert contract["hypothesis_E"] == classifier.H_E
    assert contract["support_constants_bound_directly_from_classifier_source"] == (
        classifier.SUPPORT_CONSTANTS
    )
    assert contract["evidence_outcomes"] == classifier.EVIDENCE_OUTCOMES
    assert contract["aggregate_outcomes"] == classifier.AGGREGATE_OUTCOMES
    assert contract["fail_closed_precedence"] == classifier.CLASSIFIER_PRECEDENCE
    assert len(contract["fail_closed_precedence"]) == 16
    assert contract["multiple_mechanisms_may_be_supported"] is True
    assert contract["unresolved_complete_evidence_is_admitted"] is True
    assert contract["blocked_semantics"] == {
        "aggregate_mechanism_result": "BLOCKED",
        "supported_mechanism_ids": [],
        "all_hypothesis_statuses": "NOT_EVALUATED",
        "H_E_supported": False,
    }
    assert classifier.SUPPORT_CONSTANTS["H_D"][
        "minimum_contributing_block_count_per_step"
    ] > 1
    controls = packet["classifier_control_suite"]
    assert controls["positive_control_count"] == 6
    assert controls["negative_control_count"] == 6
    assert controls["all_controls_passed"] is True
    assert all(item["passed"] for item in controls["positive_controls"])
    assert all(item["passed"] for item in controls["negative_controls"])


def test_custody_output_identity_and_execution_authority_are_closed() -> None:
    freeze, packet, matrix, identity, manifest, report = _built_artifacts()
    custody = packet["authority_basis"]
    assert custody["passed"] is True
    assert custody["all_source_artifact_hashes_exact"] is True
    assert custody["canonical_root_file_count"] == 205
    assert custody["canonical_run_output_count_checked"] == 203
    assert custody["canonical_root_digest_exact"] is True
    assert custody["canonical_directory_tree_sha256_exact"] is True
    assert custody["canonical_output_mutation_count"] == 0
    assert custody["new_simulation_run_count"] == 0
    assert packet["implementation_closure"][
        "implementation_imported_only_for_pure_schema_and_matrix_validation"
    ] is True
    assert packet["implementation_closure"][
        "evolution_or_execution_runner_invocation_count"
    ] == 0

    assert freeze.EXPERIMENT_OUTPUT_ROOT != freeze.CANONICAL_OUTPUT_ROOT
    assert identity["output_root"] == freeze.EXPERIMENT_OUTPUT_ROOT
    assert not (ROOT / freeze.EXPERIMENT_OUTPUT_ROOT).exists()
    assert identity["record_count"] == 6
    assert identity["role_payload_file_count"] == 12
    assert len(identity["auxiliary_execution_files"]) == 2
    assert identity["complete_expected_file_count_after_success"] == 14
    for record in matrix["records"]:
        assert record["json_relative_output_path"].startswith(
            freeze.EXPERIMENT_OUTPUT_ROOT + "/"
        )
        assert record["npz_relative_output_path"].startswith(
            freeze.EXPERIMENT_OUTPUT_ROOT + "/"
        )
    assert manifest["future_experiment_output_root_absent"] is True
    assert manifest["execution_authorized"] is False
    assert report["preparation_validation_status"]["simulation_invocation_count"] == 0
    assert report["preparation_validation_status"]["new_output_root_created"] is False

    boundary = packet["authority_boundary"]
    assert packet["verdict"] == "PREPARED_PENDING_INDEPENDENT_REVIEW"
    assert packet["selected_next_target"] == freeze.REVIEW_TARGET
    assert packet["authority_boundary"]["numerical_freeze_independently_accepted"] is False
    assert boundary["new_experiment_execution_authorized"] is False
    assert boundary["new_experiment_execution_performed"] is False
    assert boundary["canonical_execution_count"] == 1
    assert boundary["canonical_robustness"] == "NUMERICALLY_BLOCKED"
    assert boundary["root_mechanism"] == "UNRESOLVED"
    assert boundary["materiality"] == "NOT_EVALUATED_NUMERICAL_BLOCK"
    assert boundary["robustness_reclassification_authorized"] is False
    assert boundary["threshold_change_authorized"] is False
    assert boundary["new_E_REPRO_claim"] is False
    assert packet["output_custody_and_execution_freeze"]["execution_authorized_now"] is False
    for forbidden in [
        "No mechanism result",
        "robustness reclassification",
        "materiality",
        "E-REPRO",
        "pillar",
        "seam",
        "CCFT",
        "master-action promotion",
    ]:
        assert forbidden in packet["claim_ceiling"]
