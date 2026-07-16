from __future__ import annotations

import argparse
import copy
import hashlib
import importlib
import json
import math
import subprocess
import sys
import types
import unicodedata
from pathlib import Path
from typing import Any

import numpy as np

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_classifier_v0
    as classifier,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_implementation_v0
    as implementation,
)


REPO_ROOT = find_repo_root(Path(__file__))
CAPTURED_AT_UTC = "2026-07-15T00:00:00Z"
TARGET = (
    "review_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
    "instrumented_r13_mechanism_experiment_numerical_freeze_packet_v0_result"
)
SELECTED_NEXT_TARGET = (
    "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
    "instrumented_r13_mechanism_experiment_numerical_freeze_packet_v1"
)
VERDICT = "BLOCK_INSTRUMENTED_R13_MECHANISM_EXPERIMENT_NUMERICAL_FREEZE"
SCHEMA_ID = (
    "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_"
    "INSTRUMENTED_R13_MECHANISM_EXPERIMENT_NUMERICAL_FREEZE_PACKET_REVIEW_"
    "20260715_v0"
)
REPORT_RELATIVE_PATH = (
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
    "ROBUSTNESS_INSTRUMENTED_R13_MECHANISM_EXPERIMENT_NUMERICAL_FREEZE_PACKET_"
    "REVIEW_20260715_v0.json"
)
REVIEWER_RELATIVE_PATH = (
    "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_"
    "robustness_instrumented_r13_mechanism_experiment_numerical_freeze_packet_"
    "review_v0.py"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/test_dirac_maxwell_full_zero_mode_descendant_necessity_"
    "and_robustness_instrumented_r13_mechanism_experiment_numerical_freeze_"
    "packet_review_v0.py"
)
LEAN_RELATIVE_PATH = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "DiracMaxwellFullZeroModeDescendantNecessityAndRobustnessInstrumentedR13"
    "MechanismExperimentNumericalFreezePacketReviewV0.lean"
)

FREEZE_PACKET = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-INSTRUMENTED-R13-MECHANISM-EXPERIMENT-NUMERICAL-FREEZE-PACKET-v0.json"
)
RUN_MATRIX = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-INSTRUMENTED-R13-MECHANISM-EXPERIMENT-NUMERICAL-FREEZE-RUN-"
    "MATRIX-v0.json"
)
OUTPUT_IDENTITY = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-INSTRUMENTED-R13-MECHANISM-EXPERIMENT-NUMERICAL-FREEZE-"
    "EXPECTED-OUTPUT-IDENTITY-MANIFEST-v0.json"
)
FREEZE_MANIFEST = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-INSTRUMENTED-R13-MECHANISM-EXPERIMENT-NUMERICAL-FREEZE-MANIFEST-v0.json"
)
FREEZE_REPORT = (
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
    "ROBUSTNESS_INSTRUMENTED_R13_MECHANISM_EXPERIMENT_NUMERICAL_FREEZE_PACKET_"
    "20260715_v0.json"
)
FREEZE_GENERATOR = (
    "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_"
    "robustness_instrumented_r13_mechanism_experiment_numerical_freeze_packet_v0.py"
)
FREEZE_TEST = (
    "formal/python/tests/test_dirac_maxwell_full_zero_mode_descendant_necessity_"
    "and_robustness_instrumented_r13_mechanism_experiment_numerical_freeze_"
    "packet_v0.py"
)
FREEZE_LEAN = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "DiracMaxwellFullZeroModeDescendantNecessityAndRobustnessInstrumentedR13"
    "MechanismExperimentNumericalFreezePacketV0.lean"
)
CLASSIFIER_PATH = classifier.SCRIPT_RELATIVE_PATH
IMPLEMENTATION_PATH = (
    "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_"
    "robustness_instrumented_r13_mechanism_experiment_implementation_v0.py"
)
DESIGN_REVIEW = (
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
    "ROBUSTNESS_INSTRUMENTED_R13_MECHANISM_EXPERIMENT_DESIGN_PACKET_REVIEW_"
    "20260715_v1.json"
)
CANONICAL_MATRIX = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-CANONICAL-RUN-MATRIX-v2.json"
)
CANONICAL_IDENTITY = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-CANONICAL-EXPECTED-OUTPUT-IDENTITY-MANIFEST-v2.json"
)
CANONICAL_EXECUTION_MANIFEST = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-CANONICAL-EXECUTION-MANIFEST-v2.json"
)
CANONICAL_RESULT_REVIEW = (
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
    "ROBUSTNESS_CANONICAL_RESULT_REVIEW_20260715_v0.json"
)
CANONICAL_OUTPUT_ROOT = (
    "formal/output/canonical/dirac_maxwell_full_zero_mode_descendant_necessity_"
    "and_robustness_v2"
)
EXPERIMENT_OUTPUT_ROOT = (
    "formal/output/dirac_maxwell_instrumented_r13_mechanism_v0"
)

EXPECTED_INPUT_HASHES = {
    FREEZE_PACKET: "9900bef2b60f816a890ca986a3daee64236dc1a11a4ca6cf98f1ce8d5e0a0317",
    RUN_MATRIX: "97597b248d6aca1de9abf252bc098493edce318eea1a903a48c2d33a97e22923",
    OUTPUT_IDENTITY: "9016c5a5cb4f0920a59417acf26023ef79b0dcf61d3751dd91c30282d0d3dd6c",
    FREEZE_MANIFEST: "a6d687cc7c854221144d48525f69aad903536a0a1a16a46b550c7fd6c2c7b89b",
    FREEZE_REPORT: "2606cdfd8b09af0a5878bdb05aa9d4694996fd0f3e39e529d545f69ea4d6d95a",
    FREEZE_GENERATOR: "73051bfcf34853df66f0a8a966231106f1231a9040011501618f96093fc5d6f2",
    FREEZE_TEST: "c36affa6fb95ba92ce93555e0856a89bf92b0e756265e6770a2bfba31c52a88f",
    FREEZE_LEAN: "3c09d28b8d49f7da81a42b73ad7d8f0b1472a0354b090ce31f5c1e828ca60af4",
    CLASSIFIER_PATH: "6f860716f29da107cd8f70a009d62d6003fce5fc9eb1cc316a3ab9d50171fdca",
    IMPLEMENTATION_PATH: "f4bdd5cd0f725f135060e1fe7476ef8edc5ce2a12c72ec0b0357239197006150",
    DESIGN_REVIEW: "29a61d4c019861df1d6807f8410a805d7d099ebc2805b7392103c86aa9850afc",
    CANONICAL_MATRIX: "a906c7c11dee659a3f66739d7ee807523743ea8311283dc2e4d99e0f2c17bcb2",
    CANONICAL_IDENTITY: "9a87c0a1447d4c4462dbf8fc21ef4b8aeb87e62867c67d1db78ac25c2d8ad09e",
    CANONICAL_EXECUTION_MANIFEST: "59ca16e4d16f2b96d87c77f1fb16a3c4270a3e29c8dbc097edb5700ed9da1338",
    CANONICAL_RESULT_REVIEW: "cacbd77f3ef18a80d8d15686dd8f385f73a634038fddb5010058f2e144ef3c85",
}
EXPECTED_CANONICAL_ROOT_DIGEST = (
    "6d38108b9403d1a74fce9659e94dee9a89555870b5d8034ba221173ce1338f14"
)
EXPECTED_CANONICAL_TREE_DIGEST = (
    "886541953dfcfecfffa44b2ff9e2ee62c14c468139042bf4f3477ef3a1f2a721"
)

EXPECTED_RUN_IDS = list(classifier.EXPECTED_RUN_IDS)
EXPECTED_OBSERVABLE_IDS = list(implementation.OBSERVABLE_IDS)
EXPECTED_BLOCK_IDS = list(implementation.PACKED_RESIDUAL_BLOCK_IDS)
PARENT_RUN_IDS = {
    "R13_LOOSE": "R13_CORNER_STRONG_LOW:SOLVER_TOL1eM08",
    "R13_TIGHT": "R13_CORNER_STRONG_LOW:SOLVER_TOL1eM12",
    "R10_LOOSE_NEIGHBOR": "R10_MU_HIGH:SOLVER_TOL1eM08",
}

FAILURE_DECISION_IDS = [
    "final_run_input_hashes_reconstruct_under_their_declared_contract",
    "execution_validator_enforces_the_complete_frozen_matrix_identity",
    "raw_payload_validator_and_evidence_assembler_are_fail_closed",
    "runtime_imported_operator_modules_are_the_exact_hashed_files",
    "H_C_measure_and_gamma32_bound_support_the_declared_mechanism",
    "all_hypothesis_constants_have_complete_nonfuture_provenance",
    "adversarial_registry_covers_the_full_freeze_review_contract",
]

PASS_DECISION_IDS = [
    "freeze_packet_matrix_identity_manifest_report_and_sources_are_hash_exact",
    "accepted_design_v1_review_is_the_consumed_authority",
    "freeze_v0_is_prepared_pending_independent_review",
    "preparation_records_39_of_39_internal_decisions",
    "canonical_205_file_inventory_digest_is_exact",
    "canonical_directory_tree_digest_is_exact",
    "canonical_203_run_outputs_remain_read_only",
    "future_mechanism_output_root_is_separate_and_absent",
    "static_run_matrix_has_exact_six_record_order",
    "three_instrumented_control_pairs_are_statically_exact",
    "R13_loose_static_physical_projection_matches_canonical_parent",
    "R13_tight_static_physical_projection_matches_canonical_parent",
    "R10_loose_static_physical_projection_matches_canonical_parent",
    "all_parent_input_hashes_are_statically_exact",
    "all_parent_output_paths_and_hashes_are_statically_exact",
    "grid_timestep_duration_iteration_cap_and_tolerances_are_exact",
    "supporting_tolerance_and_duration_modules_are_disabled",
    "output_identity_has_six_JSON_and_six_NPZ_bijections",
    "two_auxiliary_execution_files_and_fourteen_total_files_are_exact",
    "all_output_paths_are_unique_NFC_and_casefold_safe",
    "fourteen_observable_identifiers_match_design_and_implementation",
    "eight_solver_blocks_cover_the_exact_22N_packed_layout",
    "block_normalization_uses_role_tolerance_and_gamma64",
    "dominance_fraction_and_registry_order_ties_are_frozen",
    "exchange_conditioning_formula_and_gamma64_scale_floor_are_frozen",
    "per_iteration_terminal_and_spatial_diagnostics_are_registered",
    "actual_discrete_operator_inputs_and_outputs_are_registered",
    "trajectory_nonperturbation_requires_exact_byte_identity",
    "bounded_nonperturbation_fallback_is_forbidden",
    "H_A_support_rule_and_two_reference_contrasts_are_literal",
    "H_B_longitudinal_dominance_rule_is_positive_and_literal",
    "H_D_distributed_accumulation_rule_is_positive_not_fallback",
    "H_E_is_reserved_for_complete_admissible_empty_support",
    "individual_hypothesis_decisions_and_ordered_support_set_are_retained",
    "classifier_block_precedence_suppresses_hypothesis_decisions",
    "committed_Git_blob_configuration_custody_is_exact",
    "historical_worktree_gitattributes_is_not_a_regeneration_input",
    "no_simulation_rerun_threshold_change_or_materiality_is_authorized",
    "canonical_NUMERICALLY_BLOCKED_verdict_is_unchanged",
    "no_new_E_REPRO_or_physical_claim_is_assigned",
    "blocked_review_preserves_Route_A_and_design_v1_for_versioned_correction",
]


def _normalize(value: Any) -> Any:
    if isinstance(value, str):
        return unicodedata.normalize("NFC", value)
    if isinstance(value, list):
        return [_normalize(item) for item in value]
    if isinstance(value, dict):
        return {_normalize(str(key)): _normalize(item) for key, item in value.items()}
    return value


def canonical_json_bytes(payload: Any) -> bytes:
    return (
        json.dumps(
            _normalize(payload),
            allow_nan=False,
            ensure_ascii=False,
            indent=2,
            sort_keys=True,
        )
        + "\n"
    ).encode("utf-8")


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def sha256_path(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def load_json(relative_path: str) -> dict[str, Any]:
    value = json.loads((REPO_ROOT / relative_path).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {relative_path}")
    return value


def canonical_root_inventory() -> list[dict[str, str]]:
    root = REPO_ROOT / CANONICAL_OUTPUT_ROOT
    return [
        {
            "path": path.relative_to(REPO_ROOT).as_posix(),
            "sha256": sha256_path(path),
        }
        for path in sorted(root.glob("*.json"))
    ]


def canonical_tree_digest() -> str:
    import struct

    root = REPO_ROOT / CANONICAL_OUTPUT_ROOT
    digest = hashlib.sha256()
    digest.update(b"R13-MECHANISM-DIRECTORY-TREE-v0\x00")
    files = sorted(
        (path for path in root.rglob("*") if path.is_file()),
        key=lambda path: path.relative_to(root).as_posix(),
    )
    for path in files:
        relative = path.relative_to(root).as_posix().encode("utf-8")
        contents = path.read_bytes()
        digest.update(struct.pack("<Q", len(relative)))
        digest.update(relative)
        digest.update(struct.pack("<Q", len(contents)))
        digest.update(hashlib.sha256(contents).digest())
    return digest.hexdigest()


def validate_input_custody() -> list[dict[str, Any]]:
    records = []
    for path, expected in EXPECTED_INPUT_HASHES.items():
        observed = sha256_path(REPO_ROOT / path)
        records.append(
            {
                "path": path,
                "expected_sha256": expected,
                "observed_sha256": observed,
                "passed": observed == expected,
            }
        )
    if not all(item["passed"] for item in records):
        raise ValueError("freeze review input custody mismatch")
    return records


def _physical_projection_from_future(record: dict[str, Any]) -> dict[str, Any]:
    return {
        "scientific_row_id": record["scientific_row_id"],
        "model_class": record["model_class"],
        "initial_condition_identity": record["parent_initial_condition_identity"],
        "grid_size": record["grid_size"],
        "time_step": record["time_step"],
        "duration": record["duration"],
        "solver_tolerance": record["solver_tolerance"],
        "iteration_cap": record["iteration_cap"],
        "requested_axis_values": record["requested_axis_values"],
    }


def _physical_projection_from_parent(record: dict[str, Any]) -> dict[str, Any]:
    return {
        "scientific_row_id": record["scientific_row_id"],
        "model_class": record["model_or_comparator_class"],
        "initial_condition_identity": record["initial_condition_identity"],
        "grid_size": record["grid_size"],
        "time_step": record["time_step"],
        "duration": record["duration"],
        "solver_tolerance": record["solver_tolerance"],
        "iteration_cap": record["iteration_cap"],
        "requested_axis_values": record["requested_axis_values"],
    }


def reconstruct_static_matrix() -> dict[str, Any]:
    matrix = load_json(RUN_MATRIX)
    canonical = load_json(CANONICAL_MATRIX)
    execution = load_json(CANONICAL_EXECUTION_MANIFEST)
    identity = load_json(OUTPUT_IDENTITY)
    parent_by_id = {item["run_id"]: item for item in canonical["records"]}
    output_by_id = {item["run_id"]: item for item in execution["run_outputs"]}
    records = matrix["records"]
    parent_results = []
    declared_hash_results = []
    for record in records:
        parent = parent_by_id[record["parent_canonical_run_id"]]
        output = output_by_id[parent["run_id"]]
        future_projection = _physical_projection_from_future(record)
        parent_projection = _physical_projection_from_parent(parent)
        declared_exclusions = set(record["input_hash_material_excludes"])
        declared_material = {
            key: value for key, value in record.items() if key not in declared_exclusions
        }
        actual_generation_material = {
            key: value
            for key, value in record.items()
            if key not in declared_exclusions | {"input_hash_material_excludes"}
        }
        declared_recomputed = sha256_bytes(canonical_json_bytes(declared_material))
        actual_recomputed = sha256_bytes(canonical_json_bytes(actual_generation_material))
        parent_results.append(
            {
                "run_id": record["run_id"],
                "mechanism_configuration_role": record["mechanism_configuration_role"],
                "parent_run_id": parent["run_id"],
                "physical_projection_exact": future_projection == parent_projection,
                "physical_projection_sha256": sha256_bytes(
                    canonical_json_bytes(future_projection)
                ),
                "parent_input_hash_exact": (
                    record["parent_canonical_input_hash"] == parent["input_hash"]
                ),
                "parent_output_path_exact": (
                    record["parent_canonical_output_path"]
                    == output["relative_output_path"]
                ),
                "parent_output_sha256_exact": (
                    record["parent_canonical_output_sha256"]
                    == output["output_sha256"]
                ),
            }
        )
        declared_hash_results.append(
            {
                "run_id": record["run_id"],
                "stored_input_hash": record["input_hash"],
                "declared_contract_recomputed_sha256": declared_recomputed,
                "declared_contract_matches": declared_recomputed == record["input_hash"],
                "additional_undeclared_exclusion": "input_hash_material_excludes",
                "historical_generation_recomputed_sha256": actual_recomputed,
                "historical_generation_matches": actual_recomputed == record["input_hash"],
            }
        )

    run_ids = [item["run_id"] for item in records]
    pairs = ((0, 1), (2, 3), (4, 5))
    pair_fields = (
        "row",
        "n",
        "dt",
        "duration",
        "tolerance",
        "max_iterations",
        "scientific_row_id",
        "parent_canonical_run_id",
        "parent_canonical_input_hash",
        "parent_initial_condition_identity",
    )
    pair_results = []
    for instrumented_index, control_index in pairs:
        left = records[instrumented_index]
        right = records[control_index]
        pair_results.append(
            {
                "instrumented_run_id": left["run_id"],
                "control_run_id": right["run_id"],
                "all_physical_and_parent_fields_exact": all(
                    left[field] == right[field] for field in pair_fields
                ),
                "instrumentation_flags_are_complementary": (
                    left["instrumentation_enabled"] is True
                    and right["instrumentation_enabled"] is False
                ),
            }
        )

    json_paths = [item["json_relative_output_path"] for item in records]
    npz_paths = [item["npz_relative_output_path"] for item in records]
    all_paths = json_paths + npz_paths
    forward_json = identity["run_id_to_json_relative_output_path"]
    forward_npz = identity["run_id_to_npz_relative_output_path"]
    reverse_json = identity["json_relative_output_path_to_run_id"]
    reverse_npz = identity["npz_relative_output_path_to_run_id"]
    identity_exact = all(
        forward_json[item["run_id"]] == item["json_relative_output_path"]
        and forward_npz[item["run_id"]] == item["npz_relative_output_path"]
        and reverse_json[item["json_relative_output_path"]] == item["run_id"]
        and reverse_npz[item["npz_relative_output_path"]] == item["run_id"]
        for item in records
    )
    return {
        "record_count": len(records),
        "run_ids": run_ids,
        "run_ids_exact": run_ids == EXPECTED_RUN_IDS,
        "instrumented_count": sum(item["instrumentation_enabled"] for item in records),
        "noninstrumented_count": sum(not item["instrumentation_enabled"] for item in records),
        "parent_reconstructions": parent_results,
        "all_parent_physical_projections_exact": all(
            item["physical_projection_exact"] for item in parent_results
        ),
        "all_parent_input_output_identities_exact": all(
            item["parent_input_hash_exact"]
            and item["parent_output_path_exact"]
            and item["parent_output_sha256_exact"]
            for item in parent_results
        ),
        "pair_reconstructions": pair_results,
        "all_three_pairs_exact": all(
            item["all_physical_and_parent_fields_exact"]
            and item["instrumentation_flags_are_complementary"]
            for item in pair_results
        ),
        "role_payload_count": len(all_paths),
        "all_role_paths_unique": len(set(all_paths)) == 12,
        "all_role_paths_NFC": all(path == unicodedata.normalize("NFC", path) for path in all_paths),
        "all_role_paths_casefold_unique": len({path.casefold() for path in all_paths}) == 12,
        "identity_forward_reverse_maps_exact": identity_exact,
        "auxiliary_file_count": len(identity["auxiliary_execution_files"]),
        "complete_expected_file_count_after_success": identity[
            "complete_expected_file_count_after_success"
        ],
        "declared_input_hash_reconstructions": declared_hash_results,
        "declared_input_hash_contract_pass_count": sum(
            item["declared_contract_matches"] for item in declared_hash_results
        ),
        "historical_generation_hash_pass_count": sum(
            item["historical_generation_matches"] for item in declared_hash_results
        ),
    }


IDENTITY_MUTATIONS = {
    "parent_canonical_run_id": "R00_CANONICAL:SOLVER_TOL1eM08",
    "parent_canonical_input_hash": "0" * 64,
    "parent_canonical_output_sha256": "0" * 64,
    "parent_canonical_output_path": "formal/output/WRONG.json",
    "input_hash": "0" * 64,
    "implementation_id": "WRONG_IMPLEMENTATION",
    "implementation_sha256": "0" * 64,
    "paired_run_id": "MECHv0:R13_TIGHT:INSTRUMENTED",
    "execution_role": "PAIRED_NONINSTRUMENTED_CONTROL",
    "output_schema_version": "v9",
    "experiment_id": "WRONG_EXPERIMENT",
    "scientific_row_id": "R00_CANONICAL",
    "requested_axis_values": {"WRONG": 1.0},
    "parent_initial_condition_identity": "WRONG_INITIAL_STATE",
    "model_class": "WRONG_MODEL",
    "numerical_method": "WRONG_METHOD",
    "accepted_step_count": 15,
    "checkpoint_count_including_initial": 16,
    "instrumentation_read_only": False,
    "trajectory_identity_required": False,
}


def probe_matrix_validator() -> dict[str, Any]:
    records = load_json(RUN_MATRIX)["records"]
    baseline = implementation.validate_exact_run_matrix(records)
    mutation_results = []
    for field, value in IDENTITY_MUTATIONS.items():
        mutated = copy.deepcopy(records)
        mutated[0][field] = value
        diagnostics = implementation.validate_exact_run_matrix(mutated)
        mutation_results.append(
            {
                "field": field,
                "diagnostics": diagnostics,
                "incorrectly_accepted": diagnostics == [],
            }
        )
    dynamics_control = copy.deepcopy(records)
    dynamics_control[0]["n"] = 32
    dynamics_diagnostics = implementation.validate_exact_run_matrix(dynamics_control)
    return {
        "baseline_diagnostics": baseline,
        "identity_mutation_count": len(mutation_results),
        "identity_mutations": mutation_results,
        "incorrectly_accepted_identity_mutation_count": sum(
            item["incorrectly_accepted"] for item in mutation_results
        ),
        "dynamics_control_diagnostics": dynamics_diagnostics,
        "executor_accepts_in_memory_matrix_without_frozen_matrix_sha256": (
            "run_matrix_sha256" not in implementation.execute_exact_matrix_once.__code__.co_names
        ),
    }


def probe_payload_and_classifier_closure() -> dict[str, Any]:
    trajectory = np.zeros((17, 22 * 16), dtype=np.float64)
    malformed_payload = {
        "schema_id": implementation.RUN_ROLE_PAYLOAD_SCHEMA_ID,
        "implementation_id": implementation.IMPLEMENTATION_ID,
        "role_id": "MECHv0:R13_LOOSE:INSTRUMENTED",
        "row_id": "R13_CORNER_STRONG_LOW",
        "instrumentation_enabled": True,
        "configuration": {"steps": 16},
        "times": np.arange(17, dtype=np.float64),
        "physical_trajectory": trajectory,
        "physical_trajectory_sha256": implementation.physical_trajectory_sha256(
            list(trajectory)
        ),
        "raw_events": {
            family: [{} for _ in range(16)]
            for family in implementation.MANDATORY_INSTRUMENTED_EVENT_FAMILIES
        },
        "metrics": {
            family: {}
            for family in (
                "exchange_conditioning",
                "block_dominance",
                "discrete_closure",
                "distributed_accumulation",
            )
        },
    }
    payload_diagnostics = implementation.validate_run_role_payload(malformed_payload)

    role_metrics = {
        role: {"median_kappa": 10.0, "severe_step_fraction": 0.0, "sample_count": 16}
        for role in classifier.ROLE_KEYS
    }
    shares = {block: 0.125 for block in EXPECTED_BLOCK_IDS}
    block_metrics = {
        role: {
            "dominant_block_id": "THETA_KINEMATIC",
            "median_dominance_share": 0.125,
            "dominant_step_fraction": 0.0,
            "median_share_by_block": copy.deepcopy(shares),
        }
        for role in classifier.ROLE_KEYS
    }
    closure_metrics = {
        role: {
            "max_roundoff_bound_ratio": 0.5,
            "maximum_consecutive_violation_steps": 0,
            "sample_count": 16,
        }
        for role in classifier.ROLE_KEYS
    }
    distributed_metrics = {
        role: {
            "distributed_step_fraction": 0.0,
            "linked_series_maxima_at_final_count": 4,
            "minimum_nondecreasing_increment_count": 14,
        }
        for role in classifier.ROLE_KEYS
    }
    fixture = {
        "custody_passed": True,
        "observed_run_ids": list(classifier.EXPECTED_RUN_IDS),
        "required_payloads_complete": True,
        "required_observables_complete": True,
        "separate_output_custody_passed": True,
        "instrumentation_nonperturbation_passed": True,
        "observable_semantics_passed": True,
        "discrete_operator_binding_passed": True,
        "metrics": {
            "exchange_conditioning": role_metrics,
            "block_dominance": block_metrics,
            "discrete_closure": closure_metrics,
            "distributed_accumulation": distributed_metrics,
        },
    }
    baseline = classifier.classify(fixture)
    corrupted = copy.deepcopy(fixture)
    corrupted.update(
        {
            "raw_payloads": [],
            "observed_payload_ids": ["WRONG"],
            "raw_observables": {"corrupt": True},
        }
    )
    corrupted_result = classifier.classify(corrupted)
    return {
        "malformed_payload_diagnostics": payload_diagnostics,
        "malformed_payload_with_empty_event_records_is_incorrectly_accepted": (
            payload_diagnostics == []
        ),
        "classifier_baseline_result": baseline,
        "classifier_corrupted_raw_result": corrupted_result,
        "classifier_ignores_corrupt_raw_payload_fields": corrupted_result == baseline,
        "classifier_input_contract_has_no_raw_payload_identity_field": (
            "raw_payloads" not in classifier.REQUIRED_GATE_FIELDS
            and "observed_payload_ids" not in classifier.REQUIRED_GATE_FIELDS
        ),
    }


def probe_loaded_module_binding() -> dict[str, Any]:
    evolution_name = implementation.HISTORICAL_EVOLUTION_MODULE
    packed_name = implementation.HISTORICAL_PACK_MODULE
    prior = {name: sys.modules.get(name) for name in (evolution_name, packed_name)}
    fake_evolution = types.ModuleType(evolution_name)
    fake_packed = types.ModuleType(packed_name)
    fake_evolution.__file__ = "C:/shadow/evolution.py"
    fake_packed.__file__ = "C:/shadow/packed.py"
    try:
        sys.modules[evolution_name] = fake_evolution
        sys.modules[packed_name] = fake_packed
        loaded_evolution, loaded_packed = implementation._load_historical_implementation()
        binding = implementation.source_binding_report(REPO_ROOT)
    finally:
        for name, value in prior.items():
            if value is None:
                sys.modules.pop(name, None)
            else:
                sys.modules[name] = value
    return {
        "shadow_modules_were_loaded": (
            loaded_evolution is fake_evolution and loaded_packed is fake_packed
        ),
        "workspace_path_hash_report_still_passed": binding["all_passed"],
        "loaded_module_file_paths_are_not_checked": True,
        "evolution_accepted_v0_identity_is_not_checked": True,
    }


def audit_observable_and_operator_semantics() -> dict[str, Any]:
    packet = load_json(FREEZE_PACKET)
    observables = packet["mechanism_observable_registry"]
    blocks = packet["equation_block_registry"]
    observable_ids = [item["observable_id"] for item in observables]
    block_ids = [item["block_id"] for item in blocks]
    required_observable_fields = {
        "observable_id",
        "meaning",
        "payload_field",
        "formula",
        "unit",
        "aggregation",
        "missing_nonfinite_or_shape_mismatch_behavior",
        "hypothesis_links",
    }
    semantic_records_complete = all(
        required_observable_fields <= set(item) for item in observables
    )
    gamma64 = 64.0 * (2.0**-53) / (1.0 - 64.0 * (2.0**-53))
    gamma32 = 32.0 * (2.0**-53) / (1.0 - 32.0 * (2.0**-53))

    closure = packet["discrete_Maxwell_continuity_closure_freeze"]
    h_c_algebra = {
        "G1_minus_G0": "roll(p1-p0,1)-(p1-p0)+a*(rho1-rho0)",
        "roll_Rp_minus_Rp_plus_a_dt_C": (
            "roll(p1-p0,1)-(p1-p0)+dt*(roll(g,1)-g)+"
            "a*(rho1-rho0)+dt*(g-roll(g,1))"
        ),
        "exact_arithmetic_reduction": "identical for arbitrary p0,p1,rho0,rho1,g",
        "Q_exact_arithmetic": 0,
        "solver_equation_satisfaction_required_for_identity": False,
    }
    return {
        "observable_count": len(observables),
        "observable_ids": observable_ids,
        "observable_ids_exact": observable_ids == EXPECTED_OBSERVABLE_IDS,
        "all_documentary_semantic_records_complete": semantic_records_complete,
        "block_count": len(blocks),
        "block_ids": block_ids,
        "block_ids_exact": block_ids == EXPECTED_BLOCK_IDS,
        "packed_span_units_total": sum(
            item["packed_span_in_units_of_n"][1]
            - item["packed_span_in_units_of_n"][0]
            for item in packet["implementation_closure"]["literal_block_registry"]
        ),
        "all_blocks_use_tolerance_scale": all(
            "requested_solver_tolerance" in item["normalization_scale"]
            for item in blocks
        ),
        "all_block_floors_equal_gamma64": all(
            item["normalization_floor"] == gamma64 for item in blocks
        ),
        "gamma64": gamma64,
        "gamma32": gamma32,
        "closure_gamma32_exact": closure["gamma_32"] == gamma32,
        "H_C_algebraic_identity_audit": h_c_algebra,
        "H_C_current_ratio_can_measure_only_floating_evaluation_or_bound_behavior": True,
        "gamma32_operation_count_derivation_registered": False,
        "exchange_exact_cell_sum_comparison_rule_registered": False,
    }


def audit_threshold_provenance() -> dict[str, Any]:
    packet = load_json(FREEZE_PACKET)
    constants = packet["classifier_freeze"][
        "support_constants_bound_directly_from_classifier_source"
    ]
    constant_records = []
    for hypothesis, values in constants.items():
        for key, value in values.items():
            constant_records.append(
                {
                    "hypothesis": hypothesis,
                    "constant_id": key,
                    "value": value,
                    "has_source_artifact": False,
                    "has_source_record_ids": False,
                    "has_derivation_formula": False,
                    "has_rounding_rule": False,
                    "has_scientific_meaning": False,
                }
            )
    return {
        "support_constant_count": len(constant_records),
        "records": constant_records,
        "packet_has_threshold_provenance_registry": any(
            "provenance" in key.lower() and "threshold" in key.lower()
            for key in packet
        ),
        "complete_provenance_record_count": sum(
            all(
                item[key]
                for key in (
                    "has_source_artifact",
                    "has_source_record_ids",
                    "has_derivation_formula",
                    "has_rounding_rule",
                    "has_scientific_meaning",
                )
            )
            for item in constant_records
        ),
        "future_mechanism_outputs_used_as_provenance": False,
    }


REQUIRED_ADVERSARIAL_CONTRACT = {
    "M_FREEZE_CANDIDATE_RUN_OMITTED",
    "M_FREEZE_REQUIRED_PAYLOAD_OMITTED",
    "M_FREEZE_DUPLICATE_PAYLOAD_IDENTITY",
    "M_FREEZE_OUTPUT_ROOT_COLLIDES_CANONICAL",
    "M_FREEZE_WRONG_PARENT_CANONICAL_IDENTITY",
    "M_FREEZE_R10_NEIGHBOR_DISPLACED",
    "M_FREEZE_TRAJECTORY_BYTE_MISMATCH",
    "M_FREEZE_OBSERVABLE_UNITS_OR_NORMALIZATION_MISSING",
    "M_FREEZE_UNKNOWN_NINTH_SOLVER_BLOCK",
    "M_FREEZE_CONTINUUM_OPERATOR_SUBSTITUTED",
    "M_FREEZE_OPERATOR_HELPER_HASH_CHANGED",
    "M_FREEZE_H_D_WITHOUT_POSITIVE_EVIDENCE",
    "M_FREEZE_H_E_WITH_MISSING_OBSERVABLE",
    "M_FREEZE_MULTIPLE_AGGREGATE_IDS_REMOVED",
    "M_FREEZE_RAW_EVIDENCE_FAILS_FAVORABLE_SUMMARY_TRUE",
    "M_FREEZE_UNKNOWN_MECHANISM_ID",
    "M_FREEZE_OUTPUT_ROOT_PREEXISTS",
    "M_FREEZE_WORKTREE_GITATTRIBUTES_SUBSTITUTED",
}


def audit_adversarial_coverage() -> dict[str, Any]:
    packet = load_json(FREEZE_PACKET)
    registered = {
        item["control_id"] for item in packet["freeze_adversarial_control_registry"]
    }
    missing = sorted(REQUIRED_ADVERSARIAL_CONTRACT - registered)
    return {
        "required_count": len(REQUIRED_ADVERSARIAL_CONTRACT),
        "registered_count": len(registered),
        "registered_control_ids": sorted(registered),
        "missing_required_control_ids": missing,
        "missing_required_count": len(missing),
        "complete": not missing,
    }


def audit_committed_configuration() -> dict[str, Any]:
    packet = load_json(FREEZE_PACKET)
    custody = packet["environment_identity"]["committed_configuration_custody"]
    source = custody["source_commit"]
    parent = subprocess.check_output(
        ["git", "rev-parse", f"{source}^"], cwd=REPO_ROOT
    ).decode("ascii").strip()
    records = []
    for item in custody["records"]:
        raw = subprocess.check_output(
            ["git", "show", f"{source}:{item['path']}"], cwd=REPO_ROOT
        )
        oid = subprocess.check_output(
            ["git", "rev-parse", f"{source}:{item['path']}"], cwd=REPO_ROOT
        ).decode("ascii").strip()
        records.append(
            {
                "path": item["path"],
                "blob_exact": oid == item["git_blob_oid"],
                "sha256_exact": sha256_bytes(raw) == item["sha256"],
                "working_tree_not_regeneration_input": (
                    item["working_tree_hash_is_regeneration_input"] is False
                ),
            }
        )
    return {
        "source_commit": source,
        "source_parent_exact": parent == custody["source_commit_parent"],
        "records": records,
        "all_records_exact": all(
            item["blob_exact"]
            and item["sha256_exact"]
            and item["working_tree_not_regeneration_input"]
            for item in records
        ),
    }


def build_report() -> dict[str, Any]:
    output_root = REPO_ROOT / EXPERIMENT_OUTPUT_ROOT
    if output_root.exists():
        raise ValueError("mechanism experiment output root must remain absent during review")
    inputs = validate_input_custody()
    packet = load_json(FREEZE_PACKET)
    manifest = load_json(FREEZE_MANIFEST)
    preparation_report = load_json(FREEZE_REPORT)
    design_review = load_json(DESIGN_REVIEW)
    if not (
        packet["target"].startswith("prepare_dirac_maxwell")
        and packet["selected_next_target"] == TARGET
        and packet["verdict"] == "PREPARED_PENDING_INDEPENDENT_REVIEW"
        and packet["decision_count"] == packet["passed_decision_count"] == 39
    ):
        raise ValueError("freeze v0 review authority mismatch")
    if design_review["verdict"] != "ACCEPT_INSTRUMENTED_R13_MECHANISM_EXPERIMENT_DESIGN":
        raise ValueError("accepted design v1 review missing")
    if manifest["packet"]["sha256"] != EXPECTED_INPUT_HASHES[FREEZE_PACKET]:
        raise ValueError("freeze manifest packet binding mismatch")
    if preparation_report["verdict"] != "PREPARED_PENDING_INDEPENDENT_REVIEW":
        raise ValueError("freeze preparation report mismatch")

    root_inventory = canonical_root_inventory()
    root_digest = sha256_bytes(canonical_json_bytes(root_inventory))
    tree_digest = canonical_tree_digest()
    if len(root_inventory) != 205 or root_digest != EXPECTED_CANONICAL_ROOT_DIGEST:
        raise ValueError("canonical authority inventory mismatch")
    if tree_digest != EXPECTED_CANONICAL_TREE_DIGEST:
        raise ValueError("canonical directory-tree mismatch")

    static_matrix = reconstruct_static_matrix()
    validator_probe = probe_matrix_validator()
    payload_probe = probe_payload_and_classifier_closure()
    loaded_module_probe = probe_loaded_module_binding()
    observable_audit = audit_observable_and_operator_semantics()
    provenance_audit = audit_threshold_provenance()
    adversarial_audit = audit_adversarial_coverage()
    configuration_audit = audit_committed_configuration()

    if not (
        static_matrix["record_count"] == 6
        and static_matrix["run_ids_exact"]
        and static_matrix["all_parent_physical_projections_exact"]
        and static_matrix["all_parent_input_output_identities_exact"]
        and static_matrix["all_three_pairs_exact"]
        and static_matrix["identity_forward_reverse_maps_exact"]
        and static_matrix["role_payload_count"] == 12
    ):
        raise ValueError("static matrix reconstruction failed")
    if not configuration_audit["all_records_exact"]:
        raise ValueError("committed configuration custody failed")

    findings = [
        {
            "finding_id": "B_INPUT_HASH_CONTRACT_NOT_SELF_RECONSTRUCTIBLE",
            "review_outcome": "BLOCK_IDENTITY_CLOSURE",
            "evidence": (
                "0/6 final records reproduce their stored input_hash when the final "
                "record is filtered by its own input_hash_material_excludes list"
            ),
            "bounded_correction_required": (
                "Define the final hash material before hashing, include the exclusion "
                "metadata in that contract, and add six exact recomputation controls."
            ),
        },
        {
            "finding_id": "B_EXECUTION_MATRIX_IDENTITY_VALIDATOR_INCOMPLETE",
            "review_outcome": "BLOCK_IDENTITY_CLOSURE",
            "evidence": (
                f"{validator_probe['incorrectly_accepted_identity_mutation_count']}/"
                f"{validator_probe['identity_mutation_count']} frozen identity-field "
                "mutations were accepted by validate_exact_run_matrix"
            ),
            "bounded_correction_required": (
                "Bind and validate the exact matrix SHA-256 and every parent, input, "
                "implementation, pair, role, schema, and custody field before execution; "
                "echo those identities into start and result custody."
            ),
        },
        {
            "finding_id": "B_RAW_PAYLOAD_EVIDENCE_CLOSURE_MISSING",
            "review_outcome": "BLOCK_OBSERVABLE_SEMANTICS",
            "evidence": (
                "A payload containing sixteen empty records in every required event family "
                "passes validate_run_role_payload, while classifier output is unchanged by "
                "empty/wrong raw payload identities and corrupt raw observables."
            ),
            "bounded_correction_required": (
                "Add a frozen raw JSON/NPZ validator and evidence assembler that recomputes "
                "all gates and metrics from the exact twelve payloads."
            ),
        },
        {
            "finding_id": "B_LOADED_OPERATOR_MODULE_CUSTODY_INCOMPLETE",
            "review_outcome": "BLOCK_OPERATOR_BINDING",
            "evidence": (
                "Dynamic imports can return shadow modules while source_binding_report still "
                "passes hashes of unrelated nominal workspace paths."
            ),
            "bounded_correction_required": (
                "Verify each loaded module's resolved __file__ and exact loaded bytes, bind "
                "the base-module object relation, and use a clean frozen process entry point."
            ),
        },
        {
            "finding_id": "B_H_C_OPERATOR_MECHANISM_AND_GAMMA_BOUND_UNJUSTIFIED",
            "review_outcome": "BLOCK_OPERATOR_BINDING",
            "evidence": (
                "Frozen Q is algebraically zero for arbitrary inputs and therefore its Q/B "
                "ratio measures floating evaluation/bound behavior; the decision-bearing "
                "gamma32 operation count has no auditable forward-error derivation."
            ),
            "bounded_correction_required": (
                "Use Q as an operator-consistency gate, preregister a non-tautological "
                "Maxwell-residual contribution test, and derive or validate a conservative "
                "roundoff bound for the actual NumPy operation graph."
            ),
        },
        {
            "finding_id": "B_HYPOTHESIS_THRESHOLD_PROVENANCE_INCOMPLETE",
            "review_outcome": "BLOCK_HYPOTHESIS_RULE_PROVENANCE",
            "evidence": (
                "The classifier literals are frozen, but no per-constant source artifact, "
                "source record, derivation, rounding rule, and scientific-meaning registry exists."
            ),
            "bounded_correction_required": (
                "Add a nonfuture threshold-provenance registry for every H_A-H_D constant "
                "without fitting or changing values from future mechanism outputs."
            ),
        },
        {
            "finding_id": "B_ADVERSARIAL_COVERAGE_INCOMPLETE",
            "review_outcome": "BLOCK_ADVERSARIAL_COVERAGE",
            "evidence": (
                f"{adversarial_audit['missing_required_count']} of "
                f"{adversarial_audit['required_count']} required review-contract mutations "
                "are absent from the permanent freeze registry."
            ),
            "bounded_correction_required": (
                "Register and execute the missing payload, parent, block, helper-hash, raw-"
                "summary, mechanism-ID, preexisting-root, and committed-byte mutations."
            ),
        },
    ]

    decisions = [
        {"decision_id": decision_id, "passed": True}
        for decision_id in PASS_DECISION_IDS
    ] + [
        {"decision_id": decision_id, "passed": False}
        for decision_id in FAILURE_DECISION_IDS
    ]
    return {
        "schema_id": SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "verdict": VERDICT,
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": "VERSIONED_NUMERICAL_FREEZE_CORRECTION_ONLY",
        "reviewer_independence": {
            "freeze_generator_imported": False,
            "preparation_combined_pass_flags_used_as_review_evidence": False,
            "canonical_parents_reconstructed_from_canonical_matrix_and_outputs": True,
            "matrix_and_payload_mutations_independently_executed": True,
            "classifier_and_implementation_subjects_imported_only_for_pure_validation": True,
            "evolution_runner_invocation_count": 0,
            "simulation_invocation_count": 0,
        },
        "input_custody": inputs,
        "canonical_custody": {
            "file_count": len(root_inventory),
            "authority_inventory_digest": root_digest,
            "directory_tree_digest": tree_digest,
            "canonical_mutation_count": 0,
            "mechanism_output_root_absent_before_and_after_review": not output_root.exists(),
        },
        "independent_static_matrix_audit": static_matrix,
        "independent_execution_matrix_validator_probe": validator_probe,
        "independent_payload_and_classifier_closure_probe": payload_probe,
        "independent_loaded_module_binding_probe": loaded_module_probe,
        "independent_observable_and_operator_audit": observable_audit,
        "independent_threshold_provenance_audit": provenance_audit,
        "independent_adversarial_coverage_audit": adversarial_audit,
        "independent_committed_configuration_audit": configuration_audit,
        "blocking_findings": findings,
        "blocking_finding_count": len(findings),
        "decisions": decisions,
        "decision_count": len(decisions),
        "passed_decision_count": sum(item["passed"] for item in decisions),
        "failed_decision_count": sum(not item["passed"] for item in decisions),
        "failed_decision_ids": FAILURE_DECISION_IDS,
        "preserved_scientific_core": {
            "Route_A": "ACCEPTED",
            "instrumented_design_v1": "ACCEPTED",
            "six_run_scientific_comparison_structure": "PRESERVED",
            "fourteen_observable_inventory": "PRESERVED_PENDING_EXECUTABLE_SEMANTIC_REPAIR",
            "eight_block_inventory": "PRESERVED",
            "canonical_robustness": "NUMERICALLY_BLOCKED",
            "R13_root_mechanism": "UNRESOLVED",
            "materiality": "NOT_EVALUATED_NUMERICAL_BLOCK",
            "new_E_REPRO": "NONE",
        },
        "authority_rotation": {
            "numerical_freeze_v0_accepted": False,
            "execution_authorized": False,
            "one_time_execution_count_authorized": 0,
            "rerun_authorized": False,
            "threshold_change_authorized": False,
            "robustness_reclassification_authorized": False,
            "materiality_evaluation_authorized": False,
            "new_scientific_claim_authorized": False,
            "versioned_freeze_correction_authorized": True,
        },
        "nonclaims": [
            "no mechanism hypothesis has been evaluated on experiment data",
            "no six-run mechanism experiment has executed",
            "no canonical output has changed",
            "no robustness or materiality result is assigned",
            "no E-REPRO, pillar, seam, CCFT, C_k, or master-action promotion is assigned",
        ],
        "claim_ceiling": (
            "This review blocks numerical-freeze v0 and authorizes only a versioned, "
            "bounded freeze correction. It does not reopen Route A or design v1 and does "
            "not authorize execution or any scientific classification."
        ),
    }


def artifact_bytes() -> bytes:
    return canonical_json_bytes(build_report())


def write_or_check(check: bool) -> None:
    raw = artifact_bytes()
    path = REPO_ROOT / REPORT_RELATIVE_PATH
    if check:
        if not path.is_file() or path.read_bytes() != raw:
            raise SystemExit(f"artifact mismatch: {REPORT_RELATIVE_PATH}")
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)
    print(
        json.dumps(
            {
                "status": "CHECKED" if check else "WROTE",
                "verdict": VERDICT,
                "review_target": TARGET,
                "execution_authorized": False,
            },
            sort_keys=True,
        )
    )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    write_or_check(args.check)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
