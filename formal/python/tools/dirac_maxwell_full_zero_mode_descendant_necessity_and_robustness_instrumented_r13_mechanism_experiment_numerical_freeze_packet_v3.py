from __future__ import annotations

"""Prepare the corrected numerical-freeze proposal for the R13 mechanism study.

This module is preparation-only.  It never calls an execution entry point,
creates the future experiment root, or calls the evolution. Freeze v3
preserves the accepted six physical configurations and corrects only the
partial-versus-resolved configuration lifecycle and the executor's mandatory
role-resolution ordering blocked by the independent v2 freeze review.
"""

import argparse
import copy
import hashlib
import importlib
import json
import math
import sys
import unicodedata
from collections.abc import Mapping
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_classifier_v3
    as classifier_v3,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_executor_custody_v3
    as executor_custody_v3,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_executor_v3
    as executor_v3,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_raw_evidence_assembler_v3
    as evidence_v3,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_semantic_contract_v1
    as semantic_v1,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_numerical_freeze_packet_v2
    as predecessor_v2,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_numerical_freeze_packet_v0
    as canonical_v0,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCRIPT_PATH = Path(__file__).resolve()
SCRIPT_RELATIVE_PATH = (
    "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_"
    "robustness_instrumented_r13_mechanism_experiment_numerical_freeze_packet_v3.py"
)
PACKET_RELATIVE_PATH = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-INSTRUMENTED-R13-MECHANISM-EXPERIMENT-NUMERICAL-FREEZE-PACKET-v3.json"
)
RUN_MATRIX_RELATIVE_PATH = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-INSTRUMENTED-R13-MECHANISM-EXPERIMENT-NUMERICAL-FREEZE-RUN-MATRIX-v3.json"
)
IDENTITY_RELATIVE_PATH = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-INSTRUMENTED-R13-MECHANISM-EXPERIMENT-NUMERICAL-FREEZE-"
    "EXPECTED-OUTPUT-IDENTITY-MANIFEST-v3.json"
)
MANIFEST_RELATIVE_PATH = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-INSTRUMENTED-R13-MECHANISM-EXPERIMENT-NUMERICAL-FREEZE-MANIFEST-v3.json"
)
REPORT_RELATIVE_PATH = (
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
    "ROBUSTNESS_INSTRUMENTED_R13_MECHANISM_EXPERIMENT_NUMERICAL_FREEZE_PACKET_"
    "20260716_v3.json"
)
PREDECESSOR_PACKET_RELATIVE_PATH = predecessor_v2.PACKET_RELATIVE_PATH
PREDECESSOR_MATRIX_RELATIVE_PATH = predecessor_v2.RUN_MATRIX_RELATIVE_PATH
PREDECESSOR_IDENTITY_RELATIVE_PATH = predecessor_v2.IDENTITY_RELATIVE_PATH
PREDECESSOR_REPORT_RELATIVE_PATH = predecessor_v2.REPORT_RELATIVE_PATH
PREDECESSOR_REVIEW_RELATIVE_PATH = (
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
    "ROBUSTNESS_INSTRUMENTED_R13_MECHANISM_EXPERIMENT_NUMERICAL_FREEZE_PACKET_"
    "REVIEW_20260716_v2.json"
)
DESIGN_REVIEW_RELATIVE_PATH = predecessor_v2.DESIGN_REVIEW_RELATIVE_PATH
CANONICAL_MATRIX_RELATIVE_PATH = predecessor_v2.CANONICAL_MATRIX_RELATIVE_PATH

CAPTURED_AT_UTC = "2026-07-16T00:00:00Z"
TARGET = (
    "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
    "instrumented_r13_mechanism_experiment_numerical_freeze_packet_v3"
)
REVIEW_TARGET = (
    "review_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
    "instrumented_r13_mechanism_experiment_numerical_freeze_packet_v3_result"
)
POST_ACCEPTANCE_TARGET = (
    "execute_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
    "instrumented_r13_mechanism_experiment_v0_once"
)
EXPERIMENT_OUTPUT_ROOT = predecessor_v2.EXPERIMENT_OUTPUT_ROOT
CANONICAL_OUTPUT_ROOT = predecessor_v2.CANONICAL_OUTPUT_ROOT
EXPECTED_CANONICAL_ROOT_DIGEST = predecessor_v2.EXPECTED_CANONICAL_ROOT_DIGEST
EXPECTED_CANONICAL_DIRECTORY_TREE_SHA256 = (
    predecessor_v2.EXPECTED_CANONICAL_DIRECTORY_TREE_SHA256
)

EXECUTOR_RELATIVE_PATH = executor_custody_v3.MODULE_PATH_BY_NAME[
    executor_custody_v3.EXECUTOR_MODULE
]
CUSTODY_RELATIVE_PATH = executor_custody_v3.MODULE_PATH_BY_NAME[
    executor_custody_v3.CUSTODY_MODULE
]
V0_IMPLEMENTATION_RELATIVE_PATH = executor_custody_v3.MODULE_PATH_BY_NAME[
    executor_custody_v3.V0_IMPLEMENTATION_MODULE
]
HISTORICAL_EVOLUTION_RELATIVE_PATH = executor_custody_v3.MODULE_PATH_BY_NAME[
    executor_custody_v3.HISTORICAL_EVOLUTION_MODULE
]
HISTORICAL_PACK_RELATIVE_PATH = executor_custody_v3.MODULE_PATH_BY_NAME[
    executor_custody_v3.HISTORICAL_PACK_MODULE
]
SEMANTIC_RELATIVE_PATH = semantic_v1.SCRIPT_RELATIVE_PATH
ASSEMBLER_RELATIVE_PATH = evidence_v3.SCRIPT_RELATIVE_PATH
CLASSIFIER_RELATIVE_PATH = classifier_v3.SCRIPT_RELATIVE_PATH

RUNTIME_MODULES = (
    (executor_custody_v3.EXECUTOR_MODULE, EXECUTOR_RELATIVE_PATH, "EXECUTION"),
    (executor_custody_v3.CUSTODY_MODULE, CUSTODY_RELATIVE_PATH, "EXECUTION"),
    (
        executor_custody_v3.V0_IMPLEMENTATION_MODULE,
        V0_IMPLEMENTATION_RELATIVE_PATH,
        "EXECUTION",
    ),
    (
        executor_custody_v3.HISTORICAL_EVOLUTION_MODULE,
        HISTORICAL_EVOLUTION_RELATIVE_PATH,
        "EXECUTION",
    ),
    (
        executor_custody_v3.HISTORICAL_PACK_MODULE,
        HISTORICAL_PACK_RELATIVE_PATH,
        "EXECUTION",
    ),
    (
        "formal.python.tools.dirac_maxwell_full_zero_mode_descendant_necessity_"
        "and_robustness_instrumented_r13_mechanism_experiment_semantic_contract_v1",
        SEMANTIC_RELATIVE_PATH,
        "CLASSIFICATION",
    ),
    (
        "formal.python.tools.dirac_maxwell_full_zero_mode_descendant_necessity_"
        "and_robustness_instrumented_r13_mechanism_experiment_raw_evidence_assembler_v3",
        ASSEMBLER_RELATIVE_PATH,
        "CLASSIFICATION",
    ),
    (
        "formal.python.tools.dirac_maxwell_full_zero_mode_descendant_necessity_"
        "and_robustness_instrumented_r13_mechanism_experiment_classifier_v3",
        CLASSIFIER_RELATIVE_PATH,
        "CLASSIFICATION",
    ),
)

DECISION_IDS = (
    "accepted_route_A_and_design_v1_are_preserved",
    "blocked_freeze_v2_review_authorizes_only_versioned_v3_freeze_correction",
    "exact_six_run_physical_matrix_is_unchanged",
    "exact_twelve_payload_paths_are_unchanged_unique_and_isolated",
    "positive_inclusion_scientific_input_contract_has_no_exclusions",
    "all_six_scientific_input_hashes_reconstruct_from_source_independent_cores",
    "three_pair_identical_physical_configuration_hashes_reconstruct",
    "all_six_complete_execution_identity_hashes_reconstruct",
    "all_six_partial_templates_pass_typed_partial_validation",
    "all_six_frozen_role_overlays_resolve_complete_metric_configurations",
    "all_six_resolved_configurations_pass_strict_final_validation",
    "read_only_preflight_constructs_exactly_six_plans_without_simulation_or_output",
    "all_eight_partial_resolution_negative_controls_fail_with_exact_diagnostics",
    "runtime_executor_accepts_no_caller_supplied_matrix_or_identity_fields",
    "runtime_executor_hard_binds_independent_freeze_review_anchor",
    "all_twenty_identity_mutations_have_exact_field_specific_diagnostics",
    "actual_loaded_module_paths_bytes_and_loader_types_are_attested",
    "historical_evolution_pack_object_identity_is_attested",
    "complete_execution_and_classification_dependency_closure_is_bound",
    "exact_six_json_and_six_npz_payloads_are_raw_evidence",
    "required_raw_event_fields_shapes_finiteness_and_time_closure_are_gated",
    "empty_event_summaries_cannot_replace_complete_raw_series",
    "supplied_booleans_and_metrics_are_non_authoritative",
    "classifier_reconstructs_nonperturbation_and_H_A_through_H_D",
    "H_E_requires_complete_admissible_evidence_and_empty_support_set",
    "H_C_uses_direct_Maxwell_defect_and_independent_Dirac_current_paths",
    "legacy_algebraic_Q_is_operator_gate_only",
    "gamma32_is_absent_from_all_v1_mechanism_decisions",
    "all_twenty_three_support_constants_have_complete_nonfuture_provenance",
    "all_support_constants_are_declared_before_future_output_exists",
    "full_adversarial_registry_contains_exact_forty_one_unique_controls",
    "all_nine_v0_review_missing_control_ids_are_present",
    "each_adversarial_control_has_exact_mutation_diagnostic_and_decision",
    "canonical_205_file_authority_inventory_digest_is_unchanged",
    "canonical_directory_tree_digest_is_unchanged",
    "future_experiment_output_root_is_absent",
    "freeze_preparation_invokes_no_evolution_or_simulation",
    "freeze_preparation_authorizes_no_execution_retry_or_overwrite",
    "canonical_NUMERICALLY_BLOCKED_verdict_is_unchanged",
    "materiality_remains_NOT_EVALUATED_NUMERICAL_BLOCK",
    "no_new_E_REPRO_or_ToE_promotion_is_authorized",
    "packet_rotates_only_to_independent_freeze_v3_review",
)


def _normalize(value: Any) -> Any:
    if isinstance(value, str):
        return unicodedata.normalize("NFC", value)
    if isinstance(value, Mapping):
        return {str(key): _normalize(item) for key, item in value.items()}
    if isinstance(value, (list, tuple)):
        return [_normalize(item) for item in value]
    if isinstance(value, float) and not math.isfinite(value):
        raise ValueError("canonical JSON forbids nonfinite floats")
    return value


def canonical_json_bytes(value: Any) -> bytes:
    return (
        json.dumps(
            _normalize(value),
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
            allow_nan=False,
        )
        + "\n"
    ).encode("utf-8")


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _load_json(relative_path: str) -> dict[str, Any]:
    value = json.loads((REPO_ROOT / relative_path).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise TypeError(f"expected JSON object: {relative_path}")
    return value


def _file_binding(
    relative_path: str,
    *,
    module_name: str | None = None,
    runtime_phase: str | None = None,
) -> dict[str, Any]:
    raw = (REPO_ROOT / relative_path).read_bytes()
    binding = {
        "relative_path": relative_path,
        "sha256": sha256_bytes(raw),
    }
    if module_name is not None:
        binding.update(
            {
                "module_name": module_name,
                "runtime_phase": runtime_phase,
                "loader_type": "SourceFileLoader",
                "expected_resolved_relative_path": relative_path,
                "loaded_source_bytes_must_equal_frozen_bytes": True,
            }
        )
    return binding


def _runtime_source_binding() -> dict[str, Any]:
    bindings = [
        _file_binding(path, module_name=name, runtime_phase=phase)
        for name, path, phase in RUNTIME_MODULES
    ]
    runtime_source_closure = {
        "schema_id": "R13_MECHANISM_RUNTIME_SOURCE_CLOSURE_v3",
        "modules": bindings,
        "operator_configuration": {
            "length": 1.0,
            "wilson_r": 1.0,
            "boundary_condition": "PERIODIC_NUMPY_ROLL_AXIS0",
            "gauge_link_rule": "EXP_PLUS_OR_MINUS_I_Q_THETA",
            "state_arithmetic": (
                "IEEE754_BINARY64_PACKED_REAL_COMPLEX128_INTERNAL"
            ),
        },
        "historical_object_identity_rule": (
            "v0._load_historical_implementation returns the exact attested modules and "
            "historical_evolution.accepted_v0 is historical_pack"
        ),
    }
    return {
        "schema_id": "R13_MECHANISM_FREEZE_RUNTIME_SOURCE_BINDING_v3",
        "runtime_source_closure": runtime_source_closure,
        "bindings": bindings,
        "closure_sha256": sha256_bytes(canonical_json_bytes(runtime_source_closure)),
        "binding_count": len(bindings),
        "actual_loaded_module_path_loader_and_byte_attestation_required": True,
        "git_commit_or_blob_identity_decision_bearing": False,
        "name_only_dynamic_import_authorized": False,
    }


def _attest_preparation_loaded_sources(
    source_binding: Mapping[str, Any],
) -> dict[str, Any]:
    closure = source_binding["runtime_source_closure"]
    reports: list[dict[str, Any]] = []
    modules: dict[str, Any] = {}
    for binding in closure["modules"]:
        module = importlib.import_module(binding["module_name"])
        expected_path = (REPO_ROOT / binding["relative_path"]).resolve()
        module_path = Path(module.__file__).resolve()
        spec = module.__spec__
        origin = Path(spec.origin).resolve() if spec and spec.origin else None
        loader_type = type(spec.loader).__name__ if spec else None
        loaded_sha256 = sha256_bytes(expected_path.read_bytes())
        if (
            sys.modules.get(module.__name__) is not module
            or module_path != expected_path
            or origin != expected_path
            or loader_type != binding["loader_type"]
            or loaded_sha256 != binding["sha256"]
        ):
            raise ValueError(f"runtime-loaded source identity mismatch: {module.__name__}")
        modules[module.__name__] = module
        reports.append(
            {
                "module_name": module.__name__,
                "relative_path": binding["relative_path"],
                "sha256": loaded_sha256,
                "loader_type": loader_type,
                "path_exact": True,
                "bytes_exact": True,
                "loader_exact": True,
            }
        )
    v0 = modules[executor_custody_v3.V0_IMPLEMENTATION_MODULE]
    evolution = modules[executor_custody_v3.HISTORICAL_EVOLUTION_MODULE]
    historical_pack = modules[executor_custody_v3.HISTORICAL_PACK_MODULE]
    loaded_evolution, loaded_pack = v0._load_historical_implementation()
    if (
        loaded_evolution is not evolution
        or loaded_pack is not historical_pack
        or getattr(evolution, "accepted_v0", None) is not historical_pack
    ):
        raise ValueError("historical runtime object identity mismatch")
    return {
        "all_passed": True,
        "loaded_module_count": len(reports),
        "runtime_source_closure_sha256": source_binding["closure_sha256"],
        "loaded_modules": reports,
        "historical_object_binding_exact": True,
    }


def build_physical_configuration_core(
    record: Mapping[str, Any], runtime_source_closure_sha256: str
) -> dict[str, Any]:
    return executor_v3.build_physical_configuration_core(
        record, runtime_source_closure_sha256
    )


def build_scientific_input_core(
    record: Mapping[str, Any],
    physical_core: Mapping[str, Any],
    runtime_source_closure_sha256: str,
) -> dict[str, Any]:
    reconstructed_physical = executor_v3.build_physical_configuration_core(
        record, runtime_source_closure_sha256
    )
    if canonical_json_bytes(physical_core) != canonical_json_bytes(
        reconstructed_physical
    ):
        raise ValueError("supplied physical core does not reconstruct")
    return executor_v3.build_scientific_input_core(
        record, runtime_source_closure_sha256
    )


def scientific_input_hash(core: Mapping[str, Any]) -> str:
    return executor_v3.scientific_input_hash(core)


def _authority_basis() -> dict[str, Any]:
    design_review = _load_json(DESIGN_REVIEW_RELATIVE_PATH)
    predecessor_review = _load_json(PREDECESSOR_REVIEW_RELATIVE_PATH)
    if design_review.get("verdict") != (
        "ACCEPT_INSTRUMENTED_R13_MECHANISM_EXPERIMENT_DESIGN"
    ):
        raise ValueError("accepted design-v1 review is not authoritative")
    if predecessor_review.get("verdict") != "BLOCK_EXECUTOR_PREFLIGHT_CONFIGURATION":
        raise ValueError("blocked freeze-v2 review is not authoritative")
    if predecessor_review.get("selected_next_target") != TARGET:
        raise ValueError("freeze-v2 review did not authorize v3 preparation")
    return {
        "accepted_design_v1_review": _file_binding(DESIGN_REVIEW_RELATIVE_PATH),
        "blocked_freeze_v2_review": _file_binding(PREDECESSOR_REVIEW_RELATIVE_PATH),
        "accepted_design_verdict": design_review["verdict"],
        "blocked_predecessor_verdict": predecessor_review["verdict"],
        "authorized_target": predecessor_review["selected_next_target"],
        "route_A_reopened": False,
        "scientific_matrix_reopened": False,
    }


def _build_run_matrix(implementation: Mapping[str, Any]) -> dict[str, Any]:
    predecessor_report = _load_json(PREDECESSOR_REPORT_RELATIVE_PATH)
    predecessor_path = REPO_ROOT / PREDECESSOR_MATRIX_RELATIVE_PATH
    predecessor_raw = predecessor_path.read_bytes()
    expected_predecessor_hash = predecessor_report["artifacts"]["run_matrix"][
        "sha256"
    ]
    if sha256_bytes(predecessor_raw) != expected_predecessor_hash:
        raise ValueError("blocked predecessor matrix bytes changed")
    matrix = json.loads(predecessor_raw.decode("utf-8"))
    if not isinstance(matrix, dict) or matrix.get("record_count") != 6:
        raise ValueError("predecessor six-run matrix schema invalid")
    result = copy.deepcopy(matrix)
    result["schema_id"] = (
        "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_"
        "INSTRUMENTED_R13_MECHANISM_EXPERIMENT_NUMERICAL_FREEZE_RUN_MATRIX_v3"
    )
    result["supersedes_blocked_predecessor"] = {
        "path": PREDECESSOR_MATRIX_RELATIVE_PATH,
        "sha256": expected_predecessor_hash,
        "scientific_configuration_changed": False,
    }
    closure_digest = str(implementation["closure_sha256"])
    scientific_hashes: dict[str, str] = {}
    physical_hashes: dict[str, str] = {}
    complete_execution_hashes: dict[str, str] = {}
    resolved_configuration_hashes: dict[str, str] = {}
    full_record_hashes: dict[str, str] = {}
    predecessor_packet = _load_json(PREDECESSOR_PACKET_RELATIVE_PATH)
    partial_template = copy.deepcopy(
        predecessor_packet["metric_configuration_template"]
    )
    for record in result["records"]:
        for stale_field in (
            "input_hash_material_excludes",
            "implementation_closure_sha256",
            "physical_configuration_core",
            "physical_configuration_core_sha256",
            "scientific_input_core",
            "scientific_input_core_sha256",
            "complete_execution_identity_core",
            "complete_execution_identity_sha256",
            "partial_metric_configuration",
            "partial_metric_configuration_sha256",
            "role_resolution_overlay",
            "role_resolution_overlay_sha256",
            "resolved_metric_configuration",
            "resolved_metric_configuration_sha256",
            "input_hash_contract",
        ):
            record.pop(stale_field, None)
        record["runtime_source_closure_sha256"] = closure_digest
        record["executor_id"] = executor_v3.EXECUTOR_ID
        record["executor_sha256"] = next(
            item["sha256"]
            for item in implementation["bindings"]
            if item["relative_path"] == EXECUTOR_RELATIVE_PATH
        )
        record["raw_evidence_assembler_id"] = evidence_v3.ASSEMBLER_ID
        record["raw_evidence_assembler_sha256"] = next(
            item["sha256"]
            for item in implementation["bindings"]
            if item["relative_path"] == ASSEMBLER_RELATIVE_PATH
        )
        record["classifier_id"] = classifier_v3.CLASSIFIER_ID
        record["classifier_sha256"] = next(
            item["sha256"]
            for item in implementation["bindings"]
            if item["relative_path"] == CLASSIFIER_RELATIVE_PATH
        )
        record["semantic_contract_id"] = semantic_v1.CONTRACT_ID
        record["semantic_contract_sha256"] = next(
            item["sha256"]
            for item in implementation["bindings"]
            if item["relative_path"] == SEMANTIC_RELATIVE_PATH
        )
        partial = {
            "schema_id": executor_v3.PARTIAL_METRIC_CONFIGURATION_SCHEMA_ID,
            "run_id": record["run_id"],
            "metric_configuration_template": copy.deepcopy(partial_template),
        }
        overlay = {
            "schema_id": executor_v3.ROLE_RESOLUTION_OVERLAY_SCHEMA_ID,
            "run_id": record["run_id"],
            "execution_role": record["execution_role"],
            "instrumentation_enabled": record["instrumentation_enabled"],
            "requested_solver_tolerance": record["tolerance"],
            "block_scales": {
                block_id: float(record["tolerance"])
                for block_id in executor_v3.METRIC_BLOCK_IDS
            },
            "block_floors": {
                block_id: executor_v3.GAMMA64
                for block_id in executor_v3.METRIC_BLOCK_IDS
            },
            "epsilon_dominance": executor_v3.GAMMA64,
        }
        resolved = executor_v3.resolve_frozen_metric_configuration(
            record, partial, overlay
        )
        partial_hash = sha256_bytes(canonical_json_bytes(partial))
        overlay_hash = sha256_bytes(canonical_json_bytes(overlay))
        resolved_hash = sha256_bytes(canonical_json_bytes(resolved))
        record["partial_metric_configuration"] = partial
        record["partial_metric_configuration_sha256"] = partial_hash
        record["role_resolution_overlay"] = overlay
        record["role_resolution_overlay_sha256"] = overlay_hash
        record["resolved_metric_configuration"] = resolved
        record["resolved_metric_configuration_sha256"] = resolved_hash
        physical = build_physical_configuration_core(record, closure_digest)
        physical_hash = sha256_bytes(canonical_json_bytes(physical))
        scientific = build_scientific_input_core(
            record, physical, closure_digest
        )
        input_hash = scientific_input_hash(scientific)
        record["physical_configuration_core"] = physical
        record["physical_configuration_core_sha256"] = physical_hash
        record["scientific_input_core"] = scientific
        record["scientific_input_core_sha256"] = input_hash
        record["input_hash"] = input_hash
        complete_execution = executor_v3.build_complete_execution_identity_core(
            record, closure_digest
        )
        complete_execution_hash = executor_v3.complete_execution_identity_sha256(
            record, closure_digest
        )
        record["complete_execution_identity_core"] = complete_execution
        record[
            "complete_execution_identity_sha256"
        ] = complete_execution_hash
        record["input_hash_contract"] = {
            "material": "scientific_input_core positive-inclusion object only",
            "excluded_field_count": 0,
            "canonical_serialization": (
                "NFC strings; sorted UTF-8 JSON keys; compact separators; finite "
                "CPython-3.10 shortest-round-trip numbers; one trailing LF"
            ),
            "hash_algorithm": "SHA-256",
            "reconstruction_formula": (
                "SHA256(canonical_json_bytes(record.scientific_input_core))"
            ),
        }
        scientific_hashes[record["run_id"]] = input_hash
        physical_hashes[record["run_id"]] = physical_hash
        complete_execution_hashes[record["run_id"]] = complete_execution_hash
        resolved_configuration_hashes[record["run_id"]] = resolved_hash
    for record in result["records"]:
        full_hash = executor_v3.full_record_identity_sha256(record)
        full_record_hashes[record["run_id"]] = full_hash
    result["scientific_input_hash_contract"] = {
        "positive_inclusion_only": True,
        "exclusion_lists_authorized": False,
        "source_code_identity_in_scientific_hash": False,
        "scientific_input_sha256_by_run_id": scientific_hashes,
        "physical_configuration_sha256_by_run_id": physical_hashes,
        "unique_scientific_input_count": len(set(scientific_hashes.values())),
        "expected_pairwise_identity": True,
    }
    result["complete_execution_identity_contract"] = {
        "runtime_source_closure_sha256": closure_digest,
        "complete_execution_sha256_by_run_id": complete_execution_hashes,
        "unique_complete_execution_identity_count": len(
            set(complete_execution_hashes.values())
        ),
        "expected_all_six_unique": True,
    }
    result["metric_configuration_resolution_contract"] = {
        "partial_schema_id": executor_v3.PARTIAL_METRIC_CONFIGURATION_SCHEMA_ID,
        "overlay_schema_id": executor_v3.ROLE_RESOLUTION_OVERLAY_SCHEMA_ID,
        "resolved_schema_id": executor_v3.RESOLVED_METRIC_CONFIGURATION_SCHEMA_ID,
        "mandatory_order": [
            "run_id_lookup",
            "frozen_partial_template_retrieval",
            "frozen_role_overlay_retrieval",
            "role_resolution",
            "strict_resolved_validation",
            "read_only_execution_plan_construction",
        ],
        "resolved_metric_configuration_sha256_by_run_id": (
            resolved_configuration_hashes
        ),
        "unique_resolved_configuration_count": len(
            set(resolved_configuration_hashes.values())
        ),
        "caller_role_or_metric_override": "FORBIDDEN",
        "unresolved_template_executable": False,
    }
    result["full_record_identity_sha256_by_run_id"] = full_record_hashes
    result["runtime_source_closure_sha256"] = closure_digest
    result.pop("implementation_closure_sha256", None)
    result["generation_policy"] = (
        "fixed accepted six-run matrix; v3 changes only typed role resolution and "
        "read-only preflight ordering; no dynamic discovery, retry, "
        "threshold calibration, or simulation"
    )
    return result


def _build_identity(matrix: Mapping[str, Any]) -> dict[str, Any]:
    predecessor = _load_json(PREDECESSOR_IDENTITY_RELATIVE_PATH)
    identity = copy.deepcopy(predecessor)
    identity["schema_id"] = (
        "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_"
        "INSTRUMENTED_R13_MECHANISM_EXPERIMENT_EXPECTED_OUTPUT_IDENTITY_MANIFEST_v3"
    )
    identity["supersedes_blocked_predecessor"] = {
        "path": PREDECESSOR_IDENTITY_RELATIVE_PATH,
        "sha256": sha256_bytes(
            (REPO_ROOT / PREDECESSOR_IDENTITY_RELATIVE_PATH).read_bytes()
        ),
    }
    identity["outputs"] = []
    for record in matrix["records"]:
        identity["outputs"].append(
            {
                "run_id": record["run_id"],
                "execution_role": record["execution_role"],
                "mechanism_configuration_role": record[
                    "mechanism_configuration_role"
                ],
                "instrumentation_enabled": record["instrumentation_enabled"],
                "paired_run_id": record["paired_run_id"],
                "scientific_row_id": record["scientific_row_id"],
                "parent_canonical_run_id": record["parent_canonical_run_id"],
                "input_hash": record["input_hash"],
                "scientific_input_core_sha256": record[
                    "scientific_input_core_sha256"
                ],
                "physical_configuration_core_sha256": record[
                    "physical_configuration_core_sha256"
                ],
                "full_record_identity_sha256": matrix[
                    "full_record_identity_sha256_by_run_id"
                ][record["run_id"]],
                "complete_execution_identity_sha256": record[
                    "complete_execution_identity_sha256"
                ],
                "resolved_metric_configuration_sha256": record[
                    "resolved_metric_configuration_sha256"
                ],
                "implementation_id": record["implementation_id"],
                "implementation_sha256": record["implementation_sha256"],
                "runtime_source_closure_sha256": record[
                    "runtime_source_closure_sha256"
                ],
                "output_schema_version": record["output_schema_version"],
                "json_safe_filename": record["json_safe_filename"],
                "npz_safe_filename": record["npz_safe_filename"],
                "json_relative_output_path": record[
                    "json_relative_output_path"
                ],
                "npz_relative_output_path": record["npz_relative_output_path"],
            }
        )
    identity["raw_evidence_contract"] = {
        "required_role_payload_count": 12,
        "required_auxiliary_payload_count": 2,
        "JSON_and_NPZ_both_required_for_each_run": True,
        "payload_summaries_authoritative": False,
        "missing_duplicate_or_orphan_behavior": "BLOCKED_REQUIRED_EVIDENCE_INCOMPLETE_OR_RUN_IDENTITY",
    }
    return identity


def _identity_mutation_diagnostic_audit(
    matrix: Mapping[str, Any],
) -> dict[str, Any]:
    if semantic_v1.IDENTITY_MUTATION_FIELDS != executor_v3.IDENTITY_DIAGNOSTIC_FIELDS:
        raise ValueError("v3 diagnostic field order differs from the reviewed 20-field domain")
    probes: list[dict[str, Any]] = []
    for field in executor_v3.IDENTITY_DIAGNOSTIC_FIELDS:
        candidate = copy.deepcopy(matrix)
        candidate["records"][0][field] = copy.deepcopy(
            semantic_v1.IDENTITY_MUTATION_VALUES[field]
        )
        expected = f"RUN_MATRIX_IDENTITY_FIELD_MISMATCH:{field}"
        observed = executor_v3.strict_validate_matrix(candidate, matrix)
        if observed != [expected]:
            raise ValueError(
                f"identity mutation diagnostic mismatch for {field}: {observed}"
            )
        probes.append(
            {
                "field": field,
                "expected_first_diagnostic": expected,
                "observed_first_diagnostic": observed[0],
                "accepted": False,
                "passed": True,
            }
        )
    return {
        "mutation_count": len(probes),
        "rejected_count": len(probes),
        "exact_first_diagnostic_count": len(probes),
        "all_passed": True,
        "probes": probes,
    }


def _configuration_resolution_audit(
    matrix: Mapping[str, Any],
) -> dict[str, Any]:
    """Exercise the v3 lifecycle without entering the numerical evolution."""

    records = matrix["records"]
    v0 = importlib.import_module(executor_custody_v3.V0_IMPLEMENTATION_MODULE)
    partial_diagnostics: dict[str, list[str]] = {}
    resolved_hashes: dict[str, str] = {}
    plan_records: list[dict[str, Any]] = []
    for record in records:
        run_id = str(record["run_id"])
        partial = record["partial_metric_configuration"]
        overlay = record["role_resolution_overlay"]
        partial_diagnostics[run_id] = (
            executor_v3.validate_partial_metric_configuration(partial)
        )
        resolved = executor_v3.resolve_frozen_metric_configuration(
            record, partial, overlay
        )
        if resolved != record["resolved_metric_configuration"]:
            raise ValueError(f"frozen role resolution mismatch: {run_id}")
        v0._validate_metric_configuration(resolved["metric_configuration"])
        resolved_hash = sha256_bytes(canonical_json_bytes(resolved))
        if resolved_hash != record["resolved_metric_configuration_sha256"]:
            raise ValueError(f"resolved configuration hash mismatch: {run_id}")
        resolved_hashes[run_id] = resolved_hash
        plan_records.append(
            executor_v3.build_read_only_execution_plan_record(
                record, resolved, overlay
            )
        )

    first = records[0]
    partial = first["partial_metric_configuration"]
    overlay = first["role_resolution_overlay"]
    resolved = first["resolved_metric_configuration"]
    negative_controls: list[dict[str, Any]] = []

    def record_diagnostic(control_id: str, expected: str, observed: str) -> None:
        if observed != expected:
            raise ValueError(
                f"configuration control {control_id} expected {expected}, got {observed}"
            )
        negative_controls.append(
            {
                "control_id": control_id,
                "expected_first_diagnostic": expected,
                "observed_first_diagnostic": observed,
                "plan_constructed": False,
                "passed": True,
            }
        )

    record_diagnostic(
        "unresolved_template_not_executable",
        "UNRESOLVED_TEMPLATE_NOT_EXECUTABLE",
        executor_v3.validate_resolved_metric_configuration(
            first, partial, overlay
        )[0],
    )
    missing_mapping = copy.deepcopy(overlay)
    missing_mapping.pop("block_floors")
    try:
        executor_v3.resolve_frozen_metric_configuration(
            first, partial, missing_mapping
        )
    except executor_v3.ConfigurationResolutionError as error:
        record_diagnostic(
            "missing_role_mapping",
            "ROLE_RESOLUTION_MISSING_METRIC_BLOCK_FLOORS",
            str(error),
        )
    else:
        raise ValueError("missing role mapping unexpectedly resolved")
    missing_resolved_floors = copy.deepcopy(resolved)
    missing_resolved_floors["metric_configuration"].pop("block_floors")
    record_diagnostic(
        "missing_block_floors_after_resolution",
        "ROLE_RESOLUTION_MISSING_METRIC_BLOCK_FLOORS",
        executor_v3.validate_resolved_metric_configuration(
            first, missing_resolved_floors, overlay
        )[0],
    )
    wrong_floors = copy.deepcopy(overlay)
    wrong_floors["block_floors"][executor_v3.METRIC_BLOCK_IDS[0]] *= 2.0
    try:
        executor_v3.resolve_frozen_metric_configuration(first, partial, wrong_floors)
    except executor_v3.ConfigurationResolutionError as error:
        record_diagnostic(
            "wrong_block_floors_for_role",
            "ROLE_RESOLUTION_WRONG_METRIC_BLOCK_FLOORS",
            str(error),
        )
    else:
        raise ValueError("wrong role floors unexpectedly resolved")
    caller_floors = copy.deepcopy(partial)
    caller_floors["metric_configuration_template"]["block_floors"] = copy.deepcopy(
        overlay["block_floors"]
    )
    record_diagnostic(
        "caller_supplied_block_floors",
        "CALLER_SUPPLIED_METRIC_BLOCK_FLOORS_FORBIDDEN",
        executor_v3.validate_partial_metric_configuration(caller_floors)[0],
    )
    mutated_overlay = copy.deepcopy(overlay)
    mutated_overlay["execution_role"] = "CALLER_MUTATION"
    record_diagnostic(
        "role_overlay_mutation",
        "ROLE_RESOLUTION_OVERLAY_IDENTITY_MISMATCH",
        executor_v3.validate_role_resolution_overlay(first, mutated_overlay)[0],
    )
    try:
        executor_v3.build_read_only_execution_plan_record(first, partial, overlay)
    except executor_v3.ConfigurationResolutionError as error:
        record_diagnostic(
            "validation_before_resolution",
            "VALIDATION_BEFORE_ROLE_RESOLUTION_FORBIDDEN",
            str(error),
        )
    else:
        raise ValueError("partial template unexpectedly produced a plan")
    try:
        executor_v3.metric_configuration_for_numerical_execution(
            first, partial, overlay
        )
    except executor_v3.ConfigurationResolutionError as error:
        record_diagnostic(
            "partial_object_to_numerical_executor",
            "PARTIAL_CONFIGURATION_NUMERICAL_EXECUTION_FORBIDDEN",
            str(error),
        )
    else:
        raise ValueError("partial template unexpectedly reached numerical execution")

    closure = matrix["runtime_source_closure_sha256"]
    pair_equalities: list[dict[str, Any]] = []
    for left_index, right_index in ((0, 1), (2, 3), (4, 5)):
        left = records[left_index]
        right = records[right_index]
        equal = executor_v3.physical_configuration_hash(
            executor_v3.build_physical_configuration_core(left, closure)
        ) == executor_v3.physical_configuration_hash(
            executor_v3.build_physical_configuration_core(right, closure)
        )
        pair_equalities.append(
            {
                "instrumented_run_id": left["run_id"],
                "control_run_id": right["run_id"],
                "physically_identical": equal,
            }
        )

    positive_controls = {
        "partial_template_validation_count": sum(
            not diagnostics for diagnostics in partial_diagnostics.values()
        ),
        "role_resolution_count": len(resolved_hashes),
        "resolved_block_floors_match_count": sum(
            record["resolved_metric_configuration"]["metric_configuration"][
                "block_floors"
            ]
            == {
                block_id: executor_v3.GAMMA64
                for block_id in executor_v3.METRIC_BLOCK_IDS
            }
            for record in records
        ),
        "strict_final_validation_count": len(resolved_hashes),
        "read_only_execution_plan_count": len(plan_records),
        "physical_pair_equality_count": sum(
            item["physically_identical"] for item in pair_equalities
        ),
        "unique_complete_execution_identity_count": len(
            {record["complete_execution_identity_sha256"] for record in records}
        ),
        "simulation_entry_count": 0,
        "future_output_root_created": False,
    }
    expected_positive = {
        "partial_template_validation_count": 6,
        "role_resolution_count": 6,
        "resolved_block_floors_match_count": 6,
        "strict_final_validation_count": 6,
        "read_only_execution_plan_count": 6,
        "physical_pair_equality_count": 3,
        "unique_complete_execution_identity_count": 6,
        "simulation_entry_count": 0,
        "future_output_root_created": False,
    }
    return {
        "all_passed": positive_controls == expected_positive
        and len(negative_controls) == 8,
        "mandatory_order": matrix["metric_configuration_resolution_contract"][
            "mandatory_order"
        ],
        "positive_controls": positive_controls,
        "expected_positive_controls": expected_positive,
        "read_only_execution_plans": plan_records,
        "pair_equalities": pair_equalities,
        "negative_control_count": len(negative_controls),
        "negative_controls": negative_controls,
    }


def _correct_observables(
    observables: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    result = copy.deepcopy(observables)
    by_id = {item["observable_id"]: item for item in result}
    operator = by_id["DISCRETE_OPERATOR_OUTPUTS"]
    operator["schema_version"] = "v1-semantic-over-v0-raw-payload"
    operator["meaning"] = (
        "raw operator inputs, direct terminal Maxwell defect, and per-species "
        "Dirac-link data required to reconstruct two independent H_C paths"
    )
    operator["required_components"] = [
        "terminal_equation_blocks[*].raw_packed_real_equation_defect",
        "discrete_closure[*].operator_inputs.p_previous",
        "discrete_closure[*].operator_inputs.p_current",
        "discrete_closure[*].operator_inputs.rho_previous",
        "discrete_closure[*].operator_inputs.rho_current",
        "discrete_closure[*].actual_discrete_operator_outputs.psi_plus_grad_contribution",
        "discrete_closure[*].actual_discrete_operator_outputs.psi_minus_grad_contribution",
        "discrete_closure[*].actual_discrete_operator_outputs.grad_theta_midpoint_registered",
        "discrete_closure[*].operator_inputs.a",
        "discrete_closure[*].operator_inputs.dt",
    ]
    closure = by_id["MAXWELL_TO_CONTINUITY_CLOSURE_RESIDUAL"]
    closure.update(
        {
            "schema_version": "v1-semantic-over-v0-raw-payload",
            "formula": (
                "A=roll(Rp_terminal_direct,1)-Rp_terminal_direct; "
                "B=(G1_raw-G0_raw)-a*dt*C_from_independently_recomputed_Dirac_current; "
                "C_independent=B-A"
            ),
            "aggregation": (
                "per-step L-infinity relative mismatch using max(|A|,|B|,role tolerance); "
                "maximum and consecutive-threshold run over all 16 steps"
            ),
            "payload_field": (
                "recomputed by raw_evidence_assembler_v3 from direct terminal P defect, "
                "raw p/rho, and per-species Dirac-link current contributions"
            ),
            "meaning": (
                "non-tautological comparison of independently sourced discrete Maxwell "
                "and charge-continuity/Gauss paths"
            ),
            "roundoff_bound": "none; gamma32 is advisory legacy payload data only",
            "legacy_Q_status": "OPERATOR_CONSISTENCY_GATE_ONLY_NOT_H_C_EVIDENCE",
        }
    )
    return result


def _runtime_authority_schema(
    implementation: Mapping[str, Any],
    matrix: Mapping[str, Any],
    identity: Mapping[str, Any],
) -> dict[str, Any]:
    run_matrix_bytes = canonical_json_bytes(matrix)
    identity_bytes = canonical_json_bytes(identity)
    artifact_bindings = {
        "run_matrix": {
            "relative_path": RUN_MATRIX_RELATIVE_PATH,
            "sha256": sha256_bytes(run_matrix_bytes),
        },
        "freeze_packet": {
            "relative_path": PACKET_RELATIVE_PATH,
            "sha256": None,
            "preparation_note": (
                "the independent v3 freeze review must bind the final packet bytes; "
                "the packet cannot self-authorize or embed its own digest"
            ),
        },
        "identity_manifest": {
            "relative_path": IDENTITY_RELATIVE_PATH,
            "sha256": sha256_bytes(identity_bytes),
        },
        "canonical_matrix": _file_binding(CANONICAL_MATRIX_RELATIVE_PATH),
    }
    expected_identity_fields = {
        record["run_id"]: {
            field: copy.deepcopy(record[field])
            for field in executor_v3.IDENTITY_DIAGNOSTIC_FIELDS
        }
        for record in matrix["records"]
    }
    proposed_authority = {
        "schema_id": "R13_MECHANISM_RUNTIME_EXECUTION_AUTHORITY_v3",
        "executor_id": executor_v3.EXECUTOR_ID,
        "execution_authorized": False,
        "one_execution_only": True,
        "automatic_retries_authorized": False,
        "exact_run_ids": copy.deepcopy(matrix["expected_run_id_order"]),
        "pair_run_ids": [
            [matrix["records"][index]["run_id"], matrix["records"][index + 1]["run_id"]]
            for index in (0, 2, 4)
        ],
        "artifact_bindings": artifact_bindings,
        "runtime_source_closure": copy.deepcopy(
            implementation["runtime_source_closure"]
        ),
        "runtime_source_closure_sha256": implementation["closure_sha256"],
        "expected_matrix_semantic_sha256": sha256_bytes(run_matrix_bytes),
        "expected_full_record_sha256_by_run_id": copy.deepcopy(
            matrix["full_record_identity_sha256_by_run_id"]
        ),
        "expected_identity_fields_by_run_id": expected_identity_fields,
        "expected_physical_configuration_sha256_by_run_id": copy.deepcopy(
            matrix["scientific_input_hash_contract"]
            ["physical_configuration_sha256_by_run_id"]
        ),
        "expected_scientific_input_sha256_by_run_id": copy.deepcopy(
            matrix["scientific_input_hash_contract"]
            ["scientific_input_sha256_by_run_id"]
        ),
        "expected_complete_execution_sha256_by_run_id": copy.deepcopy(
            matrix["complete_execution_identity_contract"]
            ["complete_execution_sha256_by_run_id"]
        ),
        "expected_resolved_metric_configuration_sha256_by_run_id": copy.deepcopy(
            matrix["metric_configuration_resolution_contract"]
            ["resolved_metric_configuration_sha256_by_run_id"]
        ),
        "canonical_directory_tree_sha256": EXPECTED_CANONICAL_DIRECTORY_TREE_SHA256,
        "canonical_directory_tree_sha256_domain": (
            "relative paths and file bytes below the immutable canonical output root"
        ),
        "experiment_output_root_relative_path": EXPERIMENT_OUTPUT_ROOT,
        "canonical_output_root_relative_path": CANONICAL_OUTPUT_ROOT,
    }
    return {
        "fixed_review_anchor_path": executor_custody_v3.REVIEW_ANCHOR_RELATIVE_PATH,
        "required_review_verdict": executor_custody_v3.EXPECTED_REVIEW_VERDICT,
        "required_review_field": executor_custody_v3.REVIEW_AUTHORITY_FIELD,
        "caller_override_of_anchor_path_or_authority": "FORBIDDEN",
        "required_review_authority_fields": [
            "schema_id",
            "executor_id",
            "execution_authorized",
            "one_execution_only",
            "automatic_retries_authorized",
            "exact_run_ids",
            "pair_run_ids",
            "artifact_bindings",
            "runtime_source_closure",
            "runtime_source_closure_sha256",
            "expected_matrix_semantic_sha256",
            "expected_full_record_sha256_by_run_id",
            "expected_identity_fields_by_run_id",
            "expected_physical_configuration_sha256_by_run_id",
            "expected_scientific_input_sha256_by_run_id",
            "expected_complete_execution_sha256_by_run_id",
            "expected_resolved_metric_configuration_sha256_by_run_id",
            "canonical_directory_tree_sha256",
            "canonical_directory_tree_sha256_domain",
            "experiment_output_root_relative_path",
            "canonical_output_root_relative_path",
        ],
        "proposed_review_authority": proposed_authority,
        "independent_review_must_bind_final_freeze_packet_bytes": True,
        "independent_review_must_set_execution_authorized_true_only_on_acceptance": True,
        "proposal_satisfies_runtime_validator_before_review": False,
        "execution_authorized_by_preparation": False,
    }


def build_packet(
    authority: Mapping[str, Any],
    implementation: Mapping[str, Any],
    matrix: Mapping[str, Any],
    identity: Mapping[str, Any],
) -> dict[str, Any]:
    predecessor = _load_json(PREDECESSOR_PACKET_RELATIVE_PATH)
    observables = _correct_observables(predecessor["mechanism_observable_registry"])
    runtime_authority = _runtime_authority_schema(implementation, matrix, identity)
    semantic_validation = semantic_v1.validate_semantic_contract()
    evidence_validation = evidence_v3.self_validate()
    classifier_validation = classifier_v3.self_validate()
    mutation_audit = _identity_mutation_diagnostic_audit(matrix)
    resolution_audit = _configuration_resolution_audit(matrix)
    source_attestation = _attest_preparation_loaded_sources(implementation)
    if semantic_validation or not all(evidence_validation.values()) or not all(
        classifier_validation.values()
    ) or not mutation_audit["all_passed"] or not resolution_audit[
        "all_passed"
    ] or not source_attestation["all_passed"]:
        raise ValueError("v3 preparation self-validation failed")
    decisions = [
        {"decision_id": decision_id, "passed": True}
        for decision_id in DECISION_IDS
    ]
    return {
        "schema_id": (
            "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_"
            "INSTRUMENTED_R13_MECHANISM_EXPERIMENT_NUMERICAL_FREEZE_PACKET_v3"
        ),
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "verdict": "PREPARED_PENDING_INDEPENDENT_REVIEW",
        "authority_basis": copy.deepcopy(dict(authority)),
        "predecessor_correction_scope": {
            "predecessor_packet": _file_binding(PREDECESSOR_PACKET_RELATIVE_PATH),
            "predecessor_review": _file_binding(PREDECESSOR_REVIEW_RELATIVE_PATH),
            "accepted_static_six_run_matrix_preserved": True,
            "route_A_or_design_reopened": False,
            "corrected_blocker_count": 1,
            "corrected_classes": [
                "partial-versus-resolved configuration typing and mandatory role-resolution-before-validation ordering",
            ],
            "v2_provenance_repairs_preserved": True,
        },
        "exact_run_matrix": {
            "path": RUN_MATRIX_RELATIVE_PATH,
            "sha256": sha256_bytes(canonical_json_bytes(matrix)),
            "record_count": 6,
            "instrumented_count": 3,
            "paired_control_count": 3,
            "scientific_configuration_changed_from_v0": False,
        },
        "expected_output_identity_manifest": {
            "path": IDENTITY_RELATIVE_PATH,
            "sha256": sha256_bytes(canonical_json_bytes(identity)),
            "role_payload_file_count": 12,
            "auxiliary_file_count": 2,
        },
        "scientific_input_identity_contract": copy.deepcopy(
            matrix["scientific_input_hash_contract"]
        ),
        "complete_execution_identity_contract": copy.deepcopy(
            matrix["complete_execution_identity_contract"]
        ),
        "metric_configuration_resolution_contract": {
            **copy.deepcopy(matrix["metric_configuration_resolution_contract"]),
            "partial_type": "FrozenRunTemplate",
            "resolved_type": "ResolvedRunConfiguration",
            "partial_may_omit_role_materialized_fields": [
                "block_scales",
                "block_floors",
            ],
            "resolved_must_contain_execution_fields": [
                "block_scales",
                "block_floors",
                "epsilon_dominance",
            ],
            "role_pair_instrumentation_metric_and_output_values_from_frozen_manifest_only": True,
            "caller_supplied_role_or_metric_floors_rejected": True,
            "unresolved_template_diagnostic": "UNRESOLVED_TEMPLATE_NOT_EXECUTABLE",
            "missing_role_floor_diagnostic": (
                "ROLE_RESOLUTION_MISSING_METRIC_BLOCK_FLOORS"
            ),
            "preparation_read_only_audit": resolution_audit,
        },
        "full_record_identity_sha256_by_run_id": copy.deepcopy(
            matrix["full_record_identity_sha256_by_run_id"]
        ),
        "source_closure_manifest": copy.deepcopy(dict(implementation)),
        "runtime_execution_authority_proposal": runtime_authority,
        "run_lookup_and_preflight_contract": {
            "public_execution_entrypoint": (
                f"{EXECUTOR_RELATIVE_PATH}:execute_frozen_matrix_once_v3"
            ),
            "caller_may_supply": ["repository root only"],
            "caller_may_not_supply": [
                "matrix",
                "record",
                "parent identity",
                "role",
                "block_floors",
                "block_scales",
                "metric configuration",
                "pair",
                "path",
                "schema",
                "implementation hash",
                "review anchor",
            ],
            "hard_preflight_before_output_root_creation": True,
            "all_twenty_v0_review_identity_fields_fail_closed": True,
            "identity_mutation_diagnostic_audit": mutation_audit,
            "configuration_resolution_audit": resolution_audit,
        },
        "equation_block_registry": copy.deepcopy(
            predecessor["equation_block_registry"]
        ),
        "equation_block_count": 8,
        "mechanism_observable_registry": observables,
        "mechanism_observable_count": 14,
        "metric_configuration_template": copy.deepcopy(
            predecessor["metric_configuration_template"]
        ),
        "raw_evidence_assembler_contract": {
            "assembler_id": evidence_v3.ASSEMBLER_ID,
            "source": _file_binding(ASSEMBLER_RELATIVE_PATH),
            "authoritative_entrypoint": "assemble_raw_evidence(repo_root)",
            "caller_path_overrides_authorized": False,
            "exact_raw_role_payload_file_count": 12,
            "exact_auxiliary_file_count": 2,
            "all_arrays_shapes_finiteness_and_cross_links_recomputed": True,
            "empty_summary_without_complete_raw_series": (
                "BLOCKED_REQUIRED_EVIDENCE_INCOMPLETE"
            ),
            "supplied_boolean_or_summary_authority": "NONE",
            "nonperturbation_recomputed_from_raw_trajectories": True,
        },
        "discrete_Maxwell_continuity_closure_freeze": {
            "decision_bearing_H_C": {
                "path_A": "divergence of directly stored terminal P_LONGITUDINAL_MAXWELL defect",
                "path_B": (
                    "Gauss drift minus continuity increment using current independently "
                    "recomputed from per-species Dirac link contributions"
                ),
                "mismatch": "path_B - path_A",
                "registered_Maxwell_source_reused_in_path_B": False,
                "gamma32_or_gamma_n_used": False,
            },
            "legacy_Q": copy.deepcopy(semantic_v1.LEGACY_Q),
            "semantic_source": _file_binding(SEMANTIC_RELATIVE_PATH),
        },
        "classifier_freeze": {
            "classifier_id": classifier_v3.CLASSIFIER_ID,
            "source": _file_binding(CLASSIFIER_RELATIVE_PATH),
            "authoritative_entrypoint": "classify_from_raw_payloads(repo_root)",
            "public_precomputed_evidence_classifier_exists": False,
            "precedence": list(classifier_v3.CLASSIFIER_PRECEDENCE),
            "support_constants": copy.deepcopy(semantic_v1.SUPPORT_CONSTANTS_V1),
            "support_constant_provenance": copy.deepcopy(
                list(semantic_v1.SUPPORT_CONSTANT_PROVENANCE)
            ),
            "support_constant_count": 23,
            "individual_H_A_through_H_D_decisions_required": True,
            "ordered_supported_mechanism_ids_required": True,
            "H_E_requires_complete_admissible_raw_evidence": True,
        },
        "freeze_adversarial_control_registry": copy.deepcopy(
            list(semantic_v1.FULL_ADVERSARIAL_REGISTRY_V1)
        ),
        "freeze_adversarial_control_count": 41,
        "identity_mutation_control_count": len(
            semantic_v1.IDENTITY_MUTATION_FIELDS
        ),
        "review_missing_control_count": len(
            semantic_v1.MISSING_REVIEW_CONTROL_IDS
        ),
        "preparation_self_validation": {
            "semantic_contract_diagnostics": semantic_validation,
            "raw_evidence_assembler": evidence_validation,
            "classifier": classifier_validation,
            "identity_mutations": mutation_audit,
            "configuration_resolution": resolution_audit,
            "runtime_loaded_source_identity": source_attestation,
            "simulation_invocation_count": 0,
            "future_output_root_created": False,
        },
        "output_custody_and_execution_freeze": {
            "canonical_output_root": CANONICAL_OUTPUT_ROOT,
            "canonical_authority_inventory_digest": EXPECTED_CANONICAL_ROOT_DIGEST,
            "canonical_directory_tree_sha256": EXPECTED_CANONICAL_DIRECTORY_TREE_SHA256,
            "new_output_root": EXPERIMENT_OUTPUT_ROOT,
            "new_output_root_must_not_exist_before_execution": True,
            "execution_authorized_now": False,
            "retry": "FORBIDDEN",
            "overwrite": "FORBIDDEN",
            "dynamic_run_discovery": "FORBIDDEN",
            "classification_during_execution_authorized": False,
        },
        "decision_count": len(decisions),
        "passed_decision_count": len(decisions),
        "failed_decision_ids": [],
        "decisions": decisions,
        "selected_next_target": REVIEW_TARGET,
        "post_acceptance_target": POST_ACCEPTANCE_TARGET,
        "authority_boundary": {
            "numerical_freeze_v2_blocked_executor_preflight_configuration": True,
            "numerical_freeze_v3_prepared": True,
            "numerical_freeze_v3_independently_accepted": False,
            "experiment_execution_authorized": False,
            "experiment_execution_performed": False,
            "canonical_execution_count": 1,
            "canonical_robustness": "NUMERICALLY_BLOCKED",
            "blocked_row": "R13_CORNER_STRONG_LOW",
            "root_mechanism": "UNRESOLVED",
            "materiality": "NOT_EVALUATED_NUMERICAL_BLOCK",
            "robustness_reclassification_authorized": False,
            "materiality_evaluation_authorized": False,
            "threshold_change_from_future_data_authorized": False,
            "new_E_REPRO_claim": False,
        },
        "claim_ceiling": classifier_v3.CLAIM_CEILING,
        "nonclaims": [
            "no simulation or mechanism output was created",
            "no canonical record was changed or rerun",
            "no R13 mechanism was identified",
            "no robustness or materiality classification changed",
            "no new E-REPRO, pillar, seam, C_k, CCFT, or master-action claim",
            "no repository-wide green claim",
        ],
        "environment_identity": copy.deepcopy(predecessor["environment_identity"]),
    }


def build_manifest(
    packet: Mapping[str, Any],
    matrix: Mapping[str, Any],
    identity: Mapping[str, Any],
    implementation: Mapping[str, Any],
) -> dict[str, Any]:
    return {
        "schema_id": (
            "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_"
            "INSTRUMENTED_R13_MECHANISM_EXPERIMENT_NUMERICAL_FREEZE_MANIFEST_v3"
        ),
        "captured_at_utc": CAPTURED_AT_UTC,
        "generator": _file_binding(SCRIPT_RELATIVE_PATH),
        "source_closure_manifest": copy.deepcopy(dict(implementation)),
        "authority_inputs": [
            _file_binding(DESIGN_REVIEW_RELATIVE_PATH),
            _file_binding(PREDECESSOR_REVIEW_RELATIVE_PATH),
            _file_binding(PREDECESSOR_MATRIX_RELATIVE_PATH),
            _file_binding(CANONICAL_MATRIX_RELATIVE_PATH),
        ],
        "packet": {
            "path": PACKET_RELATIVE_PATH,
            "sha256": sha256_bytes(canonical_json_bytes(packet)),
        },
        "run_matrix": {
            "path": RUN_MATRIX_RELATIVE_PATH,
            "sha256": sha256_bytes(canonical_json_bytes(matrix)),
            "record_count": 6,
        },
        "expected_output_identity_manifest": {
            "path": IDENTITY_RELATIVE_PATH,
            "sha256": sha256_bytes(canonical_json_bytes(identity)),
            "role_payload_file_count": 12,
        },
        "future_experiment_output_root": EXPERIMENT_OUTPUT_ROOT,
        "future_experiment_output_root_absent": not (
            REPO_ROOT / EXPERIMENT_OUTPUT_ROOT
        ).exists(),
        "canonical_authority_inventory_digest": EXPECTED_CANONICAL_ROOT_DIGEST,
        "canonical_directory_tree_sha256": EXPECTED_CANONICAL_DIRECTORY_TREE_SHA256,
        "decision_count": len(DECISION_IDS),
        "selected_next_target": REVIEW_TARGET,
        "execution_authorized": False,
    }


def build_report(
    packet: Mapping[str, Any],
    matrix: Mapping[str, Any],
    identity: Mapping[str, Any],
    manifest: Mapping[str, Any],
) -> dict[str, Any]:
    return {
        "schema_id": (
            "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_"
            "INSTRUMENTED_R13_MECHANISM_EXPERIMENT_NUMERICAL_FREEZE_PACKET_20260716_v3"
        ),
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "verdict": "PREPARED_PENDING_INDEPENDENT_REVIEW",
        "artifacts": {
            "packet": {"path": PACKET_RELATIVE_PATH, "sha256": sha256_bytes(canonical_json_bytes(packet))},
            "run_matrix": {"path": RUN_MATRIX_RELATIVE_PATH, "sha256": sha256_bytes(canonical_json_bytes(matrix))},
            "expected_output_identity": {"path": IDENTITY_RELATIVE_PATH, "sha256": sha256_bytes(canonical_json_bytes(identity))},
            "manifest": {"path": MANIFEST_RELATIVE_PATH, "sha256": sha256_bytes(canonical_json_bytes(manifest))},
            "generator": _file_binding(SCRIPT_RELATIVE_PATH),
            "executor": _file_binding(EXECUTOR_RELATIVE_PATH),
            "raw_evidence_assembler": _file_binding(ASSEMBLER_RELATIVE_PATH),
            "classifier": _file_binding(CLASSIFIER_RELATIVE_PATH),
            "semantic_contract": _file_binding(SEMANTIC_RELATIVE_PATH),
        },
        "freeze_summary": {
            "run_count": 6,
            "instrumented_run_count": 3,
            "paired_control_count": 3,
            "role_payload_file_count": 12,
            "observable_count": 14,
            "solver_block_count": 8,
            "support_constant_count": 23,
            "support_constant_provenance_count": 23,
            "adversarial_control_count": 41,
            "identity_mutation_count": 20,
            "identity_mutation_exact_diagnostic_count": 20,
            "runtime_source_module_count": 8,
            "scientific_input_reconstruction_count": 6,
            "unique_scientific_input_count": 3,
            "complete_execution_identity_reconstruction_count": 6,
            "unique_complete_execution_identity_count": 6,
            "partial_template_validation_count": 6,
            "role_resolution_count": 6,
            "resolved_configuration_strict_validation_count": 6,
            "read_only_execution_plan_count": 6,
            "configuration_resolution_negative_control_count": 8,
            "simulation_entry_count": 0,
            "input_exclusion_field_count": 0,
            "gamma32_mechanism_decision_count": 0,
        },
        "decision_ids": list(DECISION_IDS),
        "decision_count": len(DECISION_IDS),
        "passed_decision_count": len(DECISION_IDS),
        "failed_decision_ids": [],
        "preparation_validation_status": packet["preparation_self_validation"],
        "selected_next_target": REVIEW_TARGET,
        "authority_boundary": packet["authority_boundary"],
        "claim_ceiling": packet["claim_ceiling"],
        "nonclaims": packet["nonclaims"],
    }


def build_artifacts() -> tuple[
    dict[str, Any],
    dict[str, Any],
    dict[str, Any],
    dict[str, Any],
    dict[str, Any],
]:
    if (REPO_ROOT / EXPERIMENT_OUTPUT_ROOT).exists():
        raise ValueError("future mechanism output root must remain absent")
    if canonical_v0.canonical_root_digest() != EXPECTED_CANONICAL_ROOT_DIGEST:
        raise ValueError("canonical authority inventory digest changed")
    if (
        canonical_v0.canonical_directory_tree_sha256()
        != EXPECTED_CANONICAL_DIRECTORY_TREE_SHA256
    ):
        raise ValueError("canonical directory tree digest changed")
    authority = _authority_basis()
    implementation = _runtime_source_binding()
    matrix = _build_run_matrix(implementation)
    identity = _build_identity(matrix)
    packet = build_packet(authority, implementation, matrix, identity)
    manifest = build_manifest(packet, matrix, identity, implementation)
    report = build_report(packet, matrix, identity, manifest)
    return packet, matrix, identity, manifest, report


def artifact_bytes() -> dict[str, bytes]:
    packet, matrix, identity, manifest, report = build_artifacts()
    return {
        PACKET_RELATIVE_PATH: canonical_json_bytes(packet),
        RUN_MATRIX_RELATIVE_PATH: canonical_json_bytes(matrix),
        IDENTITY_RELATIVE_PATH: canonical_json_bytes(identity),
        MANIFEST_RELATIVE_PATH: canonical_json_bytes(manifest),
        REPORT_RELATIVE_PATH: canonical_json_bytes(report),
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Prepare corrected R13 mechanism numerical-freeze v3."
    )
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    canonical_before = canonical_v0.canonical_root_digest()
    tree_before = canonical_v0.canonical_directory_tree_sha256()
    try:
        artifacts = artifact_bytes()
    except (OSError, ValueError, KeyError, TypeError, json.JSONDecodeError) as error:
        print(f"ERROR: {error}", file=sys.stderr)
        return 1
    if args.write:
        for relative_path, raw in artifacts.items():
            path = REPO_ROOT / relative_path
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(raw)
    elif args.check:
        stale = [
            relative_path
            for relative_path, raw in artifacts.items()
            if not (REPO_ROOT / relative_path).is_file()
            or (REPO_ROOT / relative_path).read_bytes() != raw
        ]
        if stale:
            print(f"stale or missing numerical-freeze-v3 artifacts: {stale}", file=sys.stderr)
            return 1
    else:
        sys.stdout.buffer.write(artifacts[REPORT_RELATIVE_PATH])
    if canonical_v0.canonical_root_digest() != canonical_before:
        print("ERROR: canonical authority inventory changed", file=sys.stderr)
        return 1
    if canonical_v0.canonical_directory_tree_sha256() != tree_before:
        print("ERROR: canonical directory tree changed", file=sys.stderr)
        return 1
    if (REPO_ROOT / EXPERIMENT_OUTPUT_ROOT).exists():
        print("ERROR: preparation created future experiment root", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
