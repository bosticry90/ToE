from __future__ import annotations

"""Independent, read-only review of the R13 numerical-freeze-v2 proposal.

The reviewer does not import the v2 preparation generator and independently
reconstructs the scientific and complete execution identities.  It may write
only the fixed review anchor.  It never invokes the evolution, creates the
future experiment root, or writes any role payload.
"""

import argparse
import ast
import copy
import hashlib
import importlib
import importlib.machinery
import inspect
import json
import math
import subprocess
import sys
import types
import unicodedata
from collections.abc import Mapping, Sequence
from pathlib import Path, PurePosixPath
from typing import Any

import numpy as np

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_classifier_v2
    as classifier_v2,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_executor_custody_v2
    as custody_v2,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_executor_v2
    as executor_v2,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_implementation_v0
    as implementation_v0,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_numerical_freeze_packet_v0
    as canonical_v0,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_raw_evidence_assembler_v2
    as evidence_v2,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_semantic_contract_v1
    as semantic_v1,
)


REPO_ROOT = find_repo_root(Path(__file__))
CAPTURED_AT_UTC = "2026-07-16T00:00:00Z"
TARGET = (
    "review_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
    "instrumented_r13_mechanism_experiment_numerical_freeze_packet_v2_result"
)
ACCEPT_VERDICT = (
    "ACCEPT_INSTRUMENTED_R13_MECHANISM_EXPERIMENT_NUMERICAL_FREEZE"
)
ACCEPTED_NEXT_TARGET = (
    "execute_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
    "instrumented_r13_mechanism_experiment_v0_once"
)
BLOCKED_NEXT_TARGET = (
    "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
    "instrumented_r13_mechanism_experiment_numerical_freeze_packet_v3"
)
SCHEMA_ID = (
    "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_"
    "INSTRUMENTED_R13_MECHANISM_EXPERIMENT_NUMERICAL_FREEZE_PACKET_REVIEW_"
    "20260716_v2"
)
REPORT_RELATIVE_PATH = custody_v2.REVIEW_ANCHOR_RELATIVE_PATH
PACKET_RELATIVE_PATH = custody_v2.FREEZE_PACKET_RELATIVE_PATH
MATRIX_RELATIVE_PATH = custody_v2.RUN_MATRIX_RELATIVE_PATH
IDENTITY_RELATIVE_PATH = custody_v2.IDENTITY_MANIFEST_RELATIVE_PATH
MANIFEST_RELATIVE_PATH = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-INSTRUMENTED-R13-MECHANISM-EXPERIMENT-NUMERICAL-FREEZE-"
    "MANIFEST-v2.json"
)
PREPARATION_REPORT_RELATIVE_PATH = (
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
    "ROBUSTNESS_INSTRUMENTED_R13_MECHANISM_EXPERIMENT_NUMERICAL_FREEZE_PACKET_"
    "20260716_v2.json"
)
GENERATOR_MODULE = (
    "formal.python.tools."
    "dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
    "instrumented_r13_mechanism_experiment_numerical_freeze_packet_v2"
)
V1_GENERATOR_MODULE = (
    "formal.python.tools."
    "dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
    "instrumented_r13_mechanism_experiment_numerical_freeze_packet_v1"
)

EXPECTED_ARTIFACT_SHA256 = {
    PACKET_RELATIVE_PATH: "0c59e39491d7e055b0897b67f6665dbdfb6fbc1824c089bab4bec85829738656",
    MATRIX_RELATIVE_PATH: "db18c3a980b81e4ccc8f52710de952abcf6f1409ce2b1c4f8b714df38c454f44",
    IDENTITY_RELATIVE_PATH: "0796aa856ee7a5d78cafca56945b91766ae382c087ca88ec4f0666c1368b668e",
    MANIFEST_RELATIVE_PATH: "2f28c6078dd84ed9f123700f1bfa5052a644b8e2ceab49babccfd8efd53ed98d",
    PREPARATION_REPORT_RELATIVE_PATH: "8f6e1516f91b7c277a19421ff6d39c866eb0eaccf9e4f31ee44adfc794ce8d07",
}


def _normalize(value: Any) -> Any:
    if isinstance(value, str):
        return unicodedata.normalize("NFC", value)
    if value is None or isinstance(value, (bool, int)):
        return value
    if isinstance(value, float):
        if not math.isfinite(value):
            raise ValueError("canonical JSON forbids nonfinite floats")
        return value
    if isinstance(value, Mapping):
        return {str(key): _normalize(item) for key, item in value.items()}
    if isinstance(value, (list, tuple)):
        return [_normalize(item) for item in value]
    raise TypeError(f"unsupported canonical JSON value: {type(value)!r}")


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


def load_json(relative_path: str) -> dict[str, Any]:
    value = json.loads((REPO_ROOT / relative_path).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise TypeError(f"expected JSON object: {relative_path}")
    return value


def _independent_physical_core(record: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "schema_id": "DIRAC_MAXWELL_R13_MECHANISM_PHYSICAL_CONFIGURATION_CORE_v2",
        "canonical_parent": {
            "run_id": record["parent_canonical_run_id"],
            "input_hash": record["parent_canonical_input_hash"],
            "output_path": record["parent_canonical_output_path"],
            "output_sha256": record["parent_canonical_output_sha256"],
            "initial_condition_identity": record["parent_initial_condition_identity"],
        },
        "physical_model": {
            "scientific_row_id": record["scientific_row_id"],
            "requested_axis_values": copy.deepcopy(record["requested_axis_values"]),
            "row": copy.deepcopy(record["row"]),
            "model_class": record["model_class"],
        },
        "numerical_configuration": {
            "numerical_method": record["numerical_method"],
            "grid_size": record["grid_size"],
            "n": record["n"],
            "time_step": record["time_step"],
            "dt": record["dt"],
            "duration": record["duration"],
            "solver_tolerance": record["solver_tolerance"],
            "tolerance": record["tolerance"],
            "iteration_cap": record["iteration_cap"],
            "max_iterations": record["max_iterations"],
            "accepted_step_count": record["accepted_step_count"],
            "checkpoint_count_including_initial": record[
                "checkpoint_count_including_initial"
            ],
        },
    }


def _independent_scientific_core(record: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "schema_id": "DIRAC_MAXWELL_R13_MECHANISM_SCIENTIFIC_INPUT_CORE_v2",
        "physical_configuration_core": _independent_physical_core(record),
    }


def _independent_complete_execution_core(
    record: Mapping[str, Any], closure_sha256: str
) -> dict[str, Any]:
    scientific_sha256 = sha256_bytes(
        canonical_json_bytes(_independent_scientific_core(record))
    )
    return {
        "schema_id": "DIRAC_MAXWELL_R13_MECHANISM_COMPLETE_EXECUTION_IDENTITY_v2",
        "scientific_input_sha256": scientific_sha256,
        "runtime_source_closure_sha256": closure_sha256,
        "run_identity": {
            "experiment_id": record["experiment_id"],
            "run_id": record["run_id"],
            "execution_ordinal_zero_based": record["execution_ordinal_zero_based"],
            "execution_role": record["execution_role"],
            "mechanism_configuration_role": record["mechanism_configuration_role"],
            "paired_run_id": record["paired_run_id"],
        },
        "instrumentation_contract": {
            "enabled": record["instrumentation_enabled"],
            "read_only": record["instrumentation_read_only"],
            "observable_ids": copy.deepcopy(record["instrumented_observable_ids"]),
            "trajectory_identity_required": record["trajectory_identity_required"],
            "supporting_tolerance_ladder_module_enabled": record[
                "supporting_tolerance_ladder_module_enabled"
            ],
            "supporting_duration_scaling_module_enabled": record[
                "supporting_duration_scaling_module_enabled"
            ],
        },
        "output_contract": {
            "schema_version": record["output_schema_version"],
            "payload_identity_contract": record["payload_identity_contract"],
            "json_relative_output_path": record["json_relative_output_path"],
            "json_safe_filename": record["json_safe_filename"],
            "npz_relative_output_path": record["npz_relative_output_path"],
            "npz_safe_filename": record["npz_safe_filename"],
        },
        "v2_pipeline_identity": {
            "executor_id": record["executor_id"],
            "executor_sha256": record["executor_sha256"],
            "raw_evidence_assembler_id": record["raw_evidence_assembler_id"],
            "raw_evidence_assembler_sha256": record[
                "raw_evidence_assembler_sha256"
            ],
            "classifier_id": record["classifier_id"],
            "classifier_sha256": record["classifier_sha256"],
            "semantic_contract_id": record["semantic_contract_id"],
            "semantic_contract_sha256": record["semantic_contract_sha256"],
        },
        "historical_implementation_identity": {
            "implementation_id": record["implementation_id"],
            "implementation_sha256": record["implementation_sha256"],
        },
    }


def _independent_full_record_sha256(record: Mapping[str, Any]) -> str:
    return sha256_bytes(
        canonical_json_bytes(
            {
                "schema_id": "DIRAC_MAXWELL_R13_MECHANISM_FULL_MATRIX_RECORD_IDENTITY_v2",
                "record": copy.deepcopy(dict(record)),
            }
        )
    )


def audit_artifact_freshness() -> dict[str, Any]:
    records = []
    for relative_path, expected_sha256 in EXPECTED_ARTIFACT_SHA256.items():
        raw = (REPO_ROOT / relative_path).read_bytes()
        actual_sha256 = sha256_bytes(raw)
        records.append(
            {
                "relative_path": relative_path,
                "expected_sha256": expected_sha256,
                "actual_sha256": actual_sha256,
                "exact": actual_sha256 == expected_sha256,
            }
        )
    manifest = load_json(MANIFEST_RELATIVE_PATH)
    preparation_report = load_json(PREPARATION_REPORT_RELATIVE_PATH)
    cross_bindings_exact = (
        manifest["packet"]["sha256"]
        == EXPECTED_ARTIFACT_SHA256[PACKET_RELATIVE_PATH]
        and manifest["run_matrix"]["sha256"]
        == EXPECTED_ARTIFACT_SHA256[MATRIX_RELATIVE_PATH]
        and manifest["expected_output_identity_manifest"]["sha256"]
        == EXPECTED_ARTIFACT_SHA256[IDENTITY_RELATIVE_PATH]
        and preparation_report["artifacts"]["manifest"]["sha256"]
        == EXPECTED_ARTIFACT_SHA256[MANIFEST_RELATIVE_PATH]
    )
    v2_process = subprocess.run(
        [sys.executable, "-B", "-m", GENERATOR_MODULE, "--check"],
        cwd=REPO_ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    v1_process = subprocess.run(
        [sys.executable, "-B", "-m", V1_GENERATOR_MODULE, "--check"],
        cwd=REPO_ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    return {
        "artifact_count": len(records),
        "exact_artifact_count": sum(item["exact"] for item in records),
        "records": records,
        "cross_bindings_exact": cross_bindings_exact,
        "v2_generator_imported_by_reviewer": False,
        "v2_subprocess_regeneration_returncode": v2_process.returncode,
        "v2_subprocess_regeneration_byte_exact": v2_process.returncode == 0,
        "v2_subprocess_stderr": v2_process.stderr.strip(),
        "v1_subprocess_regeneration_returncode": v1_process.returncode,
        "v1_remains_stale": v1_process.returncode != 0,
        "v1_stale_diagnostic_preserved": (
            "stale or missing numerical-freeze-v1 artifacts" in v1_process.stderr
        ),
        "v1_subprocess_stderr": v1_process.stderr.strip(),
    }


def audit_independent_identities(
    packet: Mapping[str, Any], matrix: Mapping[str, Any]
) -> dict[str, Any]:
    records = matrix["records"]
    closure = packet["source_closure_manifest"]["runtime_source_closure"]
    closure_sha256 = sha256_bytes(canonical_json_bytes(closure))
    registered_closure_sha256 = packet["source_closure_manifest"]["closure_sha256"]
    scientific_map = matrix["scientific_input_hash_contract"][
        "scientific_input_sha256_by_run_id"
    ]
    physical_map = matrix["scientific_input_hash_contract"][
        "physical_configuration_sha256_by_run_id"
    ]
    complete_map = matrix["complete_execution_identity_contract"][
        "complete_execution_sha256_by_run_id"
    ]
    full_map = matrix["full_record_identity_sha256_by_run_id"]
    review_records = []
    for record in records:
        run_id = record["run_id"]
        physical = _independent_physical_core(record)
        scientific = _independent_scientific_core(record)
        complete = _independent_complete_execution_core(record, closure_sha256)
        physical_sha256 = sha256_bytes(canonical_json_bytes(physical))
        scientific_sha256 = sha256_bytes(canonical_json_bytes(scientific))
        complete_sha256 = sha256_bytes(canonical_json_bytes(complete))
        full_sha256 = _independent_full_record_sha256(record)
        scientific_exact = (
            physical == record["physical_configuration_core"]
            and physical_sha256 == record["physical_configuration_core_sha256"]
            and physical_sha256 == physical_map[run_id]
            and scientific == record["scientific_input_core"]
            and scientific_sha256 == record["scientific_input_core_sha256"]
            and scientific_sha256 == record["input_hash"]
            and scientific_sha256 == scientific_map[run_id]
        )
        complete_exact = (
            complete == record["complete_execution_identity_core"]
            and complete_sha256 == record["complete_execution_identity_sha256"]
            and complete_sha256 == complete_map[run_id]
        )
        full_exact = full_sha256 == full_map[run_id]
        review_records.append(
            {
                "run_id": run_id,
                "physical_configuration_sha256": physical_sha256,
                "scientific_input_sha256": scientific_sha256,
                "complete_execution_identity_sha256": complete_sha256,
                "full_record_identity_sha256": full_sha256,
                "physical_and_scientific_identity_exact": scientific_exact,
                "complete_execution_identity_exact": complete_exact,
                "full_record_identity_exact": full_exact,
            }
        )
    by_id = {record["run_id"]: record for record in review_records}
    pair_records = []
    for instrumented_id, control_id in custody_v2.PAIR_RUN_IDS:
        instrumented = by_id[instrumented_id]
        control = by_id[control_id]
        pair_records.append(
            {
                "instrumented_run_id": instrumented_id,
                "control_run_id": control_id,
                "physical_configuration_exact": instrumented[
                    "physical_configuration_sha256"
                ]
                == control["physical_configuration_sha256"],
                "scientific_input_exact": instrumented[
                    "scientific_input_sha256"
                ]
                == control["scientific_input_sha256"],
                "complete_execution_identity_distinct": instrumented[
                    "complete_execution_identity_sha256"
                ]
                != control["complete_execution_identity_sha256"],
            }
        )
    scientific_values = [item["scientific_input_sha256"] for item in review_records]
    complete_values = [
        item["complete_execution_identity_sha256"] for item in review_records
    ]
    source_independent = all(
        closure_sha256 not in canonical_json_bytes(_independent_scientific_core(record)).decode(
            "utf-8"
        )
        and "runtime_source_closure" not in _independent_scientific_core(record)
        for record in records
    )
    return {
        "run_id_order_exact": tuple(record["run_id"] for record in records)
        == custody_v2.EXACT_RUN_IDS,
        "runtime_source_closure_reconstructed_sha256": closure_sha256,
        "registered_runtime_source_closure_sha256": registered_closure_sha256,
        "runtime_source_closure_exact": closure_sha256
        == registered_closure_sha256
        == matrix["runtime_source_closure_sha256"],
        "scientific_input_reconstruction_count": sum(
            item["physical_and_scientific_identity_exact"]
            for item in review_records
        ),
        "unique_scientific_input_count": len(set(scientific_values)),
        "complete_execution_identity_reconstruction_count": sum(
            item["complete_execution_identity_exact"] for item in review_records
        ),
        "full_record_identity_reconstruction_count": sum(
            item["full_record_identity_exact"] for item in review_records
        ),
        "unique_complete_execution_identity_count": len(set(complete_values)),
        "scientific_identity_source_independent": source_independent,
        "pair_count": len(pair_records),
        "pair_records": pair_records,
        "all_three_pairs_scientifically_identical": all(
            item["physical_configuration_exact"]
            and item["scientific_input_exact"]
            for item in pair_records
        ),
        "all_three_pair_execution_identities_distinct": all(
            item["complete_execution_identity_distinct"] for item in pair_records
        ),
        "records": review_records,
    }


def _loaded_module_record(binding: Mapping[str, Any]) -> dict[str, Any]:
    module = importlib.import_module(str(binding["module_name"]))
    expected_path = (REPO_ROOT / str(binding["relative_path"])).resolve()
    spec = module.__spec__
    origin = Path(spec.origin).resolve() if spec and spec.origin else None
    loader_type = type(spec.loader).__name__ if spec else None
    actual_sha256 = sha256_bytes(expected_path.read_bytes())
    return {
        "module_name": module.__name__,
        "relative_path": binding["relative_path"],
        "expected_sha256": binding["sha256"],
        "loaded_sha256": actual_sha256,
        "expected_loader_type": binding["loader_type"],
        "loaded_loader_type": loader_type,
        "name_exact": module.__name__ == binding["module_name"],
        "path_exact": Path(module.__file__).resolve() == expected_path,
        "origin_exact": origin == expected_path,
        "bytes_exact": actual_sha256 == binding["sha256"],
        "loader_exact": loader_type == binding["loader_type"],
    }


def audit_runtime_source_closure(packet: Mapping[str, Any]) -> dict[str, Any]:
    manifest = packet["source_closure_manifest"]
    closure = manifest["runtime_source_closure"]
    authority = packet["runtime_execution_authority_proposal"][
        "proposed_review_authority"
    ]
    bindings = closure["modules"]
    loaded = [_loaded_module_record(binding) for binding in bindings]
    all_loaded_exact = all(
        item["name_exact"]
        and item["path_exact"]
        and item["origin_exact"]
        and item["bytes_exact"]
        and item["loader_exact"]
        for item in loaded
    )
    module_by_name = {
        binding["module_name"]: importlib.import_module(binding["module_name"])
        for binding in bindings
    }
    v0 = module_by_name[custody_v2.V0_IMPLEMENTATION_MODULE]
    historical_evolution = module_by_name[custody_v2.HISTORICAL_EVOLUTION_MODULE]
    historical_pack = module_by_name[custody_v2.HISTORICAL_PACK_MODULE]
    loaded_evolution, loaded_pack = v0._load_historical_implementation()
    historical_binding_exact = (
        loaded_evolution is historical_evolution
        and loaded_pack is historical_pack
        and getattr(historical_evolution, "accepted_v0", None) is historical_pack
    )

    probe_binding = next(
        binding
        for binding in bindings
        if binding["module_name"] == custody_v2.CLASSIFIER_MODULE
    )
    expected_path = (REPO_ROOT / probe_binding["relative_path"]).resolve()
    shadow_path = REPO_ROOT / "HOSTILE-IMPORT-SHADOW.py"
    hostile = types.ModuleType(probe_binding["module_name"])
    hostile.__file__ = str(shadow_path)
    hostile.__spec__ = importlib.machinery.ModuleSpec(
        hostile.__name__,
        importlib.machinery.SourceFileLoader(hostile.__name__, str(shadow_path)),
        origin=str(shadow_path),
    )
    hostile_rejected = False
    hostile_diagnostic = None
    try:
        executor_v2._attest_loaded_module(REPO_ROOT, hostile, probe_binding)
    except executor_v2.RuntimeCustodyError as error:
        hostile_rejected = True
        hostile_diagnostic = str(error)

    actual_module = module_by_name[custody_v2.CLASSIFIER_MODULE]
    wrong_bytes_binding = copy.deepcopy(probe_binding)
    wrong_bytes_binding["sha256"] = "0" * 64
    wrong_bytes_rejected = False
    wrong_bytes_diagnostic = None
    try:
        executor_v2._attest_loaded_module(
            REPO_ROOT, actual_module, wrong_bytes_binding
        )
    except executor_v2.RuntimeCustodyError as error:
        wrong_bytes_rejected = True
        wrong_bytes_diagnostic = str(error)

    wrong_loader = types.ModuleType(probe_binding["module_name"])
    wrong_loader.__file__ = str(expected_path)
    wrong_loader.__spec__ = importlib.machinery.ModuleSpec(
        wrong_loader.__name__, None, origin=str(expected_path)
    )
    wrong_loader_rejected = False
    wrong_loader_diagnostic = None
    try:
        executor_v2._attest_loaded_module(REPO_ROOT, wrong_loader, probe_binding)
    except executor_v2.RuntimeCustodyError as error:
        wrong_loader_rejected = True
        wrong_loader_diagnostic = str(error)

    closure_sha256 = sha256_bytes(canonical_json_bytes(closure))
    return {
        "frozen_module_count": len(bindings),
        "loaded_module_count": len(loaded),
        "module_name_order_exact": tuple(
            binding["module_name"] for binding in bindings
        )
        == custody_v2.REQUIRED_MODULE_NAMES,
        "closure_sha256": closure_sha256,
        "closure_digest_exact": closure_sha256
        == manifest["closure_sha256"]
        == authority["runtime_source_closure_sha256"],
        "authority_closure_exact": authority["runtime_source_closure"] == closure,
        "all_loaded_paths_bytes_and_loaders_exact": all_loaded_exact,
        "historical_object_binding_exact": historical_binding_exact,
        "hostile_same_name_wrong_path_rejected": hostile_rejected,
        "hostile_same_name_wrong_path_diagnostic": hostile_diagnostic,
        "wrong_frozen_bytes_rejected": wrong_bytes_rejected,
        "wrong_frozen_bytes_diagnostic": wrong_bytes_diagnostic,
        "wrong_loader_rejected": wrong_loader_rejected,
        "wrong_loader_diagnostic": wrong_loader_diagnostic,
        "git_identity_decision_bearing": manifest[
            "git_commit_or_blob_identity_decision_bearing"
        ],
        "loaded_modules": loaded,
    }


def audit_twenty_identity_mutations(
    packet: Mapping[str, Any], matrix: Mapping[str, Any]
) -> dict[str, Any]:
    output_root = REPO_ROOT / custody_v2.EXPERIMENT_OUTPUT_ROOT_RELATIVE_PATH
    authority = packet["runtime_execution_authority_proposal"][
        "proposed_review_authority"
    ]
    registry = {
        item["mutation"]["field"]: item
        for item in packet["freeze_adversarial_control_registry"]
        if item["category"] == "V0_REVIEW_EXACT_MATRIX_IDENTITY_MUTATION"
    }
    results = []
    for field in semantic_v1.IDENTITY_MUTATION_FIELDS:
        candidate = copy.deepcopy(matrix)
        original = matrix["records"][0]
        candidate_record = candidate["records"][0]
        candidate_record[field] = copy.deepcopy(registry[field]["mutation"]["replacement"])
        changed_fields = [
            key
            for key in original
            if canonical_json_bytes(original[key])
            != canonical_json_bytes(candidate_record[key])
        ]
        matrix_diagnostics = executor_v2.strict_validate_matrix(candidate, matrix)
        authority_diagnostics = executor_v2.strict_validate_matrix(
            candidate, authority
        )
        expected = registry[field]["expected_first_diagnostic"]
        expected_final = registry[field]["expected_decision_change"]
        results.append(
            {
                "field": field,
                "changed_top_level_record_fields": changed_fields,
                "exactly_one_registered_premise_changed": changed_fields == [field],
                "registered_first_diagnostic": expected,
                "matrix_first_diagnostic": (
                    matrix_diagnostics[0] if matrix_diagnostics else None
                ),
                "authority_first_diagnostic": (
                    authority_diagnostics[0] if authority_diagnostics else None
                ),
                "exact_first_diagnostic": matrix_diagnostics == [expected]
                and authority_diagnostics == [expected],
                "registered_final_block_decision": expected_final,
                "final_block_decision_exact": expected_final
                == "BLOCKED_RUN_IDENTITY"
                and bool(matrix_diagnostics),
                "simulation_entry_count": 0,
                "output_root_absent_after_probe": not output_root.exists(),
            }
        )
    return {
        "registered_mutation_count": len(registry),
        "executed_mutation_count": len(results),
        "atomic_mutation_count": sum(
            item["exactly_one_registered_premise_changed"] for item in results
        ),
        "rejected_before_simulation_count": sum(
            item["matrix_first_diagnostic"] is not None
            and item["simulation_entry_count"] == 0
            for item in results
        ),
        "exact_first_diagnostic_count": sum(
            item["exact_first_diagnostic"] for item in results
        ),
        "exact_final_block_decision_count": sum(
            item["final_block_decision_exact"] for item in results
        ),
        "output_creation_count": sum(
            not item["output_root_absent_after_probe"] for item in results
        ),
        "results": results,
    }


def audit_payload_identity(
    matrix: Mapping[str, Any], identity: Mapping[str, Any]
) -> dict[str, Any]:
    by_run_id = {record["run_id"]: record for record in matrix["records"]}
    output_by_run_id = {record["run_id"]: record for record in identity["outputs"]}
    all_paths = [
        output[field]
        for output in identity["outputs"]
        for field in ("json_relative_output_path", "npz_relative_output_path")
    ]
    mirrored_fields = (
        "run_id",
        "execution_role",
        "mechanism_configuration_role",
        "instrumentation_enabled",
        "paired_run_id",
        "scientific_row_id",
        "parent_canonical_run_id",
        "input_hash",
        "scientific_input_core_sha256",
        "physical_configuration_core_sha256",
        "complete_execution_identity_sha256",
        "implementation_id",
        "implementation_sha256",
        "runtime_source_closure_sha256",
        "output_schema_version",
        "json_relative_output_path",
        "npz_relative_output_path",
    )
    output_root = PurePosixPath(identity["output_root"])
    return {
        "matrix_run_ids_exact": tuple(by_run_id) == custody_v2.EXACT_RUN_IDS,
        "identity_run_id_domain_exact": set(output_by_run_id)
        == set(custody_v2.EXACT_RUN_IDS),
        "role_record_count": len(identity["outputs"]),
        "role_payload_path_count": len(all_paths),
        "unique_role_payload_path_count": len(set(all_paths)),
        "all_paths_under_frozen_root": all(
            output_root in PurePosixPath(path).parents for path in all_paths
        ),
        "matrix_manifest_fields_exact": all(
            all(output_by_run_id[run_id][field] == record[field] for field in mirrored_fields)
            for run_id, record in by_run_id.items()
        ),
        "auxiliary_execution_file_count": len(identity["auxiliary_execution_files"]),
        "complete_expected_file_count_after_success": identity[
            "complete_expected_file_count_after_success"
        ],
    }


def _assigned_names(nodes: Sequence[ast.AST]) -> set[str]:
    return {
        child.id
        for node in nodes
        for child in ast.walk(node)
        if isinstance(child, ast.Name) and isinstance(child.ctx, ast.Store)
    }


def audit_instrumentation_registration(matrix: Mapping[str, Any]) -> dict[str, Any]:
    records = {record["run_id"]: record for record in matrix["records"]}
    pair_records = []
    physics_fields = (
        "parent_canonical_run_id",
        "parent_canonical_input_hash",
        "parent_canonical_output_path",
        "parent_canonical_output_sha256",
        "parent_initial_condition_identity",
        "scientific_row_id",
        "requested_axis_values",
        "row",
        "model_class",
        "numerical_method",
        "grid_size",
        "n",
        "time_step",
        "dt",
        "duration",
        "solver_tolerance",
        "tolerance",
        "iteration_cap",
        "max_iterations",
        "accepted_step_count",
        "checkpoint_count_including_initial",
        "implementation_id",
        "implementation_sha256",
    )
    for instrumented_id, control_id in custody_v2.PAIR_RUN_IDS:
        instrumented = records[instrumented_id]
        control = records[control_id]
        pair_records.append(
            {
                "instrumented_run_id": instrumented_id,
                "control_run_id": control_id,
                "all_physics_fields_exact": all(
                    canonical_json_bytes(instrumented[field])
                    == canonical_json_bytes(control[field])
                    for field in physics_fields
                ),
                "initial_state_identity_exact": instrumented[
                    "parent_initial_condition_identity"
                ]
                == control["parent_initial_condition_identity"],
                "instrumented_observable_count": len(
                    instrumented["instrumented_observable_ids"]
                ),
                "control_observable_count": len(control["instrumented_observable_ids"]),
                "instrumentation_roles_distinct": instrumented[
                    "instrumentation_enabled"
                ]
                is True
                and control["instrumentation_enabled"] is False,
                "instrumentation_read_only": instrumented[
                    "instrumentation_read_only"
                ]
                is True
                and control["instrumentation_read_only"] is True,
            }
        )

    step_tree = ast.parse(
        inspect.getsource(implementation_v0.picard_midpoint_step_with_observer)
    )
    observer_blocks = [
        node.body
        for node in ast.walk(step_tree)
        if isinstance(node, ast.If)
        and isinstance(node.test, ast.Name)
        and node.test.id == "observer_enabled"
    ]
    observer_assigned = _assigned_names(
        [node for block in observer_blocks for node in block]
    )
    physical_step_names = {
        "guess",
        "updated",
        "update_defect",
        "update_residual",
        "converged",
        "midpoint_rhs",
        "equation_defect",
        "equation_residual",
        "solver_residual",
    }
    step_observer_cannot_write_physical_state = not (
        observer_assigned & physical_step_names
    )

    role_tree = ast.parse(inspect.getsource(implementation_v0.run_role_in_memory))
    instrumentation_blocks = [
        node.body
        for node in ast.walk(role_tree)
        if isinstance(node, ast.If)
        and any(
            isinstance(child, ast.Name)
            and child.id == "instrumentation_enabled"
            for child in ast.walk(node.test)
        )
    ]
    instrumentation_assigned = _assigned_names(
        [node for block in instrumentation_blocks for node in block]
    )
    physical_role_names = {
        "state",
        "vector",
        "previous_vector",
        "step_result",
        "physical_snapshots",
        "times",
        "all_steps_converged",
        "maximum_iterations_used",
        "maximum_solver_residual",
    }
    role_instrumentation_cannot_write_physical_state = not (
        instrumentation_assigned & physical_role_names
    )
    step_source = inspect.getsource(
        implementation_v0.picard_midpoint_step_with_observer
    )
    return {
        "pair_count": len(pair_records),
        "pairs": pair_records,
        "all_pair_physics_and_initial_states_exact": all(
            item["all_physics_fields_exact"]
            and item["initial_state_identity_exact"]
            for item in pair_records
        ),
        "all_instrumentation_registered_read_only": all(
            item["instrumentation_read_only"] for item in pair_records
        ),
        "instrumented_observable_count_each": [
            item["instrumented_observable_count"] for item in pair_records
        ],
        "control_observable_count_each": [
            item["control_observable_count"] for item in pair_records
        ],
        "step_observer_cannot_write_physical_state": (
            step_observer_cannot_write_physical_state
        ),
        "role_instrumentation_cannot_write_physical_state": (
            role_instrumentation_cannot_write_physical_state
        ),
        "stopping_test_is_independent_of_observer": (
            "if update_residual <= requested_tolerance:" in step_source
            and "observer_enabled" not in step_source.split(
                "if update_residual <= requested_tolerance:", 1
            )[1].split("break", 1)[0]
        ),
        "floating_reduction_ordering_contract": (
            "instrumentation-only reductions cannot write the packed state, "
            "updated iterate, residual used for stopping, or convergence flag; "
            "actual trajectory equality remains a post-execution result"
        ),
        "actual_nonperturbation_result_evaluated": False,
    }


def audit_raw_semantics_and_controls(packet: Mapping[str, Any]) -> dict[str, Any]:
    evidence_validation = evidence_v2.self_validate()
    classifier_validation = classifier_v2.self_validate()
    constants = semantic_v1.SUPPORT_CONSTANTS_V1
    provenance = list(semantic_v1.SUPPORT_CONSTANT_PROVENANCE)
    leaves = {
        (hypothesis, constant_id)
        for hypothesis, values in constants.items()
        for constant_id in values
    }
    provenance_leaves = {
        (item["hypothesis"], item["constant_id"]) for item in provenance
    }
    registry = packet["freeze_adversarial_control_registry"]
    return {
        "raw_evidence_assembler_self_validation": evidence_validation,
        "raw_evidence_assembler_self_validation_all_passed": all(
            evidence_validation.values()
        ),
        "classifier_self_validation": classifier_validation,
        "classifier_self_validation_all_passed": all(classifier_validation.values()),
        "classifier_public_parameters": list(
            inspect.signature(classifier_v2.classify_from_raw_payloads).parameters
        ),
        "support_constant_count": len(leaves),
        "support_constant_provenance_count": len(provenance),
        "support_constant_provenance_one_to_one": leaves == provenance_leaves,
        "all_support_constants_nonfuture": all(
            item["nonfuture"] is True
            and item["future_mechanism_outputs_used"] is False
            and item["declared_before_mechanism_execution"] is True
            for item in provenance
        ),
        "H_C_has_no_gamma_constant": all(
            "gamma" not in key.casefold() for key in constants["H_C"]
        ),
        "legacy_Q_decision_bearing": semantic_v1.LEGACY_Q[
            "mechanism_decision_bearing"
        ],
        "adversarial_control_count": len(registry),
        "unique_adversarial_control_count": len(
            {item["control_id"] for item in registry}
        ),
    }


def accepted_runtime_authority(packet: Mapping[str, Any]) -> dict[str, Any]:
    authority = copy.deepcopy(
        packet["runtime_execution_authority_proposal"]["proposed_review_authority"]
    )
    authority["execution_authorized"] = True
    authority["artifact_bindings"]["freeze_packet"]["sha256"] = (
        EXPECTED_ARTIFACT_SHA256[PACKET_RELATIVE_PATH]
    )
    return authority


def audit_authority_and_executor(packet: Mapping[str, Any]) -> dict[str, Any]:
    authority = accepted_runtime_authority(packet)
    anchor = {
        "verdict": ACCEPT_VERDICT,
        custody_v2.REVIEW_AUTHORITY_FIELD: authority,
    }
    accepted_diagnostics = executor_v2._validate_freeze_anchor(anchor)
    blocked_diagnostics = executor_v2._validate_freeze_anchor(
        {"verdict": "PREPARED_PENDING_INDEPENDENT_REVIEW"}
    )
    metric_template = copy.deepcopy(packet["metric_configuration_template"])
    template_validation_passed = True
    template_validation_diagnostic = None
    try:
        implementation_v0._validate_metric_configuration(metric_template)
    except (KeyError, TypeError, ValueError) as error:
        template_validation_passed = False
        template_validation_diagnostic = f"{type(error).__name__}:{error}"
    role_configuration_results = []
    for record in load_json(MATRIX_RELATIVE_PATH)["records"]:
        run_id = record["run_id"]
        try:
            resolved = implementation_v0._role_metric_configuration(
                metric_template, float(record["tolerance"])
            )
            implementation_v0._validate_metric_configuration(resolved)
            role_configuration_results.append(
                {"run_id": run_id, "resolved_configuration_valid": True}
            )
        except (KeyError, TypeError, ValueError) as error:
            role_configuration_results.append(
                {
                    "run_id": run_id,
                    "resolved_configuration_valid": False,
                    "diagnostic": f"{type(error).__name__}:{error}",
                }
            )
    preflight_source = inspect.getsource(executor_v2._prepare_execution_plan)
    preflight_validates_unresolved_template = (
        "v0._validate_metric_configuration(metric_configuration_template)"
        in preflight_source
    )
    return {
        "public_execution_parameters": list(
            inspect.signature(executor_v2.execute_frozen_matrix_once_v2).parameters
        ),
        "lookup_parameters": list(
            inspect.signature(executor_v2.lookup_frozen_record).parameters
        ),
        "accepted_authority_diagnostics": accepted_diagnostics,
        "absent_or_unaccepted_anchor_diagnostics": blocked_diagnostics,
        "fixed_review_anchor_path": custody_v2.REVIEW_ANCHOR_RELATIVE_PATH,
        "review_anchor_path_exact": packet["runtime_execution_authority_proposal"][
            "fixed_review_anchor_path"
        ]
        == custody_v2.REVIEW_ANCHOR_RELATIVE_PATH,
        "execution_authorized": authority["execution_authorized"],
        "one_execution_only": authority["one_execution_only"],
        "automatic_retries_authorized": authority[
            "automatic_retries_authorized"
        ],
        "exact_run_ids": authority["exact_run_ids"],
        "pair_run_ids": authority["pair_run_ids"],
        "packet_bytes_bound_by_review": authority["artifact_bindings"][
            "freeze_packet"
        ]["sha256"]
        == EXPECTED_ARTIFACT_SHA256[PACKET_RELATIVE_PATH],
        "unresolved_metric_template_validation_passed": template_validation_passed,
        "unresolved_metric_template_validation_diagnostic": (
            template_validation_diagnostic
        ),
        "resolved_role_configuration_valid_count": sum(
            item["resolved_configuration_valid"]
            for item in role_configuration_results
        ),
        "resolved_role_configuration_results": role_configuration_results,
        "executor_preflight_validates_unresolved_template": (
            preflight_validates_unresolved_template
        ),
        "accepted_anchor_can_complete_read_only_preflight": (
            template_validation_passed
            or not preflight_validates_unresolved_template
        ),
        "runtime_execution_authority": authority,
    }


def audit_hc_path_independence() -> dict[str, Any]:
    p0 = np.array([[0.2, -0.1, 0.3], [0.1, 0.0, -0.1]])
    current = np.array([[0.08, -0.06, 0.02], [0.01, 0.02, -0.03]])
    p1 = p0 - 0.01 * current
    rho0 = np.array([[0.04, -0.02, 0.01], [0.02, -0.01, 0.03]])
    rho1 = np.array([[0.03, -0.015, 0.005], [0.01, -0.02, 0.025]])
    direct_defect = np.array(
        [[2.0e-5, -1.0e-5, 3.0e-5], [1.0e-5, 2.0e-5, -1.0e-5]]
    )

    def reconstruct(defect: np.ndarray, continuity: np.ndarray) -> dict[str, Any]:
        return semantic_v1.reconstruct_independent_hc_paths(
            direct_terminal_p_equation_defect=defect,
            p_previous=p0,
            p_current=p1,
            rho_previous=rho0,
            rho_current=rho1,
            continuity_current_midpoint_independently_recomputed=continuity,
            maxwell_source_midpoint_registered=current,
            a=0.25,
            dt=0.01,
            requested_solver_tolerance=1.0e-8,
        )

    baseline = reconstruct(np.zeros_like(direct_defect), current.copy())
    maxwell_changed = reconstruct(direct_defect, current.copy())
    continuity_changed = reconstruct(
        np.zeros_like(direct_defect),
        current + np.array([[0.01, 0.0, -0.01], [0.0, 0.02, -0.02]]),
    )
    summary = semantic_v1.summarize_independent_hc_paths(maxwell_changed)
    return {
        "Maxwell_path_mutation_changes_mismatch": not np.array_equal(
            baseline["independent_path_mismatch"],
            maxwell_changed["independent_path_mismatch"],
        ),
        "continuity_path_mutation_changes_mismatch": not np.array_equal(
            baseline["independent_path_mismatch"],
            continuity_changed["independent_path_mismatch"],
        ),
        "mechanism_path_sources_independent": maxwell_changed[
            "mechanism_path_sources_independent"
        ],
        "continuity_path_reuses_registered_Maxwell_source": maxwell_changed[
            "continuity_path_uses_registered_maxwell_source"
        ],
        "gamma32_used": summary["gamma32_used"],
        "legacy_Q_used": summary["legacy_q_used"],
    }


def audit_canonical_custody(packet: Mapping[str, Any]) -> dict[str, Any]:
    output_root = REPO_ROOT / custody_v2.EXPERIMENT_OUTPUT_ROOT_RELATIVE_PATH
    inventory = canonical_v0._canonical_root_inventory()
    root_digest = canonical_v0.canonical_root_digest()
    tree_digest = canonical_v0.canonical_directory_tree_sha256()
    boundary = packet["authority_boundary"]
    return {
        "canonical_file_count": len(inventory),
        "canonical_authority_inventory_digest": root_digest,
        "canonical_directory_tree_sha256": tree_digest,
        "canonical_inventory_exact": len(inventory) == 205
        and root_digest == canonical_v0.EXPECTED_CANONICAL_ROOT_DIGEST,
        "canonical_tree_exact": tree_digest
        == canonical_v0.EXPECTED_CANONICAL_DIRECTORY_TREE_SHA256,
        "experiment_output_root_absent": not output_root.exists(),
        "canonical_mutation_count": 0,
        "simulation_invocation_count": 0,
        "canonical_robustness": boundary["canonical_robustness"],
        "R13_root_mechanism": boundary["root_mechanism"],
        "materiality": boundary["materiality"],
        "new_E_REPRO_claim": boundary["new_E_REPRO_claim"],
    }


def build_report() -> dict[str, Any]:
    output_root = REPO_ROOT / custody_v2.EXPERIMENT_OUTPUT_ROOT_RELATIVE_PATH
    if output_root.exists():
        raise ValueError("future experiment output root must be absent during review")
    packet = load_json(PACKET_RELATIVE_PATH)
    matrix = load_json(MATRIX_RELATIVE_PATH)
    identity = load_json(IDENTITY_RELATIVE_PATH)
    if (
        packet.get("verdict") != "PREPARED_PENDING_INDEPENDENT_REVIEW"
        or packet.get("selected_next_target") != TARGET
    ):
        raise ValueError("v2 preparation does not authorize this review target")

    artifact_audit = audit_artifact_freshness()
    identity_audit = audit_independent_identities(packet, matrix)
    runtime_audit = audit_runtime_source_closure(packet)
    mutation_audit = audit_twenty_identity_mutations(packet, matrix)
    payload_audit = audit_payload_identity(matrix, identity)
    instrumentation_audit = audit_instrumentation_registration(matrix)
    raw_audit = audit_raw_semantics_and_controls(packet)
    authority_audit = audit_authority_and_executor(packet)
    hc_audit = audit_hc_path_independence()
    canonical_audit = audit_canonical_custody(packet)

    acceptance_checks = [
        {
            "acceptance_id": "five_v2_artifacts_are_fresh_and_v1_block_is_preserved",
            "passed": artifact_audit["artifact_count"] == 5
            and artifact_audit["exact_artifact_count"] == 5
            and artifact_audit["cross_bindings_exact"]
            and artifact_audit["v2_subprocess_regeneration_byte_exact"]
            and artifact_audit["v1_remains_stale"]
            and artifact_audit["v1_stale_diagnostic_preserved"],
            "review_outcome_on_failure": "BLOCK_ARTIFACT_FRESHNESS",
        },
        {
            "acceptance_id": "six_scientific_inputs_and_three_physical_pairs_reconstruct",
            "passed": identity_audit["run_id_order_exact"]
            and identity_audit["runtime_source_closure_exact"]
            and identity_audit["scientific_input_reconstruction_count"] == 6
            and identity_audit["unique_scientific_input_count"] == 3
            and identity_audit["scientific_identity_source_independent"]
            and identity_audit["all_three_pairs_scientifically_identical"],
            "review_outcome_on_failure": "BLOCK_SCIENTIFIC_INPUT_IDENTITY",
        },
        {
            "acceptance_id": "six_complete_execution_identities_reconstruct_and_are_unique",
            "passed": identity_audit[
                "complete_execution_identity_reconstruction_count"
            ]
            == 6
            and identity_audit["full_record_identity_reconstruction_count"] == 6
            and identity_audit["unique_complete_execution_identity_count"] == 6
            and identity_audit[
                "all_three_pair_execution_identities_distinct"
            ],
            "review_outcome_on_failure": "BLOCK_COMPLETE_EXECUTION_IDENTITY",
        },
        {
            "acceptance_id": "eight_runtime_sources_match_paths_bytes_loaders_and_reject_substitution",
            "passed": runtime_audit["frozen_module_count"] == 8
            and runtime_audit["loaded_module_count"] == 8
            and runtime_audit["module_name_order_exact"]
            and runtime_audit["closure_digest_exact"]
            and runtime_audit["authority_closure_exact"]
            and runtime_audit["all_loaded_paths_bytes_and_loaders_exact"]
            and runtime_audit["historical_object_binding_exact"]
            and runtime_audit["hostile_same_name_wrong_path_rejected"]
            and runtime_audit["wrong_frozen_bytes_rejected"]
            and runtime_audit["wrong_loader_rejected"]
            and runtime_audit["git_identity_decision_bearing"] is False,
            "review_outcome_on_failure": "BLOCK_RUNTIME_SOURCE_CLOSURE",
        },
        {
            "acceptance_id": "twenty_identity_mutations_are_atomic_exact_and_preexecution",
            "passed": mutation_audit["registered_mutation_count"] == 20
            and mutation_audit["executed_mutation_count"] == 20
            and mutation_audit["atomic_mutation_count"] == 20
            and mutation_audit["rejected_before_simulation_count"] == 20
            and mutation_audit["exact_first_diagnostic_count"] == 20
            and mutation_audit["exact_final_block_decision_count"] == 20
            and mutation_audit["output_creation_count"] == 0,
            "review_outcome_on_failure": "BLOCK_MUTATION_COVERAGE_OR_ATOMICITY",
        },
        {
            "acceptance_id": "executor_anchor_API_and_read_only_preflight_are_exact",
            "passed": authority_audit["public_execution_parameters"] == ["repo_root"]
            and authority_audit["lookup_parameters"] == ["repo_root", "run_id"]
            and authority_audit["accepted_authority_diagnostics"] == []
            and authority_audit["absent_or_unaccepted_anchor_diagnostics"]
            == ["REVIEW_ANCHOR_NOT_ACCEPTED"]
            and authority_audit["review_anchor_path_exact"]
            and authority_audit["packet_bytes_bound_by_review"]
            and authority_audit["resolved_role_configuration_valid_count"] == 6
            and authority_audit[
                "accepted_anchor_can_complete_read_only_preflight"
            ],
            "review_outcome_on_failure": "BLOCK_EXECUTOR_PREFLIGHT_CONFIGURATION",
        },
        {
            "acceptance_id": "twelve_role_payload_paths_and_two_auxiliary_files_are_exact",
            "passed": payload_audit["matrix_run_ids_exact"]
            and payload_audit["identity_run_id_domain_exact"]
            and payload_audit["role_record_count"] == 6
            and payload_audit["role_payload_path_count"] == 12
            and payload_audit["unique_role_payload_path_count"] == 12
            and payload_audit["all_paths_under_frozen_root"]
            and payload_audit["matrix_manifest_fields_exact"]
            and payload_audit["auxiliary_execution_file_count"] == 2
            and payload_audit["complete_expected_file_count_after_success"] == 14,
            "review_outcome_on_failure": "BLOCK_OUTPUT_IDENTITY",
        },
        {
            "acceptance_id": "instrumentation_is_registered_read_only_without_physics_feedback",
            "passed": instrumentation_audit["pair_count"] == 3
            and instrumentation_audit["all_pair_physics_and_initial_states_exact"]
            and instrumentation_audit[
                "all_instrumentation_registered_read_only"
            ]
            and instrumentation_audit["instrumented_observable_count_each"]
            == [14, 14, 14]
            and instrumentation_audit["control_observable_count_each"] == [0, 0, 0]
            and instrumentation_audit[
                "step_observer_cannot_write_physical_state"
            ]
            and instrumentation_audit[
                "role_instrumentation_cannot_write_physical_state"
            ]
            and instrumentation_audit[
                "stopping_test_is_independent_of_observer"
            ]
            and instrumentation_audit[
                "actual_nonperturbation_result_evaluated"
            ]
            is False,
            "review_outcome_on_failure": "BLOCK_INSTRUMENTATION_REGISTRATION",
        },
        {
            "acceptance_id": "raw_semantics_HC_constants_and_control_registry_are_preserved",
            "passed": raw_audit[
                "raw_evidence_assembler_self_validation_all_passed"
            ]
            and raw_audit["classifier_self_validation_all_passed"]
            and raw_audit["classifier_public_parameters"] == ["repo_root"]
            and raw_audit["support_constant_count"] == 23
            and raw_audit["support_constant_provenance_count"] == 23
            and raw_audit["support_constant_provenance_one_to_one"]
            and raw_audit["all_support_constants_nonfuture"]
            and raw_audit["H_C_has_no_gamma_constant"]
            and raw_audit["legacy_Q_decision_bearing"] is False
            and raw_audit["adversarial_control_count"] == 41
            and raw_audit["unique_adversarial_control_count"] == 41
            and hc_audit["Maxwell_path_mutation_changes_mismatch"]
            and hc_audit["continuity_path_mutation_changes_mismatch"]
            and hc_audit["mechanism_path_sources_independent"]
            and not hc_audit[
                "continuity_path_reuses_registered_Maxwell_source"
            ]
            and not hc_audit["gamma32_used"]
            and not hc_audit["legacy_Q_used"],
            "review_outcome_on_failure": "BLOCK_SEMANTIC_CONTRACT",
        },
        {
            "acceptance_id": "canonical_custody_and_nonexecution_are_preserved",
            "passed": canonical_audit["canonical_inventory_exact"]
            and canonical_audit["canonical_tree_exact"]
            and canonical_audit["experiment_output_root_absent"]
            and canonical_audit["canonical_mutation_count"] == 0
            and canonical_audit["simulation_invocation_count"] == 0
            and canonical_audit["canonical_robustness"] == "NUMERICALLY_BLOCKED"
            and canonical_audit["R13_root_mechanism"] == "UNRESOLVED"
            and canonical_audit["materiality"]
            == "NOT_EVALUATED_NUMERICAL_BLOCK"
            and canonical_audit["new_E_REPRO_claim"] is False,
            "review_outcome_on_failure": "BLOCK_CANONICAL_CUSTODY",
        },
        {
            "acceptance_id": "authority_is_bounded_to_one_exact_six_run_execution",
            "passed": authority_audit["execution_authorized"] is True
            and authority_audit["one_execution_only"] is True
            and authority_audit["automatic_retries_authorized"] is False
            and authority_audit["exact_run_ids"] == list(custody_v2.EXACT_RUN_IDS)
            and authority_audit["pair_run_ids"]
            == [list(pair) for pair in custody_v2.PAIR_RUN_IDS]
            and packet["post_acceptance_target"] == ACCEPTED_NEXT_TARGET,
            "review_outcome_on_failure": "BLOCK_AUTHORITY_BOUNDARY",
        },
    ]
    failed = [item for item in acceptance_checks if not item["passed"]]
    verdict = (
        ACCEPT_VERDICT
        if not failed
        else str(failed[0]["review_outcome_on_failure"])
    )
    selected_next_target = (
        ACCEPTED_NEXT_TARGET if not failed else BLOCKED_NEXT_TARGET
    )
    report: dict[str, Any] = {
        "schema_id": SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "verdict": verdict,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": (
            "ONE_EXACT_FROZEN_SIX_RUN_EXECUTION"
            if not failed
            else "VERSIONED_NUMERICAL_FREEZE_CORRECTION_ONLY"
        ),
        "reviewer_independence": {
            "v2_generator_imported": False,
            "v2_combined_preparation_pass_flags_used_as_review_evidence": False,
            "scientific_input_cores_reconstructed_independently": True,
            "complete_execution_identities_reconstructed_independently": True,
            "runtime_source_files_loaded_and_hashed_independently": True,
            "matrix_mutations_executed_independently": True,
            "hostile_path_byte_and_loader_probes_executed": True,
            "evolution_runner_invocation_count": 0,
            "simulation_invocation_count": 0,
        },
        "reviewed_artifact_freshness": artifact_audit,
        "independent_identity_reconstruction_audit": identity_audit,
        "runtime_source_closure_audit": runtime_audit,
        "identity_mutation_audit": mutation_audit,
        "payload_identity_audit": payload_audit,
        "instrumentation_registration_audit": instrumentation_audit,
        "raw_semantics_and_control_audit": raw_audit,
        "H_C_path_independence_audit": hc_audit,
        "executor_authority_audit": {
            key: value
            for key, value in authority_audit.items()
            if key != "runtime_execution_authority"
        },
        "canonical_custody": canonical_audit,
        "acceptance_checks": acceptance_checks,
        "acceptance_check_count": len(acceptance_checks),
        "passed_acceptance_check_count": sum(
            item["passed"] for item in acceptance_checks
        ),
        "failed_acceptance_check_count": len(failed),
        "failed_acceptance_ids": [item["acceptance_id"] for item in failed],
        "blocking_outcomes": list(
            dict.fromkeys(item["review_outcome_on_failure"] for item in failed)
        ),
        "blocking_findings": (
            [
                {
                    "finding_id": (
                        "B_V2_EXECUTOR_PREFLIGHT_REJECTS_FROZEN_METRIC_TEMPLATE"
                    ),
                    "review_outcome": "BLOCK_EXECUTOR_PREFLIGHT_CONFIGURATION",
                    "evidence": (
                        "The accepted-anchor schema validates and all six per-role "
                        "metric configurations resolve correctly, but executor-v2 "
                        "read-only preflight calls _validate_metric_configuration on "
                        "the unresolved packet template. That template intentionally "
                        "lacks block_floors and is rejected before an execution plan "
                        "can be returned."
                    ),
                    "observed_first_diagnostic": authority_audit[
                        "unresolved_metric_template_validation_diagnostic"
                    ],
                    "bounded_correction_required": (
                        "Prepare numerical-freeze v3 only. Make preflight validate all "
                        "six role-resolved metric configurations (or freeze a directly "
                        "valid complete template), regenerate the five artifacts from "
                        "the resulting source closure, and independently review v3."
                    ),
                }
            ]
            if any(
                item["review_outcome_on_failure"]
                == "BLOCK_EXECUTOR_PREFLIGHT_CONFIGURATION"
                for item in failed
            )
            else []
        ),
        "preserved_scientific_core": {
            "accepted_bounded_Maxwell_Dirac_result": "PRESERVED",
            "Route_A": "ACCEPTED",
            "instrumented_design_v1": "ACCEPTED",
            "R13_diagnostic_pattern": "ACCEPTED",
            "canonical_robustness": "NUMERICALLY_BLOCKED",
            "R13_root_mechanism": "UNRESOLVED",
            "materiality": "NOT_EVALUATED_NUMERICAL_BLOCK",
            "new_E_REPRO": "NONE",
        },
        "authority_rotation": {
            "numerical_freeze_v2_accepted": not failed,
            "execution_authorized": not failed,
            "one_time_execution_count_authorized": 1 if not failed else 0,
            "exact_authorized_run_count": 6 if not failed else 0,
            "rerun_authorized": False,
            "additional_tolerances_or_durations_authorized": False,
            "threshold_change_authorized": False,
            "row_exclusion_authorized": False,
            "robustness_reclassification_authorized": False,
            "materiality_evaluation_authorized": False,
            "new_scientific_claim_authorized": False,
            "result_acceptance_authorized": False,
        },
        "nonclaims": [
            "no six-run mechanism experiment has executed",
            "no instrumentation nonperturbation result has been observed",
            "no mechanism hypothesis has been evaluated on experiment data",
            "no canonical output has changed",
            "no robustness or materiality result is assigned",
            "no E-REPRO, pillar, seam, C_k, CCFT, or master-action promotion is assigned",
        ],
        "claim_ceiling": (
            "Independent acceptance authorizes only one exact execution of the frozen "
            "six-run matrix. Outputs require a separate independent result review "
            "before any numerical-mechanism conclusion."
            if not failed
            else "Review failure authorizes only a bounded versioned freeze correction."
        ),
    }
    if not failed:
        report[custody_v2.REVIEW_AUTHORITY_FIELD] = authority_audit[
            "runtime_execution_authority"
        ]
    if output_root.exists():
        raise ValueError("independent review created the future output root")
    return report


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
    report = json.loads(raw.decode("utf-8"))
    print(
        json.dumps(
            {
                "status": "CHECKED" if check else "WROTE",
                "verdict": report["verdict"],
                "review_target": TARGET,
                "execution_authorized": report["authority_rotation"][
                    "execution_authorized"
                ],
                "simulation_invocation_count": 0,
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
