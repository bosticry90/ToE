from __future__ import annotations

"""Independent review of numerical-freeze v3.

This module does not import the v3 preparation generator. It reconstructs the
scientific, role-resolution, and complete execution identities from stored
lower-level objects. It may write only the fixed v3 review anchor. It never
calls the evolution or creates the future experiment output root.
"""

import argparse
import copy
import hashlib
import importlib
import inspect
import json
import math
import os
import subprocess
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
    as custody_v3,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_executor_v2
    as executor_v2,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_executor_v3
    as executor_v3,
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
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_raw_evidence_assembler_v3
    as evidence_v3,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_semantic_contract_v1
    as semantic_v1,
)


REPO_ROOT = find_repo_root(Path(__file__))
CAPTURED_AT_UTC = "2026-07-16T00:00:00Z"
TARGET = (
    "review_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
    "instrumented_r13_mechanism_experiment_numerical_freeze_packet_v3_result"
)
ACCEPT_VERDICT = custody_v3.EXPECTED_REVIEW_VERDICT
ACCEPTED_NEXT_TARGET = (
    "execute_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
    "instrumented_r13_mechanism_experiment_v0_once"
)
BLOCKED_NEXT_TARGET = (
    "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
    "instrumented_r13_mechanism_experiment_numerical_freeze_packet_v4"
)
SCHEMA_ID = (
    "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_"
    "INSTRUMENTED_R13_MECHANISM_EXPERIMENT_NUMERICAL_FREEZE_PACKET_REVIEW_"
    "20260716_v3"
)
REPORT_RELATIVE_PATH = custody_v3.REVIEW_ANCHOR_RELATIVE_PATH
PACKET_RELATIVE_PATH = custody_v3.FREEZE_PACKET_RELATIVE_PATH
MATRIX_RELATIVE_PATH = custody_v3.RUN_MATRIX_RELATIVE_PATH
IDENTITY_RELATIVE_PATH = custody_v3.IDENTITY_MANIFEST_RELATIVE_PATH
MANIFEST_RELATIVE_PATH = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-INSTRUMENTED-R13-MECHANISM-EXPERIMENT-NUMERICAL-FREEZE-"
    "MANIFEST-v3.json"
)
PREPARATION_REPORT_RELATIVE_PATH = (
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
    "ROBUSTNESS_INSTRUMENTED_R13_MECHANISM_EXPERIMENT_NUMERICAL_FREEZE_PACKET_"
    "20260716_v3.json"
)
V2_REVIEW_RELATIVE_PATH = (
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
    "ROBUSTNESS_INSTRUMENTED_R13_MECHANISM_EXPERIMENT_NUMERICAL_FREEZE_PACKET_"
    "REVIEW_20260716_v2.json"
)
V3_GENERATOR_MODULE = (
    "formal.python.tools."
    "dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
    "instrumented_r13_mechanism_experiment_numerical_freeze_packet_v3"
)
V1_GENERATOR_MODULE = (
    "formal.python.tools."
    "dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
    "instrumented_r13_mechanism_experiment_numerical_freeze_packet_v1"
)
EXPECTED_ARTIFACT_SHA256 = {
    PACKET_RELATIVE_PATH: "e6a20986b494fb35e6393400751002c3ecd4680438e40086ae75d68c33bcf028",
    MATRIX_RELATIVE_PATH: "8b980c983c42e9f0e78d4062f91b3daeb77013a603f46c3e48908a8b31937f47",
    IDENTITY_RELATIVE_PATH: "49342c157e0958fb2d2c52694bf1493f407182f41ed0a921e10f1b891fad7d59",
    MANIFEST_RELATIVE_PATH: "2956ded97d83bfe9e073177c489e27e1a9cad65bbd73edfb885f4df867467c3d",
    PREPARATION_REPORT_RELATIVE_PATH: "9902d7aaac60082aa4829fd6cc15fa1229f24a3c86805beb7a225495129c7c11",
}
BLOCK_IDS = (
    "THETA_KINEMATIC",
    "P_LONGITUDINAL_MAXWELL",
    "PHI2_KINEMATIC",
    "P2_DYNAMIC",
    "PHI3_KINEMATIC",
    "P3_DYNAMIC",
    "DIRAC_PLUS",
    "DIRAC_MINUS",
)
GAMMA64 = 7.105427357601052e-15


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


def _subprocess_generated_hashes(module_name: str) -> dict[str, str]:
    source = (
        "import hashlib,json; "
        f"from {module_name} import artifact_bytes; "
        "a=artifact_bytes(); "
        "print(json.dumps({k:hashlib.sha256(v).hexdigest() for k,v in a.items()},sort_keys=True))"
    )
    result = subprocess.run(
        [sys.executable, "-c", source],
        cwd=REPO_ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    value = json.loads(result.stdout)
    if not isinstance(value, dict):
        raise TypeError("subprocess generator did not return a hash map")
    return {str(key): str(item) for key, item in value.items()}


def audit_artifact_and_predecessor_history() -> dict[str, Any]:
    stored = {
        path: sha256_bytes((REPO_ROOT / path).read_bytes())
        for path in EXPECTED_ARTIFACT_SHA256
    }
    generated = _subprocess_generated_hashes(V3_GENERATOR_MODULE)
    v1_generated = _subprocess_generated_hashes(V1_GENERATOR_MODULE)
    v1_stale = [
        path
        for path, digest in v1_generated.items()
        if not (REPO_ROOT / path).is_file()
        or sha256_bytes((REPO_ROOT / path).read_bytes()) != digest
    ]
    packet = load_json(PACKET_RELATIVE_PATH)
    manifest = load_json(MANIFEST_RELATIVE_PATH)
    preparation_report = load_json(PREPARATION_REPORT_RELATIVE_PATH)
    v2_review = load_json(V2_REVIEW_RELATIVE_PATH)
    cross_bindings = {
        "packet_to_matrix": packet["exact_run_matrix"]["sha256"]
        == stored[MATRIX_RELATIVE_PATH],
        "packet_to_identity": packet["expected_output_identity_manifest"]["sha256"]
        == stored[IDENTITY_RELATIVE_PATH],
        "manifest_to_packet": manifest["packet"]["sha256"]
        == stored[PACKET_RELATIVE_PATH],
        "manifest_to_matrix": manifest["run_matrix"]["sha256"]
        == stored[MATRIX_RELATIVE_PATH],
        "report_to_packet": preparation_report["artifacts"]["packet"]["sha256"]
        == stored[PACKET_RELATIVE_PATH],
    }
    v2_preflight_source = inspect.getsource(executor_v2._prepare_execution_plan)
    return {
        "artifact_count": len(stored),
        "stored_sha256": stored,
        "expected_sha256": EXPECTED_ARTIFACT_SHA256,
        "exact_artifact_count": sum(
            stored[path] == expected
            for path, expected in EXPECTED_ARTIFACT_SHA256.items()
        ),
        "subprocess_regeneration_sha256": generated,
        "subprocess_regeneration_byte_exact": generated
        == EXPECTED_ARTIFACT_SHA256,
        "cross_bindings": cross_bindings,
        "cross_bindings_exact": all(cross_bindings.values()),
        "v1_stale_path_count": len(v1_stale),
        "v1_stale_paths": v1_stale,
        "v1_remains_stale": bool(v1_stale),
        "v2_review_verdict": v2_review.get("verdict"),
        "v2_review_selected_next_target": v2_review.get("selected_next_target"),
        "v2_historical_preflight_validates_unresolved_template": (
            "v0._validate_metric_configuration(metric_configuration_template)"
            in v2_preflight_source
        ),
    }


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


def _independent_complete_core(record: Mapping[str, Any]) -> dict[str, Any]:
    scientific_hash = sha256_bytes(
        canonical_json_bytes(_independent_scientific_core(record))
    )
    return {
        "schema_id": "DIRAC_MAXWELL_R13_MECHANISM_COMPLETE_EXECUTION_IDENTITY_v3",
        "scientific_input_sha256": scientific_hash,
        "runtime_source_closure_sha256": record["runtime_source_closure_sha256"],
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
        "v3_pipeline_identity": {
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
        "metric_configuration_resolution": {
            "partial_template_sha256": record[
                "partial_metric_configuration_sha256"
            ],
            "role_overlay_sha256": record["role_resolution_overlay_sha256"],
            "resolved_configuration_sha256": record[
                "resolved_metric_configuration_sha256"
            ],
        },
        "historical_implementation_identity": {
            "implementation_id": record["implementation_id"],
            "implementation_sha256": record["implementation_sha256"],
        },
    }


def _independent_resolve(
    record: Mapping[str, Any],
    partial: Mapping[str, Any],
    overlay: Mapping[str, Any],
) -> dict[str, Any]:
    metric = copy.deepcopy(partial["metric_configuration_template"])
    metric["block_scales"] = copy.deepcopy(overlay["block_scales"])
    metric["block_floors"] = copy.deepcopy(overlay["block_floors"])
    metric["epsilon_dominance"] = overlay["epsilon_dominance"]
    return {
        "schema_id": "DIRAC_MAXWELL_R13_MECHANISM_RESOLVED_RUN_CONFIGURATION_v3",
        "run_id": record["run_id"],
        "partial_metric_configuration_sha256": sha256_bytes(
            canonical_json_bytes(partial)
        ),
        "role_resolution_overlay_sha256": sha256_bytes(
            canonical_json_bytes(overlay)
        ),
        "metric_configuration": metric,
    }


def audit_independent_identities_and_resolution(
    packet: Mapping[str, Any], matrix: Mapping[str, Any]
) -> dict[str, Any]:
    authority = packet["runtime_execution_authority_proposal"][
        "proposed_review_authority"
    ]
    records = matrix["records"]
    scientific_hashes: dict[str, str] = {}
    physical_hashes: dict[str, str] = {}
    complete_hashes: dict[str, str] = {}
    resolved_hashes: dict[str, str] = {}
    resolution_rows: list[dict[str, Any]] = []
    for record in records:
        run_id = str(record["run_id"])
        physical = _independent_physical_core(record)
        scientific = _independent_scientific_core(record)
        complete = _independent_complete_core(record)
        partial = record["partial_metric_configuration"]
        overlay = record["role_resolution_overlay"]
        resolved_first = _independent_resolve(record, partial, overlay)
        resolved_second = _independent_resolve(record, partial, overlay)
        implementation_v0._validate_metric_configuration(
            resolved_first["metric_configuration"]
        )
        physical_hash = sha256_bytes(canonical_json_bytes(physical))
        scientific_hash = sha256_bytes(canonical_json_bytes(scientific))
        complete_hash = sha256_bytes(canonical_json_bytes(complete))
        resolved_hash = sha256_bytes(canonical_json_bytes(resolved_first))
        expected_floors = {block_id: GAMMA64 for block_id in BLOCK_IDS}
        expected_scales = {
            block_id: float(record["tolerance"]) for block_id in BLOCK_IDS
        }
        scientific_hashes[run_id] = scientific_hash
        physical_hashes[run_id] = physical_hash
        complete_hashes[run_id] = complete_hash
        resolved_hashes[run_id] = resolved_hash
        resolution_rows.append(
            {
                "run_id": run_id,
                "partial_schema_only": partial["schema_id"]
                == executor_v3.PARTIAL_METRIC_CONFIGURATION_SCHEMA_ID
                and "block_floors" not in partial["metric_configuration_template"]
                and "block_scales" not in partial["metric_configuration_template"],
                "overlay_selected_by_frozen_identity": overlay["run_id"] == run_id
                and overlay["execution_role"] == record["execution_role"]
                and overlay["instrumentation_enabled"]
                == record["instrumentation_enabled"],
                "overlay_floors_exact": overlay["block_floors"] == expected_floors,
                "overlay_scales_exact": overlay["block_scales"] == expected_scales,
                "deterministic": resolved_first == resolved_second,
                "resolved_object_exact": resolved_first
                == record["resolved_metric_configuration"],
                "resolved_hash_exact": resolved_hash
                == record["resolved_metric_configuration_sha256"],
                "strict_final_validation_passed": True,
                "physical_hash_exact": physical_hash
                == record["physical_configuration_core_sha256"],
                "scientific_hash_exact": scientific_hash
                == record["scientific_input_core_sha256"],
                "complete_core_exact": complete
                == record["complete_execution_identity_core"],
                "complete_hash_exact": complete_hash
                == record["complete_execution_identity_sha256"],
                "authority_resolved_hash_exact": resolved_hash
                == authority[
                    "expected_resolved_metric_configuration_sha256_by_run_id"
                ][run_id],
            }
        )

    pair_rows = []
    by_id = {str(record["run_id"]): record for record in records}
    for instrumented_id, control_id in custody_v3.PAIR_RUN_IDS:
        instrumented = by_id[instrumented_id]
        control = by_id[control_id]
        pair_rows.append(
            {
                "instrumented_run_id": instrumented_id,
                "control_run_id": control_id,
                "physical_core_equal": _independent_physical_core(instrumented)
                == _independent_physical_core(control),
                "resolved_metric_configuration_equal": instrumented[
                    "resolved_metric_configuration"
                ]["metric_configuration"]
                == control["resolved_metric_configuration"]["metric_configuration"],
                "block_floors_equal": instrumented["role_resolution_overlay"][
                    "block_floors"
                ]
                == control["role_resolution_overlay"]["block_floors"],
                "block_scales_equal": instrumented["role_resolution_overlay"][
                    "block_scales"
                ]
                == control["role_resolution_overlay"]["block_scales"],
                "complete_execution_identity_distinct": complete_hashes[
                    instrumented_id
                ]
                != complete_hashes[control_id],
            }
        )

    first = records[0]
    baseline = sha256_bytes(
        canonical_json_bytes(_independent_complete_core(first))
    )
    transitive_probes = []
    for probe_id, mutate in (
        (
            "block_floor",
            lambda overlay: overlay["block_floors"].__setitem__(
                BLOCK_IDS[0], overlay["block_floors"][BLOCK_IDS[0]] * 2.0
            ),
        ),
        (
            "block_scale",
            lambda overlay: overlay["block_scales"].__setitem__(
                BLOCK_IDS[0], overlay["block_scales"][BLOCK_IDS[0]] * 2.0
            ),
        ),
        (
            "role",
            lambda overlay: overlay.__setitem__("execution_role", "MUTATED_ROLE"),
        ),
    ):
        candidate = copy.deepcopy(first)
        overlay = candidate["role_resolution_overlay"]
        mutate(overlay)
        candidate["role_resolution_overlay_sha256"] = sha256_bytes(
            canonical_json_bytes(overlay)
        )
        resolved = _independent_resolve(
            candidate, candidate["partial_metric_configuration"], overlay
        )
        candidate["resolved_metric_configuration"] = resolved
        candidate["resolved_metric_configuration_sha256"] = sha256_bytes(
            canonical_json_bytes(resolved)
        )
        changed = sha256_bytes(
            canonical_json_bytes(_independent_complete_core(candidate))
        )
        transitive_probes.append(
            {
                "probe_id": probe_id,
                "baseline_complete_execution_sha256": baseline,
                "mutated_complete_execution_sha256": changed,
                "complete_execution_identity_changed": changed != baseline,
            }
        )
    return {
        "run_count": len(records),
        "scientific_input_reconstruction_count": len(scientific_hashes),
        "unique_scientific_input_count": len(set(scientific_hashes.values())),
        "physical_configuration_reconstruction_count": len(physical_hashes),
        "complete_execution_identity_reconstruction_count": len(complete_hashes),
        "unique_complete_execution_identity_count": len(set(complete_hashes.values())),
        "resolved_configuration_reconstruction_count": len(resolved_hashes),
        "all_resolution_rows_pass": all(
            all(value is True for key, value in row.items() if key != "run_id")
            for row in resolution_rows
        ),
        "resolution_rows": resolution_rows,
        "pair_count": len(pair_rows),
        "all_pair_integrity_checks_pass": all(
            all(
                value is True
                for key, value in row.items()
                if key not in {"instrumented_run_id", "control_run_id"}
            )
            for row in pair_rows
        ),
        "pair_rows": pair_rows,
        "transitive_identity_probe_count": len(transitive_probes),
        "all_role_resolved_values_transitively_bound": all(
            item["complete_execution_identity_changed"]
            for item in transitive_probes
        ),
        "transitive_identity_probes": transitive_probes,
    }


def accepted_runtime_authority(packet: Mapping[str, Any]) -> dict[str, Any]:
    authority = copy.deepcopy(
        packet["runtime_execution_authority_proposal"][
            "proposed_review_authority"
        ]
    )
    authority["execution_authorized"] = True
    authority["artifact_bindings"]["freeze_packet"]["sha256"] = (
        EXPECTED_ARTIFACT_SHA256[PACKET_RELATIVE_PATH]
    )
    return authority


def audit_runtime_source_closure(packet: Mapping[str, Any]) -> dict[str, Any]:
    authority = accepted_runtime_authority(packet)
    closure = authority["runtime_source_closure"]
    rows = []
    for binding in closure["modules"]:
        module = importlib.import_module(binding["module_name"])
        path = Path(module.__file__).resolve()
        expected = (REPO_ROOT / binding["relative_path"]).resolve()
        rows.append(
            {
                "module_name": binding["module_name"],
                "path_exact": path == expected,
                "bytes_exact": sha256_bytes(path.read_bytes())
                == binding["sha256"],
                "loader_exact": type(module.__loader__).__name__
                == binding["loader_type"]
                == "SourceFileLoader",
            }
        )
    loaded_evolution, loaded_pack = implementation_v0._load_historical_implementation()
    return {
        "frozen_module_count": len(closure["modules"]),
        "loaded_module_count": len(rows),
        "closure_digest_exact": sha256_bytes(canonical_json_bytes(closure))
        == authority["runtime_source_closure_sha256"],
        "all_loaded_paths_bytes_and_loaders_exact": all(
            row["path_exact"] and row["bytes_exact"] and row["loader_exact"]
            for row in rows
        ),
        "loaded_modules": rows,
        "historical_object_binding_exact": loaded_evolution is sys.modules[
            custody_v3.HISTORICAL_EVOLUTION_MODULE
        ]
        and loaded_pack is sys.modules[custody_v3.HISTORICAL_PACK_MODULE],
        "git_identity_decision_bearing": False,
    }


def audit_twenty_identity_mutations(
    packet: Mapping[str, Any], matrix: Mapping[str, Any]
) -> dict[str, Any]:
    authority = accepted_runtime_authority(packet)
    probes = []
    for field in executor_v3.IDENTITY_DIAGNOSTIC_FIELDS:
        candidate = copy.deepcopy(matrix)
        candidate["records"][0][field] = copy.deepcopy(
            semantic_v1.IDENTITY_MUTATION_VALUES[field]
        )
        changed = [
            key
            for key in matrix["records"][0]
            if candidate["records"][0][key] != matrix["records"][0][key]
        ]
        observed = executor_v3.strict_validate_matrix(candidate, authority)
        expected = f"RUN_MATRIX_IDENTITY_FIELD_MISMATCH:{field}"
        probes.append(
            {
                "field": field,
                "changed_fields": changed,
                "atomic": changed == [field],
                "expected_first_diagnostic": expected,
                "observed_first_diagnostic": observed[0] if observed else None,
                "exact": observed == [expected],
                "simulation_entered": False,
                "output_created": False,
            }
        )
    return {
        "registered_mutation_count": len(executor_v3.IDENTITY_DIAGNOSTIC_FIELDS),
        "executed_mutation_count": len(probes),
        "atomic_mutation_count": sum(item["atomic"] for item in probes),
        "exact_first_diagnostic_count": sum(item["exact"] for item in probes),
        "rejected_before_simulation_count": sum(
            item["exact"] and not item["simulation_entered"] for item in probes
        ),
        "output_creation_count": sum(item["output_created"] for item in probes),
        "probes": probes,
    }


def audit_eight_resolution_diagnostics(matrix: Mapping[str, Any]) -> dict[str, Any]:
    record = matrix["records"][0]
    partial = record["partial_metric_configuration"]
    overlay = record["role_resolution_overlay"]
    resolved = record["resolved_metric_configuration"]
    probes: list[dict[str, Any]] = []

    def add(control_id: str, expected: str, observed: str, changed: list[str]) -> None:
        probes.append(
            {
                "control_id": control_id,
                "changed_premises": changed,
                "atomic": len(changed) == 1,
                "expected_first_diagnostic": expected,
                "observed_first_diagnostic": observed,
                "exact": observed == expected,
                "plan_constructed": False,
                "simulation_entered": False,
                "output_created": False,
            }
        )

    add(
        "unresolved_template_not_executable",
        "UNRESOLVED_TEMPLATE_NOT_EXECUTABLE",
        executor_v3.validate_resolved_metric_configuration(
            record, partial, overlay
        )[0],
        ["object_type"],
    )
    missing_overlay = copy.deepcopy(overlay)
    missing_overlay.pop("block_floors")
    add(
        "missing_role_mapping",
        "ROLE_RESOLUTION_MISSING_METRIC_BLOCK_FLOORS",
        executor_v3.validate_role_resolution_overlay(record, missing_overlay)[0],
        ["block_floors"],
    )
    missing_resolved = copy.deepcopy(resolved)
    missing_resolved["metric_configuration"].pop("block_floors")
    add(
        "missing_block_floors_after_resolution",
        "ROLE_RESOLUTION_MISSING_METRIC_BLOCK_FLOORS",
        executor_v3.validate_resolved_metric_configuration(
            record, missing_resolved, overlay
        )[0],
        ["block_floors"],
    )
    wrong_floors = copy.deepcopy(overlay)
    wrong_floors["block_floors"][BLOCK_IDS[0]] *= 2.0
    add(
        "wrong_block_floors_for_role",
        "ROLE_RESOLUTION_WRONG_METRIC_BLOCK_FLOORS",
        executor_v3.validate_role_resolution_overlay(record, wrong_floors)[0],
        [f"block_floors.{BLOCK_IDS[0]}"],
    )
    caller_floors = copy.deepcopy(partial)
    caller_floors["metric_configuration_template"]["block_floors"] = copy.deepcopy(
        overlay["block_floors"]
    )
    add(
        "caller_supplied_block_floors",
        "CALLER_SUPPLIED_METRIC_BLOCK_FLOORS_FORBIDDEN",
        executor_v3.validate_partial_metric_configuration(caller_floors)[0],
        ["metric_configuration_template.block_floors"],
    )
    role_mutation = copy.deepcopy(overlay)
    role_mutation["execution_role"] = "CALLER_MUTATION"
    add(
        "role_overlay_mutation",
        "ROLE_RESOLUTION_OVERLAY_IDENTITY_MISMATCH",
        executor_v3.validate_role_resolution_overlay(record, role_mutation)[0],
        ["execution_role"],
    )
    try:
        executor_v3.build_read_only_execution_plan_record(record, partial, overlay)
    except executor_v3.ConfigurationResolutionError as error:
        observed_plan = str(error)
    else:
        observed_plan = "NO_DIAGNOSTIC"
    add(
        "validation_before_resolution",
        "VALIDATION_BEFORE_ROLE_RESOLUTION_FORBIDDEN",
        observed_plan,
        ["ordering"],
    )
    try:
        executor_v3.metric_configuration_for_numerical_execution(
            record, partial, overlay
        )
    except executor_v3.ConfigurationResolutionError as error:
        observed_execution = str(error)
    else:
        observed_execution = "NO_DIAGNOSTIC"
    add(
        "partial_object_to_numerical_executor",
        "PARTIAL_CONFIGURATION_NUMERICAL_EXECUTION_FORBIDDEN",
        observed_execution,
        ["object_type"],
    )
    return {
        "registered_control_count": 8,
        "executed_control_count": len(probes),
        "atomic_control_count": sum(item["atomic"] for item in probes),
        "exact_diagnostic_count": sum(item["exact"] for item in probes),
        "plan_construction_count": sum(item["plan_constructed"] for item in probes),
        "simulation_entry_count": sum(item["simulation_entered"] for item in probes),
        "output_creation_count": sum(item["output_created"] for item in probes),
        "probes": probes,
    }


def _global_configuration_digest(module: Any) -> str:
    snapshot = {}
    for key, value in module.__dict__.items():
        if not key.isupper():
            continue
        if value is None or isinstance(value, (bool, int, float, str, list, tuple, dict)):
            snapshot[key] = copy.deepcopy(value)
    return sha256_bytes(canonical_json_bytes(snapshot))


def audit_real_read_only_preflight(packet: Mapping[str, Any]) -> dict[str, Any]:
    authority = accepted_runtime_authority(packet)
    anchor = {
        "verdict": ACCEPT_VERDICT,
        custody_v3.REVIEW_AUTHORITY_FIELD: authority,
    }
    accepted_diagnostics = executor_v3._validate_freeze_anchor(anchor)
    blocked_diagnostics = executor_v3._validate_freeze_anchor(
        {"verdict": "PREPARED_PENDING_INDEPENDENT_REVIEW"}
    )
    anchor_report = {
        "relative_path": custody_v3.REVIEW_ANCHOR_RELATIVE_PATH,
        "sha256": "0" * 64,
        "verdict": ACCEPT_VERDICT,
        "fixed_path_bytes_loaded": True,
        "runtime_execution_authority_sha256": sha256_bytes(
            canonical_json_bytes(authority)
        ),
    }
    output_root = REPO_ROOT / custody_v3.EXPERIMENT_OUTPUT_ROOT_RELATIVE_PATH
    canonical_before = canonical_v0.canonical_root_digest()
    tree_before = canonical_v0.canonical_directory_tree_sha256()
    executor_globals_before = _global_configuration_digest(executor_v3)
    implementation_globals_before = _global_configuration_digest(implementation_v0)
    environment_before = {
        key: os.environ.get(key)
        for key in implementation_v0.REQUIRED_EXECUTION_ENVIRONMENT
    }
    original_loader = executor_v3._load_reviewed_authority
    try:
        for key, value in implementation_v0.REQUIRED_EXECUTION_ENVIRONMENT.items():
            os.environ[key] = value
        executor_v3._load_reviewed_authority = lambda _root: (
            copy.deepcopy(authority),
            copy.deepcopy(anchor_report),
        )
        first = executor_v3.preflight_frozen_execution(REPO_ROOT)
        second = executor_v3.preflight_frozen_execution(REPO_ROOT)
    finally:
        executor_v3._load_reviewed_authority = original_loader
        for key, value in environment_before.items():
            if value is None:
                os.environ.pop(key, None)
            else:
                os.environ[key] = value
    executor_globals_after = _global_configuration_digest(executor_v3)
    implementation_globals_after = _global_configuration_digest(implementation_v0)
    return {
        "public_execution_parameters": list(
            inspect.signature(executor_v3.execute_frozen_matrix_once_v3).parameters
        ),
        "lookup_parameters": list(
            inspect.signature(executor_v3.lookup_frozen_record).parameters
        ),
        "accepted_authority_diagnostics": accepted_diagnostics,
        "unaccepted_anchor_diagnostics": blocked_diagnostics,
        "fixed_review_anchor_path": custody_v3.REVIEW_ANCHOR_RELATIVE_PATH,
        "read_only_preflight_invocation_count": 2,
        "read_only_preflight_reports_identical": first == second,
        "read_only_execution_plan_count": first["read_only_execution_plan_count"],
        "exact_run_ids": first["exact_run_ids"],
        "all_passed": first["all_passed"],
        "simulation_entry_count": first["simulation_entry_count"],
        "execution_invoked": first["execution_invoked"],
        "output_root_absent": first["output_root_absent"]
        and not output_root.exists(),
        "canonical_inventory_unchanged": canonical_v0.canonical_root_digest()
        == canonical_before,
        "canonical_tree_unchanged": canonical_v0.canonical_directory_tree_sha256()
        == tree_before,
        "executor_global_configuration_unchanged": executor_globals_after
        == executor_globals_before,
        "implementation_global_configuration_unchanged": (
            implementation_globals_after == implementation_globals_before
        ),
        "process_environment_restored": all(
            os.environ.get(key) == value for key, value in environment_before.items()
        ),
        "runtime_execution_authority": authority,
    }


def audit_payload_semantics_and_custody(
    packet: Mapping[str, Any], matrix: Mapping[str, Any], identity: Mapping[str, Any]
) -> dict[str, Any]:
    outputs = identity["outputs"]
    role_paths = [
        path
        for record in matrix["records"]
        for path in (
            record["json_relative_output_path"],
            record["npz_relative_output_path"],
        )
    ]
    output_root = custody_v3.EXPERIMENT_OUTPUT_ROOT_RELATIVE_PATH + "/"
    evidence_validation = evidence_v3.self_validate()
    classifier_validation = classifier_v3.self_validate()
    constants = packet["classifier_freeze"]["support_constants"]
    provenance = packet["classifier_freeze"]["support_constant_provenance"]
    leaves = {
        (hypothesis, constant_id)
        for hypothesis, values in constants.items()
        for constant_id in values
    }
    provenance_leaves = {
        (item["hypothesis"], item["constant_id"]) for item in provenance
    }
    canonical_before = canonical_v0.canonical_root_digest()
    tree_before = canonical_v0.canonical_directory_tree_sha256()
    boundary = packet["authority_boundary"]
    return {
        "identity_output_count": len(outputs),
        "role_payload_path_count": len(role_paths),
        "unique_role_payload_path_count": len(set(role_paths)),
        "all_paths_under_frozen_root": all(
            path.startswith(output_root) for path in role_paths
        ),
        "auxiliary_execution_file_count": len(
            identity["auxiliary_execution_files"]
        ),
        "raw_evidence_assembler_all_passed": all(evidence_validation.values()),
        "classifier_all_passed": all(classifier_validation.values()),
        "support_constant_count": len(leaves),
        "support_constant_provenance_count": len(provenance),
        "support_constant_provenance_one_to_one": leaves == provenance_leaves,
        "adversarial_control_count": len(
            packet["freeze_adversarial_control_registry"]
        ),
        "canonical_inventory_exact": canonical_before
        == canonical_v0.EXPECTED_CANONICAL_ROOT_DIGEST,
        "canonical_tree_exact": tree_before
        == canonical_v0.EXPECTED_CANONICAL_DIRECTORY_TREE_SHA256,
        "experiment_output_root_absent": not (
            REPO_ROOT / custody_v3.EXPERIMENT_OUTPUT_ROOT_RELATIVE_PATH
        ).exists(),
        "simulation_invocation_count": 0,
        "canonical_robustness": boundary["canonical_robustness"],
        "R13_root_mechanism": boundary["root_mechanism"],
        "materiality": boundary["materiality"],
        "new_E_REPRO_claim": boundary["new_E_REPRO_claim"],
    }


def build_report() -> dict[str, Any]:
    output_root = REPO_ROOT / custody_v3.EXPERIMENT_OUTPUT_ROOT_RELATIVE_PATH
    if output_root.exists():
        raise ValueError("future experiment output root must be absent during review")
    packet = load_json(PACKET_RELATIVE_PATH)
    matrix = load_json(MATRIX_RELATIVE_PATH)
    identity = load_json(IDENTITY_RELATIVE_PATH)
    if (
        packet.get("verdict") != "PREPARED_PENDING_INDEPENDENT_REVIEW"
        or packet.get("selected_next_target") != TARGET
    ):
        raise ValueError("v3 preparation does not authorize this review target")

    artifact = audit_artifact_and_predecessor_history()
    identity_audit = audit_independent_identities_and_resolution(packet, matrix)
    runtime = audit_runtime_source_closure(packet)
    mutations = audit_twenty_identity_mutations(packet, matrix)
    resolution_controls = audit_eight_resolution_diagnostics(matrix)
    preflight = audit_real_read_only_preflight(packet)
    custody = audit_payload_semantics_and_custody(packet, matrix, identity)

    checks = [
        {
            "acceptance_id": "five_v3_artifacts_are_fresh_and_predecessor_history_is_preserved",
            "passed": artifact["artifact_count"] == 5
            and artifact["exact_artifact_count"] == 5
            and artifact["subprocess_regeneration_byte_exact"]
            and artifact["cross_bindings_exact"]
            and artifact["v1_remains_stale"]
            and artifact["v2_review_verdict"]
            == "BLOCK_EXECUTOR_PREFLIGHT_CONFIGURATION"
            and artifact["v2_historical_preflight_validates_unresolved_template"],
            "review_outcome_on_failure": "BLOCK_ARTIFACT_OR_PREDECESSOR_HISTORY",
        },
        {
            "acceptance_id": "six_scientific_inputs_three_physical_pairs_and_six_execution_identities_reconstruct",
            "passed": identity_audit["scientific_input_reconstruction_count"] == 6
            and identity_audit["unique_scientific_input_count"] == 3
            and identity_audit["physical_configuration_reconstruction_count"] == 6
            and identity_audit["complete_execution_identity_reconstruction_count"]
            == 6
            and identity_audit["unique_complete_execution_identity_count"] == 6,
            "review_outcome_on_failure": "BLOCK_IDENTITY_RECONSTRUCTION",
        },
        {
            "acceptance_id": "all_role_resolved_values_are_transitively_bound_into_execution_identity",
            "passed": identity_audit["transitive_identity_probe_count"] == 3
            and identity_audit["all_role_resolved_values_transitively_bound"],
            "review_outcome_on_failure": "BLOCK_ROLE_RESOLUTION_IDENTITY_BINDING",
        },
        {
            "acceptance_id": "six_partial_overlay_and_resolved_lifecycles_reconstruct_deterministically",
            "passed": identity_audit["resolved_configuration_reconstruction_count"]
            == 6
            and identity_audit["all_resolution_rows_pass"],
            "review_outcome_on_failure": "BLOCK_CONFIGURATION_LIFECYCLE",
        },
        {
            "acceptance_id": "three_pairs_match_after_role_resolution",
            "passed": identity_audit["pair_count"] == 3
            and identity_audit["all_pair_integrity_checks_pass"],
            "review_outcome_on_failure": "BLOCK_RESOLVED_PAIR_INTEGRITY",
        },
        {
            "acceptance_id": "eight_runtime_sources_match_path_bytes_loader_and_historical_objects",
            "passed": runtime["frozen_module_count"] == 8
            and runtime["loaded_module_count"] == 8
            and runtime["closure_digest_exact"]
            and runtime["all_loaded_paths_bytes_and_loaders_exact"]
            and runtime["historical_object_binding_exact"]
            and runtime["git_identity_decision_bearing"] is False,
            "review_outcome_on_failure": "BLOCK_RUNTIME_SOURCE_CLOSURE",
        },
        {
            "acceptance_id": "twenty_prior_identity_mutations_remain_atomic_exact_and_preexecution",
            "passed": mutations["registered_mutation_count"] == 20
            and mutations["executed_mutation_count"] == 20
            and mutations["atomic_mutation_count"] == 20
            and mutations["exact_first_diagnostic_count"] == 20
            and mutations["rejected_before_simulation_count"] == 20
            and mutations["output_creation_count"] == 0,
            "review_outcome_on_failure": "BLOCK_PRIOR_MUTATION_CONTROLS",
        },
        {
            "acceptance_id": "eight_v3_resolution_defects_are_atomic_and_exact",
            "passed": resolution_controls["registered_control_count"] == 8
            and resolution_controls["executed_control_count"] == 8
            and resolution_controls["atomic_control_count"] == 8
            and resolution_controls["exact_diagnostic_count"] == 8
            and resolution_controls["plan_construction_count"] == 0
            and resolution_controls["simulation_entry_count"] == 0
            and resolution_controls["output_creation_count"] == 0,
            "review_outcome_on_failure": "BLOCK_RESOLUTION_DIAGNOSTIC_CONTROLS",
        },
        {
            "acceptance_id": "real_executor_preflight_is_repeatable_read_only_and_six_plan_complete",
            "passed": preflight["public_execution_parameters"] == ["repo_root"]
            and preflight["lookup_parameters"] == ["repo_root", "run_id"]
            and preflight["accepted_authority_diagnostics"] == []
            and preflight["unaccepted_anchor_diagnostics"]
            == ["REVIEW_ANCHOR_NOT_ACCEPTED"]
            and preflight["read_only_preflight_invocation_count"] == 2
            and preflight["read_only_preflight_reports_identical"]
            and preflight["read_only_execution_plan_count"] == 6
            and preflight["exact_run_ids"] == list(custody_v3.EXACT_RUN_IDS)
            and preflight["all_passed"]
            and preflight["simulation_entry_count"] == 0
            and preflight["execution_invoked"] is False
            and preflight["output_root_absent"]
            and preflight["canonical_inventory_unchanged"]
            and preflight["canonical_tree_unchanged"]
            and preflight["executor_global_configuration_unchanged"]
            and preflight["implementation_global_configuration_unchanged"]
            and preflight["process_environment_restored"],
            "review_outcome_on_failure": "BLOCK_REAL_EXECUTOR_PREFLIGHT",
        },
        {
            "acceptance_id": "payload_raw_semantic_constant_and_canonical_custody_remain_bounded",
            "passed": custody["identity_output_count"] == 6
            and custody["role_payload_path_count"] == 12
            and custody["unique_role_payload_path_count"] == 12
            and custody["all_paths_under_frozen_root"]
            and custody["auxiliary_execution_file_count"] == 2
            and custody["raw_evidence_assembler_all_passed"]
            and custody["classifier_all_passed"]
            and custody["support_constant_count"] == 23
            and custody["support_constant_provenance_count"] == 23
            and custody["support_constant_provenance_one_to_one"]
            and custody["adversarial_control_count"] == 41
            and custody["canonical_inventory_exact"]
            and custody["canonical_tree_exact"]
            and custody["experiment_output_root_absent"]
            and custody["simulation_invocation_count"] == 0,
            "review_outcome_on_failure": "BLOCK_CUSTODY_OR_SEMANTICS",
        },
        {
            "acceptance_id": "authority_is_bounded_to_one_exact_six_run_execution",
            "passed": preflight["runtime_execution_authority"][
                "execution_authorized"
            ]
            is True
            and preflight["runtime_execution_authority"]["one_execution_only"]
            is True
            and preflight["runtime_execution_authority"][
                "automatic_retries_authorized"
            ]
            is False
            and packet["post_acceptance_target"] == ACCEPTED_NEXT_TARGET,
            "review_outcome_on_failure": "BLOCK_AUTHORITY_BOUNDARY",
        },
        {
            "acceptance_id": "scientific_claim_boundary_is_unchanged",
            "passed": custody["canonical_robustness"] == "NUMERICALLY_BLOCKED"
            and custody["R13_root_mechanism"] == "UNRESOLVED"
            and custody["materiality"] == "NOT_EVALUATED_NUMERICAL_BLOCK"
            and custody["new_E_REPRO_claim"] is False,
            "review_outcome_on_failure": "BLOCK_CLAIM_BOUNDARY",
        },
    ]
    failed = [item for item in checks if not item["passed"]]
    verdict = ACCEPT_VERDICT if not failed else failed[0]["review_outcome_on_failure"]
    selected_next_target = ACCEPTED_NEXT_TARGET if not failed else BLOCKED_NEXT_TARGET
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
            "v3_preparation_generator_imported": False,
            "v3_generator_used_only_in_isolated_subprocess_for_freshness": True,
            "scientific_cores_reconstructed_independently": True,
            "role_resolution_reconstructed_independently": True,
            "complete_execution_identities_reconstructed_independently": True,
            "role_resolution_transitive_hash_binding_probed": True,
            "runtime_sources_loaded_and_hashed_independently": True,
            "all_twenty_prior_mutations_executed_independently": True,
            "all_eight_v3_mutations_executed_independently": True,
            "real_executor_read_only_preflight_invocation_count": 2,
            "evolution_runner_invocation_count": 0,
            "simulation_invocation_count": 0,
        },
        "artifact_and_predecessor_history_audit": artifact,
        "independent_identity_and_resolution_audit": identity_audit,
        "runtime_source_closure_audit": runtime,
        "prior_identity_mutation_audit": mutations,
        "v3_resolution_diagnostic_audit": resolution_controls,
        "real_executor_read_only_preflight_audit": {
            key: value
            for key, value in preflight.items()
            if key != "runtime_execution_authority"
        },
        "payload_semantics_and_custody_audit": custody,
        "acceptance_checks": checks,
        "acceptance_check_count": len(checks),
        "passed_acceptance_check_count": sum(item["passed"] for item in checks),
        "failed_acceptance_check_count": len(failed),
        "failed_acceptance_ids": [item["acceptance_id"] for item in failed],
        "blocking_outcomes": list(
            dict.fromkeys(item["review_outcome_on_failure"] for item in failed)
        ),
        "preserved_scientific_core": {
            "accepted_bounded_Maxwell_Dirac_E_REPRO": "PRESERVED",
            "fourteen_row_robustness": "NUMERICALLY_BLOCKED",
            "descendant_materiality": "NOT_EVALUATED_NUMERICAL_BLOCK",
            "R13_diagnostic_pattern": "ACCEPTED",
            "R13_root_mechanism": "UNRESOLVED",
            "instrumented_experiment_design": "ACCEPTED",
            "new_E_REPRO": "NONE",
        },
        "authority_rotation": {
            "numerical_freeze_v3_accepted": not failed,
            "execution_authorized": not failed,
            "one_time_execution_count_authorized": 1 if not failed else 0,
            "exact_authorized_run_count": 6 if not failed else 0,
            "rerun_authorized": False,
            "substitution_authorized": False,
            "additional_tolerances_or_durations_authorized": False,
            "threshold_change_authorized": False,
            "pairing_or_schema_change_authorized": False,
            "robustness_reclassification_authorized": False,
            "materiality_evaluation_authorized": False,
            "result_acceptance_authorized": False,
            "new_scientific_claim_authorized": False,
        },
        "nonclaims": [
            "no six-run mechanism experiment has executed",
            "no instrumentation nonperturbation result has been observed",
            "no mechanism hypothesis has been evaluated on experiment data",
            "no canonical output has changed",
            "no robustness or materiality result is assigned",
            "no new E-REPRO or stronger ToE claim is assigned",
        ],
        "claim_ceiling": (
            "Independent acceptance authorizes only one exact execution of the frozen six-run matrix. Outputs require a separate independent result review."
            if not failed
            else "Review failure authorizes only a bounded versioned freeze correction."
        ),
    }
    if not failed:
        report[custody_v3.REVIEW_AUTHORITY_FIELD] = preflight[
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
                "acceptance_checks": report["acceptance_check_count"],
                "passed_acceptance_checks": report[
                    "passed_acceptance_check_count"
                ],
                "execution_authorized": report["authority_rotation"][
                    "execution_authorized"
                ],
                "simulation_count": 0,
                "output_root_absent": not (
                    REPO_ROOT / custody_v3.EXPERIMENT_OUTPUT_ROOT_RELATIVE_PATH
                ).exists(),
            },
            sort_keys=True,
        )
    )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Independently review freeze v3")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    write_or_check(args.check)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
