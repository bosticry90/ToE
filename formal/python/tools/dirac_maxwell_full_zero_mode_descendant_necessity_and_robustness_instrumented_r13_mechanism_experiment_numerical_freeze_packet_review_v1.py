from __future__ import annotations

"""Independently review the corrected R13 numerical-freeze-v1 proposal.

The review is deliberately read-only.  It does not import the v1 preparation
generator, create the future output root, or invoke an evolution/simulation
entry point.  A failed acceptance condition rotates authority only to a
versioned v2 freeze correction.
"""

import argparse
import copy
import hashlib
import importlib.machinery
import inspect
import json
import subprocess
import sys
import types
import unicodedata
from pathlib import Path, PurePosixPath
from typing import Any

import numpy as np

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_classifier_v1
    as classifier_v1,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_executor_custody_v1
    as custody_v1,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_executor_v1
    as executor_v1,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_numerical_freeze_packet_v0
    as predecessor_v0,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_raw_evidence_assembler_v1
    as evidence_v1,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_semantic_contract_v1
    as semantic_v1,
)


REPO_ROOT = find_repo_root(Path(__file__))
CAPTURED_AT_UTC = "2026-07-16T00:00:00Z"
TARGET = (
    "review_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
    "instrumented_r13_mechanism_experiment_numerical_freeze_packet_v1_result"
)
SELECTED_NEXT_TARGET = (
    "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
    "instrumented_r13_mechanism_experiment_numerical_freeze_packet_v2"
)
VERDICT = "BLOCK_INPUT_HASH_RECONSTRUCTION"
SECONDARY_BLOCKER = "BLOCK_MUTATION_COVERAGE_OR_ATOMICITY"
SCHEMA_ID = (
    "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_"
    "INSTRUMENTED_R13_MECHANISM_EXPERIMENT_NUMERICAL_FREEZE_PACKET_REVIEW_"
    "20260715_v1"
)
REPORT_RELATIVE_PATH = custody_v1.REVIEW_ANCHOR_RELATIVE_PATH
PACKET_RELATIVE_PATH = custody_v1.FREEZE_PACKET_RELATIVE_PATH
MATRIX_RELATIVE_PATH = custody_v1.RUN_MATRIX_RELATIVE_PATH
IDENTITY_RELATIVE_PATH = custody_v1.IDENTITY_MANIFEST_RELATIVE_PATH
MANIFEST_RELATIVE_PATH = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-INSTRUMENTED-R13-MECHANISM-EXPERIMENT-NUMERICAL-FREEZE-"
    "MANIFEST-v1.json"
)
PREPARATION_REPORT_RELATIVE_PATH = (
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
    "ROBUSTNESS_INSTRUMENTED_R13_MECHANISM_EXPERIMENT_NUMERICAL_FREEZE_PACKET_"
    "20260715_v1.json"
)
GENERATOR_RELATIVE_PATH = (
    "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_"
    "robustness_instrumented_r13_mechanism_experiment_numerical_freeze_packet_v1.py"
)

EXPECTED_ARTIFACT_SHA256 = {
    PACKET_RELATIVE_PATH: "68f735a3b125e8c57901b687729943c61bbff370ecfda8a499db97546ea499fa",
    MATRIX_RELATIVE_PATH: "9b8e60e0a118b8ad18784cd7307f3c75744223ce4ba849fe761fbae3b1aa96b6",
    IDENTITY_RELATIVE_PATH: "350ad5c30c8ffb7428733f7c2c1177f512f7e1fe432693da6a00d03eb17d7302",
    MANIFEST_RELATIVE_PATH: "8c39cf03284490e589ba2fe46c256df1a4acc43cd45a7ce46626457ac47d02c0",
    PREPARATION_REPORT_RELATIVE_PATH: "4b69b61bbb4445069a1e002ce38aa537284776049a236c55bddc2212bcc2e3a6",
}
EXPECTED_SUPPORT_CONSTANTS_SHA256 = (
    "037486b3ced7765f6b12cdef69e497aff1c18d7fe81cb57b294e6c50bae7337c"
)
STALE_ARTIFACT_PATHS = tuple(EXPECTED_ARTIFACT_SHA256)


def _normalize(value: Any) -> Any:
    if isinstance(value, str):
        return unicodedata.normalize("NFC", value)
    if value is None or isinstance(value, (bool, int)):
        return value
    if isinstance(value, float):
        if not np.isfinite(value):
            raise ValueError("nonfinite value in canonical JSON")
        return value
    if isinstance(value, list):
        return [_normalize(item) for item in value]
    if isinstance(value, tuple):
        return [_normalize(item) for item in value]
    if isinstance(value, dict):
        return {_normalize(str(key)): _normalize(item) for key, item in value.items()}
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


def git_blob_oid(raw: bytes) -> str:
    return hashlib.sha1(f"blob {len(raw)}\0".encode("ascii") + raw).hexdigest()


def load_json(relative_path: str) -> dict[str, Any]:
    value = json.loads((REPO_ROOT / relative_path).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise TypeError(f"expected JSON object: {relative_path}")
    return value


def _git(*arguments: str) -> bytes:
    process = subprocess.run(
        ["git", *arguments],
        cwd=REPO_ROOT,
        check=False,
        capture_output=True,
    )
    if process.returncode != 0:
        raise ValueError(f"git command failed: {' '.join(arguments)}")
    return process.stdout


def _last_exact_source_commit(relative_path: str, raw: bytes) -> str:
    commit = _git("log", "-1", "--format=%H", "--", relative_path).decode(
        "ascii"
    ).strip()
    if not commit or _git("show", f"{commit}:{relative_path}") != raw:
        raise ValueError(f"no exact committed source binding: {relative_path}")
    return commit


def audit_artifact_custody() -> dict[str, Any]:
    records = []
    for relative_path, expected_sha in EXPECTED_ARTIFACT_SHA256.items():
        raw = (REPO_ROOT / relative_path).read_bytes()
        actual_sha = sha256_bytes(raw)
        records.append(
            {
                "relative_path": relative_path,
                "sha256": actual_sha,
                "expected_sha256": expected_sha,
                "exact": actual_sha == expected_sha,
            }
        )
    if not all(item["exact"] for item in records):
        raise ValueError("review input artifact custody mismatch")
    manifest = load_json(MANIFEST_RELATIVE_PATH)
    report = load_json(PREPARATION_REPORT_RELATIVE_PATH)
    cross_bindings_exact = (
        manifest["packet"]["sha256"] == EXPECTED_ARTIFACT_SHA256[PACKET_RELATIVE_PATH]
        and manifest["run_matrix"]["sha256"]
        == EXPECTED_ARTIFACT_SHA256[MATRIX_RELATIVE_PATH]
        and manifest["expected_output_identity_manifest"]["sha256"]
        == EXPECTED_ARTIFACT_SHA256[IDENTITY_RELATIVE_PATH]
        and report["artifacts"]["manifest"]["sha256"]
        == EXPECTED_ARTIFACT_SHA256[MANIFEST_RELATIVE_PATH]
    )
    return {
        "records": records,
        "all_exact": True,
        "manifest_and_preparation_report_cross_bindings_exact": cross_bindings_exact,
    }


def _committed_runtime_closure(
    stored_closure: dict[str, Any],
) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    committed = copy.deepcopy(stored_closure)
    records = []
    for binding in committed["modules"]:
        relative_path = str(binding["relative_path"])
        raw = (REPO_ROOT / relative_path).read_bytes()
        source_commit = _last_exact_source_commit(relative_path, raw)
        records.append(
            {
                "module_name": binding["module_name"],
                "relative_path": relative_path,
                "sha256_exact": sha256_bytes(raw) == binding["sha256"],
                "git_blob_oid_exact": git_blob_oid(raw) == binding["git_blob_oid"],
                "frozen_source_commit": binding.get("source_commit"),
                "committed_source_commit": source_commit,
                "source_commit_exact": binding.get("source_commit") == source_commit,
            }
        )
        binding["source_commit"] = source_commit
    return committed, records


def _scientific_core_with_closure(
    stored_core: dict[str, Any], closure_sha256: str
) -> dict[str, Any]:
    core = copy.deepcopy(stored_core)
    core["implementation_closure_sha256"] = closure_sha256
    core["physical_configuration_core"]["implementation_and_operator"][
        "implementation_closure_sha256"
    ] = closure_sha256
    return core


def audit_input_hash_reconstruction(
    packet: dict[str, Any], matrix: dict[str, Any]
) -> dict[str, Any]:
    implementation = packet["implementation_closure"]
    stored_closure = implementation["runtime_closure"]
    stored_digest = sha256_bytes(canonical_json_bytes(stored_closure))
    if stored_digest != implementation["closure_sha256"]:
        raise ValueError("stored implementation closure does not self-reconstruct")
    committed_closure, bindings = _committed_runtime_closure(stored_closure)
    committed_digest = sha256_bytes(canonical_json_bytes(committed_closure))
    records = []
    for record in matrix["records"]:
        stored_core = record["scientific_input_core"]
        stored_sha = sha256_bytes(canonical_json_bytes(stored_core))
        committed_core = _scientific_core_with_closure(stored_core, committed_digest)
        committed_sha = sha256_bytes(canonical_json_bytes(committed_core))
        records.append(
            {
                "run_id": record["run_id"],
                "frozen_input_sha256": record["input_hash"],
                "stored_core_reconstructed_sha256": stored_sha,
                "stored_core_exact": stored_sha
                == record["input_hash"]
                == record["scientific_input_core_sha256"],
                "committed_closure_reconstructed_sha256": committed_sha,
                "committed_closure_exact": committed_sha == record["input_hash"],
            }
        )
    process = subprocess.run(
        [
            sys.executable,
            "-m",
            "formal.python.tools."
            "dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
            "instrumented_r13_mechanism_experiment_numerical_freeze_packet_v1",
            "--check",
        ],
        cwd=REPO_ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    return {
        "positive_inclusion_record_count": len(records),
        "frozen_stored_core_reconstruction_count": sum(
            item["stored_core_exact"] for item in records
        ),
        "current_committed_closure_reconstruction_count": sum(
            item["committed_closure_exact"] for item in records
        ),
        "frozen_implementation_closure_sha256": stored_digest,
        "current_committed_implementation_closure_sha256": committed_digest,
        "closure_digest_changed_after_source_commit_binding": (
            stored_digest != committed_digest
        ),
        "runtime_module_bindings": bindings,
        "frozen_null_source_commit_count": sum(
            item["frozen_source_commit"] is None for item in bindings
        ),
        "all_runtime_bytes_and_blob_ids_exact": all(
            item["sha256_exact"] and item["git_blob_oid_exact"] for item in bindings
        ),
        "all_frozen_source_commits_exact": all(
            item["source_commit_exact"] for item in bindings
        ),
        "records": records,
        "preparation_generator_check_returncode": process.returncode,
        "preparation_generator_check_passed": process.returncode == 0,
        "stale_artifact_paths": list(STALE_ARTIFACT_PATHS),
    }


def audit_executor_and_mutations(
    packet: dict[str, Any], matrix: dict[str, Any]
) -> dict[str, Any]:
    public_execution_parameters = list(
        inspect.signature(executor_v1.execute_frozen_matrix_once_v1).parameters
    )
    lookup_parameters = list(inspect.signature(executor_v1.lookup_frozen_record).parameters)
    registry = list(semantic_v1.FULL_ADVERSARIAL_REGISTRY_V1)
    identity_records = {
        item["mutation"]["field"]: item
        for item in registry
        if item["category"] == "V0_REVIEW_EXACT_MATRIX_IDENTITY_MUTATION"
    }
    mutation_results = []
    for field in semantic_v1.IDENTITY_MUTATION_FIELDS:
        candidate = copy.deepcopy(matrix)
        candidate["records"][0][field] = copy.deepcopy(
            semantic_v1.IDENTITY_MUTATION_VALUES[field]
        )
        diagnostics = executor_v1.strict_validate_matrix(candidate, matrix)
        expected_diagnostic = identity_records[field]["expected_first_diagnostic"]
        mutation_results.append(
            {
                "field": field,
                "rejected": bool(diagnostics),
                "actual_first_diagnostic": diagnostics[0] if diagnostics else None,
                "registered_expected_first_diagnostic": expected_diagnostic,
                "exact_registered_diagnostic": bool(diagnostics)
                and diagnostics[0] == expected_diagnostic,
            }
        )
    return {
        "public_execution_parameters": public_execution_parameters,
        "run_id_lookup_parameters": lookup_parameters,
        "caller_can_supply_matrix_or_identity": public_execution_parameters != [
            "repo_root"
        ],
        "strict_matrix_self_validation_diagnostics": executor_v1.strict_validate_matrix(
            matrix, matrix
        ),
        "identity_mutation_count": len(mutation_results),
        "identity_mutation_rejection_count": sum(
            item["rejected"] for item in mutation_results
        ),
        "identity_mutation_exact_diagnostic_count": sum(
            item["exact_registered_diagnostic"] for item in mutation_results
        ),
        "full_adversarial_registry_count": len(registry),
        "full_adversarial_registry_unique_count": len(
            {item["control_id"] for item in registry}
        ),
        "mutation_results": mutation_results,
        "blocked_anchor_diagnostic": executor_v1._validate_freeze_anchor(
            {"verdict": VERDICT}
        ),
    }


def audit_runtime_attestation(packet: dict[str, Any]) -> dict[str, Any]:
    authority = copy.deepcopy(
        packet["runtime_execution_authority_proposal"]["proposed_review_authority"]
    )
    authority["execution_authorized"] = True
    anchor = {
        "verdict": custody_v1.EXPECTED_REVIEW_VERDICT,
        custody_v1.REVIEW_AUTHORITY_FIELD: authority,
    }
    anchor_diagnostics = executor_v1._validate_freeze_anchor(anchor)
    attestation = executor_v1._attest_actual_loaded_modules_with_authority(
        REPO_ROOT, authority
    )
    hostile_name = custody_v1.REQUIRED_MODULE_NAMES[-1]
    original = sys.modules[hostile_name]
    shadow_path = REPO_ROOT / "HOSTILE-IMPORT-SHADOW.py"
    shadow = types.ModuleType(hostile_name)
    shadow.__file__ = str(shadow_path)
    shadow.__spec__ = importlib.machinery.ModuleSpec(
        hostile_name, loader=None, origin=str(shadow_path)
    )
    hostile_rejected = False
    hostile_diagnostic = None
    try:
        sys.modules[hostile_name] = shadow
        try:
            executor_v1._attest_actual_loaded_modules_with_authority(
                REPO_ROOT, authority
            )
        except executor_v1.RuntimeCustodyError as error:
            hostile_rejected = True
            hostile_diagnostic = str(error)
    finally:
        sys.modules[hostile_name] = original
    committed_count = sum(
        binding.get("source_commit") is not None
        for binding in authority["implementation_closure"]["modules"]
    )
    return {
        "synthetic_accepted_anchor_diagnostics": anchor_diagnostics,
        "loaded_module_count": attestation["loaded_module_count"],
        "all_loaded_paths_bytes_and_blob_ids_exact": attestation["all_passed"],
        "historical_object_binding_exact": attestation[
            "historical_object_binding_exact"
        ],
        "hostile_import_shadow_rejected": hostile_rejected,
        "hostile_import_first_diagnostic": hostile_diagnostic,
        "frozen_nonnull_source_commit_count": committed_count,
        "all_eight_frozen_bindings_name_a_committed_source": committed_count == 8,
    }


def audit_payload_identity(
    matrix: dict[str, Any], identity: dict[str, Any]
) -> dict[str, Any]:
    by_run_id = {record["run_id"]: record for record in matrix["records"]}
    output_by_run_id = {record["run_id"]: record for record in identity["outputs"]}
    path_fields = ("json_relative_output_path", "npz_relative_output_path")
    all_paths = [
        output[field]
        for output in identity["outputs"]
        for field in path_fields
    ]
    mirrored_fields = (
        "run_id",
        "execution_role",
        "mechanism_configuration_role",
        "paired_run_id",
        "output_schema_version",
        "json_relative_output_path",
        "json_safe_filename",
        "npz_relative_output_path",
        "npz_safe_filename",
        "input_hash",
        "implementation_closure_sha256",
        "physical_configuration_core_sha256",
        "scientific_input_core_sha256",
    )
    mirrored_exact = all(
        all(output_by_run_id[run_id][field] == record[field] for field in mirrored_fields)
        for run_id, record in by_run_id.items()
    )
    output_root = PurePosixPath(identity["output_root"])
    return {
        "matrix_run_ids_exact": tuple(by_run_id) == custody_v1.EXACT_RUN_IDS,
        "identity_run_ids_exact": tuple(output_by_run_id) == custody_v1.EXACT_RUN_IDS,
        "role_payload_record_count": len(identity["outputs"]),
        "json_npz_payload_path_count": len(all_paths),
        "unique_payload_path_count": len(set(all_paths)),
        "all_payload_paths_under_frozen_output_root": all(
            output_root in PurePosixPath(path).parents for path in all_paths
        ),
        "matrix_identity_manifest_fields_exact": mirrored_exact,
        "auxiliary_execution_file_count": len(identity["auxiliary_execution_files"]),
        "complete_expected_file_count_after_success": identity[
            "complete_expected_file_count_after_success"
        ],
    }


def audit_raw_evidence(matrix: dict[str, Any]) -> dict[str, Any]:
    self_validation = evidence_v1.self_validate()
    missing_result = classifier_v1.classify_from_raw_payloads(REPO_ROOT)
    empty_events = {family: [] for family in evidence_v1.EVENT_FAMILIES}
    empty_result = None
    empty_diagnostic = None
    try:
        evidence_v1._recompute_instrumented_metrics(
            {"raw_events": empty_events}, matrix["records"][0]
        )
    except evidence_v1.RawEvidenceError as error:
        empty_result = error.evidence_result
        empty_diagnostic = error.diagnostic
    return {
        "assembler_self_validation": self_validation,
        "assembler_self_validation_all_passed": all(self_validation.values()),
        "classifier_public_parameters": list(
            inspect.signature(classifier_v1.classify_from_raw_payloads).parameters
        ),
        "missing_registered_raw_evidence_result": missing_result["evidence_result"],
        "missing_raw_hypotheses_all_not_evaluated": all(
            item["status"] == "NOT_EVALUATED"
            for item in missing_result["hypothesis_decisions"].values()
        ),
        "empty_event_series_result": empty_result,
        "empty_event_series_diagnostic": empty_diagnostic,
    }


def audit_hc_and_gamma() -> dict[str, Any]:
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
        "maxwell_path_mutation_changes_decision_mismatch": not np.array_equal(
            baseline["independent_path_mismatch"],
            maxwell_changed["independent_path_mismatch"],
        ),
        "continuity_path_mutation_changes_decision_mismatch": not np.array_equal(
            baseline["independent_path_mismatch"],
            continuity_changed["independent_path_mismatch"],
        ),
        "continuity_path_reuses_registered_maxwell_source": maxwell_changed[
            "continuity_path_uses_registered_maxwell_source"
        ],
        "mechanism_path_sources_independent": maxwell_changed[
            "mechanism_path_sources_independent"
        ],
        "legacy_q_decision_bearing": maxwell_changed[
            "legacy_q_mechanism_decision_bearing"
        ],
        "gamma32_used": summary["gamma32_used"],
        "legacy_q_used": summary["legacy_q_used"],
        "classifier_hc_gamma_constant_count": sum(
            "gamma" in key.casefold()
            for key in classifier_v1.SUPPORT_CONSTANTS["H_C"]
        ),
    }


def audit_constant_provenance(packet: dict[str, Any]) -> dict[str, Any]:
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
    required_fields = {
        "hypothesis",
        "constant_id",
        "value",
        "source_category",
        "source_artifact",
        "source_record_ids",
        "derivation_formula",
        "rounding_rule",
        "scientific_meaning",
        "source_commit",
        "nonfuture",
        "future_mechanism_outputs_used",
    }
    source_artifacts = {
        path for item in provenance for path in item["source_artifacts"]
    }
    return {
        "support_constant_count": len(leaves),
        "provenance_record_count": len(provenance),
        "one_to_one_leaf_identity": leaves == provenance_leaves,
        "support_constants_sha256": sha256_bytes(canonical_json_bytes(constants)),
        "expected_support_constants_sha256": EXPECTED_SUPPORT_CONSTANTS_SHA256,
        "packet_constants_exact": packet["classifier_freeze"]["support_constants"]
        == constants,
        "all_required_provenance_fields_present": all(
            required_fields <= set(item) for item in provenance
        ),
        "all_source_artifacts_exist": all(
            (REPO_ROOT / relative_path).is_file() for relative_path in source_artifacts
        ),
        "all_records_nonfuture": all(
            item["nonfuture"] is True
            and item["future_mechanism_outputs_used"] is False
            and item["declared_before_mechanism_execution"] is True
            for item in provenance
        ),
        "all_derivations_rounding_and_meanings_nonempty": all(
            item["derivation_formula"]
            and item["rounding_rule"]
            and item["scientific_meaning"]
            and item["source_record_ids"]
            for item in provenance
        ),
    }


def build_report() -> dict[str, Any]:
    output_root = REPO_ROOT / custody_v1.EXPERIMENT_OUTPUT_ROOT_RELATIVE_PATH
    if output_root.exists():
        raise ValueError("future experiment output root must remain absent during review")
    artifact_custody = audit_artifact_custody()
    packet = load_json(PACKET_RELATIVE_PATH)
    matrix = load_json(MATRIX_RELATIVE_PATH)
    identity = load_json(IDENTITY_RELATIVE_PATH)
    if (
        packet["verdict"] != "PREPARED_PENDING_INDEPENDENT_REVIEW"
        or packet["selected_next_target"] != TARGET
        or packet["decision_count"] != packet["passed_decision_count"]
    ):
        raise ValueError("freeze-v1 review authority mismatch")

    input_audit = audit_input_hash_reconstruction(packet, matrix)
    executor_audit = audit_executor_and_mutations(packet, matrix)
    runtime_audit = audit_runtime_attestation(packet)
    payload_audit = audit_payload_identity(matrix, identity)
    raw_audit = audit_raw_evidence(matrix)
    hc_audit = audit_hc_and_gamma()
    provenance_audit = audit_constant_provenance(packet)
    canonical_inventory = predecessor_v0._canonical_root_inventory()
    canonical_root_digest = predecessor_v0.canonical_root_digest()
    canonical_tree_digest = predecessor_v0.canonical_directory_tree_sha256()

    acceptance_checks = [
        {
            "acceptance_id": "six_positive_inclusion_input_hashes_reconstruct",
            "passed": input_audit[
                "current_committed_closure_reconstruction_count"
            ]
            == 6
            and input_audit["preparation_generator_check_passed"],
            "review_outcome_on_failure": "BLOCK_INPUT_HASH_RECONSTRUCTION",
        },
        {
            "acceptance_id": "run_id_only_executor_and_twenty_exact_mutation_diagnostics",
            "passed": not executor_audit["caller_can_supply_matrix_or_identity"]
            and executor_audit["identity_mutation_rejection_count"] == 20
            and executor_audit["identity_mutation_exact_diagnostic_count"] == 20,
            "review_outcome_on_failure": "BLOCK_MUTATION_COVERAGE_OR_ATOMICITY",
        },
        {
            "acceptance_id": "eight_loaded_modules_match_frozen_committed_files",
            "passed": runtime_audit["loaded_module_count"] == 8
            and runtime_audit["all_loaded_paths_bytes_and_blob_ids_exact"]
            and runtime_audit["hostile_import_shadow_rejected"]
            and runtime_audit[
                "all_eight_frozen_bindings_name_a_committed_source"
            ],
            "review_outcome_on_failure": "BLOCK_RUNTIME_IMPLEMENTATION_ATTESTATION",
        },
        {
            "acceptance_id": "exact_twelve_payload_schemas_identities_and_paths",
            "passed": payload_audit["role_payload_record_count"] == 6
            and payload_audit["json_npz_payload_path_count"] == 12
            and payload_audit["unique_payload_path_count"] == 12
            and payload_audit["matrix_identity_manifest_fields_exact"],
            "review_outcome_on_failure": "BLOCK_RAW_EVIDENCE_RECONSTRUCTION",
        },
        {
            "acceptance_id": "raw_only_classification_missing_and_empty_evidence_block",
            "passed": raw_audit["assembler_self_validation_all_passed"]
            and raw_audit["missing_raw_hypotheses_all_not_evaluated"]
            and raw_audit["empty_event_series_result"]
            == "BLOCKED_REQUIRED_EVIDENCE_INCOMPLETE",
            "review_outcome_on_failure": "BLOCK_RAW_EVIDENCE_RECONSTRUCTION",
        },
        {
            "acceptance_id": "H_C_uses_independent_Maxwell_and_continuity_paths",
            "passed": hc_audit["maxwell_path_mutation_changes_decision_mismatch"]
            and hc_audit["continuity_path_mutation_changes_decision_mismatch"]
            and hc_audit["mechanism_path_sources_independent"]
            and not hc_audit["continuity_path_reuses_registered_maxwell_source"],
            "review_outcome_on_failure": "BLOCK_HC_PATH_INDEPENDENCE",
        },
        {
            "acceptance_id": "gamma32_is_nondecision_bearing",
            "passed": not hc_audit["gamma32_used"]
            and not hc_audit["legacy_q_used"]
            and hc_audit["classifier_hc_gamma_constant_count"] == 0,
            "review_outcome_on_failure": "BLOCK_HC_PATH_INDEPENDENCE",
        },
        {
            "acceptance_id": "twenty_three_constants_have_complete_nonfuture_provenance",
            "passed": provenance_audit["support_constant_count"] == 23
            and provenance_audit["provenance_record_count"] == 23
            and provenance_audit["one_to_one_leaf_identity"]
            and provenance_audit["support_constants_sha256"]
            == EXPECTED_SUPPORT_CONSTANTS_SHA256
            and provenance_audit["all_required_provenance_fields_present"]
            and provenance_audit["all_source_artifacts_exist"]
            and provenance_audit["all_records_nonfuture"]
            and provenance_audit[
                "all_derivations_rounding_and_meanings_nonempty"
            ],
            "review_outcome_on_failure": "BLOCK_MECHANISM_CONSTANT_PROVENANCE",
        },
        {
            "acceptance_id": "forty_one_controls_are_atomic_and_have_exact_outcomes",
            "passed": executor_audit["full_adversarial_registry_count"] == 41
            and executor_audit["full_adversarial_registry_unique_count"] == 41
            and executor_audit["identity_mutation_exact_diagnostic_count"] == 20,
            "review_outcome_on_failure": "BLOCK_MUTATION_COVERAGE_OR_ATOMICITY",
        },
        {
            "acceptance_id": "invalid_or_absent_acceptance_anchor_fails_closed",
            "passed": executor_audit["blocked_anchor_diagnostic"]
            == ["REVIEW_ANCHOR_NOT_ACCEPTED"],
            "review_outcome_on_failure": "BLOCK_EXECUTOR_FAIL_OPEN",
        },
        {
            "acceptance_id": "canonical_custody_and_no_simulation_are_preserved",
            "passed": len(canonical_inventory) == 205
            and canonical_root_digest == predecessor_v0.EXPECTED_CANONICAL_ROOT_DIGEST
            and canonical_tree_digest
            == predecessor_v0.EXPECTED_CANONICAL_DIRECTORY_TREE_SHA256
            and not output_root.exists(),
            "review_outcome_on_failure": "BLOCK_RUNTIME_IMPLEMENTATION_ATTESTATION",
        },
    ]
    failed = [item for item in acceptance_checks if not item["passed"]]
    blocker_ids = list(dict.fromkeys(item["review_outcome_on_failure"] for item in failed))
    if not failed or blocker_ids[0] != VERDICT:
        raise ValueError("review evidence does not support the frozen blocker precedence")
    return {
        "schema_id": SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "verdict": VERDICT,
        "blocking_outcomes": blocker_ids,
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": "VERSIONED_NUMERICAL_FREEZE_CORRECTION_ONLY",
        "reviewer_independence": {
            "freeze_v1_generator_imported": False,
            "preparation_combined_pass_flags_used_as_review_evidence": False,
            "stored_scientific_input_cores_rehashed_independently": True,
            "current_committed_runtime_closure_reconstructed_independently": True,
            "matrix_mutations_executed_independently": True,
            "hostile_import_shadow_executed": True,
            "evolution_runner_invocation_count": 0,
            "simulation_invocation_count": 0,
        },
        "reviewed_artifact_custody": artifact_custody,
        "input_hash_reconstruction_audit": input_audit,
        "executor_and_adversarial_audit": executor_audit,
        "runtime_implementation_attestation_audit": runtime_audit,
        "payload_identity_audit": payload_audit,
        "raw_evidence_reconstruction_audit": raw_audit,
        "H_C_and_gamma32_audit": hc_audit,
        "mechanism_constant_provenance_audit": provenance_audit,
        "canonical_custody": {
            "file_count": len(canonical_inventory),
            "authority_inventory_digest": canonical_root_digest,
            "directory_tree_digest": canonical_tree_digest,
            "mechanism_output_root_absent_before_and_after_review": not output_root.exists(),
            "canonical_mutation_count": 0,
        },
        "acceptance_checks": acceptance_checks,
        "acceptance_check_count": len(acceptance_checks),
        "passed_acceptance_check_count": sum(item["passed"] for item in acceptance_checks),
        "failed_acceptance_check_count": len(failed),
        "failed_acceptance_ids": [item["acceptance_id"] for item in failed],
        "blocking_findings": [
            {
                "finding_id": "B_V1_COMMITTED_CLOSURE_CHANGES_ALL_SIX_INPUT_HASHES",
                "review_outcome": "BLOCK_INPUT_HASH_RECONSTRUCTION",
                "evidence": (
                    "The stored positive-inclusion cores self-reconstruct 6/6, but the "
                    "runtime closure rebuilt from the now-committed exact source bytes "
                    "reconstructs 0/6 frozen input hashes; the v1 generator --check also "
                    "reports all five artifacts stale."
                ),
                "bounded_correction_required": (
                    "Prepare v2 only. Bind immutable committed source identities before "
                    "forming the closure digest, regenerate six hashes and five artifacts "
                    "under v2 names, and prove post-commit regeneration stability."
                ),
            },
            {
                "finding_id": "B_V1_REGISTERED_MUTATION_DIAGNOSTICS_NOT_IMPLEMENTED",
                "review_outcome": SECONDARY_BLOCKER,
                "evidence": (
                    "All 20 identity mutations are rejected before simulation, but 0/20 "
                    "produce the field-specific first diagnostics promised by the frozen "
                    "41-control registry."
                ),
                "bounded_correction_required": (
                    "In v2, either implement every registered exact diagnostic or freeze "
                    "the actual generic diagnostic; execute and attest every atomic control."
                ),
            },
            {
                "finding_id": "B_V1_SIX_RUNTIME_BINDINGS_LACK_FROZEN_COMMIT_IDS",
                "review_outcome": "BLOCK_RUNTIME_IMPLEMENTATION_ATTESTATION",
                "evidence": (
                    "All eight loaded paths, bytes, and Git blob IDs attest and a hostile "
                    "import shadow is rejected, but six of eight frozen runtime bindings "
                    "store null rather than the exact committed source identity."
                ),
                "bounded_correction_required": (
                    "Freeze all eight exact committed source identities in v2 and require "
                    "the runtime attestor to validate every one without a nullable bypass."
                ),
            },
        ],
        "preserved_scientific_core": {
            "Route_A": "ACCEPTED",
            "instrumented_design_v1": "ACCEPTED",
            "six_run_scientific_comparison_structure": "PRESERVED",
            "canonical_robustness": "NUMERICALLY_BLOCKED",
            "R13_root_mechanism": "UNRESOLVED",
            "materiality": "NOT_EVALUATED_NUMERICAL_BLOCK",
            "new_E_REPRO": "NONE",
        },
        "authority_rotation": {
            "numerical_freeze_v1_accepted": False,
            "execution_authorized": False,
            "one_time_execution_count_authorized": 0,
            "rerun_authorized": False,
            "threshold_change_authorized": False,
            "robustness_reclassification_authorized": False,
            "materiality_evaluation_authorized": False,
            "new_scientific_claim_authorized": False,
            "versioned_freeze_v2_correction_authorized": True,
        },
        "nonclaims": [
            "no six-run mechanism experiment has executed",
            "no mechanism hypothesis has been evaluated on experiment data",
            "no canonical output has changed",
            "no robustness or materiality result is assigned",
            "no E-REPRO, pillar, seam, C_k, CCFT, or master-action promotion is assigned",
        ],
        "claim_ceiling": (
            "This review blocks numerical-freeze v1 and authorizes only a versioned, "
            "bounded v2 freeze correction. It does not reopen Route A or design v1 and "
            "does not authorize execution or any scientific classification."
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
