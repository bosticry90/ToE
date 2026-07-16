from __future__ import annotations

import copy
import inspect
import json
import sys
from pathlib import Path

import pytest

from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_executor_custody_v1
    as custody,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_executor_v1
    as executor,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
V0_MATRIX = REPO_ROOT / (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-INSTRUMENTED-R13-MECHANISM-EXPERIMENT-NUMERICAL-FREEZE-RUN-"
    "MATRIX-v0.json"
)
CLOSURE_DIGEST = "a" * 64


def _matrix(closure_digest: str = CLOSURE_DIGEST) -> dict:
    matrix = json.loads(V0_MATRIX.read_text(encoding="utf-8"))
    for record in matrix["records"]:
        record.update(
            {
                "implementation_closure_sha256": closure_digest,
                "executor_id": "EXECUTOR_v1",
                "executor_sha256": "1" * 64,
                "raw_evidence_assembler_id": "ASSEMBLER_v1",
                "raw_evidence_assembler_sha256": "2" * 64,
                "classifier_id": "CLASSIFIER_v1",
                "classifier_sha256": "3" * 64,
                "semantic_contract_id": "SEMANTIC_v1",
                "semantic_contract_sha256": "4" * 64,
            }
        )
    return matrix


def _anchor() -> dict:
    modules = []
    for module_name, relative_path in custody.MODULE_PATH_BY_NAME.items():
        modules.append(
            {
                "module_name": module_name,
                "relative_path": relative_path,
                "sha256": "b" * 64,
                "git_blob_oid": "c" * 40,
                "source_commit": None,
            }
        )
    closure = {
        "schema_id": "IMPLEMENTATION_CLOSURE_v1",
        "modules": modules,
        "operator_configuration": {"length": 1.0, "wilson_r": 1.0},
    }
    closure_digest = executor.sha256_bytes(executor.canonical_json_bytes(closure))
    matrix = _matrix(closure_digest)
    full = {
        record["run_id"]: executor.full_record_identity_sha256(record)
        for record in matrix["records"]
    }
    physical = {
        record["run_id"]: executor.physical_configuration_core_sha256(
            record, closure_digest
        )
        for record in matrix["records"]
    }
    scientific = {
        record["run_id"]: executor.scientific_input_core_sha256(
            record, closure_digest
        )
        for record in matrix["records"]
    }
    artifact_bindings = {
        name: {
            "relative_path": path,
            "sha256": "d" * 64,
            "git_blob_oid": "e" * 40,
        }
        for name, path in custody.REQUIRED_ARTIFACT_PATHS.items()
    }
    return {
        "verdict": custody.EXPECTED_REVIEW_VERDICT,
        custody.REVIEW_AUTHORITY_FIELD: {
            "schema_id": "RUNTIME_EXECUTION_AUTHORITY_v1",
            "executor_id": executor.EXECUTOR_ID,
            "execution_authorized": True,
            "one_execution_only": True,
            "automatic_retries_authorized": False,
            "exact_run_ids": list(custody.EXACT_RUN_IDS),
            "pair_run_ids": [list(pair) for pair in custody.PAIR_RUN_IDS],
            "artifact_bindings": artifact_bindings,
            "implementation_closure": closure,
            "scientific_input_closure_digest": closure_digest,
            "expected_matrix_semantic_sha256": executor.sha256_bytes(
                executor.canonical_json_bytes(matrix)
            ),
            "expected_full_record_sha256_by_run_id": full,
            "expected_physical_configuration_sha256_by_run_id": physical,
            "expected_scientific_input_sha256_by_run_id": scientific,
            "canonical_directory_tree_sha256": "f" * 64,
            "canonical_directory_tree_sha256_domain": "TEST_DOMAIN",
            "experiment_output_root_relative_path": custody.EXPERIMENT_OUTPUT_ROOT_RELATIVE_PATH,
            "canonical_output_root_relative_path": custody.CANONICAL_OUTPUT_ROOT_RELATIVE_PATH,
        },
    }


def test_import_is_inert_and_public_execution_has_no_override_surface() -> None:
    output_root = REPO_ROOT / custody.EXPERIMENT_OUTPUT_ROOT_RELATIVE_PATH
    assert not output_root.exists()
    assert tuple(inspect.signature(executor.execute_frozen_matrix_once_v1).parameters) == (
        "repo_root",
    )
    assert tuple(inspect.signature(executor.preflight_frozen_execution).parameters) == (
        "repo_root",
    )
    assert tuple(inspect.signature(executor.lookup_frozen_record).parameters) == (
        "repo_root",
        "run_id",
    )
    assert not output_root.exists()


def test_fixed_review_anchor_absence_fails_closed_without_output(tmp_path: Path) -> None:
    with pytest.raises(executor.RuntimeCustodyError, match="review anchor is absent"):
        executor.preflight_frozen_execution(tmp_path)
    assert not (
        tmp_path / custody.EXPERIMENT_OUTPUT_ROOT_RELATIVE_PATH
    ).exists()


def test_pair_physical_cores_match_but_six_scientific_inputs_are_distinct() -> None:
    matrix = _matrix()
    by_id = {record["run_id"]: record for record in matrix["records"]}
    physical_hashes = {
        run_id: executor.physical_configuration_core_sha256(record, CLOSURE_DIGEST)
        for run_id, record in by_id.items()
    }
    for instrumented_id, control_id in custody.PAIR_RUN_IDS:
        assert physical_hashes[instrumented_id] == physical_hashes[control_id]
    scientific_hashes = [
        executor.scientific_input_core_sha256(by_id[run_id], CLOSURE_DIGEST)
        for run_id in custody.EXACT_RUN_IDS
    ]
    assert len(set(scientific_hashes)) == 6


@pytest.mark.parametrize(
    "field",
    [
        "parent_canonical_run_id",
        "parent_canonical_input_hash",
        "parent_canonical_output_path",
        "parent_canonical_output_sha256",
        "implementation_id",
        "implementation_sha256",
        "paired_run_id",
        "execution_role",
        "output_schema_version",
        "experiment_id",
        "scientific_row_id",
        "parent_initial_condition_identity",
        "model_class",
        "numerical_method",
        "accepted_step_count",
        "checkpoint_count_including_initial",
        "instrumentation_read_only",
        "trajectory_identity_required",
    ],
)
def test_strict_matrix_rejects_previously_accepted_identity_mutations(
    field: str,
) -> None:
    expected = _matrix()
    candidate = copy.deepcopy(expected)
    record = candidate["records"][0]
    value = record[field]
    record[field] = not value if isinstance(value, bool) else (
        value + 1 if isinstance(value, int) else f"MUTATED:{value}"
    )
    assert executor.strict_validate_matrix(candidate, expected) == [
        f"RUN_MATRIX_RECORD_IDENTITY_MISMATCH:{custody.EXACT_RUN_IDS[0]}"
    ]


def test_strict_matrix_rejects_nested_extra_missing_and_exclusion_mutations() -> None:
    expected = _matrix()
    for mutation in ("nested", "extra", "missing", "exclusion"):
        candidate = copy.deepcopy(expected)
        record = candidate["records"][0]
        if mutation == "nested":
            key = next(iter(record["requested_axis_values"]))
            record["requested_axis_values"][key] = 999.0
            diagnostic = "RUN_MATRIX_RECORD_IDENTITY_MISMATCH"
        elif mutation == "extra":
            record["unknown_field"] = "forbidden"
            diagnostic = "RUN_MATRIX_RECORD_FIELD_SET_MISMATCH"
        elif mutation == "missing":
            del record["implementation_sha256"]
            diagnostic = "RUN_MATRIX_RECORD_FIELD_SET_MISMATCH"
        else:
            record["input_hash_material_excludes"] = []
            diagnostic = "RUN_MATRIX_RECORD_IDENTITY_MISMATCH"
        assert executor.strict_validate_matrix(candidate, expected) == [
            f"{diagnostic}:{custody.EXACT_RUN_IDS[0]}"
        ]


def test_positive_inclusion_core_has_no_exclusion_list_semantics() -> None:
    record = _matrix()["records"][0]
    core = executor.build_scientific_input_core(record, CLOSURE_DIGEST)
    encoded = executor.canonical_json_bytes(core)
    assert b"input_hash_material_excludes" not in encoded
    assert core["run_identity"]["run_id"] == record["run_id"]
    assert core["run_identity"]["execution_role"] == record["execution_role"]
    assert core["instrumentation_contract"]["enabled"] is True
    assert core["output_contract"]["schema_version"] == record["output_schema_version"]
    assert core["implementation_closure_sha256"] == CLOSURE_DIGEST


def test_role_mutation_changes_scientific_but_not_physical_core() -> None:
    record = _matrix()["records"][0]
    mutated = copy.deepcopy(record)
    mutated["execution_role"] = "MUTATED_ROLE"
    mutated["instrumentation_enabled"] = False
    assert executor.physical_configuration_core_sha256(
        record, CLOSURE_DIGEST
    ) == executor.physical_configuration_core_sha256(mutated, CLOSURE_DIGEST)
    assert executor.scientific_input_core_sha256(
        record, CLOSURE_DIGEST
    ) != executor.scientific_input_core_sha256(mutated, CLOSURE_DIGEST)


def test_freeze_anchor_validator_is_fail_closed() -> None:
    anchor = _anchor()
    assert executor._validate_freeze_anchor(anchor) == []
    mutations = []
    wrong_verdict = copy.deepcopy(anchor)
    wrong_verdict["verdict"] = "PREPARED"
    mutations.append((wrong_verdict, "REVIEW_ANCHOR_NOT_ACCEPTED"))
    missing_output = copy.deepcopy(anchor)
    del missing_output[custody.REVIEW_AUTHORITY_FIELD][
        "expected_scientific_input_sha256_by_run_id"
    ]
    mutations.append((missing_output, "RUNTIME_AUTHORITY_FIELD_MISSING"))
    wrong_run = copy.deepcopy(anchor)
    wrong_run[custody.REVIEW_AUTHORITY_FIELD]["exact_run_ids"][0] = "UNKNOWN"
    mutations.append((wrong_run, "RUNTIME_AUTHORITY_RUN_ID_DOMAIN_MISMATCH"))
    wrong_closure = copy.deepcopy(anchor)
    wrong_closure[custody.REVIEW_AUTHORITY_FIELD]["implementation_closure"][
        "operator_configuration"
    ]["length"] = 2.0
    mutations.append((wrong_closure, "IMPLEMENTATION_CLOSURE_DIGEST_MISMATCH"))
    for mutant, expected_prefix in mutations:
        diagnostics = executor._validate_freeze_anchor(mutant)
        assert diagnostics and diagnostics[0].startswith(expected_prefix)


def test_actual_loaded_module_attestation_checks_path_bytes_and_git_blob() -> None:
    path = Path(executor.__file__).resolve()
    contents = path.read_bytes()
    binding = {
        "module_name": executor.__name__,
        "relative_path": path.relative_to(REPO_ROOT).as_posix(),
        "sha256": executor.sha256_bytes(contents),
        "git_blob_oid": executor.git_blob_oid(contents),
        "source_commit": None,
    }
    report = executor._attest_loaded_module(REPO_ROOT, executor, binding)
    assert report["path_exact"] and report["bytes_exact"] and report["git_blob_exact"]
    wrong = copy.deepcopy(binding)
    wrong["sha256"] = "0" * 64
    with pytest.raises(executor.RuntimeCustodyError, match="byte identity mismatch"):
        executor._attest_loaded_module(REPO_ROOT, executor, wrong)
    wrong = copy.deepcopy(binding)
    wrong["git_blob_oid"] = "0" * 40
    with pytest.raises(executor.RuntimeCustodyError, match="byte identity mismatch"):
        executor._attest_loaded_module(REPO_ROOT, executor, wrong)


def test_lookup_rejects_unknown_run_before_any_anchor_or_output(tmp_path: Path) -> None:
    with pytest.raises(executor.RuntimeCustodyError, match="not a registered"):
        executor.lookup_frozen_record(tmp_path, "UNKNOWN")
    assert not (tmp_path / custody.EXPERIMENT_OUTPUT_ROOT_RELATIVE_PATH).exists()


def test_all_eight_closure_modules_are_registered() -> None:
    assert len(custody.REQUIRED_MODULE_NAMES) == 8
    assert custody.SEMANTIC_CONTRACT_MODULE in custody.REQUIRED_MODULE_NAMES
    assert custody.RAW_EVIDENCE_ASSEMBLER_MODULE in custody.REQUIRED_MODULE_NAMES
    assert custody.CLASSIFIER_MODULE in custody.REQUIRED_MODULE_NAMES
    assert sys.modules.get(executor.__name__) is executor
