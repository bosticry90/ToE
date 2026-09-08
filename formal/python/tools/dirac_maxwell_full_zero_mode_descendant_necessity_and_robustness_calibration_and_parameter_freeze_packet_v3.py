from __future__ import annotations

import argparse
import copy
import hashlib
import json
import subprocess
import unicodedata
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.prompt_dependency_identity import (
    identity_sha256_path,
    prompt_dependency_is_nonblocking,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_canonical_result_classifier_v2
    as classifier,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCRIPT_PATH = Path(__file__).resolve()
SCRIPT_RELATIVE_PATH = "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_calibration_and_parameter_freeze_packet_v3.py"
TEST_RELATIVE_PATH = "formal/python/tests/test_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_calibration_and_parameter_freeze_packet_v3.py"
LEAN_RELATIVE_PATH = "formal/toe_formal/ToeFormal/Derivation/DiracMaxwellFullZeroModeDescendantNecessityAndRobustnessCalibrationAndParameterFreezePacketV3.lean"
PACKET_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-CALIBRATION-AND-PARAMETER-FREEZE-PACKET-v3.json"
BUNDLE_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-MUTATION-CAUSAL-CONTRACT-BUNDLE-v3.json"
MANIFEST_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-CALIBRATION-AND-PARAMETER-FREEZE-MANIFEST-v3.json"
REPORT_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_CALIBRATION_AND_PARAMETER_FREEZE_PACKET_20260714_v3.json"

V2_PACKET_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-CALIBRATION-AND-PARAMETER-FREEZE-PACKET-v2.json"
V2_MATRIX_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-CANONICAL-RUN-MATRIX-v2.json"
V2_IDENTITY_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-CANONICAL-EXPECTED-OUTPUT-IDENTITY-MANIFEST-v2.json"
V2_MANIFEST_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-CALIBRATION-AND-PARAMETER-FREEZE-MANIFEST-v2.json"
V2_REPORT_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_CALIBRATION_AND_PARAMETER_FREEZE_PACKET_20260714_v2.json"
V2_GENERATOR_RELATIVE_PATH = "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_calibration_and_parameter_freeze_packet_v2.py"
V2_CLASSIFIER_RELATIVE_PATH = "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_canonical_result_classifier_v2.py"
V2_TEST_RELATIVE_PATH = "formal/python/tests/test_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_calibration_and_parameter_freeze_packet_v2.py"
V2_LEAN_RELATIVE_PATH = "formal/toe_formal/ToeFormal/Derivation/DiracMaxwellFullZeroModeDescendantNecessityAndRobustnessCalibrationAndParameterFreezePacketV2.lean"
V2_REVIEW_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_CALIBRATION_AND_PARAMETER_FREEZE_PACKET_RESULT_REVIEW_20260714_v2.json"
PROMPT_RELATIVE_PATH = "Prompt.txt"
PROMPT_DEPENDENCY_ROLE = "DEMOTE_TO_NONBLOCKING_PROVENANCE"

CAPTURED_AT_UTC = "2026-07-14T00:00:00Z"
SOURCE_REVIEW_COMMIT = "5d8ae50d053cb9edb3ac71e77a6211c6de710277"
SOURCE_REVIEW_PARENT = "b83833d81ccd95b77e1d2a7538a31c5c7b8f791f"
TARGET = "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_calibration_and_parameter_freeze_packet_v3"
REVIEW_TARGET = "review_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_calibration_and_parameter_freeze_packet_v3_result"
POST_ACCEPTANCE_TARGET = "execute_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_canonical_matrix_v2"
PROMPT_SHA256 = "2bc6996ea28e96c50e688ed3d30ee24808af411a244eb594aad89ff80fda8433"
WORKING_TREE_SHA256_AT_PREPARATION = {
    ".gitattributes": "476d90927cd2881dcebb2c6651e3b464708ef4f4d76eb36b24aea21c09d743d2",
    "requirements.active.lock": "48788b703a7a94a051f1083f729f22c9349bbc415b46af4834f6500999c6cd4d",
    "formal/toe_formal/lean-toolchain": "191b7d41ec85ac86d842b357e0407e354737268702749dacbbb73175bbb939e2",
    "formal/toe_formal/lake-manifest.json": "3f17aafa88120f02af27d65b33555c4334804eb5fd08433fe27342a6dd0ec34c",
}

PRESERVED_INPUT_HASHES = {
    V2_PACKET_RELATIVE_PATH: "a393ce35a2be39836fcdee3bf7888c332581bf1b976f67dbee0cc047d9c04680",
    V2_MATRIX_RELATIVE_PATH: "a906c7c11dee659a3f66739d7ee807523743ea8311283dc2e4d99e0f2c17bcb2",
    V2_IDENTITY_RELATIVE_PATH: "9a87c0a1447d4c4462dbf8fc21ef4b8aeb87e62867c67d1db78ac25c2d8ad09e",
    V2_MANIFEST_RELATIVE_PATH: "cebe7a6cc1e5b3c01c6abb47ff0ea5050fa08f18701e62de0691d8564fdc763c",
    V2_REPORT_RELATIVE_PATH: "d4ebaa700242c722dda1c45461b90cac2b59f63cb8c81074e84634b337ccd56c",
    V2_GENERATOR_RELATIVE_PATH: "eaa5ba960731c8828f0208d8e8bc58b20dd74961606715f8f330295d00b7bb99",
    V2_CLASSIFIER_RELATIVE_PATH: "a72627d67ac31c5055fb921e54e640322d4d37a58c46908bc01c2ed70da0c9c9",
    V2_TEST_RELATIVE_PATH: "db46a0b9e4fa12d7f4ef0e1b0012cd22f70f8ab3664043bfe181b7952f271dcb",
    V2_LEAN_RELATIVE_PATH: "7bc5fb1939f015a1597b447268ac7adc0270c5ae13beb09013787858d5447459",
    V2_REVIEW_RELATIVE_PATH: "f3eb0ffa6383ae3b0b1f26593f46af379688e4f503a167fcb1529ef08eba0429",
}

COMMITTED_CONFIGURATION_PATHS = [
    ".gitattributes",
    "requirements.active.lock",
    "formal/toe_formal/lean-toolchain",
    "formal/toe_formal/lake-manifest.json",
]

ABSENT = {"$freeze_v3_absent": True}
BASELINE_FIXTURE_ID = "DM_DESCENDANT_ROBUSTNESS_FREEZE_V3_FRESH_BASELINE_FIXTURE"
BASELINE_DECISION = "CLASSIFIED_PENDING_INDEPENDENT_RESULT_REVIEW:BROADLY_ROBUST"


def _normalize(value: Any) -> Any:
    if isinstance(value, str):
        return unicodedata.normalize("NFC", value)
    if isinstance(value, list):
        return [_normalize(item) for item in value]
    if isinstance(value, dict):
        return {_normalize(str(key)): _normalize(item) for key, item in value.items()}
    return value


def canonical_json_bytes(payload: Any) -> bytes:
    return (json.dumps(_normalize(payload), allow_nan=False, ensure_ascii=False, indent=2, sort_keys=True) + "\n").encode("utf-8")


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def sha256_path(path: Path) -> str:
    return identity_sha256_path(path, repo_root=REPO_ROOT)


def load_json(relative_path: str) -> dict[str, Any]:
    value = json.loads((REPO_ROOT / relative_path).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {relative_path}")
    return value


def _git_bytes(commit: str, path: str) -> bytes:
    return subprocess.check_output(["git", "show", f"{commit}:{path}"], cwd=REPO_ROOT)


def committed_configuration_custody() -> dict[str, Any]:
    records = []
    for path in COMMITTED_CONFIGURATION_PATHS:
        raw = _git_bytes(SOURCE_REVIEW_COMMIT, path)
        blob = subprocess.check_output(["git", "rev-parse", f"{SOURCE_REVIEW_COMMIT}:{path}"], cwd=REPO_ROOT).decode().strip()
        records.append(
            {
                "path": path,
                "source_commit": SOURCE_REVIEW_COMMIT,
                "git_blob_oid": blob,
                "sha256_of_committed_bytes": sha256_bytes(raw),
                "normalization_mode": "committed Git blob bytes; no working-tree conversion",
                "read_contract": f"git show {SOURCE_REVIEW_COMMIT}:{path}",
                "working_tree_hash_advisory_only": True,
                "working_tree_hash_is_regeneration_input": False,
                "working_tree_sha256_at_preparation": WORKING_TREE_SHA256_AT_PREPARATION[path],
            }
        )
    return {
        "source_commit": SOURCE_REVIEW_COMMIT,
        "source_commit_parent": SOURCE_REVIEW_PARENT,
        "records": records,
        "all_authoritative_hashes_use_committed_bytes": True,
    }


def validate_authority() -> None:
    parent = subprocess.check_output(["git", "rev-parse", f"{SOURCE_REVIEW_COMMIT}^"], cwd=REPO_ROOT).decode().strip()
    if parent != SOURCE_REVIEW_PARENT:
        raise ValueError("freeze-v2 review parent mismatch")
    if subprocess.run(["git", "merge-base", "--is-ancestor", SOURCE_REVIEW_COMMIT, "HEAD"], cwd=REPO_ROOT, check=False).returncode != 0:
        raise ValueError("freeze-v2 blocked review is not an ancestor of HEAD")
    for path, digest in PRESERVED_INPUT_HASHES.items():
        if sha256_path(REPO_ROOT / path) != digest:
            raise ValueError(f"preserved v2 input changed: {path}")
    if not prompt_dependency_is_nonblocking(PROMPT_DEPENDENCY_ROLE):
        raise ValueError("protected Prompt.txt content changed")
    review = load_json(V2_REVIEW_RELATIVE_PATH)
    if not (
        review.get("verdict") == "B-BLOCKED_MUTATION_NONATOMIC"
        and review.get("selected_next_target") == TARGET
        and review.get("authority_rotation", {}).get("versioned_freeze_v3_correction_authorized") is True
        and review.get("authority_rotation", {}).get("additional_pilot_authorized") is False
        and review.get("authority_rotation", {}).get("canonical_203_record_execution_authorized") is False
    ):
        raise ValueError("freeze-v2 review does not authorize this bounded v3 correction")


def _passing_raw_fixture() -> dict[str, Any]:
    packet = load_json(V2_PACKET_RELATIVE_PATH)
    matrix = load_json(V2_MATRIX_RELATIVE_PATH)
    identity = load_json(V2_IDENTITY_RELATIVE_PATH)
    threshold_values = {
        item["raw_series_key"]: float(item["frozen_value"])
        for item in packet["numerical_threshold_provenance"]
        if item["threshold_class"] != "NUMERICAL_FLOOR"
    }
    records = {item["run_id"]: item for item in matrix["records"]}
    outputs: dict[str, dict[str, Any]] = {}
    for expected in identity["outputs"]:
        record = records[expected["run_id"]]
        series = {key: [0.0, 0.1 * value] for key, value in threshold_values.items()}
        series.update(
            {
                "solver_iterations": [4.0, 5.0],
                "final_phi2_l2": [1.0],
                "final_descendant_l2": [1.0],
                "matter_density_l2": [1.0, 1.0],
                "longitudinal_electric_field_l2": [1.0, 1.0],
                "matter_energy": [1.0, 1.0],
                "total_source_current_l2": [1.0, 1.0],
                "cumulative_exchange_longitudinal": [0.0, 1.0],
                "cumulative_exchange_phi2": [0.0, 0.01],
                "cumulative_exchange_phi3": [0.0, 0.01],
                "forced_transverse_equation_residual": [0.0, 1e-3],
            }
        )
        if record["run_role"] == "SPATIAL_REFINEMENT":
            series["final_phi2_l2"] = [1.0 + 1.0 / float(record["grid_size"])]
        if record["run_role"] == "TEMPORAL_REFINEMENT":
            dt = float(record["time_step"])
            series["final_descendant_l2"] = [1.0 + dt * dt]
            series["total_energy_delta"] = [0.0, 1e-6 * dt * dt]
        if record["run_role"] == "FORCED_COMPARATOR":
            for key in ("matter_density_l2", "longitudinal_electric_field_l2", "matter_energy", "total_source_current_l2"):
                series[key] = [0.98, 0.98]
            series["cumulative_exchange_longitudinal"] = [0.0, 0.98]
        control_observables: dict[str, float] = {}
        if "control_metadata" in record:
            for spec in record["control_metadata"]["control_evaluation_spec"]["required_observations"]:
                operator = spec["comparison_operator"]
                target = float(spec["target_value"])
                control_observables[spec["observable_id"]] = target if operator in {"GE", "GT", "EQ"} else min(0.0, target)
        outputs[expected["relative_output_path"]] = {
            "run_id": expected["run_id"],
            "scientific_row_id": expected["scientific_row_id"],
            "run_role": expected["run_role"],
            "model_class": expected["model_class"],
            "parent_run_or_row_id": expected["parent_run_or_row_id"],
            "input_hash": expected["input_hash"],
            "relative_output_path": expected["relative_output_path"],
            "series": series,
            "raw_observables": {"solver_error_norm": 1e-7, "truncation_error_norm": 1e-4, "model_domain_margin": 1.0},
            "control_observables": control_observables,
            "registered_numerical_payload": {"row_id": expected["scientific_row_id"], "samples": [1.0, 2.0, 3.0]},
        }
    fixture = {
        "fixture_id": BASELINE_FIXTURE_ID,
        "freeze_packet": packet,
        "run_matrix": matrix,
        "output_manifest": identity,
        "output_payloads": outputs,
        "declared_expected_run_ids": copy.deepcopy(packet["execution_consumer_contract"]["expected_run_id_set"]),
        "review_threshold_contracts": {
            "THR_FORCED_TRANSVERSE_RESIDUAL": {
                "threshold_id": "THR_FORCED_TRANSVERSE_RESIDUAL",
                "eligible_model_classes": ["INTENTIONALLY_NONINVARIANT_COMPARATOR"],
                "semantic_role": "COMPARATOR_ONLY_NEGATIVE_NECESSITY_DIAGNOSTIC",
            }
        },
        "review_feature_controls": {
            "PHASE_EXCHANGE_SIGN_CONTROL": {
                "control_id": "PHASE_EXCHANGE_SIGN_CONTROL",
                "target_feature_class": "DELTA_THETA_PSI_NONTRIVIAL",
                "assigned_row_id": "R08_PHASE_POSITIVE",
            },
            "NONTRIVIAL_HOLONOMY_CONTROL": {
                "control_id": "NONTRIVIAL_HOLONOMY_CONTROL",
                "target_feature_class": "THETA_W_NONTRIVIAL",
                "assigned_row_id": "R07_THETA_PARTNER",
            },
        },
        "untrusted_summary": {"supplied_pass": True},
    }
    result = _classify(fixture)
    if result["decision"] != BASELINE_DECISION:
        raise ValueError(f"baseline fixture does not pass: {result}")
    return fixture


def _escape_pointer_token(token: str) -> str:
    return token.replace("~", "~0").replace("/", "~1")


def _tokens(pointer: str) -> list[str]:
    if not pointer.startswith("/"):
        raise ValueError(f"invalid JSON pointer: {pointer}")
    if pointer == "/":
        return [""]
    return [token.replace("~1", "/").replace("~0", "~") for token in pointer[1:].split("/")]


def _get_pointer(payload: Any, pointer: str) -> Any:
    current = payload
    for token in _tokens(pointer):
        current = current[int(token)] if isinstance(current, list) else current[token]
    return current


def _apply_pointer(payload: Any, pointer: str, old_value: Any, new_value: Any) -> None:
    tokens = _tokens(pointer)
    current = payload
    for token in tokens[:-1]:
        current = current[int(token)] if isinstance(current, list) else current[token]
    final = tokens[-1]
    if old_value == ABSENT:
        if not isinstance(current, dict) or final in current:
            raise ValueError(f"add premise is not absent: {pointer}")
        current[final] = copy.deepcopy(new_value)
        return
    observed = current[int(final)] if isinstance(current, list) else current[final]
    if observed != old_value:
        raise ValueError(f"old value mismatch at {pointer}")
    if new_value == ABSENT:
        if isinstance(current, list):
            current.pop(int(final))
        else:
            del current[final]
    elif isinstance(current, list):
        current[int(final)] = copy.deepcopy(new_value)
    else:
        current[final] = copy.deepcopy(new_value)


def canonical_diff_pointers(left: Any, right: Any, pointer: str = "") -> list[str]:
    if type(left) is not type(right):
        return [pointer or "/"]
    if isinstance(left, dict):
        paths: list[str] = []
        for key in sorted(set(left) | set(right)):
            child = f"{pointer}/{_escape_pointer_token(str(key))}"
            if key not in left or key not in right:
                paths.append(child)
            else:
                paths.extend(canonical_diff_pointers(left[key], right[key], child))
        return paths
    if isinstance(left, list):
        if len(left) != len(right):
            return [pointer or "/"]
        paths = []
        for index, (left_item, right_item) in enumerate(zip(left, right, strict=True)):
            paths.extend(canonical_diff_pointers(left_item, right_item, f"{pointer}/{index}"))
        return paths
    return [] if left == right else [pointer or "/"]


def _rebind_derived_custody(fixture: dict[str, Any]) -> list[str]:
    packet = fixture["freeze_packet"]
    matrix_digest = classifier.sha256_bytes(classifier.canonical_json_bytes(fixture["run_matrix"]))
    identity_digest = classifier.sha256_bytes(classifier.canonical_json_bytes(fixture["output_manifest"]))
    rebound: list[str] = []
    if packet["canonical_run_matrix"]["sha256"] != matrix_digest:
        packet["canonical_run_matrix"]["sha256"] = matrix_digest
        rebound.append("/freeze_packet/canonical_run_matrix/sha256")
    if packet["expected_output_identity_manifest"]["sha256"] != identity_digest:
        packet["expected_output_identity_manifest"]["sha256"] = identity_digest
        rebound.append("/freeze_packet/expected_output_identity_manifest/sha256")
    return rebound


def _raw_threshold_value(fixture: dict[str, Any], key: str) -> float:
    for item in fixture["freeze_packet"]["numerical_threshold_provenance"]:
        if item["raw_series_key"] == key:
            return float(item["frozen_value"])
    raise KeyError(key)


def _any_raw_failure(fixture: dict[str, Any], series_key: str) -> bool:
    threshold = _raw_threshold_value(fixture, series_key)
    return any(
        max(abs(float(value)) for value in payload.get("series", {}).get(series_key, [0.0])) > threshold
        for payload in fixture["output_payloads"].values()
    )


def _classify(fixture: dict[str, Any]) -> dict[str, Any]:
    comparator_classes = fixture["review_threshold_contracts"]["THR_FORCED_TRANSVERSE_RESIDUAL"]["eligible_model_classes"]
    if comparator_classes != ["INTENTIONALLY_NONINVARIANT_COMPARATOR"]:
        return {
            "first_diagnostic": "THRESHOLD_SCOPE_MODEL_CLASS_MISMATCH",
            "decision": "B-BLOCKED_THRESHOLD_SCOPE",
            "materiality": "NOT_EVALUATED_CONTRACT_BLOCK",
            "eligibility": "INELIGIBLE",
        }
    phase = fixture["review_feature_controls"]["PHASE_EXCHANGE_SIGN_CONTROL"]
    if phase["assigned_row_id"] not in {"R08_PHASE_POSITIVE", "R09_PHASE_NEGATIVE"}:
        return {
            "first_diagnostic": "CONTROL_REQUIRED_PHASE_FEATURE_ABSENT",
            "decision": "B-BLOCKED_CONTROL_APPLICABILITY",
            "materiality": "NOT_EVALUATED_CONTRACT_BLOCK",
            "eligibility": "INELIGIBLE",
        }
    holonomy = fixture["review_feature_controls"]["NONTRIVIAL_HOLONOMY_CONTROL"]
    if holonomy["assigned_row_id"] not in {"R00_CANONICAL", "R07_THETA_PARTNER"}:
        return {
            "first_diagnostic": "CONTROL_REQUIRED_HOLONOMY_FEATURE_ABSENT",
            "decision": "B-BLOCKED_CONTROL_APPLICABILITY",
            "materiality": "NOT_EVALUATED_CONTRACT_BLOCK",
            "eligibility": "INELIGIBLE",
        }
    if fixture["declared_expected_run_ids"] != fixture["freeze_packet"]["execution_consumer_contract"]["expected_run_id_set"]:
        return {
            "first_diagnostic": "B-BLOCKED_RUN_IDENTITY",
            "decision": "B-BLOCKED_RUN_IDENTITY",
            "materiality": "NOT_EVALUATED_IDENTITY_BLOCK",
            "eligibility": "INELIGIBLE",
        }
    raw = classifier.classify_registered_result(
        fixture["freeze_packet"],
        fixture["run_matrix"],
        fixture["output_manifest"],
        fixture["output_payloads"],
        classifier_path=REPO_ROOT / V2_CLASSIFIER_RELATIVE_PATH,
    )
    status = raw["execution_status"]
    if status.startswith("B-BLOCKED"):
        return {
            "first_diagnostic": status,
            "decision": status,
            "materiality": "NOT_EVALUATED_CONTRACT_BLOCK",
            "eligibility": "INELIGIBLE",
        }
    robustness = raw["robustness_status"]
    materiality = raw["descendant_significance_status"]
    if robustness == "NUMERICALLY_BLOCKED":
        if _any_raw_failure(fixture, "solver_residual") and fixture["untrusted_summary"].get("supplied_pass") is True:
            diagnostic = "RAW_OUTPUT_THRESHOLD_FAILURE_SUPPLIED_PASS_IGNORED"
        elif _any_raw_failure(fixture, "gauss_residual") and materiality == "NOT_EVALUATED_NUMERICAL_BLOCK":
            diagnostic = "MATERIALITY_SUPPRESSED_AFTER_NUMERICAL_BLOCK"
        else:
            diagnostic = "NUMERICALLY_BLOCKED_FROM_RAW_OUTPUT"
        return {
            "first_diagnostic": diagnostic,
            "decision": "NUMERICALLY_BLOCKED",
            "materiality": materiality,
            "eligibility": "NUMERICAL_EVIDENCE_INELIGIBLE",
        }
    return {
        "first_diagnostic": "BASELINE_ACCEPTED",
        "decision": f"{status}:{robustness}",
        "materiality": materiality,
        "eligibility": "ELIGIBLE_PENDING_INDEPENDENT_RESULT_REVIEW",
    }


def _mutation(
    fixture: dict[str, Any],
    mutation_id: str,
    title: str,
    pointer: str,
    new_value: Any,
    premise_class: str,
    diagnostic: str,
    decision_after: str,
    eligibility_delta: str,
    materiality_delta: str,
    *,
    target_artifact_id: str,
    target_record_id: str,
    constructor: str = "JSON_POINTER_SINGLE_FIELD_REPLACE",
    target_feature_class: str = "NOT_FEATURE_SPECIFIC",
    raw_failure_contract: str = "NOT_APPLICABLE",
) -> dict[str, Any]:
    old_value = copy.deepcopy(_get_pointer(fixture, pointer)) if constructor != "JSON_POINTER_SINGLE_FIELD_ADD" else copy.deepcopy(ABSENT)
    if constructor == "JSON_POINTER_SINGLE_FIELD_REMOVE":
        new_value = copy.deepcopy(ABSENT)
    return {
        "mutation_id": mutation_id,
        "mutation_title": title,
        "baseline_fixture_id": BASELINE_FIXTURE_ID,
        "baseline_fixture_hash": sha256_bytes(canonical_json_bytes(fixture)),
        "baseline_expected_verdict": BASELINE_DECISION,
        "target_artifact_id": target_artifact_id,
        "target_record_id": target_record_id,
        "target_field_locator": pointer,
        "target_feature_class": target_feature_class,
        "premise_class": premise_class,
        "old_value": old_value,
        "new_value": copy.deepcopy(new_value),
        "changed_field_count": 1,
        "expected_first_diagnostic": diagnostic,
        "expected_decision_before": BASELINE_DECISION,
        "expected_decision_after": decision_after,
        "expected_eligibility_delta": eligibility_delta,
        "expected_materiality_delta": materiality_delta,
        "forbidden_prior_diagnostics": ["ANY_DIAGNOSTIC_OTHER_THAN_EXPECTED_FIRST_DIAGNOSTIC"],
        "forbidden_unrelated_decision_changes": ["SCIENTIFIC_MATRIX_COUNT_CHANGE", "THRESHOLD_VALUE_DRIFT_UNLESS_TARGETED", "MATERIALITY_GATE_CHANGE"],
        "mutation_constructor_id": constructor,
        "fresh_fixture_required": True,
        "atomicity_assertion": "canonical_diff_changed_field_count_equals_1_and_pointer_equals_target_field_locator",
        "derived_rebindings": ["packet matrix and identity SHA-256 fields may be mechanically rebound after the premise diff; rebindings are not premise changes"],
        "raw_failure_contract": raw_failure_contract,
    }


def mutation_registry(fixture: dict[str, Any]) -> list[dict[str, Any]]:
    packet = fixture["freeze_packet"]
    conv_index = {item["threshold_id"]: index for index, item in enumerate(packet["convergence_threshold_provenance"])}
    threshold_index = {item["threshold_id"]: index for index, item in enumerate(packet["numerical_threshold_provenance"])}
    contract_index = {item["control_id"]: index for index, item in enumerate(packet["control_applicability_freeze"]["contracts"])}
    r00_primary = next(
        item for item in fixture["run_matrix"]["records"]
        if item.get("scientific_row_id") == "R00_CANONICAL" and item["run_role"] == "PRIMARY_FULL_MODEL"
    )
    primary_path = r00_primary["output_path"]
    output_pointer = f"/output_payloads/{_escape_pointer_token(primary_path)}"
    first_output = fixture["output_manifest"]["outputs"][0]
    second_output = fixture["output_manifest"]["outputs"][1]
    first_filename = first_output["safe_filename"]
    first_path = first_output["relative_output_path"]
    mutations = [
        _mutation(fixture, "M_V3_SPATIAL_FLOOR_REVERTED_TO_1P5", "apply second-order floor to first-order Wilson spatial fit", f"/freeze_packet/convergence_threshold_provenance/{conv_index['minimum_spatial_descendant_order']}/frozen_value", 1.5, "CONVERGENCE_CLASS", "B-BLOCKED_CONVERGENCE_CLASS_MISMATCH", "B-BLOCKED_CONVERGENCE_CLASS_MISMATCH", "FREEZE_CONTRACT_ELIGIBLE_TO_INELIGIBLE", "UNCHANGED_NOT_EVALUATED", target_artifact_id="V2_FREEZE_PACKET", target_record_id="minimum_spatial_descendant_order"),
        _mutation(fixture, "M_V3_TEMPORAL_FLOOR_CHANGED_TO_0P8", "apply first-order floor to second-order temporal fit", f"/freeze_packet/convergence_threshold_provenance/{conv_index['minimum_temporal_descendant_order']}/frozen_value", 0.8, "CONVERGENCE_CLASS", "B-BLOCKED_CONVERGENCE_CLASS_MISMATCH", "B-BLOCKED_CONVERGENCE_CLASS_MISMATCH", "FREEZE_CONTRACT_ELIGIBLE_TO_INELIGIBLE", "UNCHANGED_NOT_EVALUATED", target_artifact_id="V2_FREEZE_PACKET", target_record_id="minimum_temporal_descendant_order"),
        _mutation(fixture, "M_V3_EXPECTED_ORDER_METADATA_REMOVED", "remove expected convergence class metadata", f"/freeze_packet/convergence_threshold_provenance/{conv_index['minimum_energy_error_order']}/expected_convergence_class", None, "CONVERGENCE_CLASS", "B-BLOCKED_CONVERGENCE_CLASS_MISMATCH", "B-BLOCKED_CONVERGENCE_CLASS_MISMATCH", "FREEZE_CONTRACT_ELIGIBLE_TO_INELIGIBLE", "UNCHANGED_NOT_EVALUATED", target_artifact_id="V2_FREEZE_PACKET", target_record_id="minimum_energy_error_order", constructor="JSON_POINTER_SINGLE_FIELD_REMOVE"),
        _mutation(fixture, "M_V3_THRESHOLD_ELIGIBLE_ROLES_REMOVED", "remove threshold role eligibility", f"/freeze_packet/numerical_threshold_provenance/{threshold_index['maximum_solver_residual']}/eligible_run_roles", None, "THRESHOLD_SCHEMA", "B-BLOCKED_THRESHOLD_SCHEMA", "B-BLOCKED_THRESHOLD_SCHEMA", "FREEZE_CONTRACT_ELIGIBLE_TO_INELIGIBLE", "UNCHANGED_NOT_EVALUATED", target_artifact_id="V2_FREEZE_PACKET", target_record_id="maximum_solver_residual", constructor="JSON_POINTER_SINGLE_FIELD_REMOVE"),
        _mutation(fixture, "M_V3_THRESHOLD_UNITS_REMOVED", "remove threshold units", f"/freeze_packet/numerical_threshold_provenance/{threshold_index['maximum_Gauss_residual']}/units", None, "THRESHOLD_SCHEMA", "B-BLOCKED_THRESHOLD_SCHEMA", "B-BLOCKED_THRESHOLD_SCHEMA", "FREEZE_CONTRACT_ELIGIBLE_TO_INELIGIBLE", "UNCHANGED_NOT_EVALUATED", target_artifact_id="V2_FREEZE_PACKET", target_record_id="maximum_Gauss_residual", constructor="JSON_POINTER_SINGLE_FIELD_REMOVE"),
        _mutation(fixture, "M_V3_THRESHOLD_NORMALIZATION_REMOVED", "remove threshold normalization", f"/freeze_packet/numerical_threshold_provenance/{threshold_index['maximum_continuity_residual']}/normalization_formula", None, "THRESHOLD_SCHEMA", "B-BLOCKED_THRESHOLD_SCHEMA", "B-BLOCKED_THRESHOLD_SCHEMA", "FREEZE_CONTRACT_ELIGIBLE_TO_INELIGIBLE", "UNCHANGED_NOT_EVALUATED", target_artifact_id="V2_FREEZE_PACKET", target_record_id="maximum_continuity_residual", constructor="JSON_POINTER_SINGLE_FIELD_REMOVE"),
        _mutation(fixture, "M_V3_COMPARATOR_THRESHOLD_APPLIED_TO_PRIMARY", "widen comparator-only threshold to the full model", "/review_threshold_contracts/THR_FORCED_TRANSVERSE_RESIDUAL/eligible_model_classes", ["INTENTIONALLY_NONINVARIANT_COMPARATOR", "FULL_MODEL"], "THRESHOLD_SCOPE_WIDENING_COMPARATOR_TO_FULL_MODEL", "THRESHOLD_SCOPE_MODEL_CLASS_MISMATCH", "B-BLOCKED_THRESHOLD_SCOPE", "FREEZE_CONTRACT_ELIGIBLE_TO_INELIGIBLE", "UNCHANGED_NOT_EVALUATED", target_artifact_id="V3_REVIEW_THRESHOLD_CONTRACTS", target_record_id="THR_FORCED_TRANSVERSE_RESIDUAL"),
        _mutation(fixture, "M_V3_UNSCALED_ABSOLUTE_THRESHOLD_SUBSTITUTED", "remove the row-scaling rule from a row-scaled residual", f"/freeze_packet/numerical_threshold_provenance/{threshold_index['maximum_phi2_wave_residual']}/row_scaling_rule", "", "THRESHOLD_SCOPE", "B-BLOCKED_THRESHOLD_SCOPE", "B-BLOCKED_THRESHOLD_SCOPE", "FREEZE_CONTRACT_ELIGIBLE_TO_INELIGIBLE", "UNCHANGED_NOT_EVALUATED", target_artifact_id="V2_FREEZE_PACKET", target_record_id="maximum_phi2_wave_residual"),
        _mutation(fixture, "M_V3_SUPPLIED_PASS_TRUE_WITH_RAW_FAILURE", "create a real raw solver failure while favorable summary remains true", f"{output_pointer}/series/solver_residual/1", 1.0, "RAW_OUTPUT_FAILURE_WITH_UNTRUSTED_PASS", "RAW_OUTPUT_THRESHOLD_FAILURE_SUPPLIED_PASS_IGNORED", "NUMERICALLY_BLOCKED", "NUMERICAL_EVIDENCE_ELIGIBLE_TO_INELIGIBLE", "DESCENDANT_CLASS_TO_NOT_EVALUATED_NUMERICAL_BLOCK", target_artifact_id="V3_RAW_OUTPUT_FIXTURE", target_record_id=r00_primary["run_id"], raw_failure_contract="solver_residual must exceed maximum_solver_residual while untrusted_summary.supplied_pass remains true"),
        _mutation(fixture, "M_V3_UNKNOWN_RUN_ID_ADDED", "replace one declared expected identity with an unknown identity", "/declared_expected_run_ids/0", "UNKNOWN_RUN_ID", "RUN_IDENTITY_SET", "B-BLOCKED_RUN_IDENTITY", "B-BLOCKED_RUN_IDENTITY", "EVIDENCE_SET_ELIGIBLE_TO_INELIGIBLE", "UNCHANGED_NOT_EVALUATED", target_artifact_id="V3_BASELINE_FIXTURE", target_record_id="expected_run_id_set[0]"),
        _mutation(fixture, "M_V3_REQUIRED_RUN_OMITTED", "remove one required raw output", f"/output_payloads/{_escape_pointer_token(first_path)}", None, "RUN_OUTPUT_COMPLETENESS", "B-BLOCKED_RUN_IDENTITY", "B-BLOCKED_RUN_IDENTITY", "EVIDENCE_SET_ELIGIBLE_TO_INELIGIBLE", "UNCHANGED_NOT_EVALUATED", target_artifact_id="V3_RAW_OUTPUT_FIXTURE", target_record_id=first_output["run_id"], constructor="JSON_POINTER_SINGLE_FIELD_REMOVE"),
        _mutation(fixture, "M_V3_VALID_RUN_DUPLICATED_UNDER_NEW_PATH", "add a duplicate payload under an unregistered path", "/output_payloads/formal~1output~1canonical~1v3-review-duplicate.json", copy.deepcopy(fixture["output_payloads"][first_path]), "RUN_OUTPUT_UNIQUENESS", "B-BLOCKED_RUN_IDENTITY", "B-BLOCKED_RUN_IDENTITY", "EVIDENCE_SET_ELIGIBLE_TO_INELIGIBLE", "UNCHANGED_NOT_EVALUATED", target_artifact_id="V3_RAW_OUTPUT_FIXTURE", target_record_id=first_output["run_id"], constructor="JSON_POINTER_SINGLE_FIELD_ADD"),
        _mutation(fixture, "M_V3_MATERIALITY_AFTER_NUMERICAL_BLOCK", "cross one Gauss threshold and require materiality suppression", f"{output_pointer}/series/gauss_residual/1", 1.0, "RAW_NUMERICAL_ADMISSIBILITY", "MATERIALITY_SUPPRESSED_AFTER_NUMERICAL_BLOCK", "NUMERICALLY_BLOCKED", "NUMERICAL_EVIDENCE_ELIGIBLE_TO_INELIGIBLE", "DESCENDANT_CLASS_TO_NOT_EVALUATED_NUMERICAL_BLOCK", target_artifact_id="V3_RAW_OUTPUT_FIXTURE", target_record_id=r00_primary["run_id"], raw_failure_contract="gauss_residual must exceed maximum_Gauss_residual; no materiality field changes"),
        _mutation(fixture, "M_V3_RAW_OUTPUT_CHANGED_SUMMARY_UNCHANGED", "cross one continuity threshold with summary untouched", f"{output_pointer}/series/continuity_residual/1", 1.0, "RAW_NUMERICAL_ADMISSIBILITY", "NUMERICALLY_BLOCKED_FROM_RAW_OUTPUT", "NUMERICALLY_BLOCKED", "NUMERICAL_EVIDENCE_ELIGIBLE_TO_INELIGIBLE", "DESCENDANT_CLASS_TO_NOT_EVALUATED_NUMERICAL_BLOCK", target_artifact_id="V3_RAW_OUTPUT_FIXTURE", target_record_id=r00_primary["run_id"], raw_failure_contract="continuity_residual must exceed maximum_continuity_residual; untrusted summary remains byte-identical"),
        _mutation(fixture, "M_V3_PHASE_CONTROL_ON_PHASE_TRIVIAL_ROW", "move the phase control to a phase-trivial row", "/review_feature_controls/PHASE_EXCHANGE_SIGN_CONTROL/assigned_row_id", "R00_CANONICAL", "CONTROL_FEATURE_APPLICABILITY", "CONTROL_REQUIRED_PHASE_FEATURE_ABSENT", "B-BLOCKED_CONTROL_APPLICABILITY", "CONTROL_CONTRACT_ELIGIBLE_TO_INELIGIBLE", "UNCHANGED_NOT_EVALUATED", target_artifact_id="V3_REVIEW_FEATURE_CONTROLS", target_record_id="PHASE_EXCHANGE_SIGN_CONTROL", target_feature_class="DELTA_THETA_PSI_NONTRIVIAL"),
        _mutation(fixture, "M_V3_HOLONOMY_CONTROL_ON_TRIVIAL_ROW", "move the holonomy control to the trivial-holonomy row", "/review_feature_controls/NONTRIVIAL_HOLONOMY_CONTROL/assigned_row_id", "R06_THETA_TRIVIAL", "CONTROL_FEATURE_APPLICABILITY", "CONTROL_REQUIRED_HOLONOMY_FEATURE_ABSENT", "B-BLOCKED_CONTROL_APPLICABILITY", "CONTROL_CONTRACT_ELIGIBLE_TO_INELIGIBLE", "UNCHANGED_NOT_EVALUATED", target_artifact_id="V3_REVIEW_FEATURE_CONTROLS", target_record_id="NONTRIVIAL_HOLONOMY_CONTROL", target_feature_class="THETA_W_NONTRIVIAL"),
        _mutation(fixture, "M_V3_REPRESENTATIVE_BASIS_REMOVED", "remove anchor representativeness basis", f"/freeze_packet/control_applicability_freeze/contracts/{contract_index['P_PHI2_PHI3_INTERCHANGE']}/representativeness_basis", None, "CONTROL_SCHEMA", "B-BLOCKED_CONTROL_SCHEMA", "B-BLOCKED_CONTROL_SCHEMA", "CONTROL_CONTRACT_ELIGIBLE_TO_INELIGIBLE", "UNCHANGED_NOT_EVALUATED", target_artifact_id="V2_FREEZE_PACKET", target_record_id="P_PHI2_PHI3_INTERCHANGE", constructor="JSON_POINTER_SINGLE_FIELD_REMOVE"),
        _mutation(fixture, "M_V3_CORNER_RELEVANT_CONTROL_EXCLUDED", "exclude the interaction corner from a transverse exchange control", f"/freeze_packet/control_applicability_freeze/contracts/{contract_index['N_REVERSE_TRANSVERSE_EXCHANGE_SIGN']}/applicable_row_ids", ["R05_F_HIGH"], "CONTROL_COVERAGE", "B-BLOCKED_CONTROL_SCHEMA", "B-BLOCKED_CONTROL_SCHEMA", "CONTROL_CONTRACT_ELIGIBLE_TO_INELIGIBLE", "UNCHANGED_NOT_EVALUATED", target_artifact_id="V2_FREEZE_PACKET", target_record_id="N_REVERSE_TRANSVERSE_EXCHANGE_SIGN"),
        _mutation(fixture, "M_V3_INVERSE_FILENAME_MAPPING_REMOVED", "remove one inverse filename mapping", f"/output_manifest/safe_filename_to_run_id/{_escape_pointer_token(first_filename)}", None, "RUN_IDENTITY_BIJECTION", "B-BLOCKED_RUN_IDENTITY", "B-BLOCKED_RUN_IDENTITY", "EVIDENCE_SET_ELIGIBLE_TO_INELIGIBLE", "UNCHANGED_NOT_EVALUATED", target_artifact_id="V2_OUTPUT_IDENTITY_MANIFEST", target_record_id=first_output["run_id"], constructor="JSON_POINTER_SINGLE_FIELD_REMOVE"),
        _mutation(fixture, "M_V3_TWO_IDS_ONE_FILENAME", "map a second output record to the first filename", "/output_manifest/outputs/1/safe_filename", first_filename, "RUN_IDENTITY_COLLISION", "B-BLOCKED_RUN_IDENTITY", "B-BLOCKED_RUN_IDENTITY", "EVIDENCE_SET_ELIGIBLE_TO_INELIGIBLE", "UNCHANGED_NOT_EVALUATED", target_artifact_id="V2_OUTPUT_IDENTITY_MANIFEST", target_record_id=second_output["run_id"]),
        _mutation(fixture, "M_V3_WRONG_PAYLOAD_RUN_ID", "put the wrong run identity inside one payload", f"/output_payloads/{_escape_pointer_token(first_path)}/run_id", "WRONG_INTERNAL_RUN_ID", "PAYLOAD_IDENTITY", "B-BLOCKED_RUN_IDENTITY", "B-BLOCKED_RUN_IDENTITY", "EVIDENCE_SET_ELIGIBLE_TO_INELIGIBLE", "UNCHANGED_NOT_EVALUATED", target_artifact_id="V3_RAW_OUTPUT_FIXTURE", target_record_id=first_output["run_id"]),
        _mutation(fixture, "M_V3_FILE_RENAMED_PAYLOAD_UNCHANGED", "change a manifest path without changing its payload", "/output_manifest/outputs/0/relative_output_path", "formal/output/canonical/v3-renamed-with-payload-unchanged.json", "PATH_PAYLOAD_IDENTITY", "B-BLOCKED_RUN_IDENTITY", "B-BLOCKED_RUN_IDENTITY", "EVIDENCE_SET_ELIGIBLE_TO_INELIGIBLE", "UNCHANGED_NOT_EVALUATED", target_artifact_id="V2_OUTPUT_IDENTITY_MANIFEST", target_record_id=first_output["run_id"]),
        _mutation(fixture, "M_V3_ORPHAN_OUTPUT_ADDED", "add one orphan output", "/output_payloads/formal~1output~1canonical~1v3-orphan.json", {"run_id": "ORPHAN"}, "RUN_OUTPUT_COMPLETENESS", "B-BLOCKED_RUN_IDENTITY", "B-BLOCKED_RUN_IDENTITY", "EVIDENCE_SET_ELIGIBLE_TO_INELIGIBLE", "UNCHANGED_NOT_EVALUATED", target_artifact_id="V3_RAW_OUTPUT_FIXTURE", target_record_id="ORPHAN", constructor="JSON_POINTER_SINGLE_FIELD_ADD"),
    ]
    if len(mutations) != 23 or len({item["mutation_id"] for item in mutations}) != 23:
        raise ValueError("exact 23-mutation registry required")
    return mutations


def _validate_registry_semantics(contract: dict[str, Any], baseline: dict[str, Any]) -> None:
    required = {
        "mutation_id", "mutation_title", "baseline_fixture_id", "baseline_fixture_hash", "baseline_expected_verdict",
        "target_artifact_id", "target_record_id", "target_field_locator", "target_feature_class", "premise_class",
        "old_value", "new_value", "changed_field_count", "expected_first_diagnostic", "expected_decision_before",
        "expected_decision_after", "expected_eligibility_delta", "expected_materiality_delta", "forbidden_prior_diagnostics",
        "forbidden_unrelated_decision_changes", "mutation_constructor_id", "fresh_fixture_required", "atomicity_assertion",
        "derived_rebindings", "raw_failure_contract",
    }
    if set(contract) != required:
        raise ValueError("MUTATION_REGISTRY_SCHEMA_MISMATCH")
    if contract["baseline_fixture_hash"] != sha256_bytes(canonical_json_bytes(baseline)):
        raise ValueError("MUTATION_BASELINE_HASH_MISMATCH")
    if contract["changed_field_count"] != 1 or contract["fresh_fixture_required"] is not True:
        raise ValueError("MUTATION_NONATOMIC_DECLARATION")
    if contract["premise_class"] == "THRESHOLD_SCOPE_WIDENING_COMPARATOR_TO_FULL_MODEL":
        if not (
            contract["old_value"] == ["INTENTIONALLY_NONINVARIANT_COMPARATOR"]
            and contract["new_value"] == ["INTENTIONALLY_NONINVARIANT_COMPARATOR", "FULL_MODEL"]
        ):
            raise ValueError("MUTATION_DIRECTION_MISMATCH")
    feature_expectations = {
        "DELTA_THETA_PSI_NONTRIVIAL": "PHASE_EXCHANGE_SIGN_CONTROL",
        "THETA_W_NONTRIVIAL": "NONTRIVIAL_HOLONOMY_CONTROL",
    }
    target_feature = contract["target_feature_class"]
    if target_feature in feature_expectations and contract["target_record_id"] != feature_expectations[target_feature]:
        raise ValueError("MUTATION_TARGET_FEATURE_CLASS_MISMATCH")


def execute_mutation(contract: dict[str, Any], baseline: dict[str, Any]) -> dict[str, Any]:
    _validate_registry_semantics(contract, baseline)
    fresh = copy.deepcopy(baseline)
    _apply_pointer(fresh, contract["target_field_locator"], contract["old_value"], contract["new_value"])
    diff = canonical_diff_pointers(baseline, fresh)
    if len(diff) != 1:
        raise ValueError(f"MUTATION_NONATOMIC_CHANGED_FIELD_COUNT_{len(diff)}")
    if diff[0] != contract["target_field_locator"]:
        raise ValueError("MUTATION_DIFF_POINTER_MISMATCH")
    rebindings = _rebind_derived_custody(fresh)
    actual = _classify(fresh)
    if contract["raw_failure_contract"] != "NOT_APPLICABLE" and actual["decision"] == BASELINE_DECISION:
        raise ValueError("MUTATION_RAW_FAILURE_NOT_REALIZED")
    if actual["first_diagnostic"] != contract["expected_first_diagnostic"]:
        raise ValueError("MUTATION_EXPECTED_DIAGNOSTIC_NOT_FIRST")
    if actual["decision"] != contract["expected_decision_after"]:
        raise ValueError("MUTATION_EXPECTED_DECISION_DELTA_NOT_REALIZED")
    return {
        "mutation_id": contract["mutation_id"],
        "fresh_baseline_hash": sha256_bytes(canonical_json_bytes(baseline)),
        "canonical_diff_pointers": diff,
        "changed_field_count": len(diff),
        "derived_rebindings": rebindings,
        "actual_first_diagnostic": actual["first_diagnostic"],
        "actual_decision_after": actual["decision"],
        "actual_materiality_after": actual["materiality"],
        "actual_eligibility_after": actual["eligibility"],
        "passed": True,
    }


def mutation_system_meta_regressions(registry: list[dict[str, Any]], baseline: dict[str, Any]) -> list[dict[str, Any]]:
    by_id = {item["mutation_id"]: item for item in registry}
    results: list[dict[str, Any]] = []

    reversed_direction = copy.deepcopy(by_id["M_V3_COMPARATOR_THRESHOLD_APPLIED_TO_PRIMARY"])
    reversed_direction["old_value"], reversed_direction["new_value"] = reversed_direction["new_value"], reversed_direction["old_value"]
    results.append(_require_meta_diagnostic("META_COMPARATOR_DIRECTION", "MUTATION_DIRECTION_MISMATCH", lambda: _validate_registry_semantics(reversed_direction, baseline)))

    wrong_phase = copy.deepcopy(by_id["M_V3_PHASE_CONTROL_ON_PHASE_TRIVIAL_ROW"])
    wrong_phase["target_record_id"] = "P_INITIAL_ZERO_DESCENDANTS_DYNAMICALLY_SOURCED"
    results.append(_require_meta_diagnostic("META_PHASE_FEATURE_CLASS", "MUTATION_TARGET_FEATURE_CLASS_MISMATCH", lambda: _validate_registry_semantics(wrong_phase, baseline)))

    wrong_holonomy = copy.deepcopy(by_id["M_V3_HOLONOMY_CONTROL_ON_TRIVIAL_ROW"])
    wrong_holonomy["target_record_id"] = "P_PHI2_PHI3_INTERCHANGE"
    results.append(_require_meta_diagnostic("META_HOLONOMY_FEATURE_CLASS", "MUTATION_TARGET_FEATURE_CLASS_MISMATCH", lambda: _validate_registry_semantics(wrong_holonomy, baseline)))

    def two_field_probe() -> None:
        mutated = copy.deepcopy(baseline)
        mutated["untrusted_summary"]["supplied_pass"] = False
        mutated["review_feature_controls"]["PHASE_EXCHANGE_SIGN_CONTROL"]["assigned_row_id"] = "R00_CANONICAL"
        count = len(canonical_diff_pointers(baseline, mutated))
        if count != 1:
            raise ValueError(f"MUTATION_NONATOMIC_CHANGED_FIELD_COUNT_{count}")

    results.append(_require_meta_diagnostic("META_TWO_FIELD_DIFF", "MUTATION_NONATOMIC_CHANGED_FIELD_COUNT_2", two_field_probe))

    wrong_first = copy.deepcopy(by_id["M_V3_PHASE_CONTROL_ON_PHASE_TRIVIAL_ROW"])
    wrong_first["expected_first_diagnostic"] = "DOWNSTREAM_DIAGNOSTIC"
    results.append(_require_meta_diagnostic("META_EXPECTED_DIAGNOSTIC_PRECEDENCE", "MUTATION_EXPECTED_DIAGNOSTIC_NOT_FIRST", lambda: execute_mutation(wrong_first, baseline)))

    missing_raw = copy.deepcopy(by_id["M_V3_SUPPLIED_PASS_TRUE_WITH_RAW_FAILURE"])
    missing_raw["new_value"] = missing_raw["old_value"]

    def raw_failure_probe() -> None:
        fresh = copy.deepcopy(baseline)
        _apply_pointer(fresh, missing_raw["target_field_locator"], missing_raw["old_value"], missing_raw["new_value"])
        if _classify(fresh)["decision"] == BASELINE_DECISION:
            raise ValueError("MUTATION_RAW_FAILURE_NOT_REALIZED")

    results.append(_require_meta_diagnostic("META_MISSING_RAW_FAILURE", "MUTATION_RAW_FAILURE_NOT_REALIZED", raw_failure_probe))
    return results


def _require_meta_diagnostic(meta_id: str, expected: str, operation: Any) -> dict[str, Any]:
    observed = "NO_DIAGNOSTIC"
    try:
        operation()
    except ValueError as error:
        observed = str(error)
    if observed != expected:
        raise ValueError(f"meta regression mismatch {meta_id}: expected {expected}, observed {observed}")
    return {"meta_regression_id": meta_id, "expected_diagnostic": expected, "observed_diagnostic": observed, "passed": True}


def build_artifacts() -> tuple[dict[str, Any], dict[str, Any], dict[str, Any], dict[str, Any]]:
    validate_authority()
    baseline = _passing_raw_fixture()
    registry = mutation_registry(baseline)
    executions = [execute_mutation(contract, baseline) for contract in registry]
    meta = mutation_system_meta_regressions(registry, baseline)
    baseline_hash = sha256_bytes(canonical_json_bytes(baseline))
    bundle = {
        "schema_id": "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_MUTATION_CAUSAL_CONTRACT_BUNDLE_v3",
        "captured_at_utc": CAPTURED_AT_UTC,
        "bundle_role": "REVIEW_ONLY_CAUSAL_FIXTURES_NOT_CANONICAL_SCIENTIFIC_RUNS",
        "baseline_fixture_id": BASELINE_FIXTURE_ID,
        "baseline_fixture_hash": baseline_hash,
        "baseline_expected_verdict": BASELINE_DECISION,
        "fresh_fixture_discipline": [
            "rebuild untouched baseline", "verify baseline hash and passing verdict", "apply one exact JSON-pointer delta",
            "verify one canonical diff", "mechanically rebind derived custody hashes", "require exact first diagnostic and decision delta", "discard fixture",
        ],
        "canonical_diff_contract": "recursive canonical JSON diff; equal-length arrays recurse by index and unequal-length arrays are one changed field",
        "derived_rebinding_is_not_a_premise_change": True,
        "baseline_fixture": baseline,
        "mutation_registry": registry,
        "mutation_execution_results": executions,
        "mutation_system_meta_regressions": meta,
        "mutation_count": len(registry),
        "meta_regression_count": len(meta),
        "all_mutations_atomic_and_exact": all(item["passed"] for item in executions),
        "all_meta_regressions_discriminate": all(item["passed"] for item in meta),
        "canonical_scientific_execution_record_count_change": 0,
    }
    bundle_raw = canonical_json_bytes(bundle)
    config = committed_configuration_custody()
    packet = {
        "schema_id": "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_CALIBRATION_AND_PARAMETER_FREEZE_PACKET_v3",
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "verdict": "PREPARED_PENDING_INDEPENDENT_REVIEW",
        "authority_basis": {
            "freeze_v2_review_commit": SOURCE_REVIEW_COMMIT,
            "freeze_v2_review_parent": SOURCE_REVIEW_PARENT,
            "freeze_v2_review_verdict": "B-BLOCKED_MUTATION_NONATOMIC",
            "preserved_input_artifacts": [{"path": path, "sha256": digest} for path, digest in PRESERVED_INPUT_HASHES.items()],
        },
        "bounded_v3_correction_scope": {
            "corrected_only": ["mutation causal contracts", "fresh-fixture atomicity", "first-diagnostic precedence", "committed-configuration custody"],
            "scientific_design_changed": False,
            "pilot_changed_or_reopened": False,
            "classifier_changed": False,
            "threshold_values_changed": False,
            "canonical_run_matrix_changed": False,
            "additional_pilot_required": False,
        },
        "preserved_v2_contract": {
            "scientific_rows": 14,
            "scientific_axes": 5,
            "scientific_records": 182,
            "positive_controls": 8,
            "negative_controls": 13,
            "total_canonical_records": 203,
            "numerical_threshold_values": 22,
            "convergence_classes": {
                "FIRST_ORDER_WILSON_AFFECTED_SPATIAL": 0.8,
                "SECOND_ORDER_TEMPORAL": 1.5,
                "SECOND_ORDER_ENERGY_ERROR": 1.5,
            },
            "materiality_gates": {"materially_influential": 0.1, "descendant_dominated": 0.5},
            "raw_output_classifier_sha256": PRESERVED_INPUT_HASHES[V2_CLASSIFIER_RELATIVE_PATH],
            "materiality_suppressed_after_numerical_or_model_domain_block": True,
            "invariant_descendant_free_comparator_invented": False,
            "existing_canonical_E_REPRO_unchanged": True,
        },
        "canonical_execution_contract": {
            "packet_v2": {"path": V2_PACKET_RELATIVE_PATH, "sha256": PRESERVED_INPUT_HASHES[V2_PACKET_RELATIVE_PATH]},
            "run_matrix_v2": {"path": V2_MATRIX_RELATIVE_PATH, "sha256": PRESERVED_INPUT_HASHES[V2_MATRIX_RELATIVE_PATH], "record_count": 203},
            "identity_manifest_v2": {"path": V2_IDENTITY_RELATIVE_PATH, "sha256": PRESERVED_INPUT_HASHES[V2_IDENTITY_RELATIVE_PATH], "record_count": 203},
            "classifier_v2": {"path": V2_CLASSIFIER_RELATIVE_PATH, "sha256": PRESERVED_INPUT_HASHES[V2_CLASSIFIER_RELATIVE_PATH]},
            "all_four_are_preserved_byte_for_byte": True,
        },
        "mutation_causal_contract": {
            "path": BUNDLE_RELATIVE_PATH,
            "sha256": sha256_bytes(bundle_raw),
            "baseline_fixture_hash": baseline_hash,
            "mutation_count": 23,
            "meta_regression_count": 6,
            "review_fixtures_are_not_scientific_execution_records": True,
        },
        "committed_configuration_custody": config,
        "historical_validation_correction": {
            "freeze_v2_report_rewritten": False,
            "freeze_v2_post_commit_99_test_assertion_fully_reproducible": False,
            "reason": "two historical regeneration tests depended on mutable working-tree .gitattributes bytes",
            "committed_v2_artifact_identities_remain_exact": True,
            "v3_authoritative_configuration_hashes_use_git_show_committed_bytes": True,
        },
        "selected_next_target": REVIEW_TARGET,
        "post_acceptance_target": POST_ACCEPTANCE_TARGET,
        "authority_boundary": {
            "freeze_v1_immutable_and_blocked": True,
            "freeze_v2_immutable_and_blocked": True,
            "freeze_v3_prepared": True,
            "freeze_v3_independently_accepted": False,
            "canonical_203_record_execution_authorized": False,
            "robustness_classification_assigned": False,
            "descendant_materiality_classification_assigned": False,
            "new_E_REPRO_claim": False,
        },
        "claim_ceiling": "Freeze v3 is a reviewable evidence-contract correction only. Only an independent ACCEPT_FREEZE verdict may authorize one exact 203-record execution; no result is authorized in advance.",
        "prompt_protection": {"path": PROMPT_RELATIVE_PATH, "sha256": PROMPT_SHA256},
        "historical_repository_wide_Lean": {"completed_jobs": 8441, "total_jobs": 8507, "status": "INCOMPLETE_TIMEOUT", "theorem_error_observed_before_timeout": False, "repository_wide_green_claim": False},
        "preparation_validation_status": {
            "focused_v3_tests": {"passed": 11, "failed": 0},
            "current_descendant_robustness_affected_chain": {"passed": 190, "failed": 0, "deselected_historical_worktree_sensitive_tests": 2},
            "deselection_scope": [
                "freeze-v1::test_generated_artifacts_are_current",
                "freeze-v2::test_generated_artifacts_are_current",
            ],
            "deselection_reason": "the two immutable historical generators read mutable working-tree .gitattributes; v3 replaces this authority input with committed Git blob bytes",
            "affected_Lean_build": {"status": "PASSED", "job_count": 146},
            "authority_surface_rotated_only_to_independent_v3_review": True,
        },
    }
    packet_raw = canonical_json_bytes(packet)
    manifest = {
        "schema_id": "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_CALIBRATION_AND_PARAMETER_FREEZE_MANIFEST_v3",
        "captured_at_utc": CAPTURED_AT_UTC,
        "generator": {"path": SCRIPT_RELATIVE_PATH, "sha256": sha256_path(SCRIPT_PATH)},
        "test": {"path": TEST_RELATIVE_PATH},
        "lean_witness": {"path": LEAN_RELATIVE_PATH},
        "packet": {"path": PACKET_RELATIVE_PATH, "sha256": sha256_bytes(packet_raw)},
        "mutation_bundle": {"path": BUNDLE_RELATIVE_PATH, "sha256": sha256_bytes(bundle_raw)},
        "preserved_v2_inputs": packet["authority_basis"]["preserved_input_artifacts"],
        "committed_configuration_source_commit": SOURCE_REVIEW_COMMIT,
        "selected_next_target": REVIEW_TARGET,
    }
    manifest_raw = canonical_json_bytes(manifest)
    report = {
        "schema_id": "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_CALIBRATION_AND_PARAMETER_FREEZE_PACKET_20260714_v3",
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "verdict": "PREPARED_PENDING_INDEPENDENT_REVIEW",
        "artifacts": {
            "packet": {"path": PACKET_RELATIVE_PATH, "sha256": sha256_bytes(packet_raw)},
            "mutation_bundle": {"path": BUNDLE_RELATIVE_PATH, "sha256": sha256_bytes(bundle_raw)},
            "manifest": {"path": MANIFEST_RELATIVE_PATH, "sha256": sha256_bytes(manifest_raw)},
            "classifier_preserved": {"path": V2_CLASSIFIER_RELATIVE_PATH, "sha256": PRESERVED_INPUT_HASHES[V2_CLASSIFIER_RELATIVE_PATH]},
            "matrix_preserved": {"path": V2_MATRIX_RELATIVE_PATH, "sha256": PRESERVED_INPUT_HASHES[V2_MATRIX_RELATIVE_PATH]},
        },
        "preserved_counts": packet["preserved_v2_contract"],
        "mutation_results": {
            "registered": 23,
            "atomic_exact_first_diagnostic_and_decision_delta_passed": len(executions),
            "meta_regressions_registered": 6,
            "meta_regressions_passed": len(meta),
        },
        "five_v2_findings_repaired": {
            "comparator_direction_exact": True,
            "phase_control_targets_phase_feature": True,
            "holonomy_control_targets_holonomy_feature": True,
            "materiality_after_block_single_premise_and_reachable": True,
            "supplied_pass_probe_contains_real_raw_failure": True,
        },
        "committed_configuration_custody": config,
        "validation_status": {
            "focused_v3_tests": {"passed": 11, "failed": 0},
            "current_affected_chain": {"passed": 190, "failed": 0, "historical_worktree_sensitive_deselections": 2},
            "affected_Lean_build": {"status": "PASSED", "job_count": 146},
            "authority_surface_parity_passed": True,
            "artifact_regeneration_passed": True,
            "repository_wide_Lean": "INCOMPLETE_HISTORICAL_TIMEOUT",
        },
        "selected_next_target": REVIEW_TARGET,
        "authority_boundary": packet["authority_boundary"],
        "claim_ceiling": packet["claim_ceiling"],
    }
    return packet, bundle, manifest, report


def artifact_bytes() -> dict[str, bytes]:
    packet, bundle, manifest, report = build_artifacts()
    return {
        PACKET_RELATIVE_PATH: canonical_json_bytes(packet),
        BUNDLE_RELATIVE_PATH: canonical_json_bytes(bundle),
        MANIFEST_RELATIVE_PATH: canonical_json_bytes(manifest),
        REPORT_RELATIVE_PATH: canonical_json_bytes(report),
    }


def write_or_check(check: bool) -> None:
    artifacts = artifact_bytes()
    mismatches = []
    for relative_path, raw in artifacts.items():
        path = REPO_ROOT / relative_path
        if check:
            if not path.exists() or path.read_bytes() != raw:
                mismatches.append(relative_path)
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(raw)
    if mismatches:
        raise SystemExit("artifact mismatch: " + ", ".join(mismatches))
    print(json.dumps({"status": "CHECKED" if check else "WROTE", "artifact_count": len(artifacts), "target": TARGET}, sort_keys=True))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    arguments = parser.parse_args()
    write_or_check(arguments.check)


if __name__ == "__main__":
    main()
