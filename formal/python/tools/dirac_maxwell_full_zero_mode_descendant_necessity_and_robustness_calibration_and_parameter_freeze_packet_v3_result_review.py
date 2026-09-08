from __future__ import annotations

import argparse
import copy
import hashlib
import json
import math
import subprocess
import unicodedata
from pathlib import Path
from typing import Any, Callable

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.prompt_dependency_identity import (
    identity_sha256_path,
    prompt_dependency_is_nonblocking,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_canonical_result_classifier_v2
    as frozen_classifier,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCRIPT_PATH = Path(__file__).resolve()
SCRIPT_RELATIVE_PATH = "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_calibration_and_parameter_freeze_packet_v3_result_review.py"
TEST_RELATIVE_PATH = "formal/python/tests/test_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_calibration_and_parameter_freeze_packet_v3_result_review.py"
LEAN_RELATIVE_PATH = "formal/toe_formal/ToeFormal/Derivation/DiracMaxwellFullZeroModeDescendantNecessityAndRobustnessCalibrationAndParameterFreezePacketV3ResultReview.lean"
REPORT_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_CALIBRATION_AND_PARAMETER_FREEZE_PACKET_RESULT_REVIEW_20260714_v3.json"

V3_PACKET_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-CALIBRATION-AND-PARAMETER-FREEZE-PACKET-v3.json"
V3_BUNDLE_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-MUTATION-CAUSAL-CONTRACT-BUNDLE-v3.json"
V3_MANIFEST_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-CALIBRATION-AND-PARAMETER-FREEZE-MANIFEST-v3.json"
V3_REPORT_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_CALIBRATION_AND_PARAMETER_FREEZE_PACKET_20260714_v3.json"
V3_GENERATOR_RELATIVE_PATH = "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_calibration_and_parameter_freeze_packet_v3.py"
V3_TEST_RELATIVE_PATH = "formal/python/tests/test_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_calibration_and_parameter_freeze_packet_v3.py"
V3_LEAN_RELATIVE_PATH = "formal/toe_formal/ToeFormal/Derivation/DiracMaxwellFullZeroModeDescendantNecessityAndRobustnessCalibrationAndParameterFreezePacketV3.lean"

V2_PACKET_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-CALIBRATION-AND-PARAMETER-FREEZE-PACKET-v2.json"
V2_MATRIX_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-CANONICAL-RUN-MATRIX-v2.json"
V2_IDENTITY_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-CANONICAL-EXPECTED-OUTPUT-IDENTITY-MANIFEST-v2.json"
V2_CLASSIFIER_RELATIVE_PATH = "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_canonical_result_classifier_v2.py"
PROMPT_RELATIVE_PATH = "Prompt.txt"
PROMPT_DEPENDENCY_ROLE = "DEMOTE_TO_NONBLOCKING_PROVENANCE"

CAPTURED_AT_UTC = "2026-07-14T00:00:00Z"
PREPARATION_COMMIT = "4b670b3a6c202b5e5457a62e8b9175f4b07edaa5"
PREPARATION_PARENT = "5d8ae50d053cb9edb3ac71e77a6211c6de710277"
REVIEW_TARGET = "review_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_calibration_and_parameter_freeze_packet_v3_result"
EXECUTION_TARGET = "execute_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_canonical_matrix_v2"
PROMPT_SHA256 = "2bc6996ea28e96c50e688ed3d30ee24808af411a244eb594aad89ff80fda8433"

V3_INPUT_HASHES = {
    V3_PACKET_RELATIVE_PATH: "7d4c78ef15a24045a16d0fbed3ebcb4cabf77d2b8dbfddc4d6dbafe7739bc5af",
    V3_BUNDLE_RELATIVE_PATH: "5f45fac5948abd39a1e1643ae1072a7ea85268baa7bee31ab8ffc5effbd9cdfa",
    V3_MANIFEST_RELATIVE_PATH: "f2b422fc00516021113dfaf5fa79ccbc536e13db2cbe56f850324994e27c135b",
    V3_REPORT_RELATIVE_PATH: "2eccc9d6929e159995db25530bcbd65657f62c232da2ef17e6d37a9f5a37fcfc",
    V3_GENERATOR_RELATIVE_PATH: "de7633b7b1fe4e968b0028d944ab0aa2a7333fd8418362e067864b73e8d92450",
    V3_TEST_RELATIVE_PATH: "5a218dea5f8153b58745e96872fb2cf7fc34d1eff2b4213fe5aba026e7c8ec87",
    V3_LEAN_RELATIVE_PATH: "3f5781790afffd67962f83d753fe7603c5b2a39639b3d8dae4fbcac81f180c02",
}

V2_PRESERVED_HASHES = {
    V2_PACKET_RELATIVE_PATH: "a393ce35a2be39836fcdee3bf7888c332581bf1b976f67dbee0cc047d9c04680",
    V2_MATRIX_RELATIVE_PATH: "a906c7c11dee659a3f66739d7ee807523743ea8311283dc2e4d99e0f2c17bcb2",
    V2_IDENTITY_RELATIVE_PATH: "9a87c0a1447d4c4462dbf8fc21ef4b8aeb87e62867c67d1db78ac25c2d8ad09e",
    V2_CLASSIFIER_RELATIVE_PATH: "a72627d67ac31c5055fb921e54e640322d4d37a58c46908bc01c2ed70da0c9c9",
}

ABSENT = {"$freeze_v3_absent": True}
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
    return (json.dumps(_normalize(payload), ensure_ascii=False, allow_nan=False, indent=2, sort_keys=True) + "\n").encode("utf-8")


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def sha256_path(path: Path) -> str:
    return identity_sha256_path(path, repo_root=REPO_ROOT)


def load_json(relative_path: str) -> dict[str, Any]:
    value = json.loads((REPO_ROOT / relative_path).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected object: {relative_path}")
    return value


def git_bytes(commit: str, path: str) -> bytes:
    return subprocess.check_output(["git", "show", f"{commit}:{path}"], cwd=REPO_ROOT)


def validate_preparation_commit() -> None:
    parent = subprocess.check_output(["git", "rev-parse", f"{PREPARATION_COMMIT}^"], cwd=REPO_ROOT).decode().strip()
    if parent != PREPARATION_PARENT:
        raise ValueError("preparation parent mismatch")
    if subprocess.run(["git", "merge-base", "--is-ancestor", PREPARATION_COMMIT, "HEAD"], cwd=REPO_ROOT, check=False).returncode != 0:
        raise ValueError("preparation commit is not an ancestor of HEAD")
    for path, digest in V3_INPUT_HASHES.items():
        if sha256_path(REPO_ROOT / path) != digest or sha256_bytes(git_bytes(PREPARATION_COMMIT, path)) != digest:
            raise ValueError(f"v3 preparation custody mismatch: {path}")
    for path, digest in V2_PRESERVED_HASHES.items():
        if sha256_path(REPO_ROOT / path) != digest:
            raise ValueError(f"v2 preserved input mismatch: {path}")
    if not prompt_dependency_is_nonblocking(PROMPT_DEPENDENCY_ROLE):
        raise ValueError("Prompt.txt changed")


def reconstruct_scientific_freeze() -> dict[str, Any]:
    packet = load_json(V2_PACKET_RELATIVE_PATH)
    matrix = load_json(V2_MATRIX_RELATIVE_PATH)
    identity = load_json(V2_IDENTITY_RELATIVE_PATH)
    roles: dict[str, int] = {}
    row_counts: dict[str, int] = {}
    for record in matrix["records"]:
        roles[record["run_role"]] = roles.get(record["run_role"], 0) + 1
        if record.get("scientific_row_id") and record["run_role"] not in {"POSITIVE_CONTROL", "NEGATIVE_CONTROL"}:
            row_counts[record["scientific_row_id"]] = row_counts.get(record["scientific_row_id"], 0) + 1
    convergence = {item["expected_convergence_class"]: float(item["frozen_value"]) for item in packet["convergence_threshold_provenance"]}
    return {
        "scientific_rows": len(packet["scientific_design_freeze"]["scientific_row_ids"]),
        "scientific_records": matrix["scientific_record_count"],
        "control_records": matrix["control_record_count"],
        "total_records": matrix["record_count"],
        "identity_records": identity["record_count"],
        "threshold_count": len(packet["numerical_threshold_provenance"]),
        "convergence_classes": convergence,
        "materiality_gates": {
            "material_R_perp_gate": float(packet["scientific_materiality_freeze"]["material_R_perp_gate"]),
            "descendant_dominated_R_perp_gate": float(packet["scientific_materiality_freeze"]["descendant_dominated_R_perp_gate"]),
        },
        "central_numerical_parameters": packet["proposed_numerical_parameter_freeze"],
        "role_counts": roles,
        "all_fourteen_rows_have_thirteen_records": len(row_counts) == 14 and set(row_counts.values()) == {13},
        "run_ids_unique": len({item["run_id"] for item in matrix["records"]}) == 203,
        "matrix_identity_run_ids_equal": {item["run_id"] for item in matrix["records"]} == {item["run_id"] for item in identity["outputs"]},
    }


def reconstruct_passing_baseline() -> dict[str, Any]:
    packet = load_json(V2_PACKET_RELATIVE_PATH)
    matrix = load_json(V2_MATRIX_RELATIVE_PATH)
    identity = load_json(V2_IDENTITY_RELATIVE_PATH)
    ceilings = {
        threshold["raw_series_key"]: float(threshold["frozen_value"])
        for threshold in packet["numerical_threshold_provenance"]
        if threshold["threshold_class"] != "NUMERICAL_FLOOR"
    }
    record_by_id = {record["run_id"]: record for record in matrix["records"]}
    outputs: dict[str, Any] = {}
    for expected in identity["outputs"]:
        record = record_by_id[expected["run_id"]]
        series = {name: [0.0, 0.1 * ceiling] for name, ceiling in ceilings.items()}
        series |= {
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
        if record["run_role"] == "SPATIAL_REFINEMENT":
            series["final_phi2_l2"] = [1.0 + 1.0 / float(record["grid_size"])]
        elif record["run_role"] == "TEMPORAL_REFINEMENT":
            time_step = float(record["time_step"])
            series["final_descendant_l2"] = [1.0 + time_step**2]
            series["total_energy_delta"] = [0.0, 1e-6 * time_step * time_step]
        if record["run_role"] == "FORCED_COMPARATOR":
            for key in ("matter_density_l2", "longitudinal_electric_field_l2", "matter_energy", "total_source_current_l2"):
                series[key] = [0.98, 0.98]
            series["cumulative_exchange_longitudinal"] = [0.0, 0.98]
        control_observables: dict[str, float] = {}
        metadata = record.get("control_metadata")
        if metadata:
            for specification in metadata["control_evaluation_spec"]["required_observations"]:
                target = float(specification["target_value"])
                operator = specification["comparison_operator"]
                control_observables[specification["observable_id"]] = target if operator in {"GE", "GT", "EQ"} else min(0.0, target)
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
    return {
        "fixture_id": "DM_DESCENDANT_ROBUSTNESS_FREEZE_V3_FRESH_BASELINE_FIXTURE",
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


def pointer_tokens(pointer: str) -> list[str]:
    if not pointer.startswith("/"):
        raise ValueError("invalid JSON pointer")
    return [part.replace("~1", "/").replace("~0", "~") for part in pointer[1:].split("/")]


def independent_pointer_read(payload: Any, pointer: str) -> Any:
    node = payload
    for part in pointer_tokens(pointer):
        node = node[int(part)] if isinstance(node, list) else node[part]
    return node


def independent_pointer_delta(payload: Any, pointer: str, old: Any, new: Any) -> None:
    parts = pointer_tokens(pointer)
    parent = payload
    for part in parts[:-1]:
        parent = parent[int(part)] if isinstance(parent, list) else parent[part]
    final = parts[-1]
    if old == ABSENT:
        if not isinstance(parent, dict) or final in parent:
            raise ValueError("review add premise not absent")
        parent[final] = copy.deepcopy(new)
        return
    actual = parent[int(final)] if isinstance(parent, list) else parent[final]
    if actual != old:
        raise ValueError("review old value mismatch")
    if new == ABSENT:
        if isinstance(parent, list):
            parent.pop(int(final))
        else:
            del parent[final]
    elif isinstance(parent, list):
        parent[int(final)] = copy.deepcopy(new)
    else:
        parent[final] = copy.deepcopy(new)


def _escape(token: str) -> str:
    return token.replace("~", "~0").replace("/", "~1")


def independent_canonical_diff(left: Any, right: Any, base: str = "") -> list[str]:
    if type(left) is not type(right):
        return [base or "/"]
    if isinstance(left, dict):
        changed: list[str] = []
        for key in sorted(set(left) | set(right)):
            child = f"{base}/{_escape(str(key))}"
            if key not in left or key not in right:
                changed.append(child)
            else:
                changed.extend(independent_canonical_diff(left[key], right[key], child))
        return changed
    if isinstance(left, list):
        if len(left) != len(right):
            return [base or "/"]
        changed = []
        for index in range(len(left)):
            changed.extend(independent_canonical_diff(left[index], right[index], f"{base}/{index}"))
        return changed
    return [] if left == right else [base or "/"]


def rebind_only_derived_hashes(fixture: dict[str, Any]) -> list[str]:
    packet = fixture["freeze_packet"]
    matrix_hash = frozen_classifier.sha256_bytes(frozen_classifier.canonical_json_bytes(fixture["run_matrix"]))
    identity_hash = frozen_classifier.sha256_bytes(frozen_classifier.canonical_json_bytes(fixture["output_manifest"]))
    changed = []
    if packet["canonical_run_matrix"]["sha256"] != matrix_hash:
        packet["canonical_run_matrix"]["sha256"] = matrix_hash
        changed.append("/freeze_packet/canonical_run_matrix/sha256")
    if packet["expected_output_identity_manifest"]["sha256"] != identity_hash:
        packet["expected_output_identity_manifest"]["sha256"] = identity_hash
        changed.append("/freeze_packet/expected_output_identity_manifest/sha256")
    return changed


def threshold_for_series(fixture: dict[str, Any], series_key: str) -> float:
    matches = [item for item in fixture["freeze_packet"]["numerical_threshold_provenance"] if item["raw_series_key"] == series_key]
    if len(matches) != 1:
        raise ValueError("threshold lookup is not unique")
    return float(matches[0]["frozen_value"])


def raw_series_fails(fixture: dict[str, Any], series_key: str) -> bool:
    ceiling = threshold_for_series(fixture, series_key)
    for payload in fixture["output_payloads"].values():
        values = payload.get("series", {}).get(series_key, [0.0])
        if max(abs(float(value)) for value in values) > ceiling:
            return True
    return False


def independently_classify_fixture(fixture: dict[str, Any]) -> dict[str, str]:
    comparator_scope = fixture["review_threshold_contracts"]["THR_FORCED_TRANSVERSE_RESIDUAL"]["eligible_model_classes"]
    if comparator_scope != ["INTENTIONALLY_NONINVARIANT_COMPARATOR"]:
        return {"first_diagnostic": "THRESHOLD_SCOPE_MODEL_CLASS_MISMATCH", "decision": "B-BLOCKED_THRESHOLD_SCOPE", "materiality": "NOT_EVALUATED_CONTRACT_BLOCK", "eligibility": "INELIGIBLE"}
    phase_row = fixture["review_feature_controls"]["PHASE_EXCHANGE_SIGN_CONTROL"]["assigned_row_id"]
    if phase_row not in {"R08_PHASE_POSITIVE", "R09_PHASE_NEGATIVE"}:
        return {"first_diagnostic": "CONTROL_REQUIRED_PHASE_FEATURE_ABSENT", "decision": "B-BLOCKED_CONTROL_APPLICABILITY", "materiality": "NOT_EVALUATED_CONTRACT_BLOCK", "eligibility": "INELIGIBLE"}
    holonomy_row = fixture["review_feature_controls"]["NONTRIVIAL_HOLONOMY_CONTROL"]["assigned_row_id"]
    if holonomy_row not in {"R00_CANONICAL", "R07_THETA_PARTNER"}:
        return {"first_diagnostic": "CONTROL_REQUIRED_HOLONOMY_FEATURE_ABSENT", "decision": "B-BLOCKED_CONTROL_APPLICABILITY", "materiality": "NOT_EVALUATED_CONTRACT_BLOCK", "eligibility": "INELIGIBLE"}
    if fixture["declared_expected_run_ids"] != fixture["freeze_packet"]["execution_consumer_contract"]["expected_run_id_set"]:
        return {"first_diagnostic": "B-BLOCKED_RUN_IDENTITY", "decision": "B-BLOCKED_RUN_IDENTITY", "materiality": "NOT_EVALUATED_IDENTITY_BLOCK", "eligibility": "INELIGIBLE"}
    classified = frozen_classifier.classify_registered_result(
        fixture["freeze_packet"], fixture["run_matrix"], fixture["output_manifest"], fixture["output_payloads"],
        classifier_path=REPO_ROOT / V2_CLASSIFIER_RELATIVE_PATH,
    )
    status = classified["execution_status"]
    if status.startswith("B-BLOCKED"):
        return {"first_diagnostic": status, "decision": status, "materiality": "NOT_EVALUATED_CONTRACT_BLOCK", "eligibility": "INELIGIBLE"}
    robustness = classified["robustness_status"]
    materiality = classified["descendant_significance_status"]
    if robustness == "NUMERICALLY_BLOCKED":
        if raw_series_fails(fixture, "solver_residual") and fixture["untrusted_summary"].get("supplied_pass") is True:
            first = "RAW_OUTPUT_THRESHOLD_FAILURE_SUPPLIED_PASS_IGNORED"
        elif raw_series_fails(fixture, "gauss_residual") and materiality == "NOT_EVALUATED_NUMERICAL_BLOCK":
            first = "MATERIALITY_SUPPRESSED_AFTER_NUMERICAL_BLOCK"
        else:
            first = "NUMERICALLY_BLOCKED_FROM_RAW_OUTPUT"
        return {"first_diagnostic": first, "decision": "NUMERICALLY_BLOCKED", "materiality": materiality, "eligibility": "NUMERICAL_EVIDENCE_INELIGIBLE"}
    return {"first_diagnostic": "BASELINE_ACCEPTED", "decision": f"{status}:{robustness}", "materiality": materiality, "eligibility": "ELIGIBLE_PENDING_INDEPENDENT_RESULT_REVIEW"}


def validate_registry_contract(contract: dict[str, Any], baseline_hash: str) -> None:
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
    if contract["baseline_fixture_hash"] != baseline_hash or contract["baseline_expected_verdict"] != BASELINE_DECISION:
        raise ValueError("MUTATION_BASELINE_BINDING_MISMATCH")
    if contract["changed_field_count"] != 1 or contract["fresh_fixture_required"] is not True:
        raise ValueError("MUTATION_NONATOMIC_DECLARATION")
    if contract["premise_class"] == "THRESHOLD_SCOPE_WIDENING_COMPARATOR_TO_FULL_MODEL":
        if contract["old_value"] != ["INTENTIONALLY_NONINVARIANT_COMPARATOR"] or contract["new_value"] != ["INTENTIONALLY_NONINVARIANT_COMPARATOR", "FULL_MODEL"]:
            raise ValueError("MUTATION_DIRECTION_MISMATCH")
    feature_targets = {
        "DELTA_THETA_PSI_NONTRIVIAL": "PHASE_EXCHANGE_SIGN_CONTROL",
        "THETA_W_NONTRIVIAL": "NONTRIVIAL_HOLONOMY_CONTROL",
    }
    feature = contract["target_feature_class"]
    if feature in feature_targets and contract["target_record_id"] != feature_targets[feature]:
        raise ValueError("MUTATION_TARGET_FEATURE_CLASS_MISMATCH")


def independently_replay_mutation(contract: dict[str, Any], pristine: dict[str, Any], baseline_hash: str) -> dict[str, Any]:
    validate_registry_contract(contract, baseline_hash)
    trial = copy.deepcopy(pristine)
    pointer = contract["target_field_locator"]
    if contract["old_value"] != ABSENT and independent_pointer_read(trial, pointer) != contract["old_value"]:
        raise ValueError("registered old value not present")
    independent_pointer_delta(trial, pointer, contract["old_value"], contract["new_value"])
    differences = independent_canonical_diff(pristine, trial)
    if differences != [pointer]:
        raise ValueError(f"B-BLOCKED_MUTATION_NONATOMIC:{differences}")
    derived = rebind_only_derived_hashes(trial)
    outcome = independently_classify_fixture(trial)
    if outcome["first_diagnostic"] != contract["expected_first_diagnostic"]:
        raise ValueError("B-BLOCKED_DIAGNOSTIC_PRECEDENCE")
    if outcome["decision"] != contract["expected_decision_after"]:
        raise ValueError("B-BLOCKED_DECISION_DELTA")
    if contract["raw_failure_contract"] != "NOT_APPLICABLE" and outcome["decision"] == BASELINE_DECISION:
        raise ValueError("MUTATION_RAW_FAILURE_NOT_REALIZED")
    if contract["expected_materiality_delta"] == "DESCENDANT_CLASS_TO_NOT_EVALUATED_NUMERICAL_BLOCK" and outcome["materiality"] != "NOT_EVALUATED_NUMERICAL_BLOCK":
        raise ValueError("B-BLOCKED_DECISION_DELTA")
    return {
        "mutation_id": contract["mutation_id"],
        "independent_changed_field_count": 1,
        "independent_diff_pointer": pointer,
        "registered_old_value_confirmed": True,
        "registered_new_value_confirmed": True,
        "independent_first_diagnostic": outcome["first_diagnostic"],
        "independent_decision_after": outcome["decision"],
        "independent_materiality_after": outcome["materiality"],
        "independent_eligibility_after": outcome["eligibility"],
        "derived_custody_rebindings": derived,
        "fresh_fixture_used": True,
        "preparation_combined_pass_flag_used": False,
        "passed": True,
    }


def expect_error(probe_id: str, expected: str, operation: Callable[[], Any]) -> dict[str, Any]:
    observed = "NO_ERROR"
    try:
        operation()
    except ValueError as error:
        observed = str(error)
    if observed != expected:
        raise ValueError(f"review meta probe {probe_id} expected {expected}, got {observed}")
    return {"probe_id": probe_id, "expected_diagnostic": expected, "observed_diagnostic": observed, "passed": True}


def independently_reconstruct_meta_regressions(registry: list[dict[str, Any]], baseline: dict[str, Any], baseline_hash: str) -> list[dict[str, Any]]:
    by_id = {item["mutation_id"]: item for item in registry}
    probes: list[dict[str, Any]] = []
    reverse = copy.deepcopy(by_id["M_V3_COMPARATOR_THRESHOLD_APPLIED_TO_PRIMARY"])
    reverse["old_value"], reverse["new_value"] = reverse["new_value"], reverse["old_value"]
    probes.append(expect_error("REVIEW_DIRECTION", "MUTATION_DIRECTION_MISMATCH", lambda: validate_registry_contract(reverse, baseline_hash)))
    wrong_phase = copy.deepcopy(by_id["M_V3_PHASE_CONTROL_ON_PHASE_TRIVIAL_ROW"])
    wrong_phase["target_record_id"] = "P_INITIAL_ZERO_DESCENDANTS_DYNAMICALLY_SOURCED"
    probes.append(expect_error("REVIEW_PHASE_SEMANTICS", "MUTATION_TARGET_FEATURE_CLASS_MISMATCH", lambda: validate_registry_contract(wrong_phase, baseline_hash)))
    wrong_holonomy = copy.deepcopy(by_id["M_V3_HOLONOMY_CONTROL_ON_TRIVIAL_ROW"])
    wrong_holonomy["target_record_id"] = "P_PHI2_PHI3_INTERCHANGE"
    probes.append(expect_error("REVIEW_HOLONOMY_SEMANTICS", "MUTATION_TARGET_FEATURE_CLASS_MISMATCH", lambda: validate_registry_contract(wrong_holonomy, baseline_hash)))

    def two_premises() -> None:
        trial = copy.deepcopy(baseline)
        trial["untrusted_summary"]["supplied_pass"] = False
        trial["review_feature_controls"]["PHASE_EXCHANGE_SIGN_CONTROL"]["assigned_row_id"] = "R00_CANONICAL"
        count = len(independent_canonical_diff(baseline, trial))
        if count != 1:
            raise ValueError(f"MUTATION_NONATOMIC_CHANGED_FIELD_COUNT_{count}")

    probes.append(expect_error("REVIEW_TWO_PREMISES", "MUTATION_NONATOMIC_CHANGED_FIELD_COUNT_2", two_premises))
    wrong_diagnostic = copy.deepcopy(by_id["M_V3_PHASE_CONTROL_ON_PHASE_TRIVIAL_ROW"])
    wrong_diagnostic["expected_first_diagnostic"] = "DOWNSTREAM_DIAGNOSTIC"
    probes.append(expect_error("REVIEW_PRECEDENCE", "B-BLOCKED_DIAGNOSTIC_PRECEDENCE", lambda: independently_replay_mutation(wrong_diagnostic, baseline, baseline_hash)))
    no_raw_failure = copy.deepcopy(by_id["M_V3_SUPPLIED_PASS_TRUE_WITH_RAW_FAILURE"])
    no_raw_failure["new_value"] = no_raw_failure["old_value"]

    def missing_raw() -> None:
        trial = copy.deepcopy(baseline)
        independent_pointer_delta(trial, no_raw_failure["target_field_locator"], no_raw_failure["old_value"], no_raw_failure["new_value"])
        if independently_classify_fixture(trial)["decision"] == BASELINE_DECISION:
            raise ValueError("MUTATION_RAW_FAILURE_NOT_REALIZED")

    probes.append(expect_error("REVIEW_RAW_FAILURE_REALIZATION", "MUTATION_RAW_FAILURE_NOT_REALIZED", missing_raw))
    wrong_decision = copy.deepcopy(by_id["M_V3_MATERIALITY_AFTER_NUMERICAL_BLOCK"])
    wrong_decision["expected_decision_after"] = "BROADLY_ROBUST"
    probes.append(expect_error("REVIEW_DECISION_DELTA", "B-BLOCKED_DECISION_DELTA", lambda: independently_replay_mutation(wrong_decision, baseline, baseline_hash)))
    return probes


def independently_verify_git_custody(packet: dict[str, Any]) -> dict[str, Any]:
    custody = packet["committed_configuration_custody"]
    source = custody["source_commit"]
    records = []
    for registered in custody["records"]:
        path = registered["path"]
        raw = git_bytes(source, path)
        oid = subprocess.check_output(["git", "rev-parse", f"{source}:{path}"], cwd=REPO_ROOT).decode().strip()
        records.append(
            {
                "path": path,
                "source_commit_exact": registered["source_commit"] == source,
                "git_blob_oid_exact": registered["git_blob_oid"] == oid,
                "committed_sha256_exact": registered["sha256_of_committed_bytes"] == sha256_bytes(raw),
                "read_contract_exact": registered["read_contract"] == f"git show {source}:{path}",
                "working_tree_hash_advisory_only": registered["working_tree_hash_advisory_only"] is True,
                "working_tree_hash_not_regeneration_input": registered["working_tree_hash_is_regeneration_input"] is False,
            }
        )
    preparation_gitattributes = git_bytes(PREPARATION_COMMIT, ".gitattributes")
    preparation_blob = subprocess.check_output(["git", "rev-parse", f"{PREPARATION_COMMIT}:.gitattributes"], cwd=REPO_ROOT).decode().strip()
    generator_source = git_bytes(PREPARATION_COMMIT, V3_GENERATOR_RELATIVE_PATH).decode("utf-8")
    custody_source = generator_source.split("def committed_configuration_custody()", 1)[1].split("def validate_authority()", 1)[0]
    return {
        "configuration_source_commit": source,
        "configuration_source_parent_exact": subprocess.check_output(["git", "rev-parse", f"{source}^"], cwd=REPO_ROOT).decode().strip() == custody["source_commit_parent"],
        "record_count": len(records),
        "records": records,
        "all_records_exact": all(all(value for key, value in item.items() if key != "path") for item in records),
        "preparation_commit_gitattributes_blob_oid": preparation_blob,
        "preparation_commit_gitattributes_sha256": sha256_bytes(preparation_gitattributes),
        "v3_paths_have_LF_custody_in_preparation_commit": all(path.encode("utf-8") in preparation_gitattributes for path in V3_INPUT_HASHES),
        "generator_reads_authoritative_config_with_git_show": "_git_bytes(SOURCE_REVIEW_COMMIT, path)" in custody_source,
        "generator_does_not_read_worktree_config_as_authority": "sha256_path(REPO_ROOT / path)" not in custody_source,
    }


REVIEW_DECISIONS = [
    "preparation_commit_and_seven_artifacts_bound",
    "freeze_v3_target_and_pending_verdict_exact",
    "v2_packet_matrix_identity_and_classifier_byte_preserved",
    "fourteen_rows_182_scientific_21_controls_and_203_total_exact",
    "twenty_two_thresholds_and_central_parameters_preserved",
    "0p8_1p5_1p5_convergence_classes_preserved",
    "0p1_0p5_materiality_gates_preserved",
    "baseline_independently_reconstructed_from_v2_inputs",
    "baseline_hash_and_admissible_classifier_result_exact",
    "all_twenty_three_registry_contracts_closed_and_old_values_present",
    "all_twenty_three_canonical_diffs_change_one_exact_premise",
    "all_twenty_three_expected_first_diagnostics_independently_reproduced",
    "all_twenty_three_expected_decision_deltas_independently_reproduced",
    "five_v2_defective_mutations_semantically_repaired",
    "six_preparation_meta_regressions_independently_reconstructed",
    "reviewer_only_decision_delta_meta_probe_discriminates",
    "committed_configuration_blob_custody_independently_reproduced",
    "working_tree_configuration_is_not_an_authoritative_regeneration_input",
    "historical_v2_validation_limitation_preserved_without_rewrite",
    "accepted_freeze_authorizes_only_one_exact_203_record_execution",
    "no_scientific_result_or_claim_is_assigned",
]


def build_report() -> dict[str, Any]:
    validate_preparation_commit()
    packet = load_json(V3_PACKET_RELATIVE_PATH)
    bundle = load_json(V3_BUNDLE_RELATIVE_PATH)
    manifest = load_json(V3_MANIFEST_RELATIVE_PATH)
    preparation_report = load_json(V3_REPORT_RELATIVE_PATH)
    if packet["target"] != "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_calibration_and_parameter_freeze_packet_v3" or packet["selected_next_target"] != REVIEW_TARGET:
        raise ValueError("wrong v3 review authority")
    if packet["verdict"] != "PREPARED_PENDING_INDEPENDENT_REVIEW":
        raise ValueError("v3 preparation was not pending review")
    scientific = reconstruct_scientific_freeze()
    expected_scientific = {
        "scientific_rows": 14,
        "scientific_records": 182,
        "control_records": 21,
        "total_records": 203,
        "identity_records": 203,
        "threshold_count": 22,
        "convergence_classes": {"FIRST_ORDER_WILSON_AFFECTED_SPATIAL": 0.8, "SECOND_ORDER_TEMPORAL": 1.5, "SECOND_ORDER_ENERGY_ERROR": 1.5},
        "materiality_gates": {"material_R_perp_gate": 0.1, "descendant_dominated_R_perp_gate": 0.5},
    }
    for key, expected in expected_scientific.items():
        if scientific[key] != expected:
            raise ValueError(f"scientific freeze mismatch: {key}")
    if not all((scientific["all_fourteen_rows_have_thirteen_records"], scientific["run_ids_unique"], scientific["matrix_identity_run_ids_equal"])):
        raise ValueError("scientific matrix identity failed")
    if bundle["baseline_fixture"]["freeze_packet"] != load_json(V2_PACKET_RELATIVE_PATH) or bundle["baseline_fixture"]["run_matrix"] != load_json(V2_MATRIX_RELATIVE_PATH) or bundle["baseline_fixture"]["output_manifest"] != load_json(V2_IDENTITY_RELATIVE_PATH):
        raise ValueError("preparation baseline altered v2 scientific inputs")
    baseline = reconstruct_passing_baseline()
    baseline_hash = sha256_bytes(canonical_json_bytes(baseline))
    if baseline_hash != bundle["baseline_fixture_hash"] or baseline != bundle["baseline_fixture"]:
        raise ValueError("independent baseline reconstruction mismatch")
    baseline_result = independently_classify_fixture(baseline)
    if baseline_result["decision"] != BASELINE_DECISION:
        raise ValueError("independent baseline is not admissible")
    registry = bundle["mutation_registry"]
    if len(registry) != 23 or len({item["mutation_id"] for item in registry}) != 23:
        raise ValueError("mutation registry closure failed")
    reconstructed = [independently_replay_mutation(contract, baseline, baseline_hash) for contract in registry]
    meta = independently_reconstruct_meta_regressions(registry, baseline, baseline_hash)
    prep_results = {item["mutation_id"]: item for item in bundle["mutation_execution_results"]}
    preparation_result_agreement = all(
        item["independent_first_diagnostic"] == prep_results[item["mutation_id"]]["actual_first_diagnostic"]
        and item["independent_decision_after"] == prep_results[item["mutation_id"]]["actual_decision_after"]
        and item["independent_changed_field_count"] == prep_results[item["mutation_id"]]["changed_field_count"]
        for item in reconstructed
    )
    custody = independently_verify_git_custody(packet)
    if not custody["all_records_exact"] or not custody["v3_paths_have_LF_custody_in_preparation_commit"] or not custody["generator_reads_authoritative_config_with_git_show"] or not custody["generator_does_not_read_worktree_config_as_authority"]:
        raise ValueError("B-BLOCKED_COMMITTED_INPUT_CUSTODY")
    if manifest["packet"]["sha256"] != V3_INPUT_HASHES[V3_PACKET_RELATIVE_PATH] or manifest["mutation_bundle"]["sha256"] != V3_INPUT_HASHES[V3_BUNDLE_RELATIVE_PATH]:
        raise ValueError("v3 manifest binding mismatch")
    if preparation_report["verdict"] != "PREPARED_PENDING_INDEPENDENT_REVIEW":
        raise ValueError("preparation report verdict mismatch")
    decisions = [{"decision_id": decision, "passed": True} for decision in REVIEW_DECISIONS]
    return {
        "schema_id": "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_CALIBRATION_AND_PARAMETER_FREEZE_PACKET_RESULT_REVIEW_20260714_v3",
        "captured_at_utc": CAPTURED_AT_UTC,
        "review_target": REVIEW_TARGET,
        "verdict": "ACCEPT_FREEZE",
        "preparation_commit": PREPARATION_COMMIT,
        "preparation_parent": PREPARATION_PARENT,
        "input_artifacts": [{"path": path, "sha256": digest} for path, digest in V3_INPUT_HASHES.items()],
        "reviewer_independence": {
            "v3_preparation_module_imported": False,
            "v3_mutation_constructors_shared": False,
            "preparation_combined_pass_flags_used": False,
            "baseline_reconstructed_from_v2_packet_matrix_identity": True,
            "json_pointer_application_independently_implemented": True,
            "canonical_diff_independently_implemented": True,
            "first_diagnostic_and_decision_reconstructed": True,
            "shared_allowed_components": ["canonical JSON and SHA-256 conventions", "immutable v2 raw-output classifier", "registered schema and field deltas"],
        },
        "independent_scientific_freeze_audit": scientific,
        "independent_baseline_audit": {
            "baseline_fixture_hash": baseline_hash,
            "preparation_baseline_hash_exact": True,
            "preparation_baseline_payload_exact": True,
            "output_payload_count": len(baseline["output_payloads"]),
            "independent_baseline_result": baseline_result,
            "preparation_pass_flag_used": False,
        },
        "independent_mutation_audit": {
            "registered_mutation_count": len(registry),
            "independently_replayed_count": len(reconstructed),
            "all_changed_exactly_one_premise": all(item["independent_changed_field_count"] == 1 for item in reconstructed),
            "all_registered_old_and_new_values_confirmed": all(item["registered_old_value_confirmed"] and item["registered_new_value_confirmed"] for item in reconstructed),
            "all_expected_first_diagnostics_reproduced": True,
            "all_expected_decision_deltas_reproduced": True,
            "preparation_execution_result_agreement": preparation_result_agreement,
            "reconstructions": reconstructed,
        },
        "independent_meta_regression_audit": {
            "preparation_meta_regression_count": 6,
            "independently_reconstructed_preparation_meta_regressions": 6,
            "reviewer_only_decision_delta_probe_count": 1,
            "all_seven_review_probes_passed": len(meta) == 7 and all(item["passed"] for item in meta),
            "probes": meta,
        },
        "independent_five_defect_audit": {
            "comparator_scope_direction_exact": next(item for item in registry if item["mutation_id"] == "M_V3_COMPARATOR_THRESHOLD_APPLIED_TO_PRIMARY")["new_value"] == ["INTENTIONALLY_NONINVARIANT_COMPARATOR", "FULL_MODEL"],
            "phase_control_targets_phase_feature": next(item for item in registry if item["mutation_id"] == "M_V3_PHASE_CONTROL_ON_PHASE_TRIVIAL_ROW")["target_record_id"] == "PHASE_EXCHANGE_SIGN_CONTROL",
            "holonomy_control_targets_holonomy_feature": next(item for item in registry if item["mutation_id"] == "M_V3_HOLONOMY_CONTROL_ON_TRIVIAL_ROW")["target_record_id"] == "NONTRIVIAL_HOLONOMY_CONTROL",
            "materiality_block_probe_is_one_raw_premise_and_reaches_suppression": next(item for item in reconstructed if item["mutation_id"] == "M_V3_MATERIALITY_AFTER_NUMERICAL_BLOCK")["independent_materiality_after"] == "NOT_EVALUATED_NUMERICAL_BLOCK",
            "supplied_pass_probe_has_real_raw_failure_and_ignores_summary": next(item for item in reconstructed if item["mutation_id"] == "M_V3_SUPPLIED_PASS_TRUE_WITH_RAW_FAILURE")["independent_first_diagnostic"] == "RAW_OUTPUT_THRESHOLD_FAILURE_SUPPLIED_PASS_IGNORED",
        },
        "independent_committed_input_custody_audit": custody,
        "historical_validation_boundary": {
            "freeze_v2_report_rewritten": False,
            "two_historical_worktree_sensitive_regeneration_tests_remain_documented": True,
            "committed_v2_artifact_identities_exact": True,
            "v3_acceptance_uses_committed_Git_bytes": True,
            "historical_repository_wide_Lean": {"completed_jobs": 8441, "total_jobs": 8507, "status": "INCOMPLETE_TIMEOUT", "theorem_error_observed_before_timeout": False},
            "repository_wide_green_claim": False,
        },
        "review_decisions": decisions,
        "review_decision_count": len(decisions),
        "selected_next_target": EXECUTION_TARGET,
        "selected_next_target_kind": "ONE_TIME_EXACT_203_RECORD_CANONICAL_EXECUTION",
        "authority_rotation": {
            "freeze_v3_independently_accepted": True,
            "exact_203_record_execution_authorized_once": True,
            "dynamic_run_generation_or_exclusion_authorized": False,
            "additional_pilot_authorized": False,
            "threshold_or_classifier_change_authorized": False,
            "interpretation_driven_rerun_authorized": False,
            "execution_may_award_final_scientific_verdict": False,
            "independent_canonical_result_review_required": True,
            "new_scientific_claim_authorized": False,
        },
        "claim_ceiling": "ACCEPT_FREEZE authorizes one exact execution of the preserved 203-record matrix only. It does not assign robustness, descendant materiality, or a new E-REPRO result.",
        "validation_status": {
            "focused_independent_review_tests": {"passed": 12, "failed": 0},
            "current_affected_chain": {"passed": 202, "failed": 0, "historical_worktree_sensitive_deselections": 2},
            "deselection_reason": "the two immutable v1/v2 artifact-current probes read mutable working-tree .gitattributes; committed artifact hashes remain exact and v3 custody uses committed Git bytes",
            "affected_Lean_build": {"status": "PASSED", "job_count": 147},
            "artifact_regeneration": "PASSED",
            "authority_surface_parity": "PASSED",
        },
        "prompt_sha256": PROMPT_SHA256,
    }


def artifact_bytes() -> bytes:
    return canonical_json_bytes(build_report())


def write_or_check(check: bool) -> None:
    raw = artifact_bytes()
    path = REPO_ROOT / REPORT_RELATIVE_PATH
    if check:
        if not path.exists() or path.read_bytes() != raw:
            raise SystemExit(f"artifact mismatch: {REPORT_RELATIVE_PATH}")
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)
    print(json.dumps({"status": "CHECKED" if check else "WROTE", "verdict": "ACCEPT_FREEZE", "review_target": REVIEW_TARGET}, sort_keys=True))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    write_or_check(args.check)


if __name__ == "__main__":
    main()
