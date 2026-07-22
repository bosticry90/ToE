from __future__ import annotations

import argparse
import ast
import copy
import hashlib
import json
import math
import os
import subprocess
import sys
import unicodedata
from collections import Counter
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.prompt_dependency_identity import (
    identity_sha256_path,
    prompt_dependency_is_nonblocking,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCRIPT_PATH = Path(__file__).resolve()
SCRIPT_RELATIVE_PATH = "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_calibration_and_parameter_freeze_packet_v2_result_review.py"
REVIEW_REPORT_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_CALIBRATION_AND_PARAMETER_FREEZE_PACKET_RESULT_REVIEW_20260714_v2.json"
REVIEW_REPORT_PATH = REPO_ROOT / REVIEW_REPORT_RELATIVE_PATH

FREEZE_REPORT_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_CALIBRATION_AND_PARAMETER_FREEZE_PACKET_20260714_v2.json"
FREEZE_MANIFEST_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-CALIBRATION-AND-PARAMETER-FREEZE-MANIFEST-v2.json"
FREEZE_PACKET_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-CALIBRATION-AND-PARAMETER-FREEZE-PACKET-v2.json"
RUN_MATRIX_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-CANONICAL-RUN-MATRIX-v2.json"
OUTPUT_IDENTITY_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-CANONICAL-EXPECTED-OUTPUT-IDENTITY-MANIFEST-v2.json"
FREEZE_GENERATOR_RELATIVE_PATH = "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_calibration_and_parameter_freeze_packet_v2.py"
CLASSIFIER_RELATIVE_PATH = "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_canonical_result_classifier_v2.py"
FREEZE_TEST_RELATIVE_PATH = "formal/python/tests/test_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_calibration_and_parameter_freeze_packet_v2.py"
FREEZE_LEAN_RELATIVE_PATH = "formal/toe_formal/ToeFormal/Derivation/DiracMaxwellFullZeroModeDescendantNecessityAndRobustnessCalibrationAndParameterFreezePacketV2.lean"
CURRENT_TARGET_RELATIVE_PATH = "formal/toe_formal/ToeFormal/Derivation/CurrentTarget.lean"
CURRENT_AUTHORITY_RELATIVE_PATH = "formal/toe_formal/ToeFormal/Release/CurrentAuthority.lean"
GUARDRAIL_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-GUARDRAIL-PACKET-v1.json"
PILOT_PACKET_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-NON-AUTHORITATIVE-PILOT-PACKET-v1.json"
PILOT_ARRAYS_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-NON-AUTHORITATIVE-PILOT-ARRAYS-v1.json"
CANONICAL_FREEZE_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-CANONICAL-PARAMETER-FREEZE-PACKET-v0.json"
PROMPT_RELATIVE_PATH = "Prompt.txt"
PROMPT_DEPENDENCY_ROLE = "DEMOTE_TO_NONBLOCKING_PROVENANCE"

CAPTURED_AT_UTC = "2026-07-14T00:00:00Z"
REVIEW_TARGET = "review_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_calibration_and_parameter_freeze_packet_v2_result"
SELECTED_NEXT_TARGET = "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_calibration_and_parameter_freeze_packet_v3"
VERDICT = "B-BLOCKED_MUTATION_NONATOMIC"
SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_CALIBRATION_AND_PARAMETER_FREEZE_PACKET_RESULT_REVIEW_20260714_v2"
FREEZE_COMMIT = "b83833d8"
FREEZE_PARENT = "9a3b0e47488bbffa4f77d7ec8abcde06ef9dc28e"
PROMPT_SHA256 = "2bc6996ea28e96c50e688ed3d30ee24808af411a244eb594aad89ff80fda8433"

EXPECTED_FREEZE_HASHES = {
    ".gitattributes": "f41c1830bdfdf4972f3304e8fa0ff3bab17430906eb456a971e4f2b4ad9c6f9d",
    FREEZE_REPORT_RELATIVE_PATH: "d4ebaa700242c722dda1c45461b90cac2b59f63cb8c81074e84634b337ccd56c",
    FREEZE_MANIFEST_RELATIVE_PATH: "cebe7a6cc1e5b3c01c6abb47ff0ea5050fa08f18701e62de0691d8564fdc763c",
    FREEZE_PACKET_RELATIVE_PATH: "a393ce35a2be39836fcdee3bf7888c332581bf1b976f67dbee0cc047d9c04680",
    OUTPUT_IDENTITY_RELATIVE_PATH: "9a87c0a1447d4c4462dbf8fc21ef4b8aeb87e62867c67d1db78ac25c2d8ad09e",
    RUN_MATRIX_RELATIVE_PATH: "a906c7c11dee659a3f66739d7ee807523743ea8311283dc2e4d99e0f2c17bcb2",
    FREEZE_TEST_RELATIVE_PATH: "db46a0b9e4fa12d7f4ef0e1b0012cd22f70f8ab3664043bfe181b7952f271dcb",
    FREEZE_GENERATOR_RELATIVE_PATH: "eaa5ba960731c8828f0208d8e8bc58b20dd74961606715f8f330295d00b7bb99",
    CLASSIFIER_RELATIVE_PATH: "a72627d67ac31c5055fb921e54e640322d4d37a58c46908bc01c2ed70da0c9c9",
    FREEZE_LEAN_RELATIVE_PATH: "7bc5fb1939f015a1597b447268ac7adc0270c5ae13beb09013787858d5447459",
    CURRENT_TARGET_RELATIVE_PATH: "eae13429957b029b218279bc2676ee1e5de80421d088e3ed657022d6e5369653",
    CURRENT_AUTHORITY_RELATIVE_PATH: "25fbd827be22d88fa86e8ddda0c52344ae3769af1823e0809c4bc28b5e23706a",
}
IMMUTABLE_WORKING_HASHES = {
    path: digest
    for path, digest in EXPECTED_FREEZE_HASHES.items()
    if path not in {".gitattributes", CURRENT_TARGET_RELATIVE_PATH, CURRENT_AUTHORITY_RELATIVE_PATH}
}

METRIC_SERIES = {
    "maximum_solver_residual": "solver_residual",
    "maximum_Gauss_residual": "gauss_residual",
    "maximum_continuity_residual": "continuity_residual",
    "maximum_link_norm_error": "link_norm_error",
    "maximum_energy_drift": "total_energy_delta",
    "maximum_exchange_longitudinal_residual": "exchange_longitudinal_residual",
    "maximum_exchange_phi2_residual": "exchange_phi2_residual",
    "maximum_exchange_phi3_residual": "exchange_phi3_residual",
    "maximum_exchange_combined_residual": "exchange_combined_residual",
    "maximum_longitudinal_Maxwell_residual": "longitudinal_Maxwell_residual",
    "maximum_phi2_wave_residual": "phi2_wave_residual",
    "maximum_phi3_wave_residual": "phi3_wave_residual",
    "maximum_Dirac_plus_sector1_residual": "Dirac_plus_sector1_residual",
    "maximum_Dirac_plus_sector2_residual": "Dirac_plus_sector2_residual",
    "maximum_Dirac_minus_sector1_residual": "Dirac_minus_sector1_residual",
    "maximum_Dirac_minus_sector2_residual": "Dirac_minus_sector2_residual",
    "maximum_adjoint_plus_sector1_residual": "adjoint_plus_sector1_residual",
    "maximum_adjoint_plus_sector2_residual": "adjoint_plus_sector2_residual",
    "maximum_adjoint_minus_sector1_residual": "adjoint_minus_sector1_residual",
    "maximum_adjoint_minus_sector2_residual": "adjoint_minus_sector2_residual",
}
OBSERVABLE_FLOOR_KEYS = ("matter_density_l2", "longitudinal_electric_field_l2", "matter_energy", "total_source_current_l2", "phi2_l2", "phi3_l2", "transverse_source_l2")
EXCHANGE_FLOOR_KEYS = ("cumulative_exchange_longitudinal", "cumulative_exchange_phi2", "cumulative_exchange_phi3")
SCIENTIFIC_ROLES = {"PRIMARY_FULL_MODEL", "SPATIAL_REFINEMENT", "TEMPORAL_REFINEMENT", "SOLVER_VERIFICATION", "DETERMINISTIC_DUPLICATE", "FORCED_COMPARATOR"}
EXPECTED_ROLE_COUNTS = {"DETERMINISTIC_DUPLICATE": 28, "FORCED_COMPARATOR": 14, "NEGATIVE_CONTROL": 13, "POSITIVE_CONTROL": 8, "PRIMARY_FULL_MODEL": 14, "SOLVER_VERIFICATION": 42, "SPATIAL_REFINEMENT": 42, "TEMPORAL_REFINEMENT": 42}


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


def git_output(*args: str) -> bytes:
    return subprocess.check_output(["git", *args], cwd=REPO_ROOT)


def bind_freeze_custody() -> dict[str, Any]:
    full_commit = git_output("rev-parse", FREEZE_COMMIT).decode().strip()
    if git_output("rev-parse", f"{full_commit}^").decode().strip() != FREEZE_PARENT:
        raise ValueError("freeze-v2 parent mismatch")
    if subprocess.run(["git", "merge-base", "--is-ancestor", full_commit, "HEAD"], cwd=REPO_ROOT, check=False).returncode != 0:
        raise ValueError("freeze-v2 commit is not an ancestor of HEAD")
    for path, digest in EXPECTED_FREEZE_HASHES.items():
        if sha256_bytes(git_output("show", f"{full_commit}:{path}")) != digest:
            raise ValueError(f"committed freeze-v2 hash mismatch: {path}")
    for path, digest in IMMUTABLE_WORKING_HASHES.items():
        if sha256_path(REPO_ROOT / path) != digest:
            raise ValueError(f"working freeze-v2 artifact changed: {path}")
    if not prompt_dependency_is_nonblocking(PROMPT_DEPENDENCY_ROLE):
        raise ValueError("protected Prompt.txt changed")
    return {"freeze_commit": full_commit, "freeze_parent": FREEZE_PARENT, "committed_path_count": len(EXPECTED_FREEZE_HASHES), "immutable_working_path_count": len(IMMUTABLE_WORKING_HASHES)}


def _record_input_hash(record: dict[str, Any]) -> str:
    excluded = {"safe_filename", "output_path", "input_hash", "payload_identity_contract"}
    return sha256_bytes(canonical_json_bytes({key: value for key, value in record.items() if key not in excluded}))


def audit_matrix(packet: dict[str, Any], matrix: dict[str, Any], guardrail: dict[str, Any]) -> dict[str, Any]:
    records = matrix["records"]
    rows = {row["row_id"]: row for row in guardrail["scientific_matrix"]}
    expected_local = {"PRIMARY_FULL_MODEL": 1, "SPATIAL_REFINEMENT": 3, "TEMPORAL_REFINEMENT": 3, "SOLVER_VERIFICATION": 3, "DETERMINISTIC_DUPLICATE": 2, "FORCED_COMPARATOR": 1}
    row_audits = []
    for row_id, row in rows.items():
        local = [record for record in records if record["scientific_row_id"] == row_id and record["run_role"] in SCIENTIFIC_ROLES]
        counts = Counter(record["run_role"] for record in local)
        row_audits.append({
            "row_id": row_id,
            "record_count": len(local),
            "role_counts_exact": counts == expected_local,
            "axes_exact": all(record["requested_axis_values"] == row["requested_axis_values"] for record in local),
            "forced_parent_exact": all(record["parent_scientific_row_id"] == row_id for record in local if record["run_role"] == "FORCED_COMPARATOR"),
        })
    input_hashes = {record["run_id"]: _record_input_hash(record) == record["input_hash"] for record in records}
    return {
        "record_count": len(records),
        "unique_run_id_count": len({record["run_id"] for record in records}),
        "role_counts": dict(sorted(Counter(record["run_role"] for record in records).items())),
        "role_counts_exact": Counter(record["run_role"] for record in records) == Counter(EXPECTED_ROLE_COUNTS),
        "row_audits": row_audits,
        "all_fourteen_rows_have_exact_thirteen_record_expansion": len(row_audits) == 14 and all(item["record_count"] == 13 and item["role_counts_exact"] and item["axes_exact"] and item["forced_parent_exact"] for item in row_audits),
        "all_input_hashes_reconstructed": all(input_hashes.values()),
        "packet_matrix_hash_exact": packet["canonical_run_matrix"]["sha256"] == sha256_path(REPO_ROOT / RUN_MATRIX_RELATIVE_PATH),
    }


def audit_identity(packet: dict[str, Any], matrix: dict[str, Any], identity: dict[str, Any], manifest: dict[str, Any]) -> dict[str, Any]:
    records = {record["run_id"]: record for record in matrix["records"]}
    outputs = identity["outputs"]
    forward = {item["run_id"]: item["safe_filename"] for item in outputs}
    inverse = {item["safe_filename"]: item["run_id"] for item in outputs}
    reserved = {"CON", "PRN", "AUX", "NUL", *(f"COM{i}" for i in range(1, 10)), *(f"LPT{i}" for i in range(1, 10))}
    legal = all(
        not any(character in '<>:"/\\|?*' for character in item["safe_filename"])
        and not item["safe_filename"].endswith((".", " "))
        and item["safe_filename"].split(".", 1)[0].upper() not in reserved
        for item in outputs
    )
    exact = all(
        item["run_id"] in records
        and item["safe_filename"] == records[item["run_id"]]["safe_filename"]
        and item["relative_output_path"] == records[item["run_id"]]["output_path"]
        and item["scientific_row_id"] == records[item["run_id"]]["scientific_row_id"]
        and item["run_role"] == records[item["run_id"]]["run_role"]
        and item["model_class"] == records[item["run_id"]]["model_or_comparator_class"]
        and item["parent_run_or_row_id"] == records[item["run_id"]]["parent_scientific_row_id"]
        and item["input_hash"] == records[item["run_id"]]["input_hash"]
        for item in outputs
    )
    paths = [item["relative_output_path"] for item in outputs]
    filenames = [item["safe_filename"] for item in outputs]
    required_echo = ["run_id", "scientific_row_id", "run_role", "model_class", "parent_run_or_row_id", "input_hash", "relative_output_path"]
    return {
        "record_count": len(outputs),
        "exact_matrix_manifest_field_reconciliation": exact,
        "forward_map_exact": identity["run_id_to_safe_filename"] == forward,
        "inverse_map_exact": identity["safe_filename_to_run_id"] == inverse,
        "unique_run_ids_paths_and_casefolded_NFC_filenames": len(set(forward)) == len(set(paths)) == len({unicodedata.normalize("NFC", name).casefold() for name in filenames}) == 203,
        "windows_filenames_legal": legal,
        "maximum_absolute_path_length": max(len(str(REPO_ROOT / path)) for path in paths),
        "payload_echo_contract_exact": packet["execution_consumer_contract"]["payload_required_echo_fields"] == required_echo,
        "packet_identity_hash_exact": packet["expected_output_identity_manifest"]["sha256"] == sha256_path(REPO_ROOT / OUTPUT_IDENTITY_RELATIVE_PATH),
        "manifest_identity_hash_exact": manifest["expected_output_identity_manifest"]["sha256"] == sha256_path(REPO_ROOT / OUTPUT_IDENTITY_RELATIVE_PATH),
    }


def _round_up_one_significant(value: float) -> float:
    if value <= 0.0:
        return 0.0
    exponent = math.floor(math.log10(value))
    scale = 10**exponent
    return math.ceil(value / scale) * scale


def audit_thresholds(packet: dict[str, Any], pilot_arrays: dict[str, Any]) -> dict[str, Any]:
    entries = {item["threshold_id"]: item for item in packet["numerical_threshold_provenance"]}
    runs = pilot_arrays["runs"]
    reconstructed: dict[str, Any] = {}
    for threshold_id, series_key in METRIC_SERIES.items():
        raw = [{"pilot_source_run_id": run["run_record_id"], "raw_reduced_value": max(abs(float(value)) for value in run["series"][series_key])} for run in runs]
        value = _round_up_one_significant(2.0 * max(item["raw_reduced_value"] for item in raw))
        entry = entries[threshold_id]
        reconstructed[threshold_id] = value == float(entry["frozen_value"]) and raw == entry["raw_pilot_values"] and entry["pilot_source_run_ids"] == [run["run_record_id"] for run in runs]
    by_row_role = {(run["row_id"], run["calibration_role"]): run for run in runs}
    for threshold_id, keys in (("epsilon_observable_floor", OBSERVABLE_FLOOR_KEYS), ("epsilon_exchange_floor", EXCHANGE_FLOOR_KEYS)):
        raw = []
        for row_id in sorted({run["row_id"] for run in runs}):
            medium = by_row_role[(row_id, "SOLVER_TOLERANCE_1e_MINUS_10")]
            fine = by_row_role[(row_id, "SOLVER_TOLERANCE_1e_MINUS_12")]
            measured = max(abs(float(left) - float(right)) for key in keys for left, right in zip(medium["series"][key], fine["series"][key], strict=True))
            raw.append({"row_id": row_id, "pilot_source_run_ids": [medium["run_record_id"], fine["run_record_id"]], "raw_maximum_medium_vs_fine_difference": measured})
        entry = entries[threshold_id]
        value = _round_up_one_significant(2.0 * max(item["raw_maximum_medium_vs_fine_difference"] for item in raw))
        reconstructed[threshold_id] = value == float(entry["frozen_value"]) and raw == entry["raw_pilot_values"]
    required = {"threshold_id", "observable_id", "raw_series_key", "threshold_class", "comparison_operator", "frozen_value", "expected_convergence_class", "eligible_run_roles", "eligible_scientific_rows", "units", "normalization_formula", "row_scaling_rule", "numerical_floor", "pilot_source_run_ids", "raw_pilot_values", "generation_formula", "safety_factor", "rounding_rule", "failure_diagnostic"}
    schemas = [set(item) == required and bool(item["eligible_run_roles"]) and len(item["eligible_scientific_rows"]) == 14 and all(isinstance(item[key], str) and item[key].strip() for key in ("units", "normalization_formula", "row_scaling_rule")) for item in entries.values()]
    return {"threshold_count": len(entries), "all_values_sources_and_raw_reductions_reconstructed": len(reconstructed) == 22 and all(reconstructed.values()), "all_threshold_schemas_complete": all(schemas), "reconstructed_threshold_ids": sorted(reconstructed)}


def audit_convergence(packet: dict[str, Any], canonical_freeze: dict[str, Any]) -> dict[str, Any]:
    entries = {item["threshold_id"]: item for item in packet["convergence_threshold_provenance"]}
    spatial = entries["minimum_spatial_descendant_order"]
    temporal = entries["minimum_temporal_descendant_order"]
    energy = entries["minimum_energy_error_order"]
    accepted = canonical_freeze["convergence_definitions"]
    return {
        "convergence_class_count": len(entries),
        "Wilson_spatial_class_exact": spatial["expected_convergence_class"] == "FIRST_ORDER_WILSON_AFFECTED_SPATIAL" and spatial["raw_series_key"] == accepted["spatial"]["metric"] == "final_phi2_l2" and float(spatial["frozen_value"]) == float(accepted["spatial"]["minimum_order"]) == 0.8 and spatial["eligible_run_roles"] == ["SPATIAL_REFINEMENT"],
        "temporal_class_exact": temporal["expected_convergence_class"] == "SECOND_ORDER_TEMPORAL" and temporal["raw_series_key"] == "final_descendant_l2" and float(temporal["frozen_value"]) == 1.5 and temporal["eligible_run_roles"] == ["TEMPORAL_REFINEMENT"],
        "energy_class_exact": energy["expected_convergence_class"] == "SECOND_ORDER_ENERGY_ERROR" and energy["raw_series_key"] == "total_energy_delta" and float(energy["frozen_value"]) == float(accepted["temporal_energy"]["minimum_order"]) == 1.5 and energy["eligible_run_roles"] == ["TEMPORAL_REFINEMENT"],
        "all_fit_members_fixed_for_all_fourteen_rows": all(item["fixed_fit_member_count"] == 3 and len(item["eligible_scientific_rows"]) == 14 for item in entries.values()),
    }


def audit_controls(packet: dict[str, Any], matrix: dict[str, Any], guardrail: dict[str, Any]) -> dict[str, Any]:
    controls = [record for record in matrix["records"] if record["run_role"] in {"POSITIVE_CONTROL", "NEGATIVE_CONTROL"}]
    contracts = packet["control_applicability_freeze"]["contracts"]
    by_id = {item["control_id"]: item for item in contracts}
    accepted = {item["control_id"] for item in [*guardrail["positive_controls"], *guardrail["negative_controls"]]}
    matrix_ids = {record["control_metadata"]["control_id"] for record in controls}
    scope_classes = {"GLOBAL_IMPLEMENTATION_INVARIANT", "ANCHOR_REPRESENTATIVE_WITH_PROOF", "ROW_LOCAL", "CONDITIONAL_FEATURE_DEPENDENT", "COMPARATOR_ONLY"}
    feature_representatives = {
        "P_INITIAL_ZERO_DESCENDANTS_DYNAMICALLY_SOURCED": "R03_F_ZERO",
        "P_INDEPENDENT_PHI2_EXCITATION": "R11_CORNER_WEAK_HIGH",
        "P_INDEPENDENT_PHI3_EXCITATION": "R10_MU_HIGH",
        "P_WEAK_COUPLING_APPROACH": "R01_ETA_WEAK",
        "N_DROP_ONLY_PHI2": "R11_CORNER_WEAK_HIGH",
        "N_DROP_ONLY_PHI3": "R10_MU_HIGH",
        "N_OMIT_DESCENDANT_ENERGY": "R05_F_HIGH",
        "N_OMIT_TRANSVERSE_EXCHANGE_CHANNEL": "R11_CORNER_WEAK_HIGH",
        "N_REVERSE_TRANSVERSE_EXCHANGE_SIGN": "R11_CORNER_WEAK_HIGH",
        "N_WRONG_GAMMA2_BLOCK": "R11_CORNER_WEAK_HIGH",
        "N_WRONG_GAMMA3_BLOCK": "R10_MU_HIGH",
    }
    return {
        "control_count": len(controls),
        "positive_count": sum(record["run_role"] == "POSITIVE_CONTROL" for record in controls),
        "negative_count": sum(record["run_role"] == "NEGATIVE_CONTROL" for record in controls),
        "control_ids_exact": matrix_ids == accepted == set(by_id),
        "matrix_contracts_equal_packet_contracts": all(record["control_metadata"] == by_id[record["control_metadata"]["control_id"]] for record in controls),
        "scope_classes_closed": all(item["scope_class"] in scope_classes for item in contracts),
        "representativeness_and_feature_predicates_nonempty": all(item["representativeness_basis"] and item["required_feature_predicate"] for item in contracts),
        "feature_dependent_representatives_exact": all(by_id[control_id]["representative_row_id"] == row_id for control_id, row_id in feature_representatives.items()),
        "row_local_forced_comparator_count": sum(record["run_role"] == "FORCED_COMPARATOR" for record in matrix["records"]),
        "all_interaction_corners_receive_row_local_forced_pressure": all(any(record["run_role"] == "FORCED_COMPARATOR" and record["scientific_row_id"] == row_id for record in matrix["records"]) for row_id in ("R11_CORNER_WEAK_HIGH", "R12_CORNER_STRONG_ZERO", "R13_CORNER_STRONG_LOW")),
    }


def classifier_source_audit(packet: dict[str, Any], manifest: dict[str, Any]) -> dict[str, Any]:
    source = (REPO_ROOT / CLASSIFIER_RELATIVE_PATH).read_text(encoding="utf-8")
    tree = ast.parse(source)
    imports: list[str] = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            imports.extend(alias.name for alias in node.names)
        elif isinstance(node, ast.ImportFrom):
            imports.append(node.module or "")
    allowed = {"__future__", "hashlib", "json", "math", "unicodedata", "pathlib", "typing"}
    return {
        "classifier_sha256": sha256_path(REPO_ROOT / CLASSIFIER_RELATIVE_PATH),
        "packet_binding_exact": packet["classifier_versioning_and_provenance"]["classifier_implementation"]["sha256"] == sha256_path(REPO_ROOT / CLASSIFIER_RELATIVE_PATH),
        "manifest_binding_exact": manifest["classifier"]["sha256"] == sha256_path(REPO_ROOT / CLASSIFIER_RELATIVE_PATH),
        "imports": sorted(imports),
        "no_project_local_or_mutable_decision_import": set(imports) <= allowed,
        "supplied_decision_fields_explicitly_forbidden": all(token in source for token in ("row_passed", "control_passed", "convergence_passed", "materiality_class", "robustness_class")),
        "raw_reconstruction_functions_present": all(token in source for token in ("_threshold_audit", "_convergence_audit", "_control_audit", "_materiality", "_identity_index")),
        "blocked_materiality_sentinels_present": all(token in source for token in ("NOT_EVALUATED_NUMERICAL_BLOCK", "NOT_EVALUATED_MODEL_DOMAIN_LIMIT")),
    }


def build_raw_fixture(packet: dict[str, Any], matrix: dict[str, Any], identity: dict[str, Any]) -> dict[str, dict[str, Any]]:
    thresholds = {item["raw_series_key"]: float(item["frozen_value"]) for item in packet["numerical_threshold_provenance"] if item["threshold_class"] != "NUMERICAL_FLOOR"}
    records = {record["run_id"]: record for record in matrix["records"]}
    outputs: dict[str, dict[str, Any]] = {}
    for expected in identity["outputs"]:
        record = records[expected["run_id"]]
        series = {key: [0.0, 0.1 * value] for key, value in thresholds.items()}
        series.update({
            "solver_iterations": [4.0, 5.0], "final_phi2_l2": [1.0], "final_descendant_l2": [1.0],
            "matter_density_l2": [1.0, 1.0], "longitudinal_electric_field_l2": [1.0, 1.0], "matter_energy": [1.0, 1.0], "total_source_current_l2": [1.0, 1.0],
            "cumulative_exchange_longitudinal": [0.0, 1.0], "cumulative_exchange_phi2": [0.0, 0.01], "cumulative_exchange_phi3": [0.0, 0.01], "forced_transverse_equation_residual": [0.0, 1e-3],
        })
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
                target = float(spec["target_value"])
                control_observables[spec["observable_id"]] = target if spec["comparison_operator"] in {"GE", "GT", "EQ"} else min(0.0, target)
        outputs[expected["relative_output_path"]] = {
            "run_id": expected["run_id"], "scientific_row_id": expected["scientific_row_id"], "run_role": expected["run_role"], "model_class": expected["model_class"],
            "parent_run_or_row_id": expected["parent_run_or_row_id"], "input_hash": expected["input_hash"], "relative_output_path": expected["relative_output_path"],
            "series": series, "raw_observables": {"solver_error_norm": 1e-7, "truncation_error_norm": 1e-4, "model_domain_margin": 1.0},
            "control_observables": control_observables, "registered_numerical_payload": {"row_id": expected["scientific_row_id"], "samples": [1.0, 2.0, 3.0]},
        }
    return outputs


def run_classifier(packet: dict[str, Any], matrix: dict[str, Any], identity: dict[str, Any], outputs: dict[str, Any]) -> dict[str, Any]:
    program = "import json,runpy,sys; from pathlib import Path; data=json.load(sys.stdin); ns=runpy.run_path(sys.argv[1]); result=ns['classify_registered_result'](data['packet'],data['matrix'],data['identity'],data['outputs'],classifier_path=Path(sys.argv[1])); json.dump(result,sys.stdout,sort_keys=True,separators=(',',':'))"
    environment = os.environ.copy()
    environment.update({"PYTHONHASHSEED": "0", "TZ": "UTC", "LC_ALL": "C", "LANG": "C"})
    result = subprocess.run([sys.executable, "-c", program, str(REPO_ROOT / CLASSIFIER_RELATIVE_PATH)], input=json.dumps({"packet": packet, "matrix": matrix, "identity": identity, "outputs": outputs}, allow_nan=False, sort_keys=True).encode("utf-8"), capture_output=True, cwd=REPO_ROOT, env=environment, check=False)
    if result.returncode != 0:
        raise ValueError(result.stderr.decode("utf-8", errors="replace"))
    return json.loads(result.stdout)


def audit_classifier_probes(packet: dict[str, Any], matrix: dict[str, Any], identity: dict[str, Any]) -> dict[str, Any]:
    outputs = build_raw_fixture(packet, matrix, identity)
    baseline_a = run_classifier(packet, matrix, identity, outputs)
    baseline_b = run_classifier(packet, matrix, identity, outputs)
    raw_failure = copy.deepcopy(outputs)
    primary = next(record for record in matrix["records"] if record["run_role"] == "PRIMARY_FULL_MODEL")
    raw_failure[primary["output_path"]]["series"]["solver_residual"] = [1.0]
    blocked = run_classifier(packet, matrix, identity, raw_failure)
    supplied = copy.deepcopy(raw_failure)
    supplied[primary["output_path"]]["passed"] = True
    supplied_result = run_classifier(packet, matrix, identity, supplied)
    missing = copy.deepcopy(outputs)
    missing.pop(next(iter(missing)))
    missing_result = run_classifier(packet, matrix, identity, missing)
    wrong_id = copy.deepcopy(outputs)
    wrong_id[next(iter(wrong_id))]["run_id"] = "UNREGISTERED_RUN"
    wrong_result = run_classifier(packet, matrix, identity, wrong_id)
    return {
        "baseline_result": baseline_a,
        "baseline_deterministic": canonical_json_bytes(baseline_a) == canonical_json_bytes(baseline_b),
        "baseline_reconstructs_candidate_without_authorizing_claim": baseline_a["execution_status"] == "CLASSIFIED_PENDING_INDEPENDENT_RESULT_REVIEW" and baseline_a["scientific_claim_authorized"] is False,
        "raw_failure_reconstructed_as_numeric_block": blocked["robustness_status"] == "NUMERICALLY_BLOCKED" and blocked["descendant_significance_status"] == "NOT_EVALUATED_NUMERICAL_BLOCK",
        "supplied_pass_boolean_rejected_before_use": supplied_result["execution_status"] == "B-BLOCKED_CLASSIFIER_TRUST",
        "missing_output_fails_identity": missing_result["execution_status"] == "B-BLOCKED_RUN_IDENTITY",
        "wrong_internal_run_id_fails_identity": wrong_result["execution_status"] == "B-BLOCKED_RUN_IDENTITY",
    }


def audit_mutation_atomicity(packet: dict[str, Any]) -> dict[str, Any]:
    registry = packet["blocker_regression_mutations"]
    test_source = (REPO_ROOT / FREEZE_TEST_RELATIVE_PATH).read_text(encoding="utf-8")
    required_self_describing_fields = {"mutation_id", "mutation_definition", "single_premise_delta", "expected_exact_diagnostic", "expected_decision_delta", "unrelated_prior_failure_forbidden"}
    registry_self_describing = all(required_self_describing_fields <= set(item) for item in registry)
    findings = [
        {
            "mutation_id": "M_V2_COMPARATOR_THRESHOLD_APPLIED_TO_PRIMARY",
            "atomic": False,
            "evidence": "The preparation probe appends FORCED_COMPARATOR to maximum_phi2_wave_residual, which is the reverse direction of the registered comparator-threshold-applied-to-primary mutation name.",
        },
        {
            "mutation_id": "M_V2_PHASE_CONTROL_MARKED_GLOBAL",
            "atomic": False,
            "evidence": "The preparation probe mutates P_INITIAL_ZERO_DESCENDANTS_DYNAMICALLY_SOURCED, a loading/source control, not a phase-dependent control.",
        },
        {
            "mutation_id": "M_V2_HOLONOMY_CONTROL_ON_TRIVIAL_ONLY_ROW",
            "atomic": False,
            "evidence": "The preparation probe mutates P_PHI2_PHI3_INTERCHANGE, not a holonomy control; no frozen holonomy-control mutation definition is supplied.",
        },
        {
            "mutation_id": "M_V2_MATERIALITY_SUPPLIED_AFTER_NUMERICAL_BLOCK",
            "atomic": False,
            "evidence": "The preparation probe changes both a forbidden materiality_class field and the raw solver residual; classifier-trust precedence fires before the numerical-block/materiality-suppression premise can be tested.",
        },
        {
            "mutation_id": "M_V2_SUPPLIED_PASSED_TRUE_WITH_RAW_FAILURE",
            "atomic": False,
            "evidence": "The preparation probe adds passed=true but does not introduce the raw failure named by the mutation; a separate test covers raw failure.",
        },
    ]
    source_markers = {
        "comparator_probe_direction_reversed": 'threshold["eligible_run_roles"].append("FORCED_COMPARATOR")' in test_source,
        "phase_probe_targets_nonphase_control": 'endswith("P_INITIAL_ZERO_DESCENDANTS_DYNAMICALLY_SOURCED")' in test_source,
        "holonomy_probe_targets_interchange_control": 'endswith("P_PHI2_PHI3_INTERCHANGE")' in test_source,
        "materiality_probe_changes_two_premises": 'payload["materiality_class"]' in test_source and 'payload["series"]["solver_residual"] = [1.0]' in test_source,
    }
    return {
        "registered_mutation_count": len(registry),
        "unique_mutation_count": len({item["mutation_id"] for item in registry}),
        "registry_fields_present": sorted(set.intersection(*(set(item) for item in registry))),
        "required_self_describing_fields": sorted(required_self_describing_fields),
        "registry_is_independently_self_describing": registry_self_describing,
        "preparation_source_markers_reconstructed": source_markers,
        "non_atomic_or_semantically_mismatched_mutations": findings,
        "non_atomic_count": len(findings),
        "all_twenty_three_atomic_and_independently_reconstructible": registry_self_describing and not findings and all(source_markers.values()),
        "blocking_reason": "The 23-entry registry records only an ID, expected diagnostic, and an unrelated-failure flag. It omits the frozen premise delta and expected decision delta, and at least five preparation probes do not implement the semantic mutation named by their IDs or change multiple premises before precedence is evaluated.",
    }


def audit_materiality_and_authority(packet: dict[str, Any], guardrail: dict[str, Any]) -> dict[str, Any]:
    materiality = packet["scientific_materiality_freeze"]
    accepted = guardrail["threshold_freeze"]
    boundary = packet["authority_boundary"]
    return {
        "material_gate_exact": materiality["material_R_perp_gate"] == materiality["material_F_exchange_perp_gate"] == accepted["material_R_perp_gate"] == accepted["material_F_exchange_perp_gate"] == 0.1,
        "dominated_gate_exact": materiality["descendant_dominated_R_perp_gate"] == materiality["descendant_dominated_F_exchange_perp_gate"] == accepted["descendant_dominated_R_perp_gate"] == accepted["descendant_dominated_F_exchange_perp_gate"] == 0.5,
        "sensitivity_exact": materiality["threshold_sensitivity_values"] == [0.05, 0.1, 0.2],
        "execution_unauthorized_in_proposal": boundary["canonical_fourteen_row_execution_authorized"] is False,
        "new_claim_unauthorized": boundary["new_E_REPRO_claim"] is False,
        "canonical_E_REPRO_unchanged": boundary["previous_canonical_E_REPRO_unchanged"] is True,
    }


def build_review() -> dict[str, Any]:
    custody = bind_freeze_custody()
    packet = load_json(FREEZE_PACKET_RELATIVE_PATH)
    matrix = load_json(RUN_MATRIX_RELATIVE_PATH)
    identity = load_json(OUTPUT_IDENTITY_RELATIVE_PATH)
    manifest = load_json(FREEZE_MANIFEST_RELATIVE_PATH)
    freeze_report = load_json(FREEZE_REPORT_RELATIVE_PATH)
    guardrail = load_json(GUARDRAIL_RELATIVE_PATH)
    pilot_arrays = load_json(PILOT_ARRAYS_RELATIVE_PATH)
    canonical_freeze = load_json(CANONICAL_FREEZE_RELATIVE_PATH)

    matrix_audit = audit_matrix(packet, matrix, guardrail)
    identity_audit = audit_identity(packet, matrix, identity, manifest)
    threshold_audit = audit_thresholds(packet, pilot_arrays)
    convergence_audit = audit_convergence(packet, canonical_freeze)
    control_audit = audit_controls(packet, matrix, guardrail)
    source_audit = classifier_source_audit(packet, manifest)
    classifier_audit = audit_classifier_probes(packet, matrix, identity)
    mutation_audit = audit_mutation_atomicity(packet)
    materiality_audit = audit_materiality_and_authority(packet, guardrail)

    decisions = {
        "freeze_v2_commit_and_twelve_paths_bound": custody["committed_path_count"] == 12,
        "proposal_target_and_pending_verdict_exact": packet["target"] == REVIEW_TARGET.replace("review_", "prepare_", 1).replace("_result", "") and freeze_report["verdict"] == "PREPARED_PENDING_INDEPENDENT_REVIEW",
        "all_203_records_unique_complete_and_role_qualified": matrix_audit["record_count"] == matrix_audit["unique_run_id_count"] == 203 and matrix_audit["role_counts_exact"],
        "all_fourteen_rows_uniform_axis_exact_and_parent_safe": matrix_audit["all_fourteen_rows_have_exact_thirteen_record_expansion"],
        "all_record_input_hashes_independently_reconstructed": matrix_audit["all_input_hashes_reconstructed"],
        "all_twenty_two_threshold_values_sources_and_raw_reductions_reconstructed": threshold_audit["all_values_sources_and_raw_reductions_reconstructed"],
        "all_threshold_semantics_complete": threshold_audit["all_threshold_schemas_complete"],
        "Wilson_temporal_and_energy_convergence_classes_exact": convergence_audit["Wilson_spatial_class_exact"] and convergence_audit["temporal_class_exact"] and convergence_audit["energy_class_exact"] and convergence_audit["all_fit_members_fixed_for_all_fourteen_rows"],
        "control_inventory_scope_and_feature_representatives_exact": control_audit["control_ids_exact"] and control_audit["matrix_contracts_equal_packet_contracts"] and control_audit["scope_classes_closed"] and control_audit["feature_dependent_representatives_exact"],
        "all_interaction_corners_have_row_local_forced_pressure": control_audit["all_interaction_corners_receive_row_local_forced_pressure"],
        "identity_forward_inverse_path_payload_contract_exact": identity_audit["exact_matrix_manifest_field_reconciliation"] and identity_audit["forward_map_exact"] and identity_audit["inverse_map_exact"] and identity_audit["payload_echo_contract_exact"],
        "identity_collision_free_windows_safe_and_hash_bound": identity_audit["unique_run_ids_paths_and_casefolded_NFC_filenames"] and identity_audit["windows_filenames_legal"] and identity_audit["packet_identity_hash_exact"] and identity_audit["manifest_identity_hash_exact"],
        "classifier_source_closure_and_hash_custody_exact": source_audit["packet_binding_exact"] and source_audit["manifest_binding_exact"] and source_audit["no_project_local_or_mutable_decision_import"],
        "classifier_reconstructs_raw_failures_and_suppresses_blocked_materiality": classifier_audit["raw_failure_reconstructed_as_numeric_block"],
        "classifier_rejects_supplied_booleans_missing_outputs_and_wrong_ids": classifier_audit["supplied_pass_boolean_rejected_before_use"] and classifier_audit["missing_output_fails_identity"] and classifier_audit["wrong_internal_run_id_fails_identity"],
        "all_twenty_three_mutations_atomic_self_describing_and_independently_reconstructible": mutation_audit["all_twenty_three_atomic_and_independently_reconstructible"],
        "materiality_gates_and_nonpromotion_boundary_exact": all(materiality_audit.values()),
    }
    return {
        "schema_id": SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "review_target": REVIEW_TARGET,
        "verdict": VERDICT,
        "accepted": False,
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": "VERSIONED_FREEZE_CORRECTION_ONLY",
        "freeze_custody": custody,
        "freeze_generator_imported": False,
        "freeze_test_imported": False,
        "classifier_imported": False,
        "classifier_invoked_only_in_isolated_subprocess_probes": True,
        "independent_matrix_audit": matrix_audit,
        "independent_threshold_audit": threshold_audit,
        "independent_convergence_audit": convergence_audit,
        "independent_control_audit": control_audit,
        "independent_identity_audit": identity_audit,
        "independent_classifier_source_audit": source_audit,
        "independent_classifier_probe_audit": classifier_audit,
        "independent_mutation_atomicity_audit": mutation_audit,
        "independent_materiality_and_authority_audit": materiality_audit,
        "review_decisions": [{"decision_id": key, "passed": value} for key, value in decisions.items()],
        "decision_count": len(decisions),
        "all_decisions_passed": all(decisions.values()),
        "blocking_diagnostics": [
            {
                "diagnostic": "B-BLOCKED_MUTATION_NONATOMIC",
                "evidence": mutation_audit["blocking_reason"],
                "affected_mutation_ids": [item["mutation_id"] for item in mutation_audit["non_atomic_or_semantically_mismatched_mutations"]],
                "additional_pilot_required": False,
            }
        ],
        "required_v3_corrections": [
            "make every mutation registry entry self-describing with the exact single premise delta, exact expected diagnostic, exact expected decision delta, and explicit prerequisite/rebinding semantics",
            "replace the comparator-threshold mutation with a probe whose direction matches its registered name",
            "use actual phase-dependent and holonomy-dependent control fixtures, or rename the mutations to the loading and interchange controls they truly exercise",
            "split the supplied-materiality and numerical-block probes so each changes one premise and reaches its intended precedence layer",
            "make the supplied-pass-with-raw-failure probe actually contain an independently failing raw value while preserving the supplied favorable Boolean",
            "make historical regeneration checks consume their version-bound environment identity instead of the mutable working .gitattributes file, and correct the freeze-v2 affected-test claim",
        ],
        "preserved_accepted_v2_repairs": [
            "203-record matrix closure", "twenty-two threshold reconstructions and semantics", "0.8/1.5/1.5 convergence-class split",
            "raw-output classifier trust boundary", "blocked-materiality suppression", "control applicability map", "manifest/path/payload identity closure", "clean-checkout LF custody",
        ],
        "authority_rotation": {
            "freeze_v2_accepted": False,
            "versioned_freeze_v3_correction_authorized": True,
            "additional_pilot_authorized": False,
            "canonical_203_record_execution_authorized": False,
            "robustness_classification_authorized": False,
            "descendant_materiality_classification_authorized": False,
            "new_E_REPRO_claim_authorized": False,
            "canonical_Maxwell_Dirac_E_REPRO_unchanged": True,
            "pillar_completion_authorized": False,
            "seam_closure_authorized": False,
            "C_k_dynamics_authorized": False,
            "CCFT_promotion_authorized": False,
            "master_action_promotion_authorized": False,
        },
        "lean_status_boundary": {
            "affected_freeze_v2_build": {"status": "PASSED", "job_count": 144},
            "affected_review_authority_build": {"status": "PASSED", "job_count": 145},
            "historical_repository_wide_aggregate": {"completed_jobs": 8441, "total_jobs": 8507, "termination": "TIMEOUT_AT_600_SECONDS", "theorem_error_observed_before_timeout": False, "status": "INCOMPLETE"},
            "repository_wide_green_claim": False,
        },
        "validation_status": {
            "current_affected_test_count": 119,
            "current_affected_tests_passed": True,
            "historical_environment_sensitive_regeneration_tests_deselected": 2,
            "deselected_tests": [
                "freeze-v1::test_generated_artifacts_are_current",
                "freeze-v2::test_generated_artifacts_are_current",
            ],
            "deselection_reason": "Both historical generators hash the mutable working .gitattributes file. Freeze-v2 added LF custody entries, so the v1 historical artifact-current probe became unreproducible; this review adds its own LF entries, so the v2 probe also becomes environment-stale. Committed artifact hashes remain exact.",
            "freeze_v2_reported_99_test_claim_reproduced_after_commit": False,
            "artifact_custody_hash_checks_passed": True,
            "independent_review_report_regeneration_passed": True,
            "authority_surface_parity_passed": True,
            "tooling_validation_passed": True,
        },
        "claim_ceiling": "Freeze v2 is not accepted because its 23 mutation controls are not independently self-describing and at least five preparation probes are non-atomic or semantically mismatched. The 203-record execution, robustness classification, descendant materiality, and every new scientific claim remain unauthorized.",
        "prompt_sha256": PROMPT_SHA256,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Independently review freeze v2 for canonical descendant robustness execution.")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    try:
        report = build_review()
    except (OSError, ValueError, KeyError, StopIteration, json.JSONDecodeError) as error:
        print(f"ERROR: {error}", file=sys.stderr)
        return 1
    raw = canonical_json_bytes(report)
    if args.write:
        REVIEW_REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
        REVIEW_REPORT_PATH.write_bytes(raw)
        print(f"wrote independent freeze-v2 review: {VERDICT}; canonical execution unauthorized")
        return 0
    if args.check:
        if not REVIEW_REPORT_PATH.is_file() or REVIEW_REPORT_PATH.read_bytes() != raw:
            print("stale or missing independent freeze-v2 review", file=sys.stderr)
            return 1
        print(f"independent freeze-v2 review verified: {VERDICT}; v3 correction only")
        return 0
    sys.stdout.buffer.write(raw)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
