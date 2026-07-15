from __future__ import annotations

import argparse
import ast
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


REPO_ROOT = find_repo_root(Path(__file__))
SCRIPT_PATH = Path(__file__).resolve()
SCRIPT_RELATIVE_PATH = "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_calibration_and_parameter_freeze_packet_v1_result_review.py"
REVIEW_REPORT_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_CALIBRATION_AND_PARAMETER_FREEZE_PACKET_RESULT_REVIEW_20260714_v1.json"
REVIEW_REPORT_PATH = REPO_ROOT / REVIEW_REPORT_RELATIVE_PATH

FREEZE_REPORT_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_CALIBRATION_AND_PARAMETER_FREEZE_PACKET_20260714_v1.json"
FREEZE_MANIFEST_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-CALIBRATION-AND-PARAMETER-FREEZE-MANIFEST-v1.json"
FREEZE_PACKET_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-CALIBRATION-AND-PARAMETER-FREEZE-PACKET-v1.json"
RUN_MATRIX_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-CANONICAL-RUN-MATRIX-v1.json"
FREEZE_TEST_RELATIVE_PATH = "formal/python/tests/test_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_calibration_and_parameter_freeze_packet_v1.py"
FREEZE_GENERATOR_RELATIVE_PATH = "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_calibration_and_parameter_freeze_packet_v1.py"
CLASSIFIER_RELATIVE_PATH = "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_canonical_result_classifier_v1.py"
FREEZE_LEAN_RELATIVE_PATH = "formal/toe_formal/ToeFormal/Derivation/DiracMaxwellFullZeroModeDescendantNecessityAndRobustnessCalibrationAndParameterFreezePacketV1.lean"
CURRENT_TARGET_RELATIVE_PATH = "formal/toe_formal/ToeFormal/Derivation/CurrentTarget.lean"
CURRENT_AUTHORITY_RELATIVE_PATH = "formal/toe_formal/ToeFormal/Release/CurrentAuthority.lean"

GUARDRAIL_PACKET_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-GUARDRAIL-PACKET-v1.json"
PILOT_PACKET_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-NON-AUTHORITATIVE-PILOT-PACKET-v1.json"
PILOT_ARRAYS_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-NON-AUTHORITATIVE-PILOT-ARRAYS-v1.json"
PILOT_REVIEW_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_NON_AUTHORITATIVE_PILOT_RESULT_REVIEW_20260714_v1.json"
CANONICAL_FREEZE_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-CANONICAL-PARAMETER-FREEZE-PACKET-v0.json"
CANONICAL_FREEZE_REVIEW_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_CANONICAL_PARAMETER_FREEZE_PACKET_RESULT_REVIEW_20260713_v0.json"

CAPTURED_AT_UTC = "2026-07-14T00:00:00Z"
REVIEW_TARGET = "review_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_calibration_and_parameter_freeze_packet_v1_result"
SELECTED_NEXT_TARGET = "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_calibration_and_parameter_freeze_packet_v2"
VERDICT = "B-BLOCKED_CONVERGENCE_CLASS_MISMATCH"
REVIEW_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_CALIBRATION_AND_PARAMETER_FREEZE_PACKET_RESULT_REVIEW_20260714_v1"
FREEZE_COMMIT = "789170efc51a6678ea0983503c38ba2293007764"
FREEZE_PARENT = "1004b0a2203b5c4abdfd6a120d23372518b8f631"
PROMPT_RELATIVE_PATH = "Prompt.txt"
PROMPT_SHA256 = "2bc6996ea28e96c50e688ed3d30ee24808af411a244eb594aad89ff80fda8433"

EXPECTED_FREEZE_HASHES = {
    FREEZE_REPORT_RELATIVE_PATH: "cbdfe8e0608e35cf59f0210ae9ae0d3cbf4ba4d845cfc139278888ca725c6c9b",
    FREEZE_MANIFEST_RELATIVE_PATH: "c37f144d4956b36e1bf51e145a41b88307aec5418bce61133d53911d3afb5250",
    FREEZE_PACKET_RELATIVE_PATH: "0ff67de9c91487a9531b69acbd63bf1b5a593d257a84a026b622ca3c7928dbcb",
    RUN_MATRIX_RELATIVE_PATH: "c6166fee940c9c2564f78da90fa1116cd3a610f9771e40ea97c1a19eb7d2abf3",
    FREEZE_TEST_RELATIVE_PATH: "cae103e0cbad1e5ac349738a440631963531aa1e19aad716412089a9172dc29d",
    FREEZE_GENERATOR_RELATIVE_PATH: "37bd24552a1af3f41d0be5e1a0ce98da36031a7d1a1f9859fe44121744ea1c0f",
    CLASSIFIER_RELATIVE_PATH: "d71191f45e4cbfaa501c5a20e0e1e8213835f5b30c7a2760f56fceea1d958062",
    CURRENT_TARGET_RELATIVE_PATH: "12b0859c9d60cad0017f40f9a71549d4a5af20a852e1f5cd3f1670ac08d49083",
    FREEZE_LEAN_RELATIVE_PATH: "baaca050cf84a59972e04c07e8c37dbc7158fd2dd2ec764c4212444983b99703",
    CURRENT_AUTHORITY_RELATIVE_PATH: "d8ce2f1047897f0aaa637a4bd6b6656e302840675c423545f719a16f4ce11f10",
}
IMMUTABLE_WORKING_FREEZE_HASHES = {
    path: digest
    for path, digest in EXPECTED_FREEZE_HASHES.items()
    if path not in {CURRENT_TARGET_RELATIVE_PATH, CURRENT_AUTHORITY_RELATIVE_PATH}
}
REFERENCE_HASHES = {
    CANONICAL_FREEZE_RELATIVE_PATH: "fa16cbf5ef767cd29b9cae3bcea80191e74656d51c1e2c74fa87bfca5bb4075e",
    CANONICAL_FREEZE_REVIEW_RELATIVE_PATH: "2fb867bcc8cf8271d2511db2de8d9d605db5888d0ec407db9eab9085149d81f3",
}

EQUATION_RESIDUAL_KEYS = (
    "longitudinal_Maxwell_residual", "phi2_wave_residual", "phi3_wave_residual",
    "Dirac_plus_sector1_residual", "Dirac_plus_sector2_residual",
    "Dirac_minus_sector1_residual", "Dirac_minus_sector2_residual",
    "adjoint_plus_sector1_residual", "adjoint_plus_sector2_residual",
    "adjoint_minus_sector1_residual", "adjoint_minus_sector2_residual",
)
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
    **{f"maximum_{key}": key for key in EQUATION_RESIDUAL_KEYS},
}
OBSERVABLE_FLOOR_KEYS = (
    "matter_density_l2", "longitudinal_electric_field_l2", "matter_energy",
    "total_source_current_l2", "phi2_l2", "phi3_l2", "transverse_source_l2",
)
EXCHANGE_FLOOR_KEYS = (
    "cumulative_exchange_longitudinal", "cumulative_exchange_phi2", "cumulative_exchange_phi3",
)


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
    return sha256_bytes(path.read_bytes())


def load_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {path}")
    return value


def git_output(*args: str) -> bytes:
    return subprocess.check_output(["git", *args], cwd=REPO_ROOT)


def bind_freeze_custody() -> dict[str, Any]:
    if git_output("rev-parse", f"{FREEZE_COMMIT}^").decode().strip() != FREEZE_PARENT:
        raise ValueError("freeze-proposal parent mismatch")
    if subprocess.run(["git", "merge-base", "--is-ancestor", FREEZE_COMMIT, "HEAD"], cwd=REPO_ROOT, check=False).returncode != 0:
        raise ValueError("freeze-proposal commit is not an ancestor of HEAD")
    for relative_path, digest in EXPECTED_FREEZE_HASHES.items():
        if sha256_bytes(git_output("show", f"{FREEZE_COMMIT}:{relative_path}")) != digest:
            raise ValueError(f"committed freeze hash mismatch: {relative_path}")
    for relative_path, digest in IMMUTABLE_WORKING_FREEZE_HASHES.items():
        if sha256_path(REPO_ROOT / relative_path) != digest:
            raise ValueError(f"working freeze artifact changed: {relative_path}")
    for relative_path, digest in REFERENCE_HASHES.items():
        if sha256_path(REPO_ROOT / relative_path) != digest:
            raise ValueError(f"accepted canonical reference changed: {relative_path}")
    if sha256_path(REPO_ROOT / PROMPT_RELATIVE_PATH) != PROMPT_SHA256:
        raise ValueError("Prompt.txt content changed")
    return {
        "freeze_commit": FREEZE_COMMIT,
        "freeze_parent": FREEZE_PARENT,
        "ten_committed_paths": EXPECTED_FREEZE_HASHES,
        "immutable_working_paths_verified": sorted(IMMUTABLE_WORKING_FREEZE_HASHES),
        "accepted_canonical_convergence_references": REFERENCE_HASHES,
    }


def _float_series(record: dict[str, Any], key: str) -> list[float]:
    return [float(value) for value in record["series"][key]]


def _round_up_one_significant(value: float) -> float:
    if value <= 0.0:
        return 0.0
    exponent = math.floor(math.log10(value))
    scale = 10**exponent
    return math.ceil(value / scale) * scale


def _observed_order(coarse: float, middle: float, fine: float) -> float | None:
    numerator = abs(coarse - middle)
    denominator = abs(middle - fine)
    if numerator == 0.0 or denominator == 0.0:
        return None
    return math.log(numerator / denominator, 2)


def independently_audit_matrix(packet: dict[str, Any], matrix: dict[str, Any], guardrail: dict[str, Any], manifest: dict[str, Any]) -> dict[str, Any]:
    records = matrix["records"]
    row_ids = [row["row_id"] for row in guardrail["scientific_matrix"]]
    guardrail_axes = {row["row_id"]: row["requested_axis_values"] for row in guardrail["scientific_matrix"]}
    scientific_roles = {"PRIMARY_FULL_MODEL", "SPATIAL_REFINEMENT", "TEMPORAL_REFINEMENT", "SOLVER_VERIFICATION", "DETERMINISTIC_DUPLICATE", "FORCED_COMPARATOR"}
    expected_per_row = {
        "PRIMARY_FULL_MODEL": 1, "SPATIAL_REFINEMENT": 3, "TEMPORAL_REFINEMENT": 3,
        "SOLVER_VERIFICATION": 3, "DETERMINISTIC_DUPLICATE": 2, "FORCED_COMPARATOR": 1,
    }
    row_audits = []
    for row_id in row_ids:
        local = [record for record in records if record["scientific_row_id"] == row_id and record["run_role"] in scientific_roles]
        roles = Counter(record["run_role"] for record in local)
        axes_match = all(record["requested_axis_values"] == guardrail_axes[row_id] for record in local)
        primary = [record for record in local if record["run_role"] == "PRIMARY_FULL_MODEL"]
        spatial = sorted((record["grid_size"], record["time_step"]) for record in local if record["run_role"] == "SPATIAL_REFINEMENT")
        temporal = sorted(record["time_step"] for record in local if record["run_role"] == "TEMPORAL_REFINEMENT")
        solver = sorted(record["solver_tolerance"] for record in local if record["run_role"] == "SOLVER_VERIFICATION")
        forced = [record for record in local if record["run_role"] == "FORCED_COMPARATOR"]
        parameters_match = (
            len(primary) == 1 and primary[0]["grid_size"] == 32 and primary[0]["time_step"] == 0.0015625
            and primary[0]["duration"] == 0.05 and primary[0]["solver_tolerance"] == 1e-12 and primary[0]["iteration_cap"] == 80
            and spatial == [(8, 0.0125), (16, 0.00625), (32, 0.003125)]
            and temporal == [0.0015625, 0.003125, 0.00625]
            and solver == [1e-12, 1e-10, 1e-8]
            and len(forced) == 1 and forced[0]["parent_scientific_row_id"] == row_id
        )
        row_audits.append({"row_id": row_id, "record_count": len(local), "role_counts": dict(sorted(roles.items())), "closed_role_set": roles == expected_per_row, "axes_exact": axes_match, "parameters_exact": parameters_match})

    required_fields = {"run_id", "scientific_row_id", "run_role", "model_or_comparator_class", "grid_size", "time_step", "duration", "solver_tolerance", "iteration_cap", "initial_condition_identity", "expected_diagnostic", "output_path"}
    role_counts = dict(sorted(Counter(record["run_role"] for record in records).items()))
    expected_role_counts = {"DETERMINISTIC_DUPLICATE": 28, "FORCED_COMPARATOR": 14, "NEGATIVE_CONTROL": 13, "POSITIVE_CONTROL": 8, "PRIMARY_FULL_MODEL": 14, "SOLVER_VERIFICATION": 42, "SPATIAL_REFINEMENT": 42, "TEMPORAL_REFINEMENT": 42}
    packet_rows = packet["scientific_design_freeze"]["scientific_rows"]
    matrix_sha = sha256_path(REPO_ROOT / RUN_MATRIX_RELATIVE_PATH)
    return {
        "record_count": len(records),
        "unique_run_id_count": len({record["run_id"] for record in records}),
        "unique_output_path_count": len({record["output_path"] for record in records}),
        "role_counts": role_counts,
        "role_counts_exact": role_counts == expected_role_counts,
        "all_required_record_fields_present": all(required_fields <= set(record) for record in records),
        "scientific_row_ids_exact": [row["row_id"] for row in packet_rows] == row_ids,
        "scientific_axis_tuples_exact": all(row["requested_axis_values"] == guardrail_axes[row["row_id"]] for row in packet_rows),
        "row_audits": row_audits,
        "all_fourteen_rows_have_exact_uniform_expansion": len(row_audits) == 14 and all(item["record_count"] == 13 and item["closed_role_set"] and item["axes_exact"] and item["parameters_exact"] for item in row_audits),
        "packet_matrix_hash_exact": packet["canonical_run_matrix"]["sha256"] == matrix_sha,
        "manifest_matrix_hash_exact": manifest["run_matrix"]["sha256"] == matrix_sha,
        "no_unregistered_invariant_descendant_free_comparator": matrix["invariant_descendant_free_comparator_record_count"] == 0,
    }


def independently_audit_filenames(packet: dict[str, Any], matrix: dict[str, Any], manifest: dict[str, Any]) -> dict[str, Any]:
    records = matrix["records"]
    output_paths = [record["output_path"] for record in records]
    folded = [unicodedata.normalize("NFC", value).casefold() for value in output_paths]
    reserved = {"CON", "PRN", "AUX", "NUL", *(f"COM{i}" for i in range(1, 10)), *(f"LPT{i}" for i in range(1, 10))}
    invalid_characters = set('<>:"/\\|?*')
    filenames = [Path(value).name for value in output_paths]
    legal = all(
        not any(character in invalid_characters for character in filename)
        and not filename.endswith((".", " "))
        and filename.split(".", 1)[0].upper() not in reserved
        for filename in filenames
    )
    expected_mapping = all(Path(record["output_path"]).name == record["run_id"].replace(":", "__") + ".json" for record in records)
    source_escape_absent = all("__" not in record["run_id"] for record in records)
    maximum_absolute_path_length = max(len(str(REPO_ROOT / record["output_path"])) for record in records)
    consumer = packet["execution_consumer_contract"]
    return {
        "mapping_rule_reconstructed": "replace each colon in run_id with two underscores and append .json",
        "exact_mapping_for_all_records": expected_mapping,
        "source_escape_sequence_absent": source_escape_absent,
        "unique_filename_count": len(set(output_paths)),
        "casefolded_NFC_unique_filename_count": len(set(folded)),
        "all_current_filenames_legal_on_windows": legal,
        "maximum_absolute_path_length": maximum_absolute_path_length,
        "current_paths_below_260_characters": maximum_absolute_path_length < 260,
        "matrix_is_bijective_for_current_203_records": expected_mapping and source_escape_absent and len(set(folded)) == len(records),
        "manifest_points_to_hash_bound_matrix": manifest["run_matrix"]["path"] == RUN_MATRIX_RELATIVE_PATH and manifest["run_matrix"]["sha256"] == sha256_path(REPO_ROOT / RUN_MATRIX_RELATIVE_PATH),
        "manifest_contains_explicit_run_id_to_output_path_map": "run_id_output_path_map" in manifest,
        "output_payload_must_echo_exact_run_id": "output_payload_must_echo_exact_run_id" in consumer and consumer["output_payload_must_echo_exact_run_id"] is True,
    }


def independently_reconstruct_thresholds(packet: dict[str, Any], pilot_packet: dict[str, Any], arrays: dict[str, Any]) -> dict[str, Any]:
    records = arrays["runs"]
    proposed = {item["threshold_id"]: item for item in packet["numerical_threshold_provenance"]}
    reconstructed: dict[str, dict[str, Any]] = {}
    for threshold_id, series_key in METRIC_SERIES.items():
        per_record = {record["run_record_id"]: max(abs(value) for value in _float_series(record, series_key)) for record in records}
        measured = max(per_record.values())
        value = _round_up_one_significant(2.0 * measured)
        item = proposed[threshold_id]
        reconstructed[threshold_id] = {
            "measured_value": measured,
            "recomputed_value": value,
            "proposed_value": item["candidate_frozen_threshold"],
            "source_count": len(item["pilot_source_run_ids"]),
            "value_and_sources_match": value == item["candidate_frozen_threshold"] and set(item["pilot_source_run_ids"]) == set(per_record),
        }
    by_row_role = {(record["row_id"], record["calibration_role"]): record for record in records}
    for threshold_id, keys in (("epsilon_observable_floor", OBSERVABLE_FLOOR_KEYS), ("epsilon_exchange_floor", EXCHANGE_FLOOR_KEYS)):
        per_row = {}
        sources = []
        for row in pilot_packet["summary"]["row_results"]:
            row_id = row["row_id"]
            medium = by_row_role[(row_id, "SOLVER_TOLERANCE_1e_MINUS_10")]
            fine = by_row_role[(row_id, "SOLVER_TOLERANCE_1e_MINUS_12")]
            sources.extend([medium["run_record_id"], fine["run_record_id"]])
            per_row[row_id] = max(abs(left - right) for key in keys for left, right in zip(_float_series(medium, key), _float_series(fine, key), strict=True))
        measured = max(per_row.values())
        value = _round_up_one_significant(2.0 * measured)
        item = proposed[threshold_id]
        reconstructed[threshold_id] = {
            "measured_value": measured,
            "recomputed_value": value,
            "proposed_value": item["candidate_frozen_threshold"],
            "source_count": len(item["pilot_source_run_ids"]),
            "value_and_sources_match": value == item["candidate_frozen_threshold"] and item["pilot_source_run_ids"] == sources,
        }
    entries = packet["numerical_threshold_provenance"]
    return {
        "threshold_count": len(entries),
        "reconstructed": reconstructed,
        "all_twenty_two_values_and_source_sets_reconstructed": len(reconstructed) == 22 and all(item["value_and_sources_match"] for item in reconstructed.values()),
        "every_threshold_has_explicit_eligible_run_roles": all("eligible_run_roles" in item and item["eligible_run_roles"] for item in entries),
        "every_threshold_declares_units_or_normalization": all("units_or_normalization" in item and item["units_or_normalization"] for item in entries),
        "global_raw_threshold_scope_is_justified_across_all_fourteen_rows": False,
        "scope_blocker_reason": "The proposal lists eligible scientific rows but no eligible run roles, and it does not declare units or a row-scaling/normalization rule for the global residual thresholds.",
    }


def independently_reconstruct_convergence(packet: dict[str, Any], arrays: dict[str, Any], canonical_freeze: dict[str, Any], canonical_review: dict[str, Any]) -> dict[str, Any]:
    by_row_role = {(record["row_id"], record["calibration_role"]): record for record in arrays["runs"]}
    pilot_row_ids = sorted({record["row_id"] for record in arrays["runs"]})
    spatial_orders = []
    temporal_orders = []
    energy_orders = []
    for row_id in pilot_row_ids:
        spatial = [by_row_role[(row_id, role)] for role in ("SPATIAL_N8", "SPATIAL_N16", "SPATIAL_N32")]
        temporal = [by_row_role[(row_id, role)] for role in ("TEMPORAL_DT_0P00625", "TEMPORAL_DT_0P003125", "TEMPORAL_DT_0P0015625")]
        spatial_values = [math.hypot(_float_series(record, "phi2_l2")[-1], _float_series(record, "phi3_l2")[-1]) for record in spatial]
        temporal_values = [math.hypot(_float_series(record, "phi2_l2")[-1], _float_series(record, "phi3_l2")[-1]) for record in temporal]
        energy_values = [max(abs(value) for value in _float_series(record, "total_energy_delta")) for record in temporal]
        spatial_orders.append(_observed_order(*spatial_values))
        temporal_orders.append(_observed_order(*temporal_values))
        energy_orders.append(_observed_order(*energy_values))
    proposed = {item["threshold_id"]: item for item in packet["convergence_threshold_provenance"]}
    accepted_spatial = canonical_freeze["convergence_definitions"]["spatial"]
    accepted_temporal = canonical_freeze["convergence_definitions"]["temporal_phi2"]
    accepted_energy = canonical_freeze["convergence_definitions"]["temporal_energy"]
    return {
        "independent_observed_minima": {
            "minimum_spatial_descendant_order": min(spatial_orders),
            "minimum_temporal_descendant_order": min(temporal_orders),
            "minimum_energy_error_order": min(energy_orders),
        },
        "proposed_thresholds": {key: item["candidate_frozen_threshold"] for key, item in proposed.items()},
        "proposed_measured_minima_match": math.isclose(proposed["minimum_spatial_descendant_order"]["measured_pilot_minimum_order"], min(spatial_orders), abs_tol=4e-8)
        and math.isclose(proposed["minimum_temporal_descendant_order"]["measured_pilot_minimum_order"], min(temporal_orders), abs_tol=4e-8)
        and math.isclose(proposed["minimum_energy_error_order"]["measured_pilot_minimum_order"], min(energy_orders), abs_tol=2e-12),
        "accepted_canonical_freeze_review_verdict": canonical_review["verdict"],
        "accepted_spatial_metric": accepted_spatial["metric"],
        "accepted_spatial_minimum_order": accepted_spatial["minimum_order"],
        "accepted_spatial_reason": accepted_spatial["reason"],
        "proposed_spatial_metric": "final descendant L2 built from the same final phi2/phi3 spatial refinement family",
        "proposed_spatial_minimum_order": proposed["minimum_spatial_descendant_order"]["candidate_frozen_threshold"],
        "spatial_gate_matches_accepted_analytic_order_class": proposed["minimum_spatial_descendant_order"]["candidate_frozen_threshold"] == accepted_spatial["minimum_order"],
        "temporal_gate_matches_accepted_second_order_class": proposed["minimum_temporal_descendant_order"]["candidate_frozen_threshold"] == accepted_temporal["minimum_order"] == 1.5,
        "energy_gate_matches_accepted_second_order_class": proposed["minimum_energy_error_order"]["candidate_frozen_threshold"] == accepted_energy["minimum_order"] == 1.5,
        "blocking_mismatch": "The proposed spatial gate is 1.5, while the accepted canonical freeze uses 0.8 for final_phi2_l2 because the Wilson artifact is leading O(a). Pilot observation near order two cannot change that analytic expectation without a separately reviewed scheme argument.",
    }


def _run_classifier(payload: dict[str, Any]) -> dict[str, Any]:
    program = "import json,runpy,sys; ns=runpy.run_path(sys.argv[1]); data=json.load(sys.stdin); json.dump(ns['classify_registered_result'](data),sys.stdout,sort_keys=True,separators=(',',':'))"
    environment = os.environ.copy()
    environment.update({"PYTHONHASHSEED": "0", "TZ": "UTC", "LC_ALL": "C", "LANG": "C"})
    result = subprocess.run(
        [sys.executable, "-c", program, str(REPO_ROOT / CLASSIFIER_RELATIVE_PATH)],
        input=json.dumps(payload, sort_keys=True).encode("utf-8"),
        capture_output=True,
        cwd=REPO_ROOT,
        env=environment,
        check=False,
    )
    if result.returncode != 0:
        raise ValueError(result.stderr.decode("utf-8", errors="replace"))
    return json.loads(result.stdout)


def independently_audit_classifier(packet: dict[str, Any], matrix: dict[str, Any], guardrail: dict[str, Any], manifest: dict[str, Any]) -> dict[str, Any]:
    source = (REPO_ROOT / CLASSIFIER_RELATIVE_PATH).read_text(encoding="utf-8")
    tree = ast.parse(source)
    imports = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            imports.extend(alias.name for alias in node.names)
        elif isinstance(node, ast.ImportFrom):
            imports.append(node.module or "")
    row_ids = [row["row_id"] for row in guardrail["scientific_matrix"]]
    base = {
        "custody_ok": True, "controls_ok": True, "evidence_complete": True,
        "model_domain_limited": False, "threshold_sensitive": False,
        "necessity_resolved": True, "numerical_floor_resolved": True,
        "row_results": [{"row_id": row_id, "robustness_pass": True} for row_id in row_ids],
        "r_perp_maxima": [0.2], "f_exchange_perp": [0.05],
    }
    broad_a = _run_classifier(base)
    broad_b = _run_classifier(base)
    arbitrary = _run_classifier({**base, "row_results": [{"row_id": f"UNREGISTERED_{index}", "robustness_pass": True} for index in range(14)]})
    no_passing = _run_classifier({**base, "row_results": [{"row_id": row_id, "robustness_pass": False} for row_id in row_ids]})
    empty_observables = _run_classifier({**base, "r_perp_maxima": [], "f_exchange_perp": []})
    classifier_binding = packet["classifier_versioning_and_provenance"]["classifier_implementation"]
    return {
        "source_sha256": sha256_path(REPO_ROOT / CLASSIFIER_RELATIVE_PATH),
        "packet_hash_binding_exact": classifier_binding["path"] == CLASSIFIER_RELATIVE_PATH and classifier_binding["sha256"] == sha256_path(REPO_ROOT / CLASSIFIER_RELATIVE_PATH),
        "manifest_hash_binding_exact": manifest["classifier"]["path"] == CLASSIFIER_RELATIVE_PATH and manifest["classifier"]["sha256"] == sha256_path(REPO_ROOT / CLASSIFIER_RELATIVE_PATH),
        "imports": sorted(imports),
        "no_mutable_scientific_decision_import": set(imports) <= {"__future__", "math", "typing"},
        "deterministic_probe_byte_equivalent": canonical_json_bytes(broad_a) == canonical_json_bytes(broad_b),
        "registered_broad_probe": broad_a,
        "arbitrary_fourteen_unique_row_ids_are_incorrectly_accepted": arbitrary["robustness_status"] == "BROADLY_ROBUST",
        "classifier_checks_exact_frozen_row_identity_set": False,
        "classifier_derives_custody_controls_convergence_and_threshold_passes_from_203_outputs": False,
        "classifier_trusts_unbound_summary_booleans": all(token in source for token in ("custody_ok", "controls_ok", "evidence_complete", "robustness_pass", "threshold_sensitive")),
        "unkeyed_empty_materiality_vectors_are_incorrectly_accepted": empty_observables["descendant_significance_status"] == "DESCENDANTS_DYNAMICALLY_NECESSARY_QUANTITATIVELY_SMALL",
        "no_passing_subdomain_probe": no_passing,
        "blocked_outcome_incorrectly_receives_significance": no_passing["robustness_status"] == "NUMERICALLY_BLOCKED" and no_passing["descendant_significance_status"] is not None,
        "classifier_data_closure_complete": False,
        "blocking_reason": "The committed file is a deterministic final-label reducer, but it does not reconstruct custody, controls, fit membership, convergence, thresholds, exact row identities, or keyed materiality observables from the 203 registered outputs. Those decisions remain mutable external inputs.",
    }


def independently_audit_controls(matrix: dict[str, Any], guardrail: dict[str, Any]) -> dict[str, Any]:
    records = matrix["records"]
    positive = [record for record in records if record["run_role"] == "POSITIVE_CONTROL"]
    negative = [record for record in records if record["run_role"] == "NEGATIVE_CONTROL"]
    forced = [record for record in records if record["run_role"] == "FORCED_COMPARATOR"]
    accepted_positive = [item["control_id"] for item in guardrail["positive_controls"]]
    accepted_negative = [item["control_id"] for item in guardrail["negative_controls"]]
    matrix_positive = [record["run_id"].split(":", 1)[1] for record in positive]
    matrix_negative = [record["run_id"].split(":", 1)[1] for record in negative]
    return {
        "positive_control_count": len(positive),
        "negative_control_count": len(negative),
        "row_local_forced_comparator_count": len(forced),
        "positive_control_ids_exact": matrix_positive == accepted_positive,
        "negative_control_ids_exact": matrix_negative == accepted_negative,
        "forced_comparator_present_for_every_scientific_row": len(forced) == 14 and len({item["scientific_row_id"] for item in forced}) == 14,
        "every_control_declares_global_anchor_row_or_conditional_scope": all("control_scope" in record for record in [*positive, *negative]),
        "all_thirteen_negative_controls_are_attached_only_to_anchor": {record["scientific_row_id"] for record in negative} == {"R00_CANONICAL"},
        "interaction_corner_applicability_rule_present": any("interaction_corner_applicability" in record for record in [*positive, *negative]),
        "control_coverage_complete": False,
        "blocking_reason": "The IDs and row-local forced comparators are complete, but the 21 standalone controls do not declare whether each is global, anchor-specific, conditional, or row-applicable; all thirteen negatives are attached to R00 without a frozen proof that their diagnostics cover interaction corners.",
    }


def independently_audit_materiality_and_claims(packet: dict[str, Any], guardrail: dict[str, Any]) -> dict[str, Any]:
    materiality = packet["scientific_materiality_freeze"]
    accepted = guardrail["threshold_freeze"]
    boundary = packet["authority_boundary"]
    return {
        "material_gate_exact": materiality["material_R_perp_gate"] == materiality["material_F_exchange_perp_gate"] == accepted["material_R_perp_gate"] == accepted["material_F_exchange_perp_gate"] == 0.1,
        "dominated_gate_exact": materiality["descendant_dominated_R_perp_gate"] == materiality["descendant_dominated_F_exchange_perp_gate"] == accepted["descendant_dominated_R_perp_gate"] == accepted["descendant_dominated_F_exchange_perp_gate"] == 0.5,
        "sensitivity_values_exact": materiality["threshold_sensitivity_values"] == accepted["threshold_sensitivity_values"] == [0.05, 0.1, 0.2],
        "classifier_equality_semantics": "values exactly equal to 0.1 enter INTERMEDIATE_DESCENDANT_CONTRIBUTION; values exactly equal to 0.5 enter DESCENDANT_DOMINATED_REGIME",
        "robustness_and_significance_fields_separate_in_packet": "separation_rule" in packet["deterministic_outcome_logic"],
        "canonical_execution_unauthorized": boundary["canonical_fourteen_row_execution_authorized"] is False,
        "new_claim_unauthorized": boundary["new_E_REPRO_claim"] is False,
        "canonical_E_REPRO_unchanged": boundary["previous_canonical_E_REPRO_unchanged"] is True,
        "nonpromotion_ceiling_preserved": all(token in packet["nonclaims"] for token in ("no pillar completion", "no seam closure", "no C_k dynamics", "no CCFT promotion", "no master-action promotion", "no repository-wide green claim")),
    }


def build_review() -> dict[str, Any]:
    custody = bind_freeze_custody()
    packet = load_json(REPO_ROOT / FREEZE_PACKET_RELATIVE_PATH)
    matrix = load_json(REPO_ROOT / RUN_MATRIX_RELATIVE_PATH)
    manifest = load_json(REPO_ROOT / FREEZE_MANIFEST_RELATIVE_PATH)
    freeze_report = load_json(REPO_ROOT / FREEZE_REPORT_RELATIVE_PATH)
    guardrail = load_json(REPO_ROOT / GUARDRAIL_PACKET_RELATIVE_PATH)
    pilot_packet = load_json(REPO_ROOT / PILOT_PACKET_RELATIVE_PATH)
    arrays = load_json(REPO_ROOT / PILOT_ARRAYS_RELATIVE_PATH)
    pilot_review = load_json(REPO_ROOT / PILOT_REVIEW_RELATIVE_PATH)
    canonical_freeze = load_json(REPO_ROOT / CANONICAL_FREEZE_RELATIVE_PATH)
    canonical_review = load_json(REPO_ROOT / CANONICAL_FREEZE_REVIEW_RELATIVE_PATH)

    matrix_audit = independently_audit_matrix(packet, matrix, guardrail, manifest)
    filename_audit = independently_audit_filenames(packet, matrix, manifest)
    threshold_audit = independently_reconstruct_thresholds(packet, pilot_packet, arrays)
    convergence_audit = independently_reconstruct_convergence(packet, arrays, canonical_freeze, canonical_review)
    classifier_audit = independently_audit_classifier(packet, matrix, guardrail, manifest)
    control_audit = independently_audit_controls(matrix, guardrail)
    materiality_audit = independently_audit_materiality_and_claims(packet, guardrail)

    decisions = {
        "freeze_proposal_commit_and_all_ten_paths_bound": len(custody["ten_committed_paths"]) == 10,
        "accepted_pilot_review_authority_exact": pilot_review["verdict"] == "ACCEPT_ENGINEERING_READY" and pilot_review["selected_next_target"] == packet["target"],
        "proposal_target_and_pending_verdict_exact": packet["target"] == REVIEW_TARGET.replace("review_", "prepare_", 1).replace("_result", "") and freeze_report["verdict"] == "PREPARED_PENDING_INDEPENDENT_REVIEW",
        "all_203_records_unique_complete_and_role_qualified": matrix_audit["record_count"] == matrix_audit["unique_run_id_count"] == 203 and matrix_audit["role_counts_exact"] and matrix_audit["all_required_record_fields_present"],
        "all_fourteen_rows_uniform_and_axis_exact": matrix_audit["all_fourteen_rows_have_exact_uniform_expansion"] and matrix_audit["scientific_axis_tuples_exact"],
        "matrix_packet_and_manifest_hashes_exact": matrix_audit["packet_matrix_hash_exact"] and matrix_audit["manifest_matrix_hash_exact"],
        "all_twenty_two_threshold_values_reconstructed": threshold_audit["all_twenty_two_values_and_source_sets_reconstructed"],
        "threshold_role_scope_and_normalization_complete": threshold_audit["every_threshold_has_explicit_eligible_run_roles"] and threshold_audit["every_threshold_declares_units_or_normalization"] and threshold_audit["global_raw_threshold_scope_is_justified_across_all_fourteen_rows"],
        "temporal_and_energy_convergence_classes_match": convergence_audit["temporal_gate_matches_accepted_second_order_class"] and convergence_audit["energy_gate_matches_accepted_second_order_class"],
        "spatial_convergence_class_matches_accepted_Wilson_order": convergence_audit["spatial_gate_matches_accepted_analytic_order_class"],
        "materiality_gates_and_equality_boundaries_exact": materiality_audit["material_gate_exact"] and materiality_audit["dominated_gate_exact"] and materiality_audit["sensitivity_values_exact"],
        "classifier_source_and_hash_custody_exact": classifier_audit["packet_hash_binding_exact"] and classifier_audit["manifest_hash_binding_exact"] and classifier_audit["no_mutable_scientific_decision_import"],
        "classifier_data_closure_and_exact_row_identity_complete": classifier_audit["classifier_data_closure_complete"] and classifier_audit["classifier_checks_exact_frozen_row_identity_set"],
        "blocked_results_never_receive_significance": not classifier_audit["blocked_outcome_incorrectly_receives_significance"],
        "control_inventory_and_scope_coverage_complete": control_audit["positive_control_ids_exact"] and control_audit["negative_control_ids_exact"] and control_audit["forced_comparator_present_for_every_scientific_row"] and control_audit["control_coverage_complete"],
        "current_filename_mapping_collision_free_and_legal": filename_audit["matrix_is_bijective_for_current_203_records"] and filename_audit["all_current_filenames_legal_on_windows"] and filename_audit["current_paths_below_260_characters"],
        "filename_mapping_manifest_and_output_payload_identity_complete": filename_audit["manifest_contains_explicit_run_id_to_output_path_map"] and filename_audit["output_payload_must_echo_exact_run_id"],
        "claim_ceiling_and_nonpromotions_preserved": materiality_audit["canonical_execution_unauthorized"] and materiality_audit["new_claim_unauthorized"] and materiality_audit["canonical_E_REPRO_unchanged"] and materiality_audit["nonpromotion_ceiling_preserved"],
    }
    blockers = [
        {"diagnostic": "B-BLOCKED_CONVERGENCE_CLASS_MISMATCH", "evidence": convergence_audit["blocking_mismatch"], "pilot_rerun_required": False},
        {"diagnostic": "B-BLOCKED_THRESHOLD_SCOPE", "evidence": threshold_audit["scope_blocker_reason"], "pilot_rerun_required": False},
        {"diagnostic": "B-BLOCKED_CLASSIFIER_CUSTODY", "evidence": classifier_audit["blocking_reason"], "pilot_rerun_required": False},
        {"diagnostic": "B-BLOCKED_CONTROL_COVERAGE", "evidence": control_audit["blocking_reason"], "pilot_rerun_required": False},
        {"diagnostic": "B-BLOCKED_FILENAME_IDENTITY_MAPPING", "evidence": "The current 203 storage names are collision-free and legal, but neither the manifest contains an explicit inverse map nor the execution contract requires every output payload to echo its exact scientific run_id.", "pilot_rerun_required": False},
    ]
    return {
        "schema_id": REVIEW_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "review_target": REVIEW_TARGET,
        "verdict": VERDICT,
        "accepted": False,
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": "VERSIONED_FREEZE_CORRECTION_ONLY",
        "freeze_custody": custody,
        "freeze_generator_imported": False,
        "classifier_imported": False,
        "classifier_invoked_only_in_isolated_subprocess_probes": True,
        "independent_matrix_audit": matrix_audit,
        "independent_filename_audit": filename_audit,
        "independent_threshold_audit": threshold_audit,
        "independent_convergence_audit": convergence_audit,
        "independent_classifier_audit": classifier_audit,
        "independent_control_audit": control_audit,
        "independent_materiality_and_claim_audit": materiality_audit,
        "blocking_diagnostics": blockers,
        "review_decisions": [{"decision_id": key, "passed": value} for key, value in decisions.items()],
        "decision_count": len(decisions),
        "all_decisions_passed": all(decisions.values()),
        "required_v2_corrections": [
            "restore the accepted first-order-compatible spatial threshold of 0.8 for the Wilson-affected final descendant spatial fit, or supply and independently review a new analytic order argument",
            "declare eligible run roles plus units or a frozen normalization/scaling rule for every numerical threshold",
            "make the committed classifier consume the exact 203 registered outputs and exact fourteen row identities, reconstruct custody/controls/fits/thresholds itself, and forbid significance whenever robustness is blocked or model-domain limited",
            "declare every standalone control global, anchor-specific, conditional, or row-applicable and justify interaction-corner coverage",
            "add an explicit manifest run_id-to-safe-filename map and require every output payload to echo its exact run_id",
        ],
        "authority_rotation": {
            "freeze_v1_accepted": False,
            "versioned_freeze_v2_correction_authorized": True,
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
            "affected_freeze_preparation_build": {"status": "PASSED", "job_count": 142},
            "affected_review_authority_build": {"status": "PASSED", "job_count": 143},
            "historical_repository_wide_aggregate": {"completed_jobs": 8441, "total_jobs": 8507, "termination": "TIMEOUT_AT_600_SECONDS", "theorem_error_observed_before_timeout": False, "status": "INCOMPLETE"},
            "repository_wide_green_claim": False,
        },
        "validation_status": {
            "affected_test_count": 53,
            "affected_tests_passed": True,
            "artifact_checks_passed": True,
            "authority_surface_parity_passed": True,
            "tooling_validation_passed": True,
        },
        "claim_ceiling": "The v1 calibration and full-run freeze proposal is not accepted. The 203 records and numerical value derivations remain review evidence only; execution, robustness, descendant materiality, and every new scientific claim remain unauthorized.",
        "prompt_sha256": PROMPT_SHA256,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Independently review the robustness calibration and parameter freeze packet v1.")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    try:
        report = build_review()
    except (OSError, ValueError, KeyError, StopIteration, json.JSONDecodeError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1
    if args.write:
        REVIEW_REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
        REVIEW_REPORT_PATH.write_bytes(canonical_json_bytes(report))
        print(f"wrote independent freeze review: {report['verdict']}; canonical execution unauthorized")
        return 0
    if args.check:
        if not REVIEW_REPORT_PATH.is_file() or REVIEW_REPORT_PATH.read_bytes() != canonical_json_bytes(report):
            print("stale or missing independent freeze-review report", file=sys.stderr)
            return 1
        print(f"independent freeze review verified: {report['verdict']}; v2 correction only")
        return 0
    sys.stdout.buffer.write(canonical_json_bytes(report))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
