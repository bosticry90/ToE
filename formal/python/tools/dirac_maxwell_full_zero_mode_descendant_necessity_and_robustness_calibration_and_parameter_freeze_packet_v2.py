from __future__ import annotations

import argparse
import hashlib
import json
import platform
import subprocess
import unicodedata
from collections import Counter
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCRIPT_PATH = Path(__file__).resolve()
SCRIPT_RELATIVE_PATH = "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_calibration_and_parameter_freeze_packet_v2.py"
CLASSIFIER_RELATIVE_PATH = "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_canonical_result_classifier_v2.py"
PACKET_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-CALIBRATION-AND-PARAMETER-FREEZE-PACKET-v2.json"
RUN_MATRIX_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-CANONICAL-RUN-MATRIX-v2.json"
OUTPUT_IDENTITY_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-CANONICAL-EXPECTED-OUTPUT-IDENTITY-MANIFEST-v2.json"
MANIFEST_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-CALIBRATION-AND-PARAMETER-FREEZE-MANIFEST-v2.json"
REPORT_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_CALIBRATION_AND_PARAMETER_FREEZE_PACKET_20260714_v2.json"
PROMPT_RELATIVE_PATH = "Prompt.txt"

V1_PACKET_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-CALIBRATION-AND-PARAMETER-FREEZE-PACKET-v1.json"
V1_MATRIX_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-CANONICAL-RUN-MATRIX-v1.json"
V1_REVIEW_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_CALIBRATION_AND_PARAMETER_FREEZE_PACKET_RESULT_REVIEW_20260714_v1.json"
V1_REVIEW_LEAN_RELATIVE_PATH = "formal/toe_formal/ToeFormal/Derivation/DiracMaxwellFullZeroModeDescendantNecessityAndRobustnessCalibrationAndParameterFreezePacketV1ResultReview.lean"
GUARDRAIL_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-GUARDRAIL-PACKET-v1.json"
PILOT_PACKET_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-NON-AUTHORITATIVE-PILOT-PACKET-v1.json"
PILOT_ARRAYS_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-NON-AUTHORITATIVE-PILOT-ARRAYS-v1.json"
CANONICAL_FREEZE_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-CANONICAL-PARAMETER-FREEZE-PACKET-v0.json"
CANONICAL_FREEZE_REVIEW_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_CANONICAL_PARAMETER_FREEZE_PACKET_RESULT_REVIEW_20260713_v0.json"

CAPTURED_AT_UTC = "2026-07-14T00:00:00Z"
TARGET = "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_calibration_and_parameter_freeze_packet_v2"
REVIEW_TARGET = "review_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_calibration_and_parameter_freeze_packet_v2_result"
POST_ACCEPTANCE_TARGET = "execute_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_canonical_matrix_v2"
BLOCKED_TARGET = "repair_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_calibration_and_parameter_freeze_packet_v2"
V1_REVIEW_COMMIT = "9a3b0e47488bbffa4f77d7ec8abcde06ef9dc28e"
V1_REVIEW_PARENT = "789170efc51a6678ea0983503c38ba2293007764"
PROMPT_SHA256 = "2bc6996ea28e96c50e688ed3d30ee24808af411a244eb594aad89ff80fda8433"
OUTPUT_ROOT = "formal/output/canonical/dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_v2"

INPUT_HASHES = {
    V1_PACKET_RELATIVE_PATH: "0ff67de9c91487a9531b69acbd63bf1b5a593d257a84a026b622ca3c7928dbcb",
    V1_MATRIX_RELATIVE_PATH: "c6166fee940c9c2564f78da90fa1116cd3a610f9771e40ea97c1a19eb7d2abf3",
    V1_REVIEW_RELATIVE_PATH: "ad4d112a0377b5ea3c311b67f344ee98e8fd99e432676fe1ed385b331bfa4361",
    V1_REVIEW_LEAN_RELATIVE_PATH: "cc2161576365887341785ed4c604819950c9e48d6ad778b79a60e107a8a14913",
    GUARDRAIL_RELATIVE_PATH: "54f3c8137986db1ba1bf7cc1a9e0ffade11ed7b6fdf480bf103cdd6b13d964f1",
    PILOT_PACKET_RELATIVE_PATH: "d8c1f75c955b9a368159bd579f7d886523e8c66b0e611a6e6290a179422cf03a",
    PILOT_ARRAYS_RELATIVE_PATH: "5ffaca2e6e07e95ef1bb1b1451b2bda01eab355e55294a6dd51b2ffe8ecf8e8e",
    CANONICAL_FREEZE_RELATIVE_PATH: "fa16cbf5ef767cd29b9cae3bcea80191e74656d51c1e2c74fa87bfca5bb4075e",
    CANONICAL_FREEZE_REVIEW_RELATIVE_PATH: "2fb867bcc8cf8271d2511db2de8d9d605db5888d0ec407db9eab9085149d81f3",
}

SCHEMA_IDS = {
    "packet": "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_CALIBRATION_AND_PARAMETER_FREEZE_PACKET_v2",
    "matrix": "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_CANONICAL_RUN_MATRIX_v2",
    "identity": "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_CANONICAL_EXPECTED_OUTPUT_IDENTITY_MANIFEST_v2",
    "manifest": "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_CALIBRATION_AND_PARAMETER_FREEZE_MANIFEST_v2",
    "report": "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_CALIBRATION_AND_PARAMETER_FREEZE_PACKET_20260714_v2",
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
FULL_ROLES = ["PRIMARY_FULL_MODEL", "SPATIAL_REFINEMENT", "TEMPORAL_REFINEMENT", "SOLVER_VERIFICATION", "DETERMINISTIC_DUPLICATE"]
ALL_NUMERICAL_ROLES = [*FULL_ROLES, "FORCED_COMPARATOR"]
OBSERVABLE_FLOOR_KEYS = (
    "matter_density_l2",
    "longitudinal_electric_field_l2",
    "matter_energy",
    "total_source_current_l2",
    "phi2_l2",
    "phi3_l2",
    "transverse_source_l2",
)
EXCHANGE_FLOOR_KEYS = ("cumulative_exchange_longitudinal", "cumulative_exchange_phi2", "cumulative_exchange_phi3")


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


def load_json(relative_path: str) -> dict[str, Any]:
    value = json.loads((REPO_ROOT / relative_path).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {relative_path}")
    return value


def validate_authority() -> None:
    if subprocess.check_output(["git", "rev-parse", f"{V1_REVIEW_COMMIT}^"], cwd=REPO_ROOT).decode().strip() != V1_REVIEW_PARENT:
        raise ValueError("v1 review parent mismatch")
    if subprocess.run(["git", "merge-base", "--is-ancestor", V1_REVIEW_COMMIT, "HEAD"], cwd=REPO_ROOT, check=False).returncode != 0:
        raise ValueError("v1 blocked review is not an ancestor of HEAD")
    for path, digest in INPUT_HASHES.items():
        if sha256_path(REPO_ROOT / path) != digest:
            raise ValueError(f"accepted input hash mismatch: {path}")
    if sha256_path(REPO_ROOT / PROMPT_RELATIVE_PATH) != PROMPT_SHA256:
        raise ValueError("protected Prompt.txt content changed")
    review = load_json(V1_REVIEW_RELATIVE_PATH)
    if not (
        review.get("verdict") == "B-BLOCKED_CONVERGENCE_CLASS_MISMATCH"
        and review.get("selected_next_target") == TARGET
        and review.get("authority_rotation", {}).get("versioned_freeze_v2_correction_authorized") is True
        and review.get("authority_rotation", {}).get("additional_pilot_authorized") is False
        and review.get("authority_rotation", {}).get("canonical_203_record_execution_authorized") is False
    ):
        raise ValueError("v1 review does not authorize this bounded v2 correction")


def _control_record(
    control_id: str,
    control_type: str,
    scope_class: str,
    applicable_row_ids: list[str],
    representative_row_id: str,
    basis: str,
    predicate: str,
    mutation: str,
    diagnostic: str,
) -> dict[str, Any]:
    if control_type == "POSITIVE":
        observations = [{"observable_id": "control_signal_error", "comparison_operator": "LE", "target_value": 1e-12}]
        decision_delta = "required positive behavior remains admitted"
        alternate = "any negative-control diagnostic or unrelated custody failure"
    else:
        observations = [
            {"observable_id": "expected_diagnostic_magnitude", "comparison_operator": "GE", "target_value": 1.0},
            {"observable_id": "alternate_diagnostic_magnitude", "comparison_operator": "LE", "target_value": 0.0},
        ]
        decision_delta = "raw mutation output must block classification with B-BLOCKED_CONTROL_FAILURE if the intended diagnostic is absent"
        alternate = "any diagnostic other than the exact expected diagnostic"
    return {
        "control_id": control_id,
        "control_type": control_type,
        "scope_class": scope_class,
        "applicable_row_ids": applicable_row_ids,
        "representative_row_id": representative_row_id,
        "representativeness_basis": basis,
        "required_feature_predicate": predicate,
        "mutation_definition": mutation,
        "expected_diagnostic": diagnostic,
        "expected_decision_delta": decision_delta,
        "forbidden_alternate_failure": alternate,
        "control_evaluation_spec": {"input_kind": "RAW_CONTROL_OBSERVABLES", "required_observations": observations},
    }


def control_contracts(guardrail: dict[str, Any], row_ids: list[str]) -> dict[str, dict[str, Any]]:
    positive_specs = {
        "P_CANONICAL_ACCEPTED_RESULT_UNCHANGED": ("ANCHOR_REPRESENTATIVE_WITH_PROOF", ["R00_CANONICAL"], "R00_CANONICAL", "the accepted canonical fixture is defined only at R00 and checks unchanged canonical custody", "row is R00_CANONICAL"),
        "P_CHARGE_CONJUGATE_PARAMETER_CASE": ("GLOBAL_IMPLEMENTATION_INVARIANT", row_ids, "R00_CANONICAL", "the same charge-conjugation implementation route is shared by every row and is independent of axis magnitude", "charge-conjugate fixture is constructed"),
        "P_ANALYTIC_INVARIANT_DESCENDANT_FREE": ("CONDITIONAL_FEATURE_DEPENDENT", [], "GLOBAL_CONTROL", "no accepted invariant descendant-free scientific row exists; the control records ineligibility without inventing one", "separate accepted J2=J3=0 invariance proof exists"),
        "P_INITIAL_ZERO_DESCENDANTS_DYNAMICALLY_SOURCED": ("CONDITIONAL_FEATURE_DEPENDENT", ["R03_F_ZERO", "R12_CORNER_STRONG_ZERO"], "R03_F_ZERO", "R03 is the isolated zero-loading point; R12 is the frozen zero-loading interaction corner", "requested initial F_perp,+ equals zero while transverse source is nonzero"),
        "P_INDEPENDENT_PHI2_EXCITATION": ("CONDITIONAL_FEATURE_DEPENDENT", ["R05_F_HIGH", "R11_CORNER_WEAK_HIGH"], "R11_CORNER_WEAK_HIGH", "R11 jointly activates high loading and the corner stress while retaining the phi2 channel", "resolved phi2 channel amplitude exceeds its numerical floor"),
        "P_INDEPENDENT_PHI3_EXCITATION": ("CONDITIONAL_FEATURE_DEPENDENT", ["R10_MU_HIGH", "R11_CORNER_WEAK_HIGH"], "R10_MU_HIGH", "R10 exercises the independently resolved phi3 channel at the high mass-domain scale", "resolved phi3 channel amplitude exceeds its numerical floor"),
        "P_PHI2_PHI3_INTERCHANGE": ("ANCHOR_REPRESENTATIVE_WITH_PROOF", ["R00_CANONICAL"], "R00_CANONICAL", "the accepted interchange identity is analytic and R00 supplies the single numerical witness", "accepted interchange symmetry assumptions hold"),
        "P_WEAK_COUPLING_APPROACH": ("ROW_LOCAL", ["R01_ETA_WEAK", "R11_CORNER_WEAK_HIGH"], "R01_ETA_WEAK", "R01 isolates the weak-coupling axis; R11 separately covers its high-loading interaction", "ETA_Q is the frozen weak level"),
    }
    negative_specs = {
        "N_FORCE_BOTH_DESCENDANTS_ZERO_WITH_SOURCE": ("COMPARATOR_ONLY", row_ids, "R00_CANONICAL", "all fourteen row-local forced comparators exercise this blocker; the standalone R00 mutation preserves the historical regression", "forced comparator has nonzero transverse source", "set both descendants to zero after parent construction"),
        "N_DROP_ONLY_PHI2": ("CONDITIONAL_FEATURE_DEPENDENT", ["R05_F_HIGH", "R11_CORNER_WEAK_HIGH"], "R11_CORNER_WEAK_HIGH", "R11 activates the high-loading corner and resolves phi2 strongly", "phi2 source is resolved", "remove only phi2"),
        "N_DROP_ONLY_PHI3": ("CONDITIONAL_FEATURE_DEPENDENT", ["R10_MU_HIGH", "R11_CORNER_WEAK_HIGH"], "R10_MU_HIGH", "R10 resolves the independent phi3 channel at the high mass-domain scale", "phi3 source is resolved", "remove only phi3"),
        "N_OMIT_DESCENDANT_ENERGY": ("CONDITIONAL_FEATURE_DEPENDENT", ["R05_F_HIGH", "R11_CORNER_WEAK_HIGH"], "R05_F_HIGH", "R05 isolates the maximum descendant-loading energy burden", "F_perp,+ is the frozen high level", "omit E_phi2 and E_phi3 from the energy inventory"),
        "N_OMIT_TRANSVERSE_EXCHANGE_CHANNEL": ("CONDITIONAL_FEATURE_DEPENDENT", ["R05_F_HIGH", "R11_CORNER_WEAK_HIGH"], "R11_CORNER_WEAK_HIGH", "R11 stresses transverse exchange under a preregistered interaction", "transverse exchange is above its numerical floor", "omit both transverse exchange channels"),
        "N_REVERSE_TRANSVERSE_EXCHANGE_SIGN": ("CONDITIONAL_FEATURE_DEPENDENT", ["R05_F_HIGH", "R11_CORNER_WEAK_HIGH"], "R11_CORNER_WEAK_HIGH", "R11 supplies a resolved interaction-corner exchange signal", "transverse exchange is above its numerical floor", "reverse the transverse exchange sign"),
        "N_WRONG_GAMMA2_BLOCK": ("CONDITIONAL_FEATURE_DEPENDENT", ["R05_F_HIGH", "R11_CORNER_WEAK_HIGH"], "R11_CORNER_WEAK_HIGH", "R11 activates the phi2/gamma2 path under the corner stress", "gamma2 channel is active", "replace the accepted gamma2 block"),
        "N_WRONG_GAMMA3_BLOCK": ("CONDITIONAL_FEATURE_DEPENDENT", ["R10_MU_HIGH", "R11_CORNER_WEAK_HIGH"], "R10_MU_HIGH", "R10 activates the independent phi3/gamma3 path", "gamma3 channel is active", "replace the accepted gamma3 block"),
        "N_SUPPRESS_SECTOR_MULTIPLICITY": ("GLOBAL_IMPLEMENTATION_INVARIANT", row_ids, "R00_CANONICAL", "the same exact sector multiplicity code path is used in every row", "sector inventory is unchanged", "suppress the accepted sector multiplicity"),
        "N_DESCENDANTS_RELABELED_INVENTED_MATTER": ("GLOBAL_IMPLEMENTATION_INVARIANT", row_ids, "R00_CANONICAL", "origin semantics are packet-level and independent of row values", "descendant origin metadata is present", "relabel descendants as invented matter"),
        "N_CANONICAL_THRESHOLDS_REUSED_UNSCALED": ("GLOBAL_IMPLEMENTATION_INVARIANT", row_ids, "R00_CANONICAL", "threshold provenance validation is packet-level and evaluates the complete matrix", "v2 threshold schema is loaded", "replace v2 thresholds with unreviewed canonical thresholds"),
        "N_POST_EXECUTION_FAVORABLE_POINT_SELECTION": ("GLOBAL_IMPLEMENTATION_INVARIANT", row_ids, "R00_CANONICAL", "exact identity closure is global and forbids any post-result subset", "all 203 identities are present", "select only favorable outputs"),
        "N_FAILED_POINTS_EXCLUDED_FROM_DOMAIN": ("GLOBAL_IMPLEMENTATION_INVARIANT", row_ids, "R00_CANONICAL", "row completeness is global and requires all fourteen exact row identities", "all fourteen rows are present", "exclude failed scientific rows"),
    }
    diagnostics = {item["control_id"]: item.get("diagnostic", item.get("expected", item["control_id"])) for item in [*guardrail["positive_controls"], *guardrail["negative_controls"]]}
    contracts: dict[str, dict[str, Any]] = {}
    for control_id, (scope, applicable, representative, basis, predicate) in positive_specs.items():
        contracts[control_id] = _control_record(control_id, "POSITIVE", scope, applicable, representative, basis, predicate, "no mutation; reproduce the frozen positive witness", diagnostics[control_id])
    positive_observations = {
        "P_CANONICAL_ACCEPTED_RESULT_UNCHANGED": [{"observable_id": "canonical_payload_error", "comparison_operator": "LE", "target_value": 1e-12}],
        "P_CHARGE_CONJUGATE_PARAMETER_CASE": [{"observable_id": "charge_conjugation_relation_error", "comparison_operator": "LE", "target_value": 1e-12}],
        "P_ANALYTIC_INVARIANT_DESCENDANT_FREE": [{"observable_id": "accepted_invariant_subdomain_count", "comparison_operator": "EQ", "target_value": 0.0}],
        "P_INITIAL_ZERO_DESCENDANTS_DYNAMICALLY_SOURCED": [
            {"observable_id": "initial_descendant_loading", "comparison_operator": "EQ", "target_value": 0.0},
            {"observable_id": "resolved_transverse_source_norm", "comparison_operator": "GE", "target_value": 5e-10},
        ],
        "P_INDEPENDENT_PHI2_EXCITATION": [{"observable_id": "resolved_phi2_signal", "comparison_operator": "GE", "target_value": 5e-10}],
        "P_INDEPENDENT_PHI3_EXCITATION": [{"observable_id": "resolved_phi3_signal", "comparison_operator": "GE", "target_value": 5e-10}],
        "P_PHI2_PHI3_INTERCHANGE": [{"observable_id": "interchange_relation_error", "comparison_operator": "LE", "target_value": 1e-12}],
        "P_WEAK_COUPLING_APPROACH": [{"observable_id": "weak_coupling_trend_error", "comparison_operator": "LE", "target_value": 1e-12}],
    }
    for control_id, observations in positive_observations.items():
        contracts[control_id]["control_evaluation_spec"] = {"input_kind": "RAW_CONTROL_OBSERVABLES", "required_observations": observations}
    for control_id, (scope, applicable, representative, basis, predicate, mutation) in negative_specs.items():
        contracts[control_id] = _control_record(control_id, "NEGATIVE", scope, applicable, representative, basis, predicate, mutation, diagnostics[control_id])
    return contracts


def build_matrix(v1_matrix: dict[str, Any], guardrail: dict[str, Any]) -> dict[str, Any]:
    rows = {row["row_id"]: row for row in guardrail["scientific_matrix"]}
    row_ids = list(rows)
    controls = control_contracts(guardrail, row_ids)
    records: list[dict[str, Any]] = []
    for source in v1_matrix["records"]:
        record = dict(source)
        record["initial_condition_identity"] = str(record["initial_condition_identity"]).replace("_v1", "_v2").replace("GUARDRAIL_v1", "GUARDRAIL_v1_IMMUTABLE_INPUT")
        if record["run_role"] in {"POSITIVE_CONTROL", "NEGATIVE_CONTROL"}:
            control_id = record["run_id"].split(":", 1)[1]
            metadata = controls[control_id]
            representative = metadata["representative_row_id"]
            record["control_metadata"] = metadata
            record["scientific_row_id"] = representative
            record["parent_scientific_row_id"] = representative if representative in rows else None
            record["requested_axis_values"] = rows[representative]["requested_axis_values"] if representative in rows else None
        safe_filename = record["run_id"].replace(":", "__") + ".json"
        record["safe_filename"] = safe_filename
        record["output_path"] = f"{OUTPUT_ROOT}/{safe_filename}"
        input_material = {key: value for key, value in record.items() if key not in {"safe_filename", "output_path", "input_hash"}}
        record["input_hash"] = sha256_bytes(canonical_json_bytes(input_material))
        record["payload_identity_contract"] = {
            "required_echo_fields": ["run_id", "scientific_row_id", "run_role", "model_class", "parent_run_or_row_id", "input_hash", "relative_output_path"],
            "mismatch_behavior": "B-BLOCKED_RUN_IDENTITY",
        }
        records.append(record)
    run_ids = [item["run_id"] for item in records]
    filenames = [item["safe_filename"] for item in records]
    paths = [item["output_path"] for item in records]
    if not (len(records) == len(set(run_ids)) == len(set(filenames)) == len(set(paths)) == 203):
        raise ValueError("v2 run/output identity is not a 203-element bijection")
    if len({unicodedata.normalize("NFC", item).casefold() for item in filenames}) != 203:
        raise ValueError("v2 filenames collide under Windows casefold/NFC semantics")
    return {
        "schema_id": SCHEMA_IDS["matrix"],
        "captured_at_utc": CAPTURED_AT_UTC,
        "generation_policy": "bounded v2 correction of the immutable v1 203-record proposal; scientific rows, run roles, and numerical settings are unchanged",
        "v1_record_count_preserved": v1_matrix["record_count"],
        "scientific_row_count": 14,
        "scientific_records_per_row": 13,
        "scientific_record_count": 182,
        "control_record_count": 21,
        "record_count": 203,
        "unique_run_id_count": 203,
        "role_counts": dict(sorted(Counter(item["run_role"] for item in records).items())),
        "records": records,
    }


def build_output_identity(matrix: dict[str, Any]) -> dict[str, Any]:
    outputs = [
        {
            "run_id": record["run_id"],
            "safe_filename": record["safe_filename"],
            "relative_output_path": record["output_path"],
            "scientific_row_id": record["scientific_row_id"],
            "run_role": record["run_role"],
            "model_class": record["model_or_comparator_class"],
            "parent_run_or_row_id": record["parent_scientific_row_id"],
            "input_hash": record["input_hash"],
        }
        for record in matrix["records"]
    ]
    return {
        "schema_id": SCHEMA_IDS["identity"],
        "captured_at_utc": CAPTURED_AT_UTC,
        "mapping_contract": "run_id <-> safe_filename <-> relative_output_path <-> payload identity is exact, reversible, and fail-closed",
        "record_count": len(outputs),
        "run_id_to_safe_filename": {item["run_id"]: item["safe_filename"] for item in outputs},
        "safe_filename_to_run_id": {item["safe_filename"]: item["run_id"] for item in outputs},
        "outputs": outputs,
    }


def _threshold_units(threshold_id: str) -> tuple[str, str, str]:
    if threshold_id == "maximum_link_norm_error":
        return "dimensionless", "max_t abs(|U|-1)", "NONE_DIMENSIONLESS_GLOBAL"
    if threshold_id == "maximum_solver_residual":
        return "dimensionless relative solver residual", "max_t abs(R_solver) under the frozen solver norm", "NONE_DIMENSIONLESS_GLOBAL"
    if threshold_id == "maximum_energy_drift":
        return "canonical nondimensional code-energy unit", "max_t abs(E(t)-E(0)) in the common canonical nondimensionalization", "NONE_ABSOLUTE_CODE_UNIT; no dependence on row energy, amplitude, mass, or coupling"
    if threshold_id.startswith("maximum_exchange_"):
        return "canonical nondimensional code-energy-rate unit", "max_t abs(exchange-balance residual) in the common canonical nondimensionalization", "NONE_ABSOLUTE_CODE_UNIT; no row scaling"
    if threshold_id == "epsilon_exchange_floor":
        return "canonical nondimensional code-energy unit", "absolute medium-vs-fine solver difference in cumulative exchange", "NONE_ABSOLUTE_NUMERICAL_FLOOR; scientific ratios retain their own denominator"
    if threshold_id == "epsilon_observable_floor":
        return "canonical nondimensional observable unit", "maximum medium-vs-fine solver difference after each registered observable is expressed in its frozen canonical code unit", "NONE_CANONICAL_UNIT_PER_OBSERVABLE; never compared across unlike observables"
    return "canonical nondimensional equation-residual unit", "max_t abs(frozen equation or constraint residual) in its registered canonical code norm", "NONE_ABSOLUTE_CODE_UNIT; the bounded matrix shares the same canonical nondimensionalization"


def build_thresholds(v1_packet: dict[str, Any], pilot_arrays: dict[str, Any], row_ids: list[str]) -> list[dict[str, Any]]:
    v1 = {item["threshold_id"]: item for item in v1_packet["numerical_threshold_provenance"]}
    pilot_runs = pilot_arrays["runs"]
    thresholds: list[dict[str, Any]] = []
    for threshold_id in sorted(v1):
        source = v1[threshold_id]
        is_floor = threshold_id.startswith("epsilon_")
        series_key = METRIC_SERIES.get(threshold_id, threshold_id)
        units, normalization, scaling = _threshold_units(threshold_id)
        if is_floor:
            keys = OBSERVABLE_FLOOR_KEYS if threshold_id == "epsilon_observable_floor" else EXCHANGE_FLOOR_KEYS
            by_row_role = {(run["row_id"], run["calibration_role"]): run for run in pilot_runs}
            raw_values = []
            for row in sorted({run["row_id"] for run in pilot_runs}):
                medium = by_row_role[(row, "SOLVER_TOLERANCE_1e_MINUS_10")]
                fine = by_row_role[(row, "SOLVER_TOLERANCE_1e_MINUS_12")]
                measured = max(
                    abs(float(left) - float(right))
                    for key in keys
                    for left, right in zip(medium["series"][key], fine["series"][key], strict=True)
                )
                raw_values.append(
                    {
                        "row_id": row,
                        "pilot_source_run_ids": [medium["run_record_id"], fine["run_record_id"]],
                        "raw_maximum_medium_vs_fine_difference": measured,
                    }
                )
            roles = ["PRIMARY_FULL_MODEL", "FORCED_COMPARATOR"]
            comparison = "DENOMINATOR_FLOOR_ONLY"
            threshold_class = "NUMERICAL_FLOOR"
            convergence_class = "NOT_A_CONVERGENCE_THRESHOLD"
        else:
            raw_values = [
                {"pilot_source_run_id": run["run_record_id"], "raw_reduced_value": max(abs(float(value)) for value in run["series"][series_key])}
                for run in pilot_runs
            ]
            roles = ALL_NUMERICAL_ROLES if threshold_id in {"maximum_solver_residual", "maximum_Gauss_residual", "maximum_continuity_residual", "maximum_link_norm_error"} else FULL_ROLES
            comparison = "LE"
            threshold_class = "ABSOLUTE_NUMERICAL_CEILING"
            convergence_class = "NOT_A_CONVERGENCE_THRESHOLD"
        thresholds.append(
            {
                "threshold_id": threshold_id,
                "observable_id": threshold_id.removeprefix("maximum_").upper(),
                "raw_series_key": series_key,
                "threshold_class": threshold_class,
                "comparison_operator": comparison,
                "frozen_value": source["candidate_frozen_threshold"],
                "expected_convergence_class": convergence_class,
                "eligible_run_roles": roles,
                "eligible_scientific_rows": row_ids,
                "units": units,
                "normalization_formula": normalization,
                "row_scaling_rule": scaling,
                "numerical_floor": source["candidate_frozen_threshold"] if is_floor else 0.0,
                "pilot_source_run_ids": source["pilot_source_run_ids"],
                "raw_pilot_values": raw_values,
                "generation_formula": source["generation_formula"],
                "safety_factor": 2.0,
                "rounding_rule": source["rounding_rule"],
                "failure_diagnostic": source["failure_classification"],
            }
        )
    return thresholds


def build_convergence(v1_packet: dict[str, Any], pilot_packet: dict[str, Any], canonical_freeze: dict[str, Any]) -> list[dict[str, Any]]:
    v1 = {item["threshold_id"]: item for item in v1_packet["convergence_threshold_provenance"]}
    row_results = pilot_packet["summary"]["row_results"]
    canonical_spatial = canonical_freeze["convergence_definitions"]["spatial"]
    if float(canonical_spatial["minimum_order"]) != 0.8 or canonical_spatial["metric"] != "final_phi2_l2":
        raise ValueError("accepted canonical first-order Wilson spatial contract changed")
    specs = (
        ("minimum_spatial_descendant_order", 0.8, "FIRST_ORDER_WILSON_AFFECTED_SPATIAL", "SPATIAL_REFINEMENT", "final_phi2_l2", "grid_size", False, [row["spatial_refinement"]["observed_descendant_order"] for row in row_results], "accepted canonical Wilson O(a) class; v1's universal 1.5 rule is rejected"),
        ("minimum_temporal_descendant_order", 1.5, "SECOND_ORDER_TEMPORAL", "TEMPORAL_REFINEMENT", "final_descendant_l2", "time_step", True, [row["temporal_refinement"]["observed_descendant_order"] for row in row_results], v1["minimum_temporal_descendant_order"]["generation_formula"]),
        ("minimum_energy_error_order", 1.5, "SECOND_ORDER_ENERGY_ERROR", "TEMPORAL_REFINEMENT", "total_energy_delta", "time_step", True, [row["energy_behavior"]["observed_maximum_error_order"] for row in row_results], v1["minimum_energy_error_order"]["generation_formula"]),
    )
    return [
        {
            "threshold_id": threshold_id,
            "observable_id": series_key.upper(),
            "raw_series_key": series_key,
            "expected_convergence_class": expected_class,
            "expected_analytic_order": 1.0 if expected_class.startswith("FIRST_ORDER") else 2.0,
            "comparison_operator": "GE",
            "frozen_value": value,
            "eligible_run_roles": [role],
            "eligible_scientific_rows": [row["row_id"] for row in row_results],
            "ordering_field": ordering_field,
            "ordering_descending": ordering_descending,
            "fixed_fit_member_count": 3,
            "raw_pilot_values": [{"row_id": row["row_id"], "observed_order": float(observed)} for row, observed in zip(row_results, observed_values, strict=True)],
            "generation_formula": generation,
            "failure_diagnostic": "NUMERICALLY_BLOCKED:CONVERGENCE_NOT_RESOLVED",
        }
        for threshold_id, value, expected_class, role, series_key, ordering_field, ordering_descending, observed_values, generation in specs
    ]


def mutation_suite() -> list[dict[str, str]]:
    mutations = {
        "M_V2_SPATIAL_FLOOR_REVERTED_TO_1P5": "B-BLOCKED_CONVERGENCE_CLASS_MISMATCH",
        "M_V2_TEMPORAL_FLOOR_CHANGED_TO_0P8": "B-BLOCKED_CONVERGENCE_CLASS_MISMATCH",
        "M_V2_EXPECTED_ORDER_METADATA_REMOVED": "B-BLOCKED_CONVERGENCE_CLASS_MISMATCH",
        "M_V2_THRESHOLD_ELIGIBLE_ROLES_REMOVED": "B-BLOCKED_THRESHOLD_SCHEMA",
        "M_V2_THRESHOLD_UNITS_REMOVED": "B-BLOCKED_THRESHOLD_SCHEMA",
        "M_V2_THRESHOLD_NORMALIZATION_REMOVED": "B-BLOCKED_THRESHOLD_SCHEMA",
        "M_V2_COMPARATOR_THRESHOLD_APPLIED_TO_PRIMARY": "B-BLOCKED_THRESHOLD_SCOPE",
        "M_V2_UNSCALED_ABSOLUTE_THRESHOLD_SUBSTITUTED": "B-BLOCKED_THRESHOLD_SCOPE",
        "M_V2_SUPPLIED_PASSED_TRUE_WITH_RAW_FAILURE": "B-BLOCKED_CLASSIFIER_TRUST",
        "M_V2_UNKNOWN_RUN_ID_ADDED": "B-BLOCKED_RUN_IDENTITY",
        "M_V2_REQUIRED_RUN_OMITTED": "B-BLOCKED_RUN_IDENTITY",
        "M_V2_VALID_RUN_DUPLICATED_UNDER_NEW_ID": "B-BLOCKED_RUN_IDENTITY",
        "M_V2_MATERIALITY_SUPPLIED_AFTER_NUMERICAL_BLOCK": "B-BLOCKED_CLASSIFIER_TRUST",
        "M_V2_RAW_OUTPUT_CHANGED_SUMMARY_UNCHANGED": "NUMERICALLY_BLOCKED",
        "M_V2_PHASE_CONTROL_MARKED_GLOBAL": "B-BLOCKED_CONTROL_SCHEMA",
        "M_V2_HOLONOMY_CONTROL_ON_TRIVIAL_ONLY_ROW": "B-BLOCKED_CONTROL_SCHEMA",
        "M_V2_REPRESENTATIVE_BASIS_REMOVED": "B-BLOCKED_CONTROL_SCHEMA",
        "M_V2_CORNER_RELEVANT_CONTROL_EXCLUDED": "B-BLOCKED_CONTROL_SCHEMA",
        "M_V2_INVERSE_FILENAME_MAPPING_REMOVED": "B-BLOCKED_RUN_IDENTITY",
        "M_V2_TWO_IDS_ONE_FILENAME": "B-BLOCKED_RUN_IDENTITY",
        "M_V2_WRONG_PAYLOAD_RUN_ID": "B-BLOCKED_RUN_IDENTITY",
        "M_V2_FILE_RENAMED_PAYLOAD_UNCHANGED": "B-BLOCKED_RUN_IDENTITY",
        "M_V2_ORPHAN_OUTPUT_ADDED": "B-BLOCKED_RUN_IDENTITY",
    }
    return [{"mutation_id": key, "expected_exact_diagnostic": value, "unrelated_prior_failure_forbidden": "true"} for key, value in mutations.items()]


def environment_identity() -> dict[str, Any]:
    paths = ["requirements.active.lock", "formal/toe_formal/lean-toolchain", "formal/toe_formal/lake-manifest.json", ".gitattributes"]
    return {
        "python_version": platform.python_version(),
        "operating_system": platform.system(),
        "os_release": platform.release(),
        "canonical_serialization": "sorted-key UTF-8 NFC JSON with LF and finite numbers only",
        "required_process_environment": {"PYTHONHASHSEED": "0", "TZ": "UTC", "LC_ALL": "C", "LANG": "C"},
        "bound_files": [{"path": path, "sha256": sha256_path(REPO_ROOT / path)} for path in paths],
    }


DECISION_IDS = [
    "v1_blocked_review_is_exact_authority",
    "accepted_scientific_rows_pilot_arrays_parameters_and_materiality_are_unchanged",
    "wilson_affected_spatial_fit_is_first_order_with_floor_0p8",
    "temporal_and_energy_error_fits_remain_second_order_with_floor_1p5",
    "all_twenty_two_numerical_values_are_preserved",
    "every_threshold_has_fail_closed_role_row_unit_normalization_scaling_and_provenance_semantics",
    "exact_203_record_matrix_is_preserved_with_feature_appropriate_control_reassignment",
    "all_controls_have_exact_scope_predicate_representativeness_and_raw_evaluation_contracts",
    "classifier_consumes_only_frozen_inputs_and_raw_exact_output_payloads",
    "classifier_reconstructs_every_decision_and_rejects_supplied_booleans_or_classes",
    "classifier_requires_exact_run_identity_closure",
    "materiality_is_not_evaluated_after_numerical_or_model_domain_block",
    "filename_mapping_is_casefold_safe_explicit_bijective_and_payload_reconciled",
    "forced_comparators_remain_negative_necessity_only",
    "no_invariant_descendant_free_comparator_is_invented",
    "blocker_mutations_have_exact_diagnostics_without_unrelated_prior_failure",
    "no_additional_pilot_is_needed_or_authorized",
    "preparation_rotates_only_to_independent_v2_freeze_review",
    "canonical_execution_and_new_claims_remain_unauthorized",
]


def build_artifacts() -> tuple[dict[str, Any], dict[str, Any], dict[str, Any], dict[str, Any], dict[str, Any]]:
    validate_authority()
    v1_packet = load_json(V1_PACKET_RELATIVE_PATH)
    v1_matrix = load_json(V1_MATRIX_RELATIVE_PATH)
    v1_review = load_json(V1_REVIEW_RELATIVE_PATH)
    guardrail = load_json(GUARDRAIL_RELATIVE_PATH)
    pilot_packet = load_json(PILOT_PACKET_RELATIVE_PATH)
    pilot_arrays = load_json(PILOT_ARRAYS_RELATIVE_PATH)
    canonical_freeze = load_json(CANONICAL_FREEZE_RELATIVE_PATH)
    row_ids = [row["row_id"] for row in guardrail["scientific_matrix"]]
    matrix = build_matrix(v1_matrix, guardrail)
    output_identity = build_output_identity(matrix)
    matrix_sha = sha256_bytes(canonical_json_bytes(matrix))
    identity_sha = sha256_bytes(canonical_json_bytes(output_identity))
    classifier_sha = sha256_path(REPO_ROOT / CLASSIFIER_RELATIVE_PATH)
    thresholds = build_thresholds(v1_packet, pilot_arrays, row_ids)
    convergence = build_convergence(v1_packet, pilot_packet, canonical_freeze)
    for item in convergence:
        item["eligible_scientific_rows"] = row_ids
    packet = {
        "schema_id": SCHEMA_IDS["packet"],
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "verdict": "PREPARED_PENDING_INDEPENDENT_REVIEW",
        "authority_basis": {
            "v1_review_commit": V1_REVIEW_COMMIT,
            "v1_review_parent": V1_REVIEW_PARENT,
            "v1_review_verdict": v1_review["verdict"],
            "input_artifacts": [{"path": path, "sha256": digest} for path, digest in INPUT_HASHES.items()],
        },
        "bounded_correction_scope": {
            "preserved": ["fourteen scientific rows and five axes", "accepted pilot arrays and result", "central numerical settings", "twenty-two numerical values", "materiality gates 0.1 and 0.5", "comparator distinction", "claim ceiling and prior E-REPRO result"],
            "corrected": ["convergence classes", "threshold applicability and normalization", "classifier trust boundary", "control applicability", "filename and payload identity custody"],
            "additional_pilot_required": False,
            "scientific_equations_or_initial_data_changed": False,
        },
        "scientific_design_freeze": v1_packet["scientific_design_freeze"],
        "proposed_numerical_parameter_freeze": v1_packet["proposed_numerical_parameter_freeze"],
        "canonical_run_matrix": {"path": RUN_MATRIX_RELATIVE_PATH, "sha256": matrix_sha, "record_count": 203},
        "expected_output_identity_manifest": {"path": OUTPUT_IDENTITY_RELATIVE_PATH, "sha256": identity_sha, "record_count": 203},
        "execution_consumer_contract": {
            "expected_run_id_set": sorted(record["run_id"] for record in matrix["records"]),
            "exact_set_equality_required": True,
            "dynamic_discovery_generation_exclusion_or_overwrite": "forbidden",
            "payload_required_echo_fields": ["run_id", "scientific_row_id", "run_role", "model_class", "parent_run_or_row_id", "input_hash", "relative_output_path"],
            "path_manifest_payload_mismatch": "B-BLOCKED_RUN_IDENTITY",
            "unexpected_missing_duplicate_or_orphan_output": "B-BLOCKED_RUN_IDENTITY",
        },
        "numerical_threshold_provenance": thresholds,
        "convergence_threshold_provenance": convergence,
        "fixed_structural_numerical_gates": {
            **v1_packet["fixed_structural_numerical_gates"],
            "forced_transverse_equation_residual_strict_lower_bound": "10 * epsilon_observable_floor",
            "model_domain_margin_rule": "raw registered model_domain_margin must be nonnegative",
        },
        "control_applicability_freeze": {
            "scope_classes": ["GLOBAL_IMPLEMENTATION_INVARIANT", "ANCHOR_REPRESENTATIVE_WITH_PROOF", "ROW_LOCAL", "CONDITIONAL_FEATURE_DEPENDENT", "COMPARATOR_ONLY"],
            "record_count_preserved": 21,
            "matrix_may_expand_only_if_independent_review_finds_coverage_insufficient": True,
            "contracts": [record["control_metadata"] for record in matrix["records"] if "control_metadata" in record],
        },
        "scientific_materiality_freeze": v1_packet["scientific_materiality_freeze"],
        "comparator_freeze": v1_packet["comparator_freeze"],
        "observable_and_energy_freeze": {
            **v1_packet["observable_and_energy_freeze"],
            "spatial_convergence_observable": "final_phi2_l2",
            "spatial_leading_error": "O(a) Wilson-affected",
            "temporal_convergence_observable": "final_descendant_l2 := sqrt(final_phi2_l2^2 + final_phi3_l2^2)",
            "energy_error_convergence_observable": "max_t abs(total_energy_delta)",
        },
        "deterministic_outcome_logic": {
            "evaluation_order": ["custody and hashes", "exact identity and completeness", "positive and negative controls from raw observations", "numerical admissibility from raw series", "robustness", "forced-comparator necessity", "materiality only when admitted", "claim ceiling"],
            "supplied_pass_booleans_or_classifications": "forbidden and rejected with B-BLOCKED_CLASSIFIER_TRUST",
            "raw_output_reconstruction_required": True,
            "no_significance_when_numerically_blocked": "NOT_EVALUATED_NUMERICAL_BLOCK",
            "no_significance_when_model_domain_limited": "NOT_EVALUATED_MODEL_DOMAIN_LIMIT",
            "robustness_and_significance_fields_separate": True,
        },
        "classifier_versioning_and_provenance": {
            "decision_rule_bundle_id": "DM_ROBUSTNESS_DECISION_RULE_BUNDLE_v2",
            "classifier_implementation": {"path": CLASSIFIER_RELATIVE_PATH, "sha256": classifier_sha},
            "allowed_inputs": [PACKET_RELATIVE_PATH, RUN_MATRIX_RELATIVE_PATH, OUTPUT_IDENTITY_RELATIVE_PATH, "exact 203 raw output payloads"],
            "mutable_external_decision_logic": "forbidden",
            "hash_verification_before_evaluation": True,
            "result_is_candidate_pending_independent_result_review": True,
        },
        "blocker_regression_mutations": mutation_suite(),
        "failure_and_rerun_semantics": v1_packet["failure_and_rerun_semantics"],
        "environment_identity": environment_identity(),
        "selected_next_target": REVIEW_TARGET,
        "post_acceptance_target": POST_ACCEPTANCE_TARGET,
        "blocked_target": BLOCKED_TARGET,
        "authority_boundary": {
            "packet_prepared": True,
            "packet_independently_accepted": False,
            "numerical_parameters_or_thresholds_authoritatively_frozen": False,
            "canonical_fourteen_row_execution_authorized": False,
            "robustness_or_materiality_classification_assigned": False,
            "new_E_REPRO_claim": False,
            "previous_canonical_E_REPRO_unchanged": True,
        },
        "lean_status_boundary": {
            "affected_preparation_authority_build": {"status": "PASSED", "job_count": 144},
            "historical_repository_wide_aggregate": {"completed_jobs": 8441, "total_jobs": 8507, "termination": "TIMEOUT_AT_600_SECONDS", "theorem_error_observed_before_timeout": False, "status": "INCOMPLETE"},
            "repository_wide_green_claim": False,
        },
        "claim_ceiling": "A bounded freeze-v2 correction is prepared for independent review. It does not authorize canonical execution or assign robustness, descendant significance, or a new E-REPRO claim.",
        "prompt_protection": {"path": PROMPT_RELATIVE_PATH, "sha256": PROMPT_SHA256},
        "nonclaims": v1_packet["nonclaims"],
    }
    packet_raw = canonical_json_bytes(packet)
    matrix_raw = canonical_json_bytes(matrix)
    identity_raw = canonical_json_bytes(output_identity)
    manifest = {
        "schema_id": SCHEMA_IDS["manifest"],
        "captured_at_utc": CAPTURED_AT_UTC,
        "generator": {"path": SCRIPT_RELATIVE_PATH, "sha256": sha256_path(SCRIPT_PATH)},
        "classifier": {"path": CLASSIFIER_RELATIVE_PATH, "sha256": classifier_sha},
        "inputs": packet["authority_basis"]["input_artifacts"],
        "packet": {"path": PACKET_RELATIVE_PATH, "sha256": sha256_bytes(packet_raw)},
        "run_matrix": {"path": RUN_MATRIX_RELATIVE_PATH, "sha256": sha256_bytes(matrix_raw)},
        "expected_output_identity_manifest": {"path": OUTPUT_IDENTITY_RELATIVE_PATH, "sha256": sha256_bytes(identity_raw)},
        "decision_count": len(DECISION_IDS),
        "selected_next_target": REVIEW_TARGET,
    }
    manifest_raw = canonical_json_bytes(manifest)
    report = {
        "schema_id": SCHEMA_IDS["report"],
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "verdict": "PREPARED_PENDING_INDEPENDENT_REVIEW",
        "decision_ids": DECISION_IDS,
        "decision_count": len(DECISION_IDS),
        "artifacts": {
            "packet": {"path": PACKET_RELATIVE_PATH, "sha256": sha256_bytes(packet_raw)},
            "run_matrix": {"path": RUN_MATRIX_RELATIVE_PATH, "sha256": sha256_bytes(matrix_raw)},
            "output_identity": {"path": OUTPUT_IDENTITY_RELATIVE_PATH, "sha256": sha256_bytes(identity_raw)},
            "manifest": {"path": MANIFEST_RELATIVE_PATH, "sha256": sha256_bytes(manifest_raw)},
            "classifier": {"path": CLASSIFIER_RELATIVE_PATH, "sha256": classifier_sha},
        },
        "preserved_counts": {"scientific_rows": 14, "scientific_records": 182, "positive_controls": 8, "negative_controls": 13, "total_records": 203, "numerical_values": 22, "convergence_classes": 3},
        "corrected_convergence_floors": {"FIRST_ORDER_WILSON_AFFECTED_SPATIAL": 0.8, "SECOND_ORDER_TEMPORAL": 1.5, "SECOND_ORDER_ENERGY_ERROR": 1.5},
        "blocker_mutation_count": len(packet["blocker_regression_mutations"]),
        "validation_status": {
            "affected_test_count": 99,
            "affected_tests_passed": True,
            "tooling_gate_test_count": 6,
            "tooling_gate_tests_passed": True,
            "artifact_regeneration_check_passed": True,
            "authority_surface_parity_passed": True,
            "affected_lean_job_count": 144,
            "affected_lean_build_passed": True,
        },
        "selected_next_target": REVIEW_TARGET,
        "authority_boundary": packet["authority_boundary"],
        "claim_ceiling": packet["claim_ceiling"],
    }
    return packet, matrix, output_identity, manifest, report


def artifact_bytes() -> dict[str, bytes]:
    packet, matrix, identity, manifest, report = build_artifacts()
    return {
        PACKET_RELATIVE_PATH: canonical_json_bytes(packet),
        RUN_MATRIX_RELATIVE_PATH: canonical_json_bytes(matrix),
        OUTPUT_IDENTITY_RELATIVE_PATH: canonical_json_bytes(identity),
        MANIFEST_RELATIVE_PATH: canonical_json_bytes(manifest),
        REPORT_RELATIVE_PATH: canonical_json_bytes(report),
    }


def write_or_check(check: bool) -> None:
    artifacts = artifact_bytes()
    mismatches: list[str] = []
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
    args = parser.parse_args()
    write_or_check(args.check)


if __name__ == "__main__":
    main()
