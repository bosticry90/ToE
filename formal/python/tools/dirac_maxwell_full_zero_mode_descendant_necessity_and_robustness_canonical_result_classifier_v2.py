from __future__ import annotations

import hashlib
import json
import math
import unicodedata
from pathlib import Path
from typing import Any


CLASSIFIER_ID = "DM_ROBUSTNESS_CANONICAL_RESULT_CLASSIFIER_v2"
FULL_MODEL_ROLES = {
    "PRIMARY_FULL_MODEL",
    "SPATIAL_REFINEMENT",
    "TEMPORAL_REFINEMENT",
    "SOLVER_VERIFICATION",
    "DETERMINISTIC_DUPLICATE",
}
FORBIDDEN_DECISION_KEYS = {
    "passed",
    "row_passed",
    "control_passed",
    "convergence_passed",
    "robustness_pass",
    "robustness_class",
    "materiality_class",
    "descendant_significance_class",
    "execution_status",
    "scientific_claim_authorized",
}


class ClassificationBlock(RuntimeError):
    def __init__(self, diagnostic: str, detail: str) -> None:
        super().__init__(detail)
        self.diagnostic = diagnostic
        self.detail = detail


def _normalize(value: Any) -> Any:
    if isinstance(value, str):
        return unicodedata.normalize("NFC", value)
    if isinstance(value, list):
        return [_normalize(item) for item in value]
    if isinstance(value, dict):
        return {_normalize(str(key)): _normalize(item) for key, item in value.items()}
    return value


def canonical_json_bytes(payload: Any) -> bytes:
    return (
        json.dumps(
            _normalize(payload),
            allow_nan=False,
            ensure_ascii=False,
            indent=2,
            sort_keys=True,
        )
        + "\n"
    ).encode("utf-8")


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _blocked(diagnostic: str, detail: str) -> dict[str, Any]:
    return {
        "classifier_id": CLASSIFIER_ID,
        "execution_status": diagnostic,
        "robustness_status": None,
        "descendant_significance_status": "NOT_EVALUATED_PRECLASSIFICATION_BLOCK",
        "scientific_claim_authorized": False,
        "detail": detail,
    }


def _finite_series(payload: dict[str, Any], key: str) -> list[float]:
    series = payload.get("series")
    if not isinstance(series, dict) or not isinstance(series.get(key), list) or not series[key]:
        raise ClassificationBlock("B-BLOCKED_RAW_OUTPUT_SCHEMA", f"missing nonempty raw series {key}")
    try:
        values = [float(value) for value in series[key]]
    except (TypeError, ValueError) as error:
        raise ClassificationBlock("B-BLOCKED_RAW_OUTPUT_SCHEMA", f"non-numeric raw series {key}") from error
    if any(not math.isfinite(value) for value in values):
        raise ClassificationBlock("B-BLOCKED_RAW_OUTPUT_SCHEMA", f"non-finite raw series {key}")
    return values


def _raw_scalar(payload: dict[str, Any], key: str) -> float:
    raw = payload.get("raw_observables")
    if not isinstance(raw, dict) or key not in raw:
        raise ClassificationBlock("B-BLOCKED_RAW_OUTPUT_SCHEMA", f"missing raw observable {key}")
    try:
        value = float(raw[key])
    except (TypeError, ValueError) as error:
        raise ClassificationBlock("B-BLOCKED_RAW_OUTPUT_SCHEMA", f"non-numeric raw observable {key}") from error
    if not math.isfinite(value):
        raise ClassificationBlock("B-BLOCKED_RAW_OUTPUT_SCHEMA", f"non-finite raw observable {key}")
    return value


def _walk_forbidden_keys(value: Any, path: str = "payload") -> None:
    if isinstance(value, dict):
        for key, item in value.items():
            lowered = str(key).lower()
            if lowered in FORBIDDEN_DECISION_KEYS or lowered.endswith("_passed"):
                raise ClassificationBlock(
                    "B-BLOCKED_CLASSIFIER_TRUST",
                    f"externally supplied decision field is forbidden: {path}.{key}",
                )
            _walk_forbidden_keys(item, f"{path}.{key}")
    elif isinstance(value, list):
        for index, item in enumerate(value):
            _walk_forbidden_keys(item, f"{path}[{index}]")


def _compare(value: float, operator: str, target: float) -> bool:
    if operator == "LE":
        return value <= target
    if operator == "LT":
        return value < target
    if operator == "GE":
        return value >= target
    if operator == "GT":
        return value > target
    if operator == "EQ":
        return value == target
    raise ClassificationBlock("B-BLOCKED_CONTROL_SCHEMA", f"unknown comparison operator {operator}")


def _three_level_order(values: list[float]) -> float:
    if len(values) != 3:
        raise ClassificationBlock("B-BLOCKED_CONVERGENCE_INPUT", "three-level fit requires exactly three values")
    coarse_medium = abs(values[0] - values[1])
    medium_fine = abs(values[1] - values[2])
    if coarse_medium <= 0.0 or medium_fine <= 0.0:
        raise ClassificationBlock("B-BLOCKED_CONVERGENCE_INPUT", "three-level differences must be strictly positive")
    return math.log(coarse_medium / medium_fine, 2.0)


def _validate_freeze_bindings(
    freeze_packet: dict[str, Any],
    run_matrix: dict[str, Any],
    output_manifest: dict[str, Any],
    classifier_path: Path | None,
) -> None:
    matrix_binding = freeze_packet.get("canonical_run_matrix")
    identity_binding = freeze_packet.get("expected_output_identity_manifest")
    classifier_binding = freeze_packet.get("classifier_versioning_and_provenance", {}).get("classifier_implementation")
    if not isinstance(matrix_binding, dict) or not isinstance(identity_binding, dict) or not isinstance(classifier_binding, dict):
        raise ClassificationBlock("B-BLOCKED_CUSTODY", "freeze packet lacks required matrix, identity, or classifier binding")
    if sha256_bytes(canonical_json_bytes(run_matrix)) != matrix_binding.get("sha256"):
        raise ClassificationBlock("B-BLOCKED_CUSTODY", "run-matrix hash mismatch")
    if sha256_bytes(canonical_json_bytes(output_manifest)) != identity_binding.get("sha256"):
        raise ClassificationBlock("B-BLOCKED_CUSTODY", "expected-output identity-manifest hash mismatch")
    if classifier_path is None:
        raise ClassificationBlock("B-BLOCKED_CUSTODY", "classifier source path is required for pre-evaluation hash verification")
    if hashlib.sha256(classifier_path.read_bytes()).hexdigest() != classifier_binding.get("sha256"):
        raise ClassificationBlock("B-BLOCKED_CUSTODY", "classifier source hash mismatch")


def _identity_index(
    run_matrix: dict[str, Any], output_manifest: dict[str, Any], output_payloads: dict[str, dict[str, Any]]
) -> tuple[dict[str, dict[str, Any]], dict[str, dict[str, Any]]]:
    records = run_matrix.get("records")
    identities = output_manifest.get("outputs")
    if not isinstance(records, list) or not isinstance(identities, list):
        raise ClassificationBlock("B-BLOCKED_RUN_IDENTITY", "matrix records or output identities are absent")
    matrix_ids = [item.get("run_id") for item in records if isinstance(item, dict)]
    identity_ids = [item.get("run_id") for item in identities if isinstance(item, dict)]
    identity_paths = [item.get("relative_output_path") for item in identities if isinstance(item, dict)]
    identity_filenames = [item.get("safe_filename") for item in identities if isinstance(item, dict)]
    if len(records) != 203 or len(identities) != 203:
        raise ClassificationBlock("B-BLOCKED_RUN_IDENTITY", "exact 203-record identity closure failed")
    if len(set(matrix_ids)) != 203 or len(set(identity_ids)) != 203 or set(matrix_ids) != set(identity_ids):
        raise ClassificationBlock("B-BLOCKED_RUN_IDENTITY", "missing, unexpected, or duplicate run identity")
    if len(set(identity_paths)) != 203 or len(set(identity_filenames)) != 203 or set(output_payloads) != set(identity_paths):
        raise ClassificationBlock("B-BLOCKED_RUN_IDENTITY", "missing, orphaned, or duplicate output path")
    expected_forward = {item["run_id"]: item["safe_filename"] for item in identities}
    expected_inverse = {item["safe_filename"]: item["run_id"] for item in identities}
    if output_manifest.get("run_id_to_safe_filename") != expected_forward or output_manifest.get("safe_filename_to_run_id") != expected_inverse:
        raise ClassificationBlock("B-BLOCKED_RUN_IDENTITY", "explicit filename bijection is absent or inconsistent")
    by_run = {item["run_id"]: item for item in records}
    payload_by_run: dict[str, dict[str, Any]] = {}
    for identity in identities:
        run_id = identity["run_id"]
        record = by_run[run_id]
        path = identity["relative_output_path"]
        payload = output_payloads[path]
        _walk_forbidden_keys(payload)
        expected = {
            "run_id": run_id,
            "scientific_row_id": identity["scientific_row_id"],
            "run_role": identity["run_role"],
            "model_class": identity["model_class"],
            "parent_run_or_row_id": identity["parent_run_or_row_id"],
            "input_hash": identity["input_hash"],
            "relative_output_path": path,
        }
        for key, value in expected.items():
            if payload.get(key) != value:
                raise ClassificationBlock("B-BLOCKED_RUN_IDENTITY", f"payload/manifest mismatch for {run_id}: {key}")
        if record.get("input_hash") != identity["input_hash"] or record.get("output_path") != path:
            raise ClassificationBlock("B-BLOCKED_RUN_IDENTITY", f"matrix/manifest mismatch for {run_id}")
        payload_by_run[run_id] = payload
    return by_run, payload_by_run


def _control_audit(
    packet: dict[str, Any], by_run: dict[str, dict[str, Any]], payload_by_run: dict[str, dict[str, Any]]
) -> list[str]:
    diagnostics: list[str] = []
    frozen_contracts = packet.get("control_applicability_freeze", {}).get("contracts")
    if not isinstance(frozen_contracts, list) or len(frozen_contracts) != 21:
        raise ClassificationBlock("B-BLOCKED_CONTROL_SCHEMA", "exact frozen control applicability inventory missing")
    frozen_by_id = {item.get("control_id"): item for item in frozen_contracts if isinstance(item, dict)}
    for run_id, record in by_run.items():
        if record.get("run_role") not in {"POSITIVE_CONTROL", "NEGATIVE_CONTROL"}:
            continue
        metadata = record.get("control_metadata")
        if not isinstance(metadata, dict):
            raise ClassificationBlock("B-BLOCKED_CONTROL_SCHEMA", f"missing control metadata: {run_id}")
        required_fields = {
            "control_id",
            "control_type",
            "scope_class",
            "applicable_row_ids",
            "representative_row_id",
            "representativeness_basis",
            "required_feature_predicate",
            "mutation_definition",
            "expected_diagnostic",
            "expected_decision_delta",
            "forbidden_alternate_failure",
            "control_evaluation_spec",
        }
        if set(metadata) != required_fields:
            raise ClassificationBlock("B-BLOCKED_CONTROL_SCHEMA", f"incomplete control applicability record: {run_id}")
        if metadata != frozen_by_id.get(metadata.get("control_id")):
            raise ClassificationBlock("B-BLOCKED_CONTROL_SCHEMA", f"control applicability differs from frozen contract: {run_id}")
        if not metadata["representativeness_basis"] or not metadata["required_feature_predicate"]:
            raise ClassificationBlock("B-BLOCKED_CONTROL_SCHEMA", f"empty control applicability semantics: {run_id}")
        observations = payload_by_run[run_id].get("control_observables")
        if not isinstance(observations, dict):
            raise ClassificationBlock("B-BLOCKED_RAW_OUTPUT_SCHEMA", f"missing raw control observables: {run_id}")
        for spec in metadata["control_evaluation_spec"]["required_observations"]:
            observable = spec["observable_id"]
            if observable not in observations:
                raise ClassificationBlock("B-BLOCKED_RAW_OUTPUT_SCHEMA", f"missing control observable {observable}: {run_id}")
            value = float(observations[observable])
            if not math.isfinite(value) or not _compare(value, spec["comparison_operator"], float(spec["target_value"])):
                raise ClassificationBlock(
                    "B-BLOCKED_CONTROL_FAILURE",
                    f"{metadata['control_id']} did not produce only {metadata['expected_diagnostic']}",
                )
        diagnostics.append(metadata["control_id"])
    if len(diagnostics) != 21 or len(set(diagnostics)) != 21:
        raise ClassificationBlock("B-BLOCKED_CONTROL_SCHEMA", "exact 8-positive/13-negative control inventory failed")
    return diagnostics


def _threshold_audit(
    packet: dict[str, Any], by_run: dict[str, dict[str, Any]], payload_by_run: dict[str, dict[str, Any]]
) -> dict[str, list[str]]:
    failures: dict[str, list[str]] = {}
    row_ids = set(packet["scientific_design_freeze"]["scientific_row_ids"])
    thresholds = packet.get("numerical_threshold_provenance")
    if not isinstance(thresholds, list) or len(thresholds) != 22:
        raise ClassificationBlock("B-BLOCKED_THRESHOLD_SCHEMA", "exact 22-threshold schema missing")
    required = {
        "threshold_id",
        "observable_id",
        "raw_series_key",
        "threshold_class",
        "comparison_operator",
        "frozen_value",
        "expected_convergence_class",
        "eligible_run_roles",
        "eligible_scientific_rows",
        "units",
        "normalization_formula",
        "row_scaling_rule",
        "numerical_floor",
        "pilot_source_run_ids",
        "raw_pilot_values",
        "generation_formula",
        "safety_factor",
        "rounding_rule",
        "failure_diagnostic",
    }
    for threshold in thresholds:
        if not isinstance(threshold, dict) or set(threshold) != required:
            raise ClassificationBlock("B-BLOCKED_THRESHOLD_SCHEMA", "threshold applicability or normalization metadata missing")
        eligible_rows = set(threshold["eligible_scientific_rows"])
        eligible_roles = set(threshold["eligible_run_roles"])
        if not eligible_rows or not eligible_roles or not eligible_rows <= row_ids:
            raise ClassificationBlock("B-BLOCKED_THRESHOLD_SCOPE", f"fail-closed scope invalid: {threshold['threshold_id']}")
        all_numerical_roles = FULL_MODEL_ROLES | {"FORCED_COMPARATOR"}
        if threshold["threshold_class"] == "NUMERICAL_FLOOR":
            expected_roles = {"PRIMARY_FULL_MODEL", "FORCED_COMPARATOR"}
        elif threshold["threshold_id"] in {"maximum_solver_residual", "maximum_Gauss_residual", "maximum_continuity_residual", "maximum_link_norm_error"}:
            expected_roles = all_numerical_roles
        else:
            expected_roles = FULL_MODEL_ROLES
        if eligible_roles != expected_roles:
            raise ClassificationBlock("B-BLOCKED_THRESHOLD_SCOPE", f"threshold applied outside its frozen roles: {threshold['threshold_id']}")
        for semantic_key in ("units", "normalization_formula", "row_scaling_rule"):
            if not isinstance(threshold[semantic_key], str) or not threshold[semantic_key].strip():
                raise ClassificationBlock("B-BLOCKED_THRESHOLD_SCOPE", f"empty threshold semantics: {threshold['threshold_id']}/{semantic_key}")
        if threshold["threshold_class"] == "NUMERICAL_FLOOR":
            continue
        for run_id, record in by_run.items():
            if record.get("scientific_row_id") not in eligible_rows or record.get("run_role") not in eligible_roles:
                continue
            values = _finite_series(payload_by_run[run_id], threshold["raw_series_key"])
            observed = max(abs(value) for value in values)
            if not _compare(observed, threshold["comparison_operator"], float(threshold["frozen_value"])):
                failures.setdefault(record["scientific_row_id"], []).append(threshold["failure_diagnostic"])
    return failures


def _convergence_audit(
    packet: dict[str, Any], by_run: dict[str, dict[str, Any]], payload_by_run: dict[str, dict[str, Any]]
) -> tuple[dict[str, list[str]], dict[str, dict[str, float]]]:
    failures: dict[str, list[str]] = {}
    observed: dict[str, dict[str, float]] = {}
    specs = packet.get("convergence_threshold_provenance")
    expected_classes = {
        "minimum_spatial_descendant_order": ("FIRST_ORDER_WILSON_AFFECTED_SPATIAL", 0.8, "SPATIAL_REFINEMENT", "final_phi2_l2"),
        "minimum_temporal_descendant_order": ("SECOND_ORDER_TEMPORAL", 1.5, "TEMPORAL_REFINEMENT", "final_descendant_l2"),
        "minimum_energy_error_order": ("SECOND_ORDER_ENERGY_ERROR", 1.5, "TEMPORAL_REFINEMENT", "total_energy_delta"),
    }
    if not isinstance(specs, list) or {item.get("threshold_id") for item in specs} != set(expected_classes):
        raise ClassificationBlock("B-BLOCKED_CONVERGENCE_CLASS_MISMATCH", "exact three convergence classes missing")
    for spec in specs:
        expected_class, expected_floor, role, series_key = expected_classes[spec["threshold_id"]]
        if (
            spec.get("expected_convergence_class") != expected_class
            or float(spec.get("frozen_value")) != expected_floor
            or spec.get("eligible_run_roles") != [role]
            or spec.get("raw_series_key") != series_key
        ):
            raise ClassificationBlock("B-BLOCKED_CONVERGENCE_CLASS_MISMATCH", f"wrong convergence semantics: {spec['threshold_id']}")
    for row_id in packet["scientific_design_freeze"]["scientific_row_ids"]:
        observed[row_id] = {}
        for spec in specs:
            role = spec["eligible_run_roles"][0]
            records = sorted(
                (record for record in by_run.values() if record.get("scientific_row_id") == row_id and record.get("run_role") == role),
                key=lambda record: record[spec["ordering_field"]],
                reverse=bool(spec["ordering_descending"]),
            )
            if len(records) != 3:
                raise ClassificationBlock("B-BLOCKED_CONVERGENCE_INPUT", f"wrong fit membership for {row_id}/{role}")
            if spec["threshold_id"] == "minimum_energy_error_order":
                values = [max(abs(value) for value in _finite_series(payload_by_run[record["run_id"]], spec["raw_series_key"])) for record in records]
                order = math.log(values[0] / values[1], 2.0) if values[0] > 0.0 and values[1] > 0.0 else float("-inf")
                second_order = math.log(values[1] / values[2], 2.0) if values[1] > 0.0 and values[2] > 0.0 else float("-inf")
                order = min(order, second_order)
            else:
                values = [_finite_series(payload_by_run[record["run_id"]], spec["raw_series_key"])[-1] for record in records]
                order = _three_level_order(values)
            observed[row_id][spec["threshold_id"]] = order
            if not math.isfinite(order) or order < float(spec["frozen_value"]):
                failures.setdefault(row_id, []).append(spec["failure_diagnostic"])
    return failures, observed


def _determinism_audit(by_run: dict[str, dict[str, Any]], payload_by_run: dict[str, dict[str, Any]]) -> dict[str, list[str]]:
    failures: dict[str, list[str]] = {}
    rows = {record["scientific_row_id"] for record in by_run.values() if record.get("run_role") == "PRIMARY_FULL_MODEL"}
    for row_id in rows:
        duplicates = sorted(
            (record for record in by_run.values() if record.get("scientific_row_id") == row_id and record.get("run_role") == "DETERMINISTIC_DUPLICATE"),
            key=lambda record: record["run_id"],
        )
        if len(duplicates) != 2:
            raise ClassificationBlock("B-BLOCKED_RUN_IDENTITY", f"missing deterministic pair: {row_id}")
        payloads = [payload_by_run[item["run_id"]].get("registered_numerical_payload") for item in duplicates]
        if any(item is None for item in payloads) or canonical_json_bytes(payloads[0]) != canonical_json_bytes(payloads[1]):
            failures.setdefault(row_id, []).append("DETERMINISTIC_REPRODUCTION_MISMATCH")
    return failures


def _solver_audit(packet: dict[str, Any], by_run: dict[str, dict[str, Any]], payload_by_run: dict[str, dict[str, Any]]) -> dict[str, list[str]]:
    failures: dict[str, list[str]] = {}
    gate = float(packet["fixed_structural_numerical_gates"]["maximum_solver_to_truncation_ratio"])
    cap = int(packet["fixed_structural_numerical_gates"]["maximum_iterations"])
    for row_id in packet["scientific_design_freeze"]["scientific_row_ids"]:
        runs = [record for record in by_run.values() if record.get("scientific_row_id") == row_id and record.get("run_role") == "SOLVER_VERIFICATION"]
        if len(runs) != 3:
            raise ClassificationBlock("B-BLOCKED_RUN_IDENTITY", f"missing solver hierarchy: {row_id}")
        tight = min(runs, key=lambda record: record["solver_tolerance"])
        payload = payload_by_run[tight["run_id"]]
        solver_error = _raw_scalar(payload, "solver_error_norm")
        truncation_error = _raw_scalar(payload, "truncation_error_norm")
        if truncation_error <= 0.0 or solver_error / truncation_error > gate:
            failures.setdefault(row_id, []).append("SOLVER_TO_TRUNCATION_HIERARCHY_FAILED")
        for record in runs:
            if max(_finite_series(payload_by_run[record["run_id"]], "solver_iterations")) > cap:
                failures.setdefault(row_id, []).append("SOLVER_ITERATION_CAP_EXCEEDED")
    return failures


def _materiality(
    packet: dict[str, Any], by_run: dict[str, dict[str, Any]], payload_by_run: dict[str, dict[str, Any]]
) -> tuple[str, dict[str, Any]]:
    thresholds = {item["threshold_id"]: float(item["frozen_value"]) for item in packet["numerical_threshold_provenance"]}
    epsilon_o = thresholds["epsilon_observable_floor"]
    epsilon_x = thresholds["epsilon_exchange_floor"]
    r_keys = {
        "MATTER_DENSITY": "matter_density_l2",
        "LONGITUDINAL_ELECTRIC_FIELD": "longitudinal_electric_field_l2",
        "MATTER_ENERGY": "matter_energy",
        "LONGITUDINAL_EXCHANGE": "cumulative_exchange_longitudinal",
        "TOTAL_SOURCE_CURRENT": "total_source_current_l2",
    }
    maxima: list[float] = []
    per_row: dict[str, Any] = {}
    necessity_floor = 10.0 * epsilon_o
    for row_id in packet["scientific_design_freeze"]["scientific_row_ids"]:
        primary_record = next(record for record in by_run.values() if record.get("scientific_row_id") == row_id and record.get("run_role") == "PRIMARY_FULL_MODEL")
        comparator_record = next(record for record in by_run.values() if record.get("scientific_row_id") == row_id and record.get("run_role") == "FORCED_COMPARATOR")
        primary = payload_by_run[primary_record["run_id"]]
        comparator = payload_by_run[comparator_record["run_id"]]
        residual = max(abs(value) for value in _finite_series(comparator, "forced_transverse_equation_residual"))
        if residual <= necessity_floor:
            return "NOT_EVALUATED_NECESSITY_UNRESOLVED", {"unresolved_row_id": row_id, "observed_residual": residual, "required_strict_lower_bound": necessity_floor}
        row_r: dict[str, float] = {}
        for observable_id, series_key in r_keys.items():
            full_values = _finite_series(primary, series_key)
            forced_values = _finite_series(comparator, series_key)
            if len(full_values) != len(forced_values):
                raise ClassificationBlock("B-BLOCKED_RAW_OUTPUT_SCHEMA", f"unaligned full/comparator series: {row_id}/{observable_id}")
            value = max(abs(left - right) for left, right in zip(full_values, forced_values, strict=True)) / (max(abs(item) for item in full_values) + epsilon_o)
            row_r[observable_id] = value
            maxima.append(value)
        x2 = max(abs(value) for value in _finite_series(primary, "cumulative_exchange_phi2"))
        x3 = max(abs(value) for value in _finite_series(primary, "cumulative_exchange_phi3"))
        xl = max(abs(value) for value in _finite_series(primary, "cumulative_exchange_longitudinal"))
        fraction = (x2 + x3) / (xl + x2 + x3 + epsilon_x)
        maxima.append(fraction)
        per_row[row_id] = {"R_PERP_OBSERVABLE": row_r, "F_EXCHANGE_PERP": fraction, "R_TRUNC_EQUATION_RESIDUAL": residual}
    maximum = max(maxima, default=0.0)
    materiality = packet["scientific_materiality_freeze"]
    material_gate = float(materiality["material_R_perp_gate"])
    dominated_gate = float(materiality["descendant_dominated_R_perp_gate"])
    if maximum >= dominated_gate:
        status = "DESCENDANT_DOMINATED_REGIME"
    elif maximum >= material_gate:
        status = "INTERMEDIATE_DESCENDANT_CONTRIBUTION"
    else:
        status = "DESCENDANTS_DYNAMICALLY_NECESSARY_QUANTITATIVELY_SMALL"
    sensitivity = {}
    for gate in materiality["threshold_sensitivity_values"]:
        if maximum >= dominated_gate:
            candidate = "DESCENDANT_DOMINATED_REGIME"
        elif maximum >= float(gate):
            candidate = "INTERMEDIATE_DESCENDANT_CONTRIBUTION"
        else:
            candidate = "DESCENDANTS_DYNAMICALLY_NECESSARY_QUANTITATIVELY_SMALL"
        sensitivity[str(gate)] = candidate
    return status, {"maximum_materiality_measure": maximum, "per_row": per_row, "threshold_sensitivity": sensitivity}


def classify_registered_result(
    freeze_packet: dict[str, Any],
    run_matrix: dict[str, Any],
    output_manifest: dict[str, Any],
    output_payloads: dict[str, dict[str, Any]],
    *,
    classifier_path: Path | None = None,
) -> dict[str, Any]:
    """Reconstruct v2 decisions from exact identities and raw registered outputs only."""
    try:
        _validate_freeze_bindings(freeze_packet, run_matrix, output_manifest, classifier_path)
        by_run, payload_by_run = _identity_index(run_matrix, output_manifest, output_payloads)
        controls = _control_audit(freeze_packet, by_run, payload_by_run)
        failures = _threshold_audit(freeze_packet, by_run, payload_by_run)
        convergence_failures, orders = _convergence_audit(freeze_packet, by_run, payload_by_run)
        deterministic_failures = _determinism_audit(by_run, payload_by_run)
        solver_failures = _solver_audit(freeze_packet, by_run, payload_by_run)
        for source in (convergence_failures, deterministic_failures, solver_failures):
            for row_id, diagnostics in source.items():
                failures.setdefault(row_id, []).extend(diagnostics)
        model_limited_rows: list[str] = []
        for row_id in freeze_packet["scientific_design_freeze"]["scientific_row_ids"]:
            primary = next(record for record in by_run.values() if record.get("scientific_row_id") == row_id and record.get("run_role") == "PRIMARY_FULL_MODEL")
            if _raw_scalar(payload_by_run[primary["run_id"]], "model_domain_margin") < 0.0:
                model_limited_rows.append(row_id)
        if failures:
            return {
                "classifier_id": CLASSIFIER_ID,
                "execution_status": "CLASSIFIED_BLOCKED",
                "robustness_status": "NUMERICALLY_BLOCKED",
                "descendant_significance_status": "NOT_EVALUATED_NUMERICAL_BLOCK",
                "scientific_claim_authorized": False,
                "numerically_blocked_rows": sorted(failures),
                "failure_diagnostics": {key: sorted(set(value)) for key, value in sorted(failures.items())},
                "observed_convergence_orders": orders,
            }
        if model_limited_rows:
            return {
                "classifier_id": CLASSIFIER_ID,
                "execution_status": "CLASSIFIED_BLOCKED",
                "robustness_status": "MODEL_DOMAIN_LIMITED",
                "descendant_significance_status": "NOT_EVALUATED_MODEL_DOMAIN_LIMIT",
                "scientific_claim_authorized": False,
                "model_domain_limited_rows": sorted(model_limited_rows),
                "observed_convergence_orders": orders,
            }
        materiality_status, materiality_evidence = _materiality(freeze_packet, by_run, payload_by_run)
        sensitivity_changed = len(set(materiality_evidence.get("threshold_sensitivity", {}).values())) > 1
        return {
            "classifier_id": CLASSIFIER_ID,
            "execution_status": "CLASSIFIED_PENDING_INDEPENDENT_RESULT_REVIEW",
            "robustness_status": "THRESHOLD_SENSITIVE" if sensitivity_changed else "BROADLY_ROBUST",
            "descendant_significance_status": materiality_status,
            "scientific_claim_authorized": False,
            "passing_scientific_row_ids": freeze_packet["scientific_design_freeze"]["scientific_row_ids"],
            "control_ids_reconstructed": sorted(controls),
            "observed_convergence_orders": orders,
            "materiality_evidence": materiality_evidence,
            "claim_ceiling": "candidate classification only; independent result review is required before any E-REPRO claim",
        }
    except ClassificationBlock as block:
        return _blocked(block.diagnostic, block.detail)
