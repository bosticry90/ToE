from __future__ import annotations

import argparse
import copy
import hashlib
import json
import math
from pathlib import Path
from typing import Any, Callable

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import scalar_multi_background_robustness_reports as contract


REPO_ROOT = find_repo_root(Path(__file__))
CALCULATION_ID = contract.CALCULATION_ID
CAPTURED_AT_UTC = contract.CAPTURED_AT_UTC
GUARDRAIL_RELATIVE_PATH = contract.GUARDRAIL_REPORT_RELATIVE_PATH
GUARDRAIL_SHA256 = contract.EXPECTED_GUARDRAIL_SHA256
SCRIPT_RELATIVE_PATH = contract.CALCULATION_SCRIPT_RELATIVE_PATH
TEST_RELATIVE_PATH = contract.CALCULATION_TEST_RELATIVE_PATH
OUTPUT_RELATIVE_PATH = contract.CALCULATION_OUTPUT_RELATIVE_PATH
MANIFEST_RELATIVE_PATH = contract.CALCULATION_MANIFEST_RELATIVE_PATH
EXECUTION_REPORT_RELATIVE_PATH = contract.EXECUTION_REPORT_RELATIVE_PATH
PREFLIGHT_DIAGNOSTIC_RELATIVE_PATH = contract.PREFLIGHT_DIAGNOSTIC_RELATIVE_PATH
RESULT_SCHEMA_ID = contract.CALCULATION_RESULT_SCHEMA_ID
MANIFEST_SCHEMA_ID = contract.CALCULATION_MANIFEST_SCHEMA_ID
PREFLIGHT_DIAGNOSTIC_SCHEMA_ID = contract.PREFLIGHT_DIAGNOSTIC_SCHEMA_ID
RESULT_REVIEW_TARGET = contract.REVIEW_TARGET
EVIDENCE_FAILURE_TARGET = contract.EVIDENCE_FAILURE_TARGET
UNIT_LEDGER_TARGET = contract.UNIT_LEDGER_TARGET
EXECUTION_COMMAND = contract.CALCULATION_EXECUTION_COMMAND

OUTPUT_PATH = REPO_ROOT / OUTPUT_RELATIVE_PATH
MANIFEST_PATH = REPO_ROOT / MANIFEST_RELATIVE_PATH
PREFLIGHT_DIAGNOSTIC_PATH = REPO_ROOT / PREFLIGHT_DIAGNOSTIC_RELATIVE_PATH

JSON_ARTIFACT_ROLES = {
    "guardrail",
    "calculation_result",
    "calculation_manifest",
    "execution_report",
    "independent_review",
}
COMPACT_JSON_ROLES = {"calculation_result", "calculation_manifest"}
EXPECTED_ARTIFACT_ROLES = (
    "guardrail",
    "calculation_script",
    "calculation_result",
    "calculation_manifest",
    "execution_report",
    "independent_review",
)
ALLOWED_FAMILY_ENVELOPES = (
    "dimensionless_second_order_convergence_p_min",
    "within_background_dimensionless_off_shell_relative_identity_error",
)


class PreflightError(ValueError):
    """The immutable evidence family failed before synthesis could execute."""

    def __init__(self, code: str, message: str) -> None:
        super().__init__(message)
        self.code = code
        self.error_codes = [code]


class SynthesisStateError(ValueError):
    """An in-memory synthesis state is malformed after successful preflight."""


def canonical_json_bytes(payload: Any) -> bytes:
    return contract.canonical_json_bytes(payload)


def report_json_bytes(payload: Any) -> bytes:
    return contract.report_json_bytes(payload)


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _reject_nonfinite_constant(value: str) -> None:
    raise ValueError(f"nonfinite JSON constant is forbidden: {value}")


def _reject_duplicate_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key is forbidden: {key}")
        result[key] = value
    return result


def strict_json_load(path: Path) -> dict[str, Any]:
    raw = path.read_bytes()
    if raw.startswith(b"\xef\xbb\xbf"):
        raise ValueError("UTF-8 BOM is forbidden")
    if b"\r" in raw:
        raise ValueError("CR or CRLF newlines are forbidden")
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise ValueError("artifact is not valid UTF-8") from exc
    payload = json.loads(
        text,
        parse_constant=_reject_nonfinite_constant,
        object_pairs_hook=_reject_duplicate_keys,
    )
    if not isinstance(payload, dict):
        raise ValueError("JSON root must be an object")
    return payload


def _relative_path(path: Path, repo_root: Path) -> str:
    try:
        return path.resolve().relative_to(repo_root.resolve()).as_posix()
    except ValueError:
        return path.name


def _preflight_error(code: str, message: str) -> PreflightError:
    return PreflightError(code, message)


def _require(condition: bool, code: str, message: str) -> None:
    if not condition:
        raise _preflight_error(code, message)


def _canonical_bytes_for_role(role: str, payload: dict[str, Any]) -> bytes:
    return (
        canonical_json_bytes(payload)
        if role in COMPACT_JSON_ROLES
        else report_json_bytes(payload)
    )


def _artifact_by_role(chain: dict[str, Any], role: str) -> dict[str, str]:
    matches = [
        item for item in chain["artifacts"] if item["artifact_role"] == role
    ]
    if len(matches) != 1:
        raise SynthesisStateError(
            f"chain {chain.get('chain_id')} has {len(matches)} {role} artifacts"
        )
    return matches[0]


def load_guardrail(
    *, repo_root: Path | None = None
) -> tuple[dict[str, Any], str]:
    root = REPO_ROOT if repo_root is None else repo_root
    path = root / GUARDRAIL_RELATIVE_PATH
    if not path.is_file():
        raise _preflight_error(
            "guardrail_missing", f"guardrail missing: {GUARDRAIL_RELATIVE_PATH}"
        )
    actual_hash = sha256_file(path)
    _require(
        actual_hash == GUARDRAIL_SHA256,
        "guardrail_hash_mismatch",
        f"guardrail hash mismatch: {GUARDRAIL_RELATIVE_PATH}",
    )
    try:
        payload = strict_json_load(path)
    except ValueError as exc:
        raise _preflight_error(
            "guardrail_invalid_json", f"guardrail JSON invalid: {exc}"
        ) from exc
    _require(
        path.read_bytes() == report_json_bytes(payload),
        "guardrail_noncanonical_bytes",
        "guardrail does not use the frozen canonical report serialization",
    )
    _require(
        payload.get("schema_id") == contract.PACKET_SCHEMA_ID,
        "guardrail_schema_mismatch",
        "guardrail schema differs from the frozen packet schema",
    )
    try:
        contract.validate_guardrail_payload(payload)
    except ValueError as exc:
        raise _preflight_error(
            "guardrail_contract_mismatch", f"guardrail contract mismatch: {exc}"
        ) from exc
    return payload, actual_hash


def _validate_json_schema(
    role: str,
    artifact: dict[str, str],
    payload: dict[str, Any],
) -> None:
    schema = payload.get("schema_id")
    _require(
        isinstance(schema, str) and bool(schema),
        "source_schema_missing",
        f"source schema missing: {artifact['path']}",
    )
    if role in {"guardrail", "execution_report", "independent_review"}:
        expected = Path(artifact["path"]).stem
    elif role == "calculation_result":
        expected = f"{payload.get('calculation_id')}-RESULT"
    elif role == "calculation_manifest":
        expected = f"{payload.get('calculation_id')}-MANIFEST"
    else:
        return
    _require(
        schema == expected,
        "source_schema_mismatch",
        f"source schema mismatch: {artifact['path']}",
    )


def _validate_source_links(
    chain: dict[str, Any], payloads: dict[str, dict[str, Any]]
) -> None:
    chain_id = chain["chain_id"]
    result = payloads["calculation_result"]
    manifest = payloads["calculation_manifest"]
    execution = payloads["execution_report"]
    review = payloads["independent_review"]
    result_artifact = _artifact_by_role(chain, "calculation_result")
    manifest_artifact = _artifact_by_role(chain, "calculation_manifest")
    guardrail_artifact = _artifact_by_role(chain, "guardrail")
    script_artifact = _artifact_by_role(chain, "calculation_script")

    _require(
        result.get("result_review")
        == {"status": "pending", "target": chain["review_target"]},
        "source_result_review_link_mismatch",
        f"source result review link mismatch: {chain_id}",
    )
    _require(
        manifest.get("calculation_id") == result.get("calculation_id")
        and manifest.get("guardrail_path") == guardrail_artifact["path"]
        and manifest.get("guardrail_sha256") == guardrail_artifact["sha256"]
        and manifest.get("script_path") == script_artifact["path"]
        and manifest.get("script_sha256") == script_artifact["sha256"]
        and manifest.get("output_path") == result_artifact["path"]
        and manifest.get("output_sha256") == result_artifact["sha256"]
        and manifest.get("result_review_target") == chain["review_target"],
        "source_manifest_link_mismatch",
        f"source manifest link mismatch: {chain_id}",
    )
    _require(
        execution.get("calculation_id") == result.get("calculation_id")
        and execution.get("calculation_output_path") == result_artifact["path"]
        and execution.get("calculation_output_sha256")
        == result_artifact["sha256"]
        and execution.get("calculation_manifest_path")
        == manifest_artifact["path"]
        and execution.get("calculation_manifest_sha256")
        == manifest_artifact["sha256"]
        and execution.get("guardrail_sha256") == guardrail_artifact["sha256"]
        and (
            execution.get("script_sha256", execution.get("calculation_script_sha256"))
            == script_artifact["sha256"]
        )
        and execution.get("selected_next_target") == chain["review_target"]
        and execution.get("all_thresholds_passed") is True,
        "source_execution_link_mismatch",
        f"source execution link mismatch: {chain_id}",
    )
    verification = review.get("verification")
    claim = review.get("claim")
    _require(
        review.get("consumed_target") == chain["review_target"]
        and review.get("status") == chain["review_status"]
        and isinstance(verification, dict)
        and verification.get("accepted") is True
        and verification.get("primary_claim_label") == "E-REPRO"
        and verification.get("mismatch_codes") == []
        and isinstance(claim, dict)
        and claim.get("claim_ceiling_level") == 3
        and claim.get("primary_label") == "E-REPRO",
        "source_review_acceptance_mismatch",
        f"source review is not an accepted Level 3 E-REPRO: {chain_id}",
    )
    actual_hashes = verification.get("actual_hashes")
    expected_hashes = verification.get("expected_hashes")
    _require(
        isinstance(actual_hashes, dict) and isinstance(expected_hashes, dict),
        "source_review_hash_links_missing",
        f"source review hash links missing: {chain_id}",
    )
    role_to_hash_key = {
        "guardrail": "guardrail_sha256",
        "calculation_script": "script_sha256",
        "calculation_result": "output_sha256",
        "calculation_manifest": "manifest_sha256",
        "execution_report": "execution_report_sha256",
    }
    for role, hash_key in role_to_hash_key.items():
        expected_hash = _artifact_by_role(chain, role)["sha256"]
        _require(
            actual_hashes.get(hash_key) == expected_hash
            and expected_hashes.get(hash_key) == expected_hash,
            "source_review_hash_link_mismatch",
            f"source review hash link mismatch: {chain_id}:{role}",
        )
    if chain_id == "warped_2plus1":
        reproduction = verification.get("fresh_subprocess_reproduction")
        _require(
            isinstance(reproduction, dict)
            and reproduction.get("run_count") == 2
            and reproduction.get("both_runs_byte_identical") is True
            and reproduction.get("fresh_runs_match_repository_artifacts") is True,
            "source_fresh_reproduction_mismatch",
            "warped source review fresh-subprocess evidence differs",
        )
    else:
        _require(
            "fresh_subprocess_reproduction" not in verification,
            "legacy_reproduction_strength_changed",
            f"legacy review reproduction strength changed: {chain_id}",
        )


def preflight_source_family(
    *, repo_root: Path | None = None
) -> dict[str, Any]:
    """Verify immutable inputs before any canonical execution artifact exists."""

    root = REPO_ROOT if repo_root is None else repo_root
    guardrail, guardrail_sha256 = load_guardrail(repo_root=root)
    chains = guardrail.get("source_chains")
    _require(
        isinstance(chains, list) and len(chains) == 4,
        "source_chain_count_mismatch",
        "guardrail must bind exactly four source chains",
    )
    all_artifacts = [item for chain in chains for item in chain["artifacts"]]
    _require(
        len(all_artifacts) == 24
        and len({item["path"] for item in all_artifacts}) == 24,
        "source_artifact_inventory_mismatch",
        "guardrail must bind exactly twenty-four unique source artifacts",
    )

    loaded_chains: list[dict[str, Any]] = []
    for chain in chains:
        roles = [item["artifact_role"] for item in chain["artifacts"]]
        _require(
            tuple(roles) == EXPECTED_ARTIFACT_ROLES,
            "source_artifact_role_mismatch",
            f"source artifact roles differ: {chain['chain_id']}",
        )
        payloads: dict[str, dict[str, Any]] = {}
        verified_artifacts: list[dict[str, Any]] = []
        for artifact in chain["artifacts"]:
            role = artifact["artifact_role"]
            path = root / artifact["path"]
            _require(
                path.is_file(),
                "source_artifact_missing",
                f"source artifact missing: {artifact['path']}",
            )
            actual_hash = sha256_file(path)
            _require(
                actual_hash == artifact["sha256"],
                "source_artifact_hash_mismatch",
                f"source artifact hash mismatch: {artifact['path']}",
            )
            raw = path.read_bytes()
            _require(
                not raw.startswith(b"\xef\xbb\xbf") and b"\r" not in raw,
                "source_artifact_encoding_mismatch",
                f"source artifact encoding/newline mismatch: {artifact['path']}",
            )
            if role in JSON_ARTIFACT_ROLES:
                try:
                    payload = strict_json_load(path)
                except ValueError as exc:
                    raise _preflight_error(
                        "source_invalid_json",
                        f"source JSON invalid: {artifact['path']}: {exc}",
                    ) from exc
                _require(
                    raw == _canonical_bytes_for_role(role, payload),
                    "source_noncanonical_json",
                    f"source JSON bytes are noncanonical: {artifact['path']}",
                )
                _validate_json_schema(role, artifact, payload)
                payloads[role] = payload
            else:
                try:
                    raw.decode("utf-8")
                except UnicodeDecodeError as exc:
                    raise _preflight_error(
                        "source_script_invalid_utf8",
                        f"source script is not UTF-8: {artifact['path']}",
                    ) from exc
            verified_artifacts.append(
                {
                    **copy.deepcopy(artifact),
                    "actual_sha256": actual_hash,
                    "verified": True,
                }
            )
        _validate_source_links(chain, payloads)
        result = payloads["calculation_result"]
        checks = result.get("threshold_checks")
        _require(
            isinstance(checks, dict)
            and list(sorted(checks)) == list(sorted(chain["upstream_gate_ids"]))
            and len(checks) == chain["upstream_decision_count"]
            and all(value is True for value in checks.values())
            and result.get("all_thresholds_passed") is True,
            "source_gate_inventory_or_status_mismatch",
            f"source threshold inventory/status mismatch: {chain['chain_id']}",
        )
        _require(
            result.get("parameters", {}).get("resolutions_N")
            == chain["grid_schedule"],
            "source_grid_schedule_mismatch",
            f"source grid schedule mismatch: {chain['chain_id']}",
        )
        loaded_chains.append(
            {
                "contract": copy.deepcopy(chain),
                "artifacts": verified_artifacts,
                "payloads": payloads,
            }
        )

    compendium_contract = guardrail["equation_compendium_boundary"]
    compendium_path = root / compendium_contract["path"]
    _require(
        compendium_path.is_file()
        and sha256_file(compendium_path) == compendium_contract["sha256"],
        "equation_compendium_hash_mismatch",
        "equation compendium boundary hash mismatch",
    )
    return {
        "repo_root": root,
        "guardrail": guardrail,
        "guardrail_sha256": guardrail_sha256,
        "chains": loaded_chains,
        "preflight_verified": True,
    }


def _typed_check(
    *,
    contract_status: str,
    status: str,
    value: bool | int | float | None,
    source_gate_ids: list[str] | None = None,
    reason: str | None = None,
) -> dict[str, Any]:
    row: dict[str, Any] = {
        "contract_status": contract_status,
        "status": status,
        "value": value,
        "source_gate_ids": [] if source_gate_ids is None else source_gate_ids,
    }
    if reason is not None:
        row["reason"] = reason
    return row


def _applicable_check(
    contract_status: str,
    passed: bool,
    *,
    source_gate_ids: list[str],
    value: bool | int | float = True,
) -> dict[str, Any]:
    return _typed_check(
        contract_status=contract_status,
        status="passed" if passed else "failed",
        value=value,
        source_gate_ids=source_gate_ids,
    )


def _not_applicable_check(
    contract_status: str, *, reason: str
) -> dict[str, Any]:
    return _typed_check(
        contract_status=contract_status,
        status="not_applicable",
        value=None,
        reason=reason,
    )


def _baseline_check(contract_status: str) -> dict[str, Any]:
    return _typed_check(
        contract_status=contract_status,
        status="baseline_not_recovery_test",
        value=None,
        reason="Minkowski is the flat specialization baseline, not a limit test",
    )


def _local_check_row(
    chain_id: str,
    checks: dict[str, dict[str, Any]],
) -> dict[str, Any]:
    passed = all(
        check["status"] in {
            "passed",
            "not_applicable",
            "baseline_not_recovery_test",
        }
        and (
            check["value"] is None
            if check["status"] != "passed"
            else check["value"] is not None
        )
        for check in checks.values()
    )
    ordered_checks = {key: checks[key] for key in sorted(checks)}
    return {"chain_id": chain_id, "checks": ordered_checks, "passed": passed}


def _base_background_row(
    chain: dict[str, Any],
    *,
    finest_grid_shape: list[int],
    actual_geometry_evidence: dict[str, Any],
) -> dict[str, Any]:
    return {
        "chain_id": chain["chain_id"],
        "spacetime_dimension": chain["spacetime_dimension"],
        "divergence_component_count": chain["divergence_component_count"],
        "geometry_class": chain["geometry_class"],
        "connection_class": chain["connection_class"],
        "curvature_class": chain["curvature_class"],
        "grid_schedule": copy.deepcopy(chain["grid_schedule"]),
        "grid_meaning": chain["grid_meaning"],
        "finest_grid_shape": finest_grid_shape,
        "profile_coverage": copy.deepcopy(chain["profile_coverage"]),
        "actual_geometry_evidence": actual_geometry_evidence,
    }


def _profile_row(
    chain_id: str,
    profile_row_id: str,
    p_min: float,
    off_shell_error: float,
    p_source_field: str,
    error_source_field: str,
) -> dict[str, Any]:
    return {
        "chain_id": chain_id,
        "profile_row_id": profile_row_id,
        "p_min": p_min,
        "off_shell_relative_identity_error": off_shell_error,
        "p_source_field": p_source_field,
        "error_source_field": error_source_field,
        "metric_kind": "within_background_dimensionless_off_shell_relative_identity_error",
    }


def _on_shell_row(
    chain: dict[str, Any],
    *,
    passed: bool,
    relative_error_against_zero_formed: bool,
    evidence: dict[str, Any],
) -> dict[str, Any]:
    return {
        "chain_id": chain["chain_id"],
        "policy": copy.deepcopy(chain["on_shell_policy"]),
        "passed": passed,
        "relative_error_against_zero_formed": (
            relative_error_against_zero_formed
        ),
        "source_evidence": evidence,
    }


def _control(
    control_instance_id: str,
    chain_id: str,
    mechanism_class: str,
    *,
    detected: bool,
    source_evidence: dict[str, Any],
    adjudication_role: str,
) -> dict[str, Any]:
    return {
        "control_instance_id": control_instance_id,
        "chain_id": chain_id,
        "mechanism_class": mechanism_class,
        "detected": detected,
        "source_evidence": source_evidence,
        "adjudication_role": adjudication_role,
    }


def _adapt_minkowski(bundle: dict[str, Any]) -> dict[str, Any]:
    chain = bundle["contract"]
    guardrail = bundle["payloads"]["guardrail"]
    result = bundle["payloads"]["calculation_result"]
    review = bundle["payloads"]["independent_review"]
    checks = result["threshold_checks"]
    evidence = result["threshold_evidence"]
    assumptions = guardrail["assumptions"]
    if "fixed 1+1-dimensional Minkowski spacetime" not in assumptions:
        raise SynthesisStateError("Minkowski dimensional assumption missing")
    identity = result["mathematical_convention"]["identity"]
    if identity != "partial_mu T^{mu nu} = E_phi partial^nu phi":
        raise SynthesisStateError("Minkowski identity convention differs")
    components = set(
        result["off_shell"]["resolution_aggregates"][-1]["divergence_norms"]
    ) - {"combined"}
    if components != {"nu_0", "nu_1"}:
        raise SynthesisStateError("Minkowski divergence components differ")
    profile = _profile_row(
        chain["chain_id"],
        "minkowski_off_shell",
        evidence["minimum_observed_two_finest_convergence_order"],
        evidence["finest_combined_off_shell_relative_error"],
        "threshold_evidence.minimum_observed_two_finest_convergence_order",
        "threshold_evidence.finest_combined_off_shell_relative_error",
    )
    local_contract = contract.LOCAL_CHECK_LEDGER[0]
    local = _local_check_row(
        chain["chain_id"],
        {
            "analytic_reference": _applicable_check(
                local_contract["analytic_reference"],
                checks["exact_coefficient_error_at_most_1e_12"],
                source_gate_ids=["exact_coefficient_error_at_most_1e_12"],
                value=evidence["exact_coefficient_absolute_error"],
            ),
            "metric_compatibility": _not_applicable_check(
                local_contract["metric_compatibility"],
                reason="exact Cartesian Minkowski metric",
            ),
            "curvature_route": _not_applicable_check(
                local_contract["curvature_route"],
                reason="flat Cartesian baseline",
            ),
            "patch_or_geometry_safety": _not_applicable_check(
                local_contract["patch_or_geometry_safety"],
                reason="global Cartesian chart",
            ),
            "flat_limit": _baseline_check(local_contract["flat_limit"]),
            "on_off_shell_witness": _applicable_check(
                local_contract["on_off_shell_witness"],
                checks["finest_off_shell_divergence_over_100_times_on_shell"],
                source_gate_ids=[
                    "finest_off_shell_divergence_over_100_times_on_shell"
                ],
                value=evidence["finest_off_to_on_divergence_norm_ratio"],
            ),
        },
    )
    on_shell = result["on_shell"]
    on_shell_row = _on_shell_row(
        chain,
        passed=(
            checks["finest_off_shell_divergence_over_100_times_on_shell"]
            and on_shell["relative_error_against_zero_formed"] is False
        ),
        relative_error_against_zero_formed=on_shell[
            "relative_error_against_zero_formed"
        ],
        evidence={
            "finest_off_to_on_divergence_norm_ratio": evidence[
                "finest_off_to_on_divergence_norm_ratio"
            ]
        },
    )
    control_row = _control(
        "minkowski_off_shell_nonconservation",
        chain["chain_id"],
        "off_shell_nonconservation",
        detected=checks[
            "finest_off_shell_divergence_over_100_times_on_shell"
        ],
        source_evidence={
            "off_to_on_divergence_norm_ratio": evidence[
                "finest_off_to_on_divergence_norm_ratio"
            ]
        },
        adjudication_role="frozen_source_threshold",
    )
    return {
        "background": _base_background_row(
            chain,
            finest_grid_shape=[chain["grid_schedule"][-1]],
            actual_geometry_evidence={
                "assumption": "fixed 1+1-dimensional Minkowski spacetime",
                "connection_component_count": 0,
                "curvature": 0,
                "divergence_components": sorted(components),
            },
        ),
        "profiles": [profile],
        "on_shell": on_shell_row,
        "local": local,
        "controls": [control_row],
        "identity_signature": "positive_residual_times_raised_gradient_flat_specialization",
        "review_acceptance": {
            "accepted": review["verification"]["accepted"],
            "claim_ceiling_level": review["claim"]["claim_ceiling_level"],
            "primary_label": review["claim"]["primary_label"],
        },
    }


def _adapt_conformal(bundle: dict[str, Any]) -> dict[str, Any]:
    chain = bundle["contract"]
    guardrail = bundle["payloads"]["guardrail"]
    result = bundle["payloads"]["calculation_result"]
    review = bundle["payloads"]["independent_review"]
    checks = result["threshold_checks"]
    evidence = result["threshold_evidence"]
    geometry = result["background_geometry"]
    if guardrail["inputs"]["dimension"] != 2:
        raise SynthesisStateError("conformal dimension differs")
    if (
        geometry["scalar_curvature"] != 0.0
        or geometry["nonzero_connection_component_count"] <= 0
        or geometry["background_geometry_classification"]
        != "locally_flat_nontrivial_conformal_connection"
    ):
        raise SynthesisStateError("conformal geometry classification differs")
    if result["mathematical_convention"]["identity"] != (
        "nabla_mu T^{mu nu} = E_phi nabla^nu phi"
    ):
        raise SynthesisStateError("conformal identity convention differs")
    profile = _profile_row(
        chain["chain_id"],
        "conformal_off_shell",
        evidence["minimum_observed_two_finest_convergence_order"],
        evidence["finest_combined_off_shell_relative_error"],
        "threshold_evidence.minimum_observed_two_finest_convergence_order",
        "threshold_evidence.finest_combined_off_shell_relative_error",
    )
    local_contract = contract.LOCAL_CHECK_LEDGER[1]
    local = _local_check_row(
        chain["chain_id"],
        {
            "analytic_reference": _applicable_check(
                local_contract["analytic_reference"],
                checks["exact_coefficient_error_at_most_1e_12"],
                source_gate_ids=["exact_coefficient_error_at_most_1e_12"],
                value=evidence["exact_coefficient_absolute_error"],
            ),
            "metric_compatibility": _applicable_check(
                local_contract["metric_compatibility"],
                checks["metric_compatibility_error_at_most_1e_12"],
                source_gate_ids=["metric_compatibility_error_at_most_1e_12"],
                value=evidence["metric_compatibility_max_absolute_error"],
            ),
            "curvature_route": _not_applicable_check(
                local_contract["curvature_route"],
                reason="reviewed locally flat classification",
            ),
            "patch_or_geometry_safety": _applicable_check(
                local_contract["patch_or_geometry_safety"],
                geometry["background_geometry_classification"]
                == "locally_flat_nontrivial_conformal_connection",
                source_gate_ids=[],
            ),
            "flat_limit": _applicable_check(
                local_contract["flat_limit"],
                checks["flat_limit_discrepancy_at_most_1e_12"],
                source_gate_ids=["flat_limit_discrepancy_at_most_1e_12"],
                value=evidence["flat_limit_max_absolute_discrepancy"],
            ),
            "on_off_shell_witness": _applicable_check(
                local_contract["on_off_shell_witness"],
                checks["finest_off_shell_divergence_over_100_times_on_shell"],
                source_gate_ids=[
                    "finest_off_shell_divergence_over_100_times_on_shell"
                ],
                value=evidence["finest_off_to_on_divergence_norm_ratio"],
            ),
        },
    )
    on_shell = result["on_shell"]
    on_shell_row = _on_shell_row(
        chain,
        passed=(
            checks["finest_off_shell_divergence_over_100_times_on_shell"]
            and on_shell["relative_error_against_zero_formed"] is False
        ),
        relative_error_against_zero_formed=on_shell[
            "relative_error_against_zero_formed"
        ],
        evidence={
            "finest_off_to_on_divergence_norm_ratio": evidence[
                "finest_off_to_on_divergence_norm_ratio"
            ]
        },
    )
    diagnostic = result["naive_partial_divergence_negative_control"]
    control_row = _control(
        "conformal_naive_partial",
        chain["chain_id"],
        "naive_partial_divergence",
        detected=diagnostic["failure_detected"],
        source_evidence={
            "finest_on_shell_naive_to_covariant_error_ratio": diagnostic[
                "finest_on_shell_naive_to_covariant_error_ratio"
            ],
            "diagnostic_only_not_guardrail_threshold": diagnostic[
                "diagnostic_only_not_guardrail_threshold"
            ],
        },
        adjudication_role="source_diagnostic_without_new_threshold",
    )
    return {
        "background": _base_background_row(
            chain,
            finest_grid_shape=[chain["grid_schedule"][-1]],
            actual_geometry_evidence={
                "source_classification": geometry[
                    "background_geometry_classification"
                ],
                "connection_component_count": geometry[
                    "nonzero_connection_component_count"
                ],
                "scalar_curvature": geometry["scalar_curvature"],
                "riemann_tensor_max_absolute_component": geometry[
                    "riemann_tensor_max_absolute_component"
                ],
            },
        ),
        "profiles": [profile],
        "on_shell": on_shell_row,
        "local": local,
        "controls": [control_row],
        "identity_signature": "positive_residual_times_raised_gradient_covariant",
        "review_acceptance": {
            "accepted": review["verification"]["accepted"],
            "claim_ceiling_level": review["claim"]["claim_ceiling_level"],
            "primary_label": review["claim"]["primary_label"],
        },
    }


def _adapt_de_sitter(bundle: dict[str, Any]) -> dict[str, Any]:
    chain = bundle["contract"]
    guardrail = bundle["payloads"]["guardrail"]
    result = bundle["payloads"]["calculation_result"]
    review = bundle["payloads"]["independent_review"]
    checks = result["threshold_checks"]
    evidence = result["threshold_evidence"]
    geometry = result["curvature_verification"]
    safety = result["patch_domain_safety"]
    if (
        guardrail["inputs"]["dimension"] != 2
        or guardrail["background_geometry"]["classification"]
        != "fixed_1_plus_1_de_sitter_conformal_patch"
        or result["background_geometry_classification"]
        != "fixed_nonzero_curvature_1plus1_de_sitter_patch"
    ):
        raise SynthesisStateError("de Sitter geometry classification differs")
    if result["mathematical_convention"]["identity"] != (
        "nabla_mu T^{mu nu} = E_phi nabla^nu phi"
    ):
        raise SynthesisStateError("de Sitter identity convention differs")
    profile = _profile_row(
        chain["chain_id"],
        "de_sitter_off_shell",
        evidence["minimum_observed_two_finest_convergence_order"],
        evidence["finest_combined_off_shell_relative_error"],
        "threshold_evidence.minimum_observed_two_finest_convergence_order",
        "threshold_evidence.finest_combined_off_shell_relative_error",
    )
    local_contract = contract.LOCAL_CHECK_LEDGER[2]
    local = _local_check_row(
        chain["chain_id"],
        {
            "analytic_reference": _applicable_check(
                local_contract["analytic_reference"],
                checks["exact_coefficient_error_at_most_1e_12"],
                source_gate_ids=["exact_coefficient_error_at_most_1e_12"],
                value=evidence["exact_coefficient_absolute_error"],
            ),
            "metric_compatibility": _applicable_check(
                local_contract["metric_compatibility"],
                checks["metric_compatibility_error_at_most_1e_12"],
                source_gate_ids=["metric_compatibility_error_at_most_1e_12"],
                value=evidence["metric_compatibility_max_absolute_error"],
            ),
            "curvature_route": _applicable_check(
                local_contract["curvature_route"],
                checks["absolute_scalar_curvature_at_least_0_05"]
                and checks["curvature_route_discrepancy_at_most_1e_12"],
                source_gate_ids=[
                    "absolute_scalar_curvature_at_least_0_05",
                    "curvature_route_discrepancy_at_most_1e_12",
                ],
                value=geometry["maximum_route_agreement_absolute_error"],
            ),
            "patch_or_geometry_safety": _applicable_check(
                local_contract["patch_or_geometry_safety"],
                safety["strictly_inside_coordinate_patch"],
                source_gate_ids=[],
                value=safety["minimum_coordinate_distance_to_patch_singularity_over_domain"],
            ),
            "flat_limit": _applicable_check(
                local_contract["flat_limit"],
                checks["flat_limit_discrepancy_at_most_1e_12"],
                source_gate_ids=["flat_limit_discrepancy_at_most_1e_12"],
                value=evidence["flat_limit_max_absolute_discrepancy"],
            ),
            "on_off_shell_witness": _applicable_check(
                local_contract["on_off_shell_witness"],
                checks["finest_off_shell_divergence_over_100_times_on_shell"],
                source_gate_ids=[
                    "finest_off_shell_divergence_over_100_times_on_shell"
                ],
                value=evidence["finest_off_to_on_divergence_norm_ratio"],
            ),
        },
    )
    on_shell = result["on_shell"]
    on_shell_row = _on_shell_row(
        chain,
        passed=(
            checks["finest_off_shell_divergence_over_100_times_on_shell"]
            and on_shell["relative_error_against_zero_formed"] is False
        ),
        relative_error_against_zero_formed=on_shell[
            "relative_error_against_zero_formed"
        ],
        evidence={
            "finest_off_to_on_divergence_norm_ratio": evidence[
                "finest_off_to_on_divergence_norm_ratio"
            ]
        },
    )
    negatives = result["negative_controls"]
    controls = [
        _control(
            "de_sitter_naive_partial",
            chain["chain_id"],
            "naive_partial_divergence",
            detected=negatives["naive_partial_divergence"]["failure_detected"]
            and checks["naive_partial_divergence_error_ratio_at_least_100"],
            source_evidence={
                "finest_on_shell_error_ratio": negatives[
                    "naive_partial_divergence"
                ]["finest_on_shell_error_ratio"]
            },
            adjudication_role="frozen_source_threshold",
        ),
        _control(
            "de_sitter_frozen_connection",
            chain["chain_id"],
            "inconsistent_connection",
            detected=negatives["inconsistent_frozen_connection"][
                "failure_detected"
            ]
            and checks[
                "inconsistent_frozen_connection_error_ratio_at_least_50"
            ],
            source_evidence={
                "minimum_finest_on_off_error_ratio": negatives[
                    "inconsistent_frozen_connection"
                ]["minimum_finest_on_off_error_ratio"]
            },
            adjudication_role="frozen_source_threshold",
        ),
        _control(
            "de_sitter_curvature_omission",
            chain["chain_id"],
            "curvature_derivative_omission",
            detected=negatives["curvature_derivative_omission"][
                "failure_detected"
            ]
            and checks["curvature_omission_discrepancy_at_least_0_04"],
            source_evidence={
                "minimum_absolute_discrepancy_from_correct_route": negatives[
                    "curvature_derivative_omission"
                ]["minimum_absolute_discrepancy_from_correct_route"]
            },
            adjudication_role="frozen_source_threshold",
        ),
    ]
    return {
        "background": _base_background_row(
            chain,
            finest_grid_shape=[chain["grid_schedule"][-1]],
            actual_geometry_evidence={
                "source_classification": result[
                    "background_geometry_classification"
                ],
                "scalar_curvature_expected": geometry[
                    "scalar_curvature_expected"
                ],
                "scalar_curvature_measured": geometry[
                    "scalar_curvature_measured"
                ],
                "strictly_inside_coordinate_patch": safety[
                    "strictly_inside_coordinate_patch"
                ],
            },
        ),
        "profiles": [profile],
        "on_shell": on_shell_row,
        "local": local,
        "controls": controls,
        "identity_signature": "positive_residual_times_raised_gradient_covariant",
        "review_acceptance": {
            "accepted": review["verification"]["accepted"],
            "claim_ceiling_level": review["claim"]["claim_ceiling_level"],
            "primary_label": review["claim"]["primary_label"],
        },
    }


def _adapt_warped(bundle: dict[str, Any]) -> dict[str, Any]:
    chain = bundle["contract"]
    guardrail = bundle["payloads"]["guardrail"]
    result = bundle["payloads"]["calculation_result"]
    review = bundle["payloads"]["independent_review"]
    checks = result["threshold_checks"]
    evidence = result["threshold_evidence"]
    geometry = result["geometry_verification"]
    safety = result["geometry_safety_verification"]
    if (
        guardrail["inputs"]["spacetime_dimension"] != 3
        or result["spacetime_dimension"] != 3
        or result["background_geometry_classification"]
        != "fixed_nonzero_spatially_varying_curvature_2plus1_warped_periodic_background"
    ):
        raise SynthesisStateError("warped geometry classification differs")
    if result["mathematical_convention"]["identity"] != (
        "nabla_mu T^{mu nu}=E_phi*nabla^nu phi"
    ):
        raise SynthesisStateError("warped identity convention differs")
    profiles = [
        _profile_row(
            chain["chain_id"],
            "warped_x_off_shell",
            evidence["minimum_two_finest_x_mode_convergence_order"],
            evidence["finest_x_mode_combined_relative_identity_error"],
            "threshold_evidence.minimum_two_finest_x_mode_convergence_order",
            "threshold_evidence.finest_x_mode_combined_relative_identity_error",
        ),
        _profile_row(
            chain["chain_id"],
            "warped_y_off_shell",
            evidence["minimum_two_finest_y_mode_convergence_order"],
            evidence["finest_y_mode_combined_relative_identity_error"],
            "threshold_evidence.minimum_two_finest_y_mode_convergence_order",
            "threshold_evidence.finest_y_mode_combined_relative_identity_error",
        ),
    ]
    local_contract = contract.LOCAL_CHECK_LEDGER[3]
    local = _local_check_row(
        chain["chain_id"],
        {
            "analytic_reference": _applicable_check(
                local_contract["analytic_reference"],
                checks["maximum_analytic_profile_residual_reference_error"],
                source_gate_ids=[
                    "maximum_analytic_profile_residual_reference_error"
                ],
                value=evidence[
                    "maximum_analytic_profile_residual_reference_error"
                ],
            ),
            "metric_compatibility": _applicable_check(
                local_contract["metric_compatibility"],
                checks["maximum_metric_compatibility_absolute_error"],
                source_gate_ids=[
                    "maximum_metric_compatibility_absolute_error"
                ],
                value=evidence["maximum_metric_compatibility_absolute_error"],
            ),
            "curvature_route": _applicable_check(
                local_contract["curvature_route"],
                checks["maximum_curvature_route_absolute_discrepancy"]
                and checks["minimum_curvature_peak_absolute_value"]
                and checks["minimum_curvature_peak_to_peak_variation"],
                source_gate_ids=[
                    "maximum_curvature_route_absolute_discrepancy",
                    "minimum_curvature_peak_absolute_value",
                    "minimum_curvature_peak_to_peak_variation",
                ],
                value=geometry[
                    "maximum_curvature_route_absolute_discrepancy"
                ],
            ),
            "patch_or_geometry_safety": _applicable_check(
                local_contract["patch_or_geometry_safety"],
                safety["all_frozen_grids_nonsingular"],
                source_gate_ids=[],
                value=safety["minimum_absolute_determinant"],
            ),
            "flat_limit": _applicable_check(
                local_contract["flat_limit"],
                checks["maximum_flat_limit_absolute_discrepancy"],
                source_gate_ids=["maximum_flat_limit_absolute_discrepancy"],
                value=evidence["maximum_flat_limit_absolute_discrepancy"],
            ),
            "on_off_shell_witness": _applicable_check(
                local_contract["on_off_shell_witness"],
                checks["maximum_finest_on_shell_combined_absolute_divergence_error"]
                and checks[
                    "maximum_finest_x_mode_combined_relative_identity_error"
                ]
                and checks[
                    "maximum_finest_y_mode_combined_relative_identity_error"
                ],
                source_gate_ids=[
                    "maximum_finest_on_shell_combined_absolute_divergence_error",
                    "maximum_finest_x_mode_combined_relative_identity_error",
                    "maximum_finest_y_mode_combined_relative_identity_error",
                ],
                value=evidence[
                    "finest_on_shell_combined_absolute_divergence_error"
                ],
            ),
        },
    )
    convergence = result["convergence_diagnostics"]["on_shell_temporal_mode"][
        "combined"
    ]
    relative_formed = not (
        convergence["convergence_status"] == "not_applicable_exact_zero"
        and convergence["minimum_two_finest_order"] is None
        and convergence["p_min"] is None
    )
    on_shell_row = _on_shell_row(
        chain,
        passed=checks[
            "maximum_finest_on_shell_combined_absolute_divergence_error"
        ]
        and not relative_formed,
        relative_error_against_zero_formed=relative_formed,
        evidence={
            "finest_absolute_divergence": evidence[
                "finest_on_shell_combined_absolute_divergence_error"
            ],
            "convergence_status": convergence["convergence_status"],
        },
    )
    adjudication = result["negative_controls"][
        "finest_resolution_adjudication"
    ]
    warped_controls = (
        (
            "warped_naive_partial",
            "naive_partial_divergence",
            "naive_partial_divergence",
        ),
        (
            "warped_omit_tensor_index",
            "omitted_tensor_index_connection",
            "omitted_tensor_index_connection_term",
        ),
        (
            "warped_omit_volume_trace",
            "omitted_volume_trace_connection",
            "omitted_volume_trace_connection_term",
        ),
        (
            "warped_flat_substitution",
            "flat_geometry_substitution",
            "curved_case_flat_geometry_substitution",
        ),
        (
            "warped_wrong_inverse_metric",
            "incorrect_inverse_metric_factor",
            "incorrect_y_inverse_metric_factor",
        ),
    )
    controls = []
    for control_id, mechanism, source_key in warped_controls:
        source = adjudication[source_key]
        controls.append(
            _control(
                control_id,
                chain["chain_id"],
                mechanism,
                detected=source["pass"],
                source_evidence={
                    "comparison_value": source["comparison_value"],
                    "threshold": source["threshold"],
                    "resolution_N": source["resolution_N"],
                },
                adjudication_role="finest_resolution_frozen_source_threshold",
            )
        )
    return {
        "background": _base_background_row(
            chain,
            finest_grid_shape=[
                chain["grid_schedule"][-1],
                chain["grid_schedule"][-1],
            ],
            actual_geometry_evidence={
                "source_classification": result[
                    "background_geometry_classification"
                ],
                "scalar_curvature_minimum": geometry[
                    "scalar_curvature_minimum"
                ],
                "scalar_curvature_maximum": geometry[
                    "scalar_curvature_maximum"
                ],
                "curvature_zero_reporting_is_non_gating": geometry[
                    "curvature_zero_reporting_is_non_gating"
                ],
                "all_frozen_grids_nonsingular": safety[
                    "all_frozen_grids_nonsingular"
                ],
                "divergence_components": ["nu_t", "nu_x", "nu_y"],
            },
        ),
        "profiles": profiles,
        "on_shell": on_shell_row,
        "local": local,
        "controls": controls,
        "identity_signature": "positive_residual_times_raised_gradient_covariant",
        "review_acceptance": {
            "accepted": review["verification"]["accepted"],
            "claim_ceiling_level": review["claim"]["claim_ceiling_level"],
            "primary_label": review["claim"]["primary_label"],
        },
    }


CHAIN_ADAPTERS: dict[str, Callable[[dict[str, Any]], dict[str, Any]]] = {
    "minkowski_1plus1": _adapt_minkowski,
    "conformal_connection_1plus1": _adapt_conformal,
    "de_sitter_1plus1": _adapt_de_sitter,
    "warped_2plus1": _adapt_warped,
}


def _fresh_review_status(review: dict[str, Any]) -> str:
    reproduction = review["verification"].get("fresh_subprocess_reproduction")
    if reproduction is None:
        return "not_recorded_in_legacy_review"
    if (
        reproduction.get("run_count") == 2
        and reproduction.get("both_runs_byte_identical") is True
        and reproduction.get("fresh_runs_match_repository_artifacts") is True
    ):
        return "two_fresh_subprocesses_matched"
    return "fresh_subprocess_reproduction_failed"


def reconstruct_source_family(
    preflight: dict[str, Any] | None = None,
) -> dict[str, Any]:
    """Adapt four heterogeneous accepted chains into one typed evidence state."""

    if preflight is None:
        preflight = preflight_source_family()
    if preflight.get("preflight_verified") is not True:
        raise SynthesisStateError("source family was not preflight verified")
    guardrail = preflight["guardrail"]
    bundles_by_id = {
        bundle["contract"]["chain_id"]: bundle
        for bundle in preflight["chains"]
    }
    expected_chain_ids = [
        chain["chain_id"] for chain in guardrail["source_chains"]
    ]
    if list(bundles_by_id) != expected_chain_ids:
        raise SynthesisStateError("preflight chain order differs")

    adapted: dict[str, dict[str, Any]] = {}
    source_rows: list[dict[str, Any]] = []
    for chain in guardrail["source_chains"]:
        chain_id = chain["chain_id"]
        bundle = bundles_by_id[chain_id]
        adapter = CHAIN_ADAPTERS.get(chain_id)
        if adapter is None:
            raise SynthesisStateError(f"no adapter for {chain_id}")
        adapted[chain_id] = adapter(bundle)
        review = bundle["payloads"]["independent_review"]
        source_rows.append(
            {
                "chain_id": chain_id,
                "label": chain["label"],
                "artifacts": copy.deepcopy(chain["artifacts"]),
                "artifact_integrity_verified": all(
                    item["verified"] for item in bundle["artifacts"]
                ),
                "review_status": review["status"],
                "claim_ceiling_level": review["claim"]["claim_ceiling_level"],
                "primary_label": review["claim"]["primary_label"],
                "accepted": review["verification"]["accepted"],
                "fresh_subprocess_review_status": _fresh_review_status(review),
                "identity_signature": adapted[chain_id]["identity_signature"],
                "equation_mapping": copy.deepcopy(chain["equation_mapping"]),
            }
        )

    qualified: list[dict[str, Any]] = []
    for frozen in guardrail["upstream_decision_contract"]["gate_inventory"]:
        bundle = bundles_by_id[frozen["chain_id"]]
        result = bundle["payloads"]["calculation_result"]
        source_gate_id = frozen["source_gate_id"]
        qualified.append(
            {
                **copy.deepcopy(frozen),
                "passed": result["threshold_checks"][source_gate_id],
                "source_all_thresholds_passed": result[
                    "all_thresholds_passed"
                ],
            }
        )

    backgrounds = [adapted[item]["background"] for item in expected_chain_ids]
    profiles = [
        profile
        for chain_id in expected_chain_ids
        for profile in adapted[chain_id]["profiles"]
    ]
    on_shell_rows = [
        adapted[item]["on_shell"] for item in expected_chain_ids
    ]
    local_rows = [adapted[item]["local"] for item in expected_chain_ids]
    controls = [
        control_row
        for chain_id in expected_chain_ids
        for control_row in adapted[chain_id]["controls"]
    ]
    expected_controls = guardrail["control_contract"]["instances"]
    actual_control_identity = [
        {
            "control_instance_id": row["control_instance_id"],
            "chain_id": row["chain_id"],
            "mechanism_class": row["mechanism_class"],
        }
        for row in controls
    ]
    if actual_control_identity != expected_controls:
        raise SynthesisStateError("chain adapters produced a different control order")

    state = {
        "guardrail": guardrail,
        "guardrail_sha256": preflight["guardrail_sha256"],
        "preflight_verified": True,
        "artifact_integrity_verified": True,
        "source_chains": source_rows,
        "background_comparison_rows": backgrounds,
        "profiles": profiles,
        "qualified_source_decisions": qualified,
        "source_local_on_shell_policy_rows": on_shell_rows,
        "applicability_typed_local_check_rows": local_rows,
        "control_instances": controls,
        "control_mechanism_classes": sorted(
            {row["mechanism_class"] for row in controls}
        ),
        "family_envelope_metric_ids": list(ALLOWED_FAMILY_ENVELOPES),
        "forbidden_cross_background_pooling_detected": False,
        "candidate_claim_level": 3,
        "candidate_primary_label": "E-REPRO",
        "review_accepted": False,
        "equation_surface_upgraded": False,
        "boundary": copy.deepcopy(guardrail["boundary"]),
        "unit_ledger_target": UNIT_LEDGER_TARGET,
        "unit_ledger_status": "queued_non_live_hard_gate",
        "warped_two_dimensional_einstein_degeneracy_language": False,
    }
    return state


def _all_finite(value: Any) -> bool:
    if isinstance(value, float):
        return math.isfinite(value)
    if isinstance(value, dict):
        return all(_all_finite(key) and _all_finite(item) for key, item in value.items())
    if isinstance(value, (list, tuple)):
        return all(_all_finite(item) for item in value)
    return True


def _expected_chain_by_id(
    guardrail: dict[str, Any]
) -> dict[str, dict[str, Any]]:
    return {chain["chain_id"]: chain for chain in guardrail["source_chains"]}


def _decision_1(state: dict[str, Any], guardrail: dict[str, Any]) -> bool:
    source_rows = state.get("source_chains")
    if not isinstance(source_rows, list) or len(source_rows) != 4:
        return False
    expected = guardrail["source_chains"]
    if [row.get("chain_id") for row in source_rows] != [
        row["chain_id"] for row in expected
    ]:
        return False
    artifacts = []
    for row, frozen in zip(source_rows, expected):
        if row.get("artifacts") != frozen["artifacts"]:
            return False
        if row.get("artifact_integrity_verified") is not True:
            return False
        artifacts.extend(row["artifacts"])
    return (
        state.get("preflight_verified") is True
        and state.get("artifact_integrity_verified") is True
        and len(artifacts) == 24
        and len({item["path"] for item in artifacts}) == 24
        and _all_finite(state)
    )


def _decision_2(state: dict[str, Any], guardrail: dict[str, Any]) -> bool:
    rows = state.get("source_chains", [])
    return len(rows) == 4 and all(
        row.get("accepted") is True
        and row.get("claim_ceiling_level") == 3
        and row.get("primary_label") == "E-REPRO"
        for row in rows
    )


def _decision_3(state: dict[str, Any], guardrail: dict[str, Any]) -> bool:
    rows = state.get("source_chains", [])
    if len(rows) != 4:
        return False
    by_id = {row["chain_id"]: row for row in rows}
    minkowski = by_id.get("minkowski_1plus1", {})
    if minkowski.get("identity_signature") != (
        "positive_residual_times_raised_gradient_flat_specialization"
    ):
        return False
    if minkowski.get("equation_mapping", {}).get("family_role") != (
        "flat_specialization_bridge"
    ):
        return False
    return all(
        by_id[chain_id].get("identity_signature")
        == "positive_residual_times_raised_gradient_covariant"
        for chain_id in (
            "conformal_connection_1plus1",
            "de_sitter_1plus1",
            "warped_2plus1",
        )
    )


def _decision_4(state: dict[str, Any], guardrail: dict[str, Any]) -> bool:
    rows = state.get("background_comparison_rows", [])
    expected = [row["geometry_class"] for row in guardrail["source_chains"]]
    actual = [row.get("geometry_class") for row in rows]
    return len(rows) == 4 and actual == expected and len(set(actual)) == 4


def _decision_5(state: dict[str, Any], guardrail: dict[str, Any]) -> bool:
    rows = state.get("background_comparison_rows", [])
    return (
        {row.get("spacetime_dimension") for row in rows} == {2, 3}
        and {row.get("divergence_component_count") for row in rows} == {2, 3}
    )


def _decision_6(state: dict[str, Any], guardrail: dict[str, Any]) -> bool:
    return {
        row.get("connection_class")
        for row in state.get("background_comparison_rows", [])
    } == {"zero_connection", "nonzero_connection"}


def _decision_7(state: dict[str, Any], guardrail: dict[str, Any]) -> bool:
    return {
        row.get("curvature_class")
        for row in state.get("background_comparison_rows", [])
    } == {
        "zero_curvature",
        "constant_nonzero_curvature",
        "spatially_varying_signed_curvature_with_zero_crossings",
    }


def _decision_8(state: dict[str, Any], guardrail: dict[str, Any]) -> bool:
    rows = state.get("background_comparison_rows", [])
    expected = _expected_chain_by_id(guardrail)
    if {row.get("chain_id") for row in rows} != set(expected):
        return False
    for row in rows:
        if row.get("profile_coverage") != expected[row["chain_id"]][
            "profile_coverage"
        ]:
            return False
    warped = next(row for row in rows if row["chain_id"] == "warped_2plus1")
    return (
        warped["profile_coverage"]["off_shell_y"] == "off_shell_y_mode"
        and warped["profile_coverage"]["applicable_divergence_components"]
        == ["nu_t", "nu_x", "nu_y"]
    )


def _decision_9(state: dict[str, Any], guardrail: dict[str, Any]) -> bool:
    rows = state.get("qualified_source_decisions", [])
    frozen = guardrail["upstream_decision_contract"]["gate_inventory"]
    if len(rows) != 37 or [row.get("qualified_gate_id") for row in rows] != [
        row["qualified_gate_id"] for row in frozen
    ]:
        return False
    counts: dict[str, int] = {}
    for row in rows:
        counts[row["chain_id"]] = counts.get(row["chain_id"], 0) + 1
    return (
        counts == guardrail["upstream_decision_contract"]["per_chain_counts"]
        and all(
            row.get("passed") is True
            and row.get("source_all_thresholds_passed") is True
            for row in rows
        )
    )


def _decision_10(state: dict[str, Any], guardrail: dict[str, Any]) -> bool:
    profiles = state.get("profiles", [])
    p_values = [row.get("p_min") for row in profiles]
    return (
        len(profiles) == 5
        and all(
            isinstance(value, (int, float)) and math.isfinite(float(value))
            for value in p_values
        )
        and min(p_values) >= guardrail["success_criteria"][
            "minimum_family_convergence_order"
        ]
    )


def _decision_11(state: dict[str, Any], guardrail: dict[str, Any]) -> bool:
    profiles = state.get("profiles", [])
    errors = [row.get("off_shell_relative_identity_error") for row in profiles]
    return (
        len(profiles) == 5
        and all(
            isinstance(value, (int, float)) and math.isfinite(float(value))
            for value in errors
        )
        and max(errors) <= guardrail["success_criteria"][
            "maximum_family_off_shell_relative_error"
        ]
    )


def _decision_12(state: dict[str, Any], guardrail: dict[str, Any]) -> bool:
    rows = state.get("source_local_on_shell_policy_rows", [])
    expected = guardrail["source_local_policy_contract"]["on_shell_policies"]
    return len(rows) == 4 and all(
        row.get("chain_id") in expected
        and row.get("policy") == expected[row["chain_id"]]
        and row.get("passed") is True
        and row.get("relative_error_against_zero_formed") is False
        for row in rows
    )


def _decision_13(state: dict[str, Any], guardrail: dict[str, Any]) -> bool:
    rows = state.get("applicability_typed_local_check_rows", [])
    frozen = {
        row["chain_id"]: {key: value for key, value in row.items() if key != "chain_id"}
        for row in guardrail["applicability_typed_local_check_ledger"]
    }
    if len(rows) != 4 or {row.get("chain_id") for row in rows} != set(frozen):
        return False
    for row in rows:
        checks = row.get("checks")
        if not isinstance(checks, dict) or set(checks) != set(frozen[row["chain_id"]]):
            return False
        for check_id, check in checks.items():
            if not isinstance(check, dict):
                return False
            if check.get("contract_status") != frozen[row["chain_id"]][check_id]:
                return False
            status = check.get("status")
            value = check.get("value")
            contract_status = check["contract_status"]
            if contract_status.startswith("not_applicable_"):
                if status != "not_applicable" or value is not None:
                    return False
                continue
            if contract_status == "baseline_not_recovery_test":
                if status != "baseline_not_recovery_test" or value is not None:
                    return False
                continue
            if status == "passed":
                if value is None:
                    return False
            else:
                return False
        if row.get("passed") is not True:
            return False
    return True


def _decision_14(state: dict[str, Any], guardrail: dict[str, Any]) -> bool:
    rows = state.get("control_instances", [])
    identity = [
        {
            "control_instance_id": row.get("control_instance_id"),
            "chain_id": row.get("chain_id"),
            "mechanism_class": row.get("mechanism_class"),
        }
        for row in rows
    ]
    return (
        len(rows) == 10
        and identity == guardrail["control_contract"]["instances"]
        and all(row.get("detected") is True for row in rows)
        and state.get("control_mechanism_classes")
        == guardrail["control_contract"]["mechanism_classes"]
    )


def _decision_15(state: dict[str, Any], guardrail: dict[str, Any]) -> bool:
    return (
        state.get("family_envelope_metric_ids")
        == list(ALLOWED_FAMILY_ENVELOPES)
        and state.get("forbidden_cross_background_pooling_detected") is False
        and all(
            row.get("metric_kind")
            == "within_background_dimensionless_off_shell_relative_identity_error"
            for row in state.get("profiles", [])
        )
    )


def _decision_16(state: dict[str, Any], guardrail: dict[str, Any]) -> bool:
    return (
        state.get("candidate_claim_level") == 3
        and state.get("candidate_primary_label") == "E-REPRO"
        and state.get("review_accepted") is False
        and state.get("equation_surface_upgraded") is False
        and state.get("boundary") == guardrail["boundary"]
        and state.get("unit_ledger_target") == UNIT_LEDGER_TARGET
        and state.get("unit_ledger_status") == "queued_non_live_hard_gate"
        and state.get("warped_two_dimensional_einstein_degeneracy_language")
        is False
    )


DECISION_EVALUATORS: dict[str, Callable[[dict[str, Any], dict[str, Any]], bool]] = {
    "exact_twenty_four_artifact_chain_integrity": _decision_1,
    "four_level3_review_acceptances": _decision_2,
    "identity_and_flat_specialization_mapping": _decision_3,
    "four_geometry_class_coverage": _decision_4,
    "dimension_and_component_coverage": _decision_5,
    "connection_class_coverage": _decision_6,
    "curvature_class_coverage": _decision_7,
    "profile_and_component_role_coverage": _decision_8,
    "all_thirty_seven_upstream_decisions_pass": _decision_9,
    "family_minimum_convergence_order": _decision_10,
    "family_maximum_off_shell_relative_error": _decision_11,
    "source_local_on_shell_policies": _decision_12,
    "applicability_typed_local_checks": _decision_13,
    "ten_control_instances_eight_mechanisms": _decision_14,
    "comparison_policy_no_invalid_pooling": _decision_15,
    "lifecycle_claim_and_unit_ledger_boundaries": _decision_16,
}


def evaluate_synthesis_decisions(
    state: dict[str, Any],
    guardrail: dict[str, Any] | None = None,
) -> list[dict[str, Any]]:
    guardrail = state["guardrail"] if guardrail is None else guardrail
    rows: list[dict[str, Any]] = []
    for frozen in guardrail["frozen_decisions"]:
        decision_id = frozen["decision_id"]
        evaluator = DECISION_EVALUATORS[decision_id]
        try:
            passed = bool(evaluator(state, guardrail))
        except (KeyError, TypeError, ValueError, IndexError):
            passed = False
        rows.append({**copy.deepcopy(frozen), "passed": passed})
    return rows


def _mutate_omitted_background(state: dict[str, Any]) -> None:
    state["background_comparison_rows"].pop()


def _mutate_swapped_chain_artifacts(state: dict[str, Any]) -> None:
    first = state["source_chains"][0]["artifacts"]
    second = state["source_chains"][1]["artifacts"]
    state["source_chains"][0]["artifacts"] = second
    state["source_chains"][1]["artifacts"] = first


def _mutate_masked_upstream_failure(state: dict[str, Any]) -> None:
    state["qualified_source_decisions"][0]["passed"] = False


def _mutate_inapplicable_zero_fill(state: dict[str, Any]) -> None:
    for row in state["applicability_typed_local_check_rows"]:
        for check in row["checks"].values():
            if check["status"] == "not_applicable":
                check["status"] = "passed"
                check["value"] = 0
                return
    raise SynthesisStateError("no inapplicable check to mutate")


def _mutate_on_shell_relative_error(state: dict[str, Any]) -> None:
    state["source_local_on_shell_policy_rows"][-1][
        "relative_error_against_zero_formed"
    ] = True


def _mutate_raw_absolute_error(state: dict[str, Any]) -> None:
    state["profiles"][0]["metric_kind"] = "raw_absolute_divergence_error"


def _mutate_removed_control(state: dict[str, Any]) -> None:
    state["control_instances"].pop()


def _mutate_artifact_hash(state: dict[str, Any], role: str) -> None:
    for source in state["source_chains"]:
        for artifact in source["artifacts"]:
            if artifact["artifact_role"] == role:
                artifact["sha256"] = "0" * 64
                return
    raise SynthesisStateError(f"no artifact role to mutate: {role}")


def _mutate_nonfinite(state: dict[str, Any]) -> None:
    state["source_chains"][0]["artifact_integrity_probe"] = float("nan")


def _mutate_degeneracy_language(state: dict[str, Any]) -> None:
    state["warped_two_dimensional_einstein_degeneracy_language"] = True


def _mutate_collapsed_curvature(state: dict[str, Any]) -> None:
    for row in state["background_comparison_rows"]:
        if row["chain_id"] == "warped_2plus1":
            row["curvature_class"] = "constant_nonzero_curvature"
            return


def _mutate_forbidden_claim(state: dict[str, Any]) -> None:
    state["boundary"]["qft_gr_seam_admissibility_claimed"] = True


TAMPER_MUTATORS: dict[str, Callable[[dict[str, Any]], None]] = {
    "omitted_background": _mutate_omitted_background,
    "swapped_chain_artifacts": _mutate_swapped_chain_artifacts,
    "masked_upstream_failure": _mutate_masked_upstream_failure,
    "inapplicable_zero_fill": _mutate_inapplicable_zero_fill,
    "on_shell_relative_error_injection": _mutate_on_shell_relative_error,
    "raw_absolute_error_substitution": _mutate_raw_absolute_error,
    "removed_control_instance": _mutate_removed_control,
    "input_hash_tamper": lambda state: _mutate_artifact_hash(state, "guardrail"),
    "review_hash_tamper": lambda state: _mutate_artifact_hash(
        state, "independent_review"
    ),
    "result_hash_tamper": lambda state: _mutate_artifact_hash(
        state, "calculation_result"
    ),
    "nonfinite_injection": _mutate_nonfinite,
    "degeneracy_language_leak": _mutate_degeneracy_language,
    "collapsed_curvature_classes": _mutate_collapsed_curvature,
    "forbidden_claim_promotion": _mutate_forbidden_claim,
}


def run_synthesis_tamper_controls(
    state: dict[str, Any],
    guardrail: dict[str, Any] | None = None,
) -> list[dict[str, Any]]:
    """Run every mutation on a fresh deep copy and retain localized failures."""

    guardrail = state["guardrail"] if guardrail is None else guardrail
    rows: list[dict[str, Any]] = []
    for frozen in guardrail["synthesis_tamper_controls"]:
        control_id = frozen["control_id"]
        mutation_state = copy.deepcopy(state)
        TAMPER_MUTATORS[control_id](mutation_state)
        decisions = evaluate_synthesis_decisions(mutation_state, guardrail)
        failures = [
            row["decision_id"] for row in decisions if row["passed"] is False
        ]
        expected = frozen["expected_failed_decision_id"]
        passed = expected in failures
        rows.append(
            {
                "control_id": control_id,
                "exact_mutation": frozen["exact_mutation"],
                "expected_failed_decision_id": expected,
                "observed_failed_decision_id": expected if passed else (
                    failures[0] if failures else None
                ),
                "observed_failed_decision_ids": failures,
                "fresh_deep_copy_used": True,
                "passed": passed,
            }
        )
    return rows


def _public_source_rows(state: dict[str, Any]) -> list[dict[str, Any]]:
    return copy.deepcopy(state["source_chains"])


def build_result(
    *,
    captured_at_utc: str = CAPTURED_AT_UTC,
    state: dict[str, Any] | None = None,
    preflight: dict[str, Any] | None = None,
) -> dict[str, Any]:
    if state is None:
        state = reconstruct_source_family(preflight)
    guardrail = state["guardrail"]
    decisions = evaluate_synthesis_decisions(state, guardrail)
    tamper_controls = run_synthesis_tamper_controls(state, guardrail)
    threshold_checks = {
        row["decision_id"]: row["passed"] for row in decisions
    }
    combined_pass = all(threshold_checks.values()) and all(
        row["passed"] for row in tamper_controls
    )
    status = (
        "executed_candidate_e_repro_pending_independent_review"
        if combined_pass
        else "executed_blocked_evidence_incompatibility"
    )
    selected_target = (
        RESULT_REVIEW_TARGET if combined_pass else EVIDENCE_FAILURE_TARGET
    )
    claim_scope = guardrail["claim_ceiling"][
        "allowed_after_successful_review"
    ]
    profiles = state["profiles"]
    convergence_rows = [
        {
            "chain_id": row["chain_id"],
            "profile_row_id": row["profile_row_id"],
            "p_min": row["p_min"],
            "source_field": row["p_source_field"],
        }
        for row in profiles
    ]
    error_rows = [
        {
            "chain_id": row["chain_id"],
            "profile_row_id": row["profile_row_id"],
            "off_shell_relative_identity_error": row[
                "off_shell_relative_identity_error"
            ],
            "metric_kind": row["metric_kind"],
            "source_field": row["error_source_field"],
        }
        for row in profiles
    ]
    result = {
        "schema_id": RESULT_SCHEMA_ID,
        "calculation_id": CALCULATION_ID,
        "calculation_status": status,
        "captured_at_utc": captured_at_utc,
        "guardrail": {
            "path": GUARDRAIL_RELATIVE_PATH,
            "sha256": state["guardrail_sha256"],
            "schema_id": guardrail["schema_id"],
        },
        "question": guardrail["question"],
        "source_chain_count": len(state["source_chains"]),
        "bound_artifact_count": sum(
            len(row["artifacts"]) for row in state["source_chains"]
        ),
        "source_chains": _public_source_rows(state),
        "background_comparison_rows": copy.deepcopy(
            state["background_comparison_rows"]
        ),
        "comparable_metric_contract": {
            "convergence_rows": convergence_rows,
            "off_shell_relative_error_rows": error_rows,
            "family_minimum_p_min": min(
                row["p_min"] for row in convergence_rows
            ),
            "family_maximum_off_shell_relative_identity_error": max(
                row["off_shell_relative_identity_error"] for row in error_rows
            ),
        },
        "qualified_source_decisions": copy.deepcopy(
            state["qualified_source_decisions"]
        ),
        "source_local_on_shell_policy_rows": copy.deepcopy(
            state["source_local_on_shell_policy_rows"]
        ),
        "applicability_typed_local_check_rows": copy.deepcopy(
            state["applicability_typed_local_check_rows"]
        ),
        "control_coverage": {
            "instance_count": len(state["control_instances"]),
            "mechanism_count": len(state["control_mechanism_classes"]),
            "instances": copy.deepcopy(state["control_instances"]),
            "mechanism_classes": copy.deepcopy(
                state["control_mechanism_classes"]
            ),
            "all_detected": all(
                row["detected"] for row in state["control_instances"]
            ),
        },
        "synthesis_decision_count": len(decisions),
        "synthesis_decisions": decisions,
        "threshold_checks": threshold_checks,
        "synthesis_tamper_control_count": len(tamper_controls),
        "synthesis_tamper_controls": tamper_controls,
        "all_decisions_passed": combined_pass,
        "all_thresholds_passed": combined_pass,
        "selected_next_target": selected_target,
        "claim": {
            "primary_label": "E-REPRO" if combined_pass else "B-BLOCKED",
            "claim_status": (
                "candidate_pending_independent_result_review"
                if combined_pass
                else "blocked_evidence_incompatibility"
            ),
            "claim_ceiling_level": 3,
            "claim_scope": claim_scope,
            "review_accepted": False,
            "equation_surface_upgraded": False,
        },
        "boundary": copy.deepcopy(guardrail["boundary"]),
        "result_review": {
            "status": (
                "pending" if combined_pass else "not_created_synthesis_failure"
            ),
            "target": RESULT_REVIEW_TARGET if combined_pass else None,
        },
    }
    canonical_json_bytes(result)
    return result


def build_manifest(
    *,
    output_path: Path,
    result: dict[str, Any] | None = None,
    captured_at_utc: str = CAPTURED_AT_UTC,
) -> dict[str, Any]:
    guardrail, guardrail_sha256 = load_guardrail()
    if result is None:
        result = strict_json_load(output_path)
    scientific_inputs = [
        {
            "chain_id": chain["chain_id"],
            "artifact_role": artifact["artifact_role"],
            "path": artifact["path"],
            "sha256": artifact["sha256"],
        }
        for chain in guardrail["source_chains"]
        for artifact in chain["artifacts"]
    ]
    return {
        "schema_id": MANIFEST_SCHEMA_ID,
        "calculation_id": CALCULATION_ID,
        "captured_at_utc": captured_at_utc,
        "guardrail_path": GUARDRAIL_RELATIVE_PATH,
        "guardrail_schema_id": guardrail["schema_id"],
        "guardrail_sha256": guardrail_sha256,
        "script_path": SCRIPT_RELATIVE_PATH,
        "script_sha256": sha256_file(REPO_ROOT / SCRIPT_RELATIVE_PATH),
        "test_path": TEST_RELATIVE_PATH,
        "execution_command": EXECUTION_COMMAND,
        "output_path": OUTPUT_RELATIVE_PATH,
        "output_sha256": sha256_file(output_path),
        "execution_report_path": EXECUTION_REPORT_RELATIVE_PATH,
        "canonical_json_contract": {
            "encoding": "UTF-8 without BOM",
            "newline": "LF",
            "object_keys": "sorted",
            "separators": [",", ":"],
            "ensure_ascii": True,
            "allow_nan": False,
            "array_order": "preserved",
            "trailing_newline": "exactly one LF",
        },
        "scientific_input_artifacts": scientific_inputs,
        "source_chain_count": result["source_chain_count"],
        "bound_artifact_count": result["bound_artifact_count"],
        "claim_label": result["claim"]["primary_label"],
        "claim_scope": result["claim"]["claim_scope"],
        "claim_ceiling_level": result["claim"]["claim_ceiling_level"],
        "calculation_status": result["calculation_status"],
        "all_decisions_passed": result["all_decisions_passed"],
        "all_thresholds_passed": result["all_thresholds_passed"],
        "result_review_status": result["result_review"]["status"],
        "result_review_target": result["result_review"]["target"],
        "selected_next_target": result["selected_next_target"],
        "boundary": copy.deepcopy(result["boundary"]),
        "ambient_repository_state_serialized": False,
        "execution_commit_hash_serialized": False,
    }


def write_artifacts(
    *,
    output_path: Path,
    manifest_path: Path,
    captured_at_utc: str = CAPTURED_AT_UTC,
    state: dict[str, Any] | None = None,
) -> tuple[dict[str, Any], dict[str, Any]]:
    preflight = None if state is not None else preflight_source_family()
    result = build_result(
        captured_at_utc=captured_at_utc,
        state=state,
        preflight=preflight,
    )
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_bytes(canonical_json_bytes(result))
    manifest = build_manifest(
        output_path=output_path,
        result=result,
        captured_at_utc=captured_at_utc,
    )
    manifest_path.parent.mkdir(parents=True, exist_ok=True)
    manifest_path.write_bytes(canonical_json_bytes(manifest))
    return result, manifest


def build_preflight_diagnostic(error: PreflightError) -> dict[str, Any]:
    return {
        "schema_id": PREFLIGHT_DIAGNOSTIC_SCHEMA_ID,
        "calculation_id": CALCULATION_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "status": "preflight_evidence_incompatibility",
        "primary_label": "B-BLOCKED",
        "error_codes": copy.deepcopy(error.error_codes),
        "message": str(error),
        "canonical_result_created": False,
        "canonical_manifest_created": False,
        "canonical_execution_report_created": False,
        "selected_next_target": EVIDENCE_FAILURE_TARGET,
        "ambient_repository_state_serialized": False,
    }


def write_preflight_diagnostic(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(report_json_bytes(payload))


def _resolve(path: Path) -> Path:
    return path if path.is_absolute() else REPO_ROOT / path


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Synthesize the exact four accepted scalar fixed-background "
            "stress-energy divergence identity evidence chains."
        )
    )
    parser.add_argument("--output", type=Path, default=Path(OUTPUT_RELATIVE_PATH))
    parser.add_argument(
        "--manifest", type=Path, default=Path(MANIFEST_RELATIVE_PATH)
    )
    parser.add_argument(
        "--preflight-diagnostic",
        type=Path,
        default=Path(PREFLIGHT_DIAGNOSTIC_RELATIVE_PATH),
    )
    args = parser.parse_args(argv)
    output_path = _resolve(args.output)
    manifest_path = _resolve(args.manifest)
    diagnostic_path = _resolve(args.preflight_diagnostic)
    try:
        result, manifest = write_artifacts(
            output_path=output_path,
            manifest_path=manifest_path,
        )
    except PreflightError as exc:
        diagnostic = build_preflight_diagnostic(exc)
        write_preflight_diagnostic(diagnostic_path, diagnostic)
        print(json.dumps(diagnostic, indent=2, sort_keys=True))
        return 2
    print(
        json.dumps(
            {
                "calculation_id": CALCULATION_ID,
                "all_decisions_passed": result["all_decisions_passed"],
                "claim_label": result["claim"]["primary_label"],
                "output": OUTPUT_RELATIVE_PATH,
                "output_sha256": manifest["output_sha256"],
                "manifest": MANIFEST_RELATIVE_PATH,
                "selected_next_target": result["selected_next_target"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0 if result["all_decisions_passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
