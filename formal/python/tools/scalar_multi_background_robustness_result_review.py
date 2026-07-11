from __future__ import annotations

import argparse
import copy
import hashlib
import json
import math
import os
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any, Iterable

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
CAPTURED_AT_UTC = "2026-07-10T00:00:00Z"
CALCULATION_ID = (
    "CALC-SCALAR-STRESS-ENERGY-COVARIANT-DIVERGENCE-IDENTITY-MULTI-"
    "BACKGROUND-ROBUSTNESS-v0"
)
REVIEW_TARGET = (
    "review_calc_scalar_stress_energy_covariant_divergence_identity_multi_"
    "background_robustness_v0_result"
)
REVIEW_TARGET_KIND = (
    "scalar_stress_energy_covariant_divergence_identity_multi_background_"
    "robustness_calculation_result_review"
)
SUCCESS_TARGET = "prepare_pillar_seam_unit_mapping_ledger_guardrail_packet"
SUCCESS_TARGET_KIND = "pillar_seam_unit_mapping_ledger_guardrail_packet"
SUCCESS_SELECTION_BASIS = (
    "unit mapping is a hard gate before Level 4/5, physical calibration, "
    "cross-sector coupling, or C_k action embedding"
)
EXECUTION_COMMIT = "f733587fedf78cfa4c2fc3a6ce8c7f63f1885b49"
FAILURE_TARGET = (
    "diagnose_calc_scalar_stress_energy_covariant_divergence_identity_multi_"
    "background_robustness_v0_reproducibility_mismatch"
)
FAILURE_TARGET_KIND = "scientific_reproducibility_mismatch_diagnosis"

REVIEW_SCHEMA_ID = (
    "SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_MULTI_BACKGROUND_"
    "ROBUSTNESS_CALCULATION_RESULT_REVIEW_20260710_v0"
)
REVIEW_ID = (
    "SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_MULTI_BACKGROUND_"
    "ROBUSTNESS_CALCULATION_RESULT_REVIEW_v0"
)
REVIEW_OUTCOME = (
    "SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_MULTI_BACKGROUND_"
    "ROBUSTNESS_RESULT_REVIEW_ACCEPTS_REPRODUCIBLE_ROBUSTNESS_ACROSS_THE_"
    "EXACT_FOUR_ENUMERATED_FIXED_BACKGROUND_EVIDENCE_CHAINS"
)
REVIEW_STRICT_OUTCOME = (
    "SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_MULTI_BACKGROUND_"
    "ROBUSTNESS_RESULT_REVIEW_ACCEPTS_LEVEL3_CLOSED_ENUMERATED_FIXED_"
    "BACKGROUND_FIXED_COORDINATE_SHARED_LINEAGE_E_REPRO_ONLY_NO_THEOREM_"
    "NO_STATISTICAL_OR_ARBITRARY_BACKGROUND_GENERALIZATION_NO_LEVEL4_OR5"
)

GUARDRAIL_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_"
    "MULTI_BACKGROUND_ROBUSTNESS_GUARDRAIL_PACKET_20260710_v0.json"
)
SCRIPT_RELATIVE_PATH = (
    "formal/python/toe/calculations/"
    "calc_scalar_stress_energy_covariant_divergence_identity_multi_"
    "background_robustness.py"
)
OUTPUT_RELATIVE_PATH = (
    "formal/output/CALC-SCALAR-STRESS-ENERGY-COVARIANT-DIVERGENCE-IDENTITY-"
    "MULTI-BACKGROUND-ROBUSTNESS-v0.json"
)
MANIFEST_RELATIVE_PATH = (
    "formal/output/CALC-SCALAR-STRESS-ENERGY-COVARIANT-DIVERGENCE-IDENTITY-"
    "MULTI-BACKGROUND-ROBUSTNESS-MANIFEST-v0.json"
)
EXECUTION_REPORT_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_"
    "MULTI_BACKGROUND_ROBUSTNESS_CALCULATION_EXECUTION_20260710_v0.json"
)
REVIEW_REPORT_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_"
    "MULTI_BACKGROUND_ROBUSTNESS_CALCULATION_RESULT_REVIEW_20260710_v0.json"
)
PREFLIGHT_DIAGNOSTIC_RELATIVE_PATH = (
    "formal/output/diagnostics/CALC-SCALAR-STRESS-ENERGY-COVARIANT-"
    "DIVERGENCE-IDENTITY-"
    "MULTI-BACKGROUND-ROBUSTNESS-PREFLIGHT-DIAGNOSTIC-v0.json"
)

GUARDRAIL_PATH = REPO_ROOT / GUARDRAIL_RELATIVE_PATH
SCRIPT_PATH = REPO_ROOT / SCRIPT_RELATIVE_PATH
OUTPUT_PATH = REPO_ROOT / OUTPUT_RELATIVE_PATH
MANIFEST_PATH = REPO_ROOT / MANIFEST_RELATIVE_PATH
EXECUTION_REPORT_PATH = REPO_ROOT / EXECUTION_REPORT_RELATIVE_PATH
REVIEW_REPORT_PATH = REPO_ROOT / REVIEW_REPORT_RELATIVE_PATH

GUARDRAIL_SCHEMA_ID = (
    "SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_MULTI_BACKGROUND_"
    "ROBUSTNESS_GUARDRAIL_PACKET_20260710_v0"
)
RESULT_SCHEMA_ID = f"{CALCULATION_ID}-RESULT"
MANIFEST_SCHEMA_ID = f"{CALCULATION_ID}-MANIFEST"
EXECUTION_SCHEMA_ID = (
    "SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_MULTI_BACKGROUND_"
    "ROBUSTNESS_CALCULATION_EXECUTION_20260710_v0"
)

# The guardrail is already frozen.  The remaining values must be replaced only
# after the execution commit exists; an unfrozen reviewer can never accept.
UNFROZEN_HASH_SENTINEL = "__FREEZE_AFTER_EXECUTION_COMMIT__"
EXPECTED_EXECUTION_HASHES = {
    "guardrail_sha256": (
        "be308d23673273bf2533f25c58280e92845da146b128dc74a7aad345557c5b95"
    ),
    "script_sha256": (
        "31c6748161d7e489b35ed25dc298197d5b4c3b67c7d9cb49a98cd30518965342"
    ),
    "output_sha256": (
        "c05c89a469682375ae6c4f2385596bb02296680b3d0a62c36146f144ef60ab65"
    ),
    "manifest_sha256": (
        "5b2bc32e1ba42992f367ec19e4d380fc09ee16bd1c570696f8252eeadcee04b3"
    ),
    "execution_report_sha256": (
        "3475e11a9cfee79e895732c0719864f797e8be4f1cdc11de7e776c728daf0a87"
    ),
}

RESULT_KEYS = {
    "schema_id",
    "calculation_id",
    "calculation_status",
    "captured_at_utc",
    "guardrail",
    "question",
    "source_chain_count",
    "bound_artifact_count",
    "source_chains",
    "background_comparison_rows",
    "comparable_metric_contract",
    "qualified_source_decisions",
    "source_local_on_shell_policy_rows",
    "applicability_typed_local_check_rows",
    "control_coverage",
    "synthesis_decision_count",
    "synthesis_decisions",
    "threshold_checks",
    "synthesis_tamper_control_count",
    "synthesis_tamper_controls",
    "all_decisions_passed",
    "all_thresholds_passed",
    "selected_next_target",
    "claim",
    "boundary",
    "result_review",
}
MANIFEST_KEYS = {
    "schema_id",
    "calculation_id",
    "captured_at_utc",
    "guardrail_path",
    "guardrail_schema_id",
    "guardrail_sha256",
    "script_path",
    "script_sha256",
    "test_path",
    "execution_command",
    "output_path",
    "output_sha256",
    "execution_report_path",
    "canonical_json_contract",
    "scientific_input_artifacts",
    "source_chain_count",
    "bound_artifact_count",
    "claim_label",
    "claim_scope",
    "claim_ceiling_level",
    "calculation_status",
    "all_decisions_passed",
    "all_thresholds_passed",
    "result_review_status",
    "result_review_target",
    "selected_next_target",
    "boundary",
    "ambient_repository_state_serialized",
    "execution_commit_hash_serialized",
}
EXECUTION_KEYS = {
    "schema_id",
    "report_id",
    "calculation_id",
    "status",
    "captured_at_utc",
    "consumed_target",
    "consumed_target_kind",
    "selected_next_target",
    "selected_next_target_kind",
    "packet_result",
    "strict_packet_result",
    "preflight",
    "guardrail_path",
    "guardrail_schema_id",
    "guardrail_sha256",
    "calculation_script_path",
    "calculation_script_sha256",
    "calculation_output_path",
    "calculation_output_sha256",
    "calculation_manifest_path",
    "calculation_manifest_sha256",
    "execution_report_path",
    "five_artifact_chain_prepared_for_independent_review",
    "canonical_json_contract",
    "execution_command",
    "scientific_input_artifacts",
    "source_chain_count",
    "bound_artifact_count",
    "source_chains",
    "background_comparison_rows",
    "comparable_metric_contract",
    "qualified_source_decisions",
    "source_local_on_shell_policy_rows",
    "applicability_typed_local_check_rows",
    "control_coverage",
    "synthesis_decision_count",
    "synthesis_decisions",
    "threshold_checks",
    "synthesis_tamper_control_count",
    "synthesis_tamper_controls",
    "all_decisions_passed",
    "all_thresholds_passed",
    "claim",
    "result_review",
    "equation_compendium_edited",
    "ambient_repository_state_serialized",
    "execution_commit_hash_serialized",
    "boundary",
    "full_ToeFormal_aggregate_run_or_upgraded",
    "lean_status_wording",
}

COMPENDIUM_RELATIVE_PATH = (
    "formal/docs/paper/TOE_MATH_PHYSICS_WORK_AND_EQUATIONS_COMPENDIUM_v0.md"
)
COMPENDIUM_SHA256 = (
    "7a7f9e564fd2e902b731b6ddceb7adb687e854d3a7970462c8ba29b51c05427e"
)
FLAT_EQUATION_ID = "EQ-QFT-SCALAR-STRESS-DIVERGENCE-IDENTITY-v0"
COVARIANT_EQUATION_ID = (
    "EQ-QFT-SCALAR-COVARIANT-STRESS-DIVERGENCE-IDENTITY-v0"
)

CHAIN_ORDER = (
    "minkowski_1plus1",
    "conformal_connection_1plus1",
    "de_sitter_1plus1",
    "warped_2plus1",
)
CHAIN_EXPECTATIONS: dict[str, dict[str, Any]] = {
    "minkowski_1plus1": {
        "dimension": 2,
        "component_count": 2,
        "geometry_class": "cartesian_flat_trivial_connection",
        "connection_class": "zero_connection",
        "curvature_class": "zero_curvature",
        "grid_schedule": [64, 128, 256, 512],
        "grid_shape_semantics": "N spatial points",
        "review_status": "accepted_scoped_e_repro",
        "profile_id": "minkowski_off_shell",
        "p_key": "minimum_observed_two_finest_convergence_order",
        "error_key": "finest_combined_off_shell_relative_error",
    },
    "conformal_connection_1plus1": {
        "dimension": 2,
        "component_count": 2,
        "geometry_class": "locally_flat_nontrivial_connection",
        "connection_class": "nonzero_connection",
        "curvature_class": "zero_curvature",
        "grid_schedule": [64, 128, 256, 512],
        "grid_shape_semantics": "N spatial points",
        "review_status": "accepted_scoped_e_repro",
        "profile_id": "conformal_off_shell",
        "p_key": "minimum_observed_two_finest_convergence_order",
        "error_key": "finest_combined_off_shell_relative_error",
    },
    "de_sitter_1plus1": {
        "dimension": 2,
        "component_count": 2,
        "geometry_class": "constant_nonzero_curvature_de_sitter",
        "connection_class": "nonzero_connection",
        "curvature_class": "constant_nonzero_curvature",
        "grid_schedule": [64, 128, 256, 512],
        "grid_shape_semantics": "N spatial points",
        "review_status": "accepted_scoped_e_repro",
        "profile_id": "de_sitter_off_shell",
        "p_key": "minimum_observed_two_finest_convergence_order",
        "error_key": "finest_combined_off_shell_relative_error",
    },
    "warped_2plus1": {
        "dimension": 3,
        "component_count": 3,
        "geometry_class": "spatially_varying_signed_curvature_warped",
        "connection_class": "nonzero_connection",
        "curvature_class": (
            "spatially_varying_signed_curvature_with_zero_crossings"
        ),
        "grid_schedule": [32, 64, 128, 256],
        "grid_shape_semantics": "N x N spatial points",
        "review_status": "accepted_level_3_scoped_e_repro",
    },
}

DECISION_IDS = (
    "exact_twenty_four_artifact_chain_integrity",
    "four_level3_review_acceptances",
    "identity_and_flat_specialization_mapping",
    "four_geometry_class_coverage",
    "dimension_and_component_coverage",
    "connection_class_coverage",
    "curvature_class_coverage",
    "profile_and_component_role_coverage",
    "all_thirty_seven_upstream_decisions_pass",
    "family_minimum_convergence_order",
    "family_maximum_off_shell_relative_error",
    "source_local_on_shell_policies",
    "applicability_typed_local_checks",
    "ten_control_instances_eight_mechanisms",
    "comparison_policy_no_invalid_pooling",
    "lifecycle_claim_and_unit_ledger_boundaries",
)
TAMPER_EXPECTATIONS = {
    "omitted_background": "four_geometry_class_coverage",
    "swapped_chain_artifacts": "exact_twenty_four_artifact_chain_integrity",
    "masked_upstream_failure": "all_thirty_seven_upstream_decisions_pass",
    "inapplicable_zero_fill": "applicability_typed_local_checks",
    "on_shell_relative_error_injection": "source_local_on_shell_policies",
    "raw_absolute_error_substitution": "comparison_policy_no_invalid_pooling",
    "removed_control_instance": "ten_control_instances_eight_mechanisms",
    "input_hash_tamper": "exact_twenty_four_artifact_chain_integrity",
    "review_hash_tamper": "exact_twenty_four_artifact_chain_integrity",
    "result_hash_tamper": "exact_twenty_four_artifact_chain_integrity",
    "nonfinite_injection": "exact_twenty_four_artifact_chain_integrity",
    "degeneracy_language_leak": "lifecycle_claim_and_unit_ledger_boundaries",
    "collapsed_curvature_classes": "curvature_class_coverage",
    "forbidden_claim_promotion": "lifecycle_claim_and_unit_ledger_boundaries",
}
CONTROL_MECHANISMS = {
    "off_shell_nonconservation",
    "naive_partial_divergence",
    "inconsistent_connection",
    "curvature_derivative_omission",
    "omitted_tensor_index_connection",
    "omitted_volume_trace_connection",
    "flat_geometry_substitution",
    "incorrect_inverse_metric_factor",
}
FORBIDDEN_BOUNDARY_TRUE = {
    "new_pde_solve_authorized",
    "gravity_evolution_claimed",
    "einstein_source_compatibility_claimed",
    "bianchi_compatibility_claimed",
    "qft_gr_seam_admissibility_claimed",
    "qft_gr_seam_closure_claimed",
    "scalar_qft_pillar_recovery_claimed",
    "level_4_or_level_5_claimed",
    "quantum_or_renormalized_stress_energy_claimed",
    "ccft_resumed",
    "C_k_dynamics_claimed",
    "C_k_action_embedding_authorized",
    "master_action_promoted",
}


class DuplicateKeyError(ValueError):
    pass


class NonFiniteJSONError(ValueError):
    pass


def canonical_json_bytes(payload: Any) -> bytes:
    return (
        json.dumps(
            payload,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=True,
            allow_nan=False,
        )
        + "\n"
    ).encode("utf-8")


def report_json_bytes(payload: Any) -> bytes:
    return (
        json.dumps(
            payload,
            indent=2,
            sort_keys=True,
            ensure_ascii=True,
            allow_nan=False,
        )
        + "\n"
    ).encode("utf-8")


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def sha256_path(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def _reject_constant(token: str) -> None:
    raise NonFiniteJSONError(f"nonfinite JSON token: {token}")


def _object_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise DuplicateKeyError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _all_finite(value: Any) -> bool:
    if isinstance(value, float):
        return math.isfinite(value)
    if isinstance(value, dict):
        return all(_all_finite(item) for item in value.values())
    if isinstance(value, list):
        return all(_all_finite(item) for item in value)
    return True


def load_strict_json_object(path: Path, *, style: str) -> dict[str, Any]:
    raw = path.read_bytes()
    if raw.startswith(b"\xef\xbb\xbf"):
        raise ValueError("UTF-8 BOM is forbidden")
    payload = json.loads(
        raw.decode("utf-8", errors="strict"),
        object_pairs_hook=_object_pairs,
        parse_constant=_reject_constant,
    )
    if not isinstance(payload, dict):
        raise ValueError("top-level JSON value must be an object")
    if not _all_finite(payload):
        raise NonFiniteJSONError("decoded JSON contains a nonfinite number")
    if style == "compact":
        expected = canonical_json_bytes(payload)
    elif style == "report":
        expected = report_json_bytes(payload)
    else:
        raise ValueError(f"unknown JSON style: {style}")
    if raw != expected:
        raise ValueError("JSON bytes are not canonical")
    return payload


def _artifact(chain: dict[str, Any], role: str) -> dict[str, str]:
    matches = [item for item in chain.get("artifacts", []) if item.get("artifact_role") == role]
    if len(matches) != 1:
        raise ValueError(f"expected exactly one {role} artifact")
    return matches[0]


def _hash_key_for_role(role: str) -> str:
    return {
        "guardrail": "guardrail_sha256",
        "calculation_script": "script_sha256",
        "calculation_result": "output_sha256",
        "calculation_manifest": "manifest_sha256",
        "execution_report": "execution_report_sha256",
    }[role]


def _load_source_json(artifact: dict[str, str]) -> dict[str, Any]:
    role = artifact["artifact_role"]
    style = "compact" if role in {"calculation_result", "calculation_manifest"} else "report"
    return load_strict_json_object(REPO_ROOT / artifact["path"], style=style)


def _source_internal_links(
    chain: dict[str, Any], loaded: dict[str, dict[str, Any]]
) -> bool:
    result = loaded["calculation_result"]
    manifest = loaded["calculation_manifest"]
    execution = loaded["execution_report"]
    review = loaded["independent_review"]
    review_target = chain["review_target"]
    expected_by_role = {
        role: _artifact(chain, role)["sha256"]
        for role in (
            "guardrail",
            "calculation_script",
            "calculation_result",
            "calculation_manifest",
            "execution_report",
        )
    }
    manifest_ok = (
        manifest.get("guardrail_path") == _artifact(chain, "guardrail")["path"]
        and manifest.get("guardrail_sha256") == expected_by_role["guardrail"]
        and manifest.get("script_path") == _artifact(chain, "calculation_script")["path"]
        and manifest.get("script_sha256") == expected_by_role["calculation_script"]
        and manifest.get("output_path") == _artifact(chain, "calculation_result")["path"]
        and manifest.get("output_sha256") == expected_by_role["calculation_result"]
        and manifest.get("result_review_target") == review_target
    )
    execution_script_hash = execution.get(
        "calculation_script_sha256", execution.get("script_sha256")
    )
    execution_ok = (
        execution.get("guardrail_sha256") == expected_by_role["guardrail"]
        and execution_script_hash == expected_by_role["calculation_script"]
        and execution.get("calculation_output_sha256")
        == expected_by_role["calculation_result"]
        and execution.get("calculation_manifest_sha256")
        == expected_by_role["calculation_manifest"]
        and execution.get("selected_next_target") == review_target
    )
    review_verification = review.get("verification", {})
    expected_hashes = review_verification.get("expected_hashes", {})
    actual_hashes = review_verification.get("actual_hashes", {})
    review_hashes_ok = all(
        expected_hashes.get(_hash_key_for_role(role)) == digest
        and actual_hashes.get(_hash_key_for_role(role)) == digest
        for role, digest in expected_by_role.items()
    )
    result_ok = result.get("result_review") == {
        "status": "pending",
        "target": review_target,
    }
    return bool(
        manifest_ok
        and execution_ok
        and review_hashes_ok
        and result_ok
        and review.get("consumed_target") == review_target
    )


def _control_rows(
    chain_id: str, result: dict[str, Any]
) -> list[dict[str, Any]]:
    if chain_id == "minkowski_1plus1":
        passed = (
            result.get("threshold_checks", {}).get(
                "finest_off_shell_divergence_over_100_times_on_shell"
            )
            is True
            and result.get("off_shell", {}).get("control_role")
            == "negative nonconservation control"
        )
        return [{
            "control_instance_id": "minkowski_off_shell_nonconservation",
            "chain_id": chain_id,
            "mechanism_class": "off_shell_nonconservation",
            "detected": passed,
        }]
    if chain_id == "conformal_connection_1plus1":
        control = result.get("naive_partial_divergence_negative_control", {})
        return [{
            "control_instance_id": "conformal_naive_partial",
            "chain_id": chain_id,
            "mechanism_class": "naive_partial_divergence",
            "detected": control.get("failure_detected") is True,
            "diagnostic_only_without_new_threshold": (
                control.get("diagnostic_only_not_guardrail_threshold") is True
            ),
        }]
    if chain_id == "de_sitter_1plus1":
        controls = result.get("negative_controls", {})
        return [
            {
                "control_instance_id": "de_sitter_naive_partial",
                "chain_id": chain_id,
                "mechanism_class": "naive_partial_divergence",
                "detected": controls.get("naive_partial_divergence", {}).get(
                    "failure_detected"
                ) is True,
            },
            {
                "control_instance_id": "de_sitter_frozen_connection",
                "chain_id": chain_id,
                "mechanism_class": "inconsistent_connection",
                "detected": controls.get("inconsistent_frozen_connection", {}).get(
                    "failure_detected"
                ) is True,
            },
            {
                "control_instance_id": "de_sitter_curvature_omission",
                "chain_id": chain_id,
                "mechanism_class": "curvature_derivative_omission",
                "detected": controls.get("curvature_derivative_omission", {}).get(
                    "failure_detected"
                ) is True,
            },
        ]
    adjudication = result.get("negative_controls", {}).get(
        "finest_resolution_adjudication", {}
    )
    mappings = (
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
    return [
        {
            "control_instance_id": instance,
            "chain_id": chain_id,
            "mechanism_class": mechanism,
            "detected": adjudication.get(source_key, {}).get("pass") is True,
        }
        for instance, mechanism, source_key in mappings
    ]


def _actual_geometry_evidence_passes(
    chain_id: str, result: dict[str, Any]
) -> bool:
    if chain_id == "minkowski_1plus1":
        return (
            result.get("mathematical_convention", {}).get("identity")
            == "partial_mu T^{mu nu} = E_phi partial^nu phi"
            and result.get("parameters", {}).get("resolutions_N")
            == [64, 128, 256, 512]
        )
    geometry = result.get("background_geometry", {})
    if chain_id == "conformal_connection_1plus1":
        return (
            geometry.get("background_geometry_classification")
            == "locally_flat_nontrivial_conformal_connection"
            and geometry.get("nonzero_connection_component_count") == 4
            and geometry.get("riemann_tensor_max_absolute_component") == 0.0
            and geometry.get("scalar_curvature") == 0.0
        )
    if chain_id == "de_sitter_1plus1":
        curvature = result.get("curvature_verification", {})
        return (
            result.get("background_geometry_classification")
            == "fixed_nonzero_curvature_1plus1_de_sitter_patch"
            and geometry.get("genuinely_nonzero_curvature_test_executed") is True
            and _same_number(geometry.get("scalar_curvature_measured"), 0.08)
            and curvature.get("minimum_absolute_measured_scalar_curvature", 0.0)
            > 0.05
            and curvature.get("maximum_route_agreement_absolute_error", 1.0)
            <= 1e-12
        )
    verification = result.get("geometry_verification", {})
    return (
        result.get("background_geometry_classification")
        == "fixed_nonzero_spatially_varying_curvature_2plus1_warped_periodic_background"
        and geometry.get("scalar_curvature_minimum", 0.0) < 0.0
        and geometry.get("scalar_curvature_maximum", 0.0) > 0.0
        and len(geometry.get("curvature_zero_crossings", [])) == 2
        and verification.get("structurally_allowed_nonzero_christoffel_component_count")
        == 3
        and verification.get("maximum_curvature_route_absolute_discrepancy", 1.0)
        <= 1e-12
    )


def _actual_profile_component_evidence_passes(
    chain_id: str, result: dict[str, Any]
) -> bool:
    if chain_id == "minkowski_1plus1":
        aggregates = result.get("off_shell", {}).get("resolution_aggregates", [])
        components = (
            set(aggregates[-1].get("divergence_norms", {})) - {"combined"}
            if aggregates
            else set()
        )
        return (
            components == {"nu_0", "nu_1"}
            and result.get("on_shell", {}).get("control_role")
            == "positive conservation control"
            and result.get("off_shell", {}).get("control_role")
            == "negative nonconservation control"
        )
    if chain_id in {"conformal_connection_1plus1", "de_sitter_1plus1"}:
        aggregates = result.get("off_shell", {}).get("resolution_aggregates", [])
        components = (
            set(aggregates[-1].get("covariant_divergence_norms", {}))
            - {"combined"}
            if aggregates
            else set()
        )
        return components == {"nu_eta", "nu_x"} and bool(
            result.get("on_shell", {}).get("control_role")
        ) and bool(result.get("off_shell", {}).get("control_role"))
    aggregates = result.get("profile_resolution_aggregates", [])
    profiles = {row.get("profile_id") for row in aggregates}
    component_sets = [
        set(row.get("identity_metrics", {}).get("components", {}))
        for row in aggregates
    ]
    return (
        profiles
        == {"on_shell_temporal_mode", "off_shell_x_mode", "off_shell_y_mode"}
        and len(aggregates) == 12
        and all(components == {"nu_t", "nu_x", "nu_y"} for components in component_sets)
    )


def _on_shell_policy_row(
    chain_id: str, result: dict[str, Any]
) -> dict[str, Any]:
    if chain_id != "warped_2plus1":
        on_shell = result.get("on_shell", {})
        passed = (
            on_shell.get("relative_error_against_zero_formed") is False
            and result.get("threshold_checks", {}).get(
                "finest_off_shell_divergence_over_100_times_on_shell"
            )
            is True
        )
        return {
            "chain_id": chain_id,
            "policy_id": "legacy_off_to_on_separation",
            "policy_passed": passed,
            "relative_error_against_exact_zero_formed": False,
        }
    aggregates = [
        row
        for row in result.get("profile_resolution_aggregates", [])
        if row.get("profile_id") == "on_shell_temporal_mode"
    ]
    metrics = [row.get("identity_metrics", {}).get("combined", {}) for row in aggregates]
    exact_zero_policy = bool(metrics) and all(
        item.get("reference_rms") == 0.0
        and item.get("relative_error") is None
        and item.get("relative_error_applicable") is False
        and item.get("convergence_status") == "not_applicable_exact_zero"
        for item in metrics
    )
    passed = (
        exact_zero_policy
        and result.get("threshold_checks", {}).get(
            "maximum_finest_on_shell_combined_absolute_divergence_error"
        )
        is True
    )
    return {
        "chain_id": chain_id,
        "policy_id": "exact_zero_absolute_divergence",
        "policy_passed": passed,
        "maximum_absolute_divergence": 1e-11,
        "relative_error_against_exact_zero_formed": False,
    }


LOCAL_GATE_MAP: dict[str, dict[str, tuple[str, ...]]] = {
    "minkowski_1plus1": {
        "analytic_reference": ("exact_coefficient_error_at_most_1e_12",),
        "on_off_shell_witness": (
            "finest_off_shell_divergence_over_100_times_on_shell",
        ),
    },
    "conformal_connection_1plus1": {
        "analytic_reference": ("exact_coefficient_error_at_most_1e_12",),
        "metric_compatibility": ("metric_compatibility_error_at_most_1e_12",),
        "patch_or_geometry_safety": (),
        "flat_limit": ("flat_limit_discrepancy_at_most_1e_12",),
        "on_off_shell_witness": (
            "finest_off_shell_divergence_over_100_times_on_shell",
        ),
    },
    "de_sitter_1plus1": {
        "analytic_reference": ("exact_coefficient_error_at_most_1e_12",),
        "metric_compatibility": ("metric_compatibility_error_at_most_1e_12",),
        "curvature_route": (
            "absolute_scalar_curvature_at_least_0_05",
            "curvature_route_discrepancy_at_most_1e_12",
        ),
        "patch_or_geometry_safety": (),
        "flat_limit": ("flat_limit_discrepancy_at_most_1e_12",),
        "on_off_shell_witness": (
            "finest_off_shell_divergence_over_100_times_on_shell",
        ),
    },
    "warped_2plus1": {
        "analytic_reference": (
            "maximum_analytic_profile_residual_reference_error",
        ),
        "metric_compatibility": (
            "maximum_metric_compatibility_absolute_error",
        ),
        "curvature_route": (
            "maximum_curvature_route_absolute_discrepancy",
            "minimum_curvature_peak_absolute_value",
            "minimum_curvature_peak_to_peak_variation",
        ),
        "patch_or_geometry_safety": (),
        "flat_limit": ("maximum_flat_limit_absolute_discrepancy",),
        "on_off_shell_witness": (
            "maximum_finest_on_shell_combined_absolute_divergence_error",
            "maximum_finest_x_mode_combined_relative_identity_error",
            "maximum_finest_y_mode_combined_relative_identity_error",
        ),
    },
}


def _source_local_check_row(
    chain_id: str,
    result: dict[str, Any],
    contract_row: dict[str, Any],
) -> dict[str, Any]:
    thresholds = result.get("threshold_checks", {})
    checks: list[dict[str, Any]] = []
    for check_id, source_status in contract_row.items():
        if check_id == "chain_id":
            continue
        if source_status.startswith("not_applicable"):
            status, value = "not_applicable", None
        elif source_status == "baseline_not_recovery_test":
            status, value = "baseline_not_recovery_test", None
        else:
            gate_ids = LOCAL_GATE_MAP[chain_id][check_id]
            if gate_ids:
                passed = all(thresholds.get(gate_id) is True for gate_id in gate_ids)
            elif chain_id == "conformal_connection_1plus1":
                geometry = result.get("background_geometry", {})
                passed = (
                    geometry.get("background_geometry_classification")
                    == "locally_flat_nontrivial_conformal_connection"
                    and geometry.get("curvature_test_claimed") is False
                    and geometry.get("riemann_tensor_max_absolute_component") == 0.0
                )
            elif chain_id == "de_sitter_1plus1":
                safety = result.get("patch_domain_safety", {})
                passed = (
                    safety.get("strictly_inside_coordinate_patch") is True
                    and safety.get(
                        "coordinate_patch_boundary_is_physical_curvature_singularity"
                    )
                    is False
                    and safety.get("minimum_one_minus_H_eta_over_domain", 0.0) > 0.0
                )
            else:
                safety = result.get("geometry_safety_verification", {})
                passed = (
                    safety.get("all_frozen_grids_nonsingular") is True
                    and safety.get("minimum_absolute_determinant", 0.0) > 0.0
                    and len(safety.get("rows", [])) == 4
                    and all(row.get("nonsingular") is True for row in safety["rows"])
                )
            status, value = ("applicable_passed", True) if passed else ("failed", False)
        checks.append(
            {
                "check_id": check_id,
                "status": status,
                "value": value,
                "source_classification": source_status,
            }
        )
    return {"chain_id": chain_id, "checks": checks}


def independent_reconstruct_source_family(
    guardrail_path: Path = GUARDRAIL_PATH,
) -> dict[str, Any]:
    """Reconstruct the family directly from the guardrail and 24 source artifacts.

    This code deliberately does not import or call the execution calculation's
    extraction, decision, or tamper-control implementations.
    """

    guardrail = load_strict_json_object(guardrail_path, style="report")
    guardrail_hash_ok = sha256_path(guardrail_path) == EXPECTED_EXECUTION_HASHES[
        "guardrail_sha256"
    ]
    chains = guardrail.get("source_chains", [])
    chain_ids = [chain.get("chain_id") for chain in chains]
    all_artifacts = [item for chain in chains for item in chain.get("artifacts", [])]
    paths_unique = len({item.get("path") for item in all_artifacts}) == 24
    chain_records: list[dict[str, Any]] = []
    background_rows: list[dict[str, Any]] = []
    comparable_rows: list[dict[str, Any]] = []
    source_decisions: list[dict[str, Any]] = []
    on_shell_rows: list[dict[str, Any]] = []
    local_checks: list[dict[str, Any]] = []
    controls: list[dict[str, Any]] = []
    canonical_source_json_passed = True
    internal_links_passed = True
    source_hashes_passed = True
    identity_sources_passed = True
    warped_language_isolated = True

    for chain in chains:
        chain_id = chain.get("chain_id")
        expectation = CHAIN_EXPECTATIONS.get(str(chain_id), {})
        loaded: dict[str, dict[str, Any]] = {}
        artifact_rows: list[dict[str, Any]] = []
        for artifact in chain.get("artifacts", []):
            path = REPO_ROOT / artifact["path"]
            actual_hash = sha256_path(path)
            matches = actual_hash == artifact.get("sha256")
            source_hashes_passed &= matches
            artifact_rows.append(
                {
                    "artifact_role": artifact["artifact_role"],
                    "path": artifact["path"],
                    "expected_sha256": artifact["sha256"],
                    "actual_sha256": actual_hash,
                    "hash_matches": matches,
                }
            )
            if artifact["artifact_role"] != "calculation_script":
                try:
                    loaded[artifact["artifact_role"]] = _load_source_json(artifact)
                except (OSError, UnicodeError, json.JSONDecodeError, ValueError):
                    canonical_source_json_passed = False
                    raise
        links_ok = _source_internal_links(chain, loaded)
        internal_links_passed &= links_ok
        result = loaded["calculation_result"]
        review = loaded["independent_review"]
        manifest = loaded["calculation_manifest"]
        thresholds = result.get("threshold_checks", {})
        gate_ids = chain.get("upstream_gate_ids", [])
        for gate_id in gate_ids:
            source_decisions.append(
                {
                    "chain_id": chain_id,
                    "qualified_gate_id": f"{chain_id}::{gate_id}",
                    "source_gate_id": gate_id,
                    "passed": thresholds.get(gate_id) is True,
                }
            )
        review_verification = review.get("verification", {})
        if chain_id == "warped_2plus1":
            reproduction = review_verification.get("fresh_subprocess_reproduction", {})
            reproduction_strength_preserved = (
                reproduction.get("run_count") == 2
                and reproduction.get("both_runs_byte_identical") is True
                and reproduction.get("fresh_runs_match_repository_artifacts") is True
            )
        else:
            reproduction_strength_preserved = (
                "fresh_subprocess_reproduction" not in review_verification
            )
        accepted = (
            review.get("status") == expectation.get("review_status")
            and review.get("claim", {}).get("claim_ceiling_level") == 3
            and review.get("claim", {}).get("primary_label") == "E-REPRO"
            and review_verification.get("accepted") is True
            and review_verification.get("primary_claim_label") == "E-REPRO"
            and review_verification.get("mismatch_codes") == []
            and reproduction_strength_preserved
        )
        grid_schedule = result.get("parameters", {}).get("resolutions_N")
        metadata_ok = (
            chain.get("spacetime_dimension") == expectation.get("dimension")
            and chain.get("divergence_component_count")
            == expectation.get("component_count")
            and chain.get("geometry_class") == expectation.get("geometry_class")
            and chain.get("connection_class") == expectation.get("connection_class")
            and chain.get("curvature_class") == expectation.get("curvature_class")
            and grid_schedule == expectation.get("grid_schedule")
            and manifest.get("calculation_id") == result.get("calculation_id")
            and _actual_geometry_evidence_passes(str(chain_id), result)
        )
        background_rows.append(
            {
                "chain_id": chain_id,
                "spacetime_dimension": expectation.get("dimension"),
                "divergence_component_count": expectation.get("component_count"),
                "geometry_class": expectation.get("geometry_class"),
                "connection_class": expectation.get("connection_class"),
                "curvature_class": expectation.get("curvature_class"),
                "grid_schedule": grid_schedule,
                "grid_shape_semantics": expectation.get("grid_shape_semantics"),
                "grid_meaning": expectation.get("grid_shape_semantics"),
                "finest_grid_shape": (
                    [grid_schedule[-1], grid_schedule[-1]]
                    if expectation.get("dimension") == 3
                    else [grid_schedule[-1]]
                ),
                "metadata_verified_from_source": metadata_ok,
                "profile_component_evidence_verified_from_source": (
                    _actual_profile_component_evidence_passes(
                        str(chain_id), result
                    )
                ),
            }
        )
        evidence = result.get("threshold_evidence", {})
        if chain_id != "warped_2plus1":
            comparable_rows.append(
                {
                    "chain_id": chain_id,
                    "profile_row_id": expectation["profile_id"],
                    "p_min": evidence.get(expectation["p_key"]),
                    "off_shell_relative_identity_error": evidence.get(
                        expectation["error_key"]
                    ),
                    "metric_kind": (
                        "within_background_dimensionless_off_shell_relative_"
                        "identity_error"
                    ),
                }
            )
        else:
            comparable_rows.extend(
                [
                    {
                        "chain_id": chain_id,
                        "profile_row_id": "warped_x_off_shell",
                        "p_min": evidence.get(
                            "minimum_two_finest_x_mode_convergence_order"
                        ),
                        "off_shell_relative_identity_error": evidence.get(
                            "finest_x_mode_combined_relative_identity_error"
                        ),
                        "metric_kind": (
                            "within_background_dimensionless_off_shell_"
                            "relative_identity_error"
                        ),
                    },
                    {
                        "chain_id": chain_id,
                        "profile_row_id": "warped_y_off_shell",
                        "p_min": evidence.get(
                            "minimum_two_finest_y_mode_convergence_order"
                        ),
                        "off_shell_relative_identity_error": evidence.get(
                            "finest_y_mode_combined_relative_identity_error"
                        ),
                        "metric_kind": (
                            "within_background_dimensionless_off_shell_"
                            "relative_identity_error"
                        ),
                    },
                ]
            )
        on_shell_rows.append(_on_shell_policy_row(str(chain_id), result))
        local_contract = next(
            row
            for row in guardrail["applicability_typed_local_check_ledger"]
            if row["chain_id"] == chain_id
        )
        local_checks.append(
            _source_local_check_row(str(chain_id), result, local_contract)
        )
        controls.extend(_control_rows(str(chain_id), result))

        convention = result.get("mathematical_convention", {}).get("identity", "")
        if chain_id == "minkowski_1plus1":
            identity_sources_passed &= (
                convention
                == "partial_mu T^{mu nu} = E_phi partial^nu phi"
                and chain.get("equation_mapping", {}).get("source_equation_id")
                == FLAT_EQUATION_ID
                and chain.get("equation_mapping", {}).get("covariant_equation_id")
                == COVARIANT_EQUATION_ID
            )
        else:
            expected_convention = (
                "nabla_mu T^{mu nu}=E_phi*nabla^nu phi"
                if chain_id == "warped_2plus1"
                else "nabla_mu T^{mu nu} = E_phi nabla^nu phi"
            )
            identity_sources_passed &= (
                convention == expected_convention
                and chain.get("equation_mapping", {}).get("source_equation_id")
                == COVARIANT_EQUATION_ID
            )
        if chain_id == "warped_2plus1":
            forbidden = {
                "two_dimensional_einstein_gravity_degenerate",
                "einstein_tensor_identically_zero_in_two_dimensions",
            }
            warped_language_isolated &= not _contains_key(result, forbidden)

        chain_records.append(
            {
                "chain_id": chain_id,
                "artifacts": artifact_rows,
                "artifact_hashes_match": all(row["hash_matches"] for row in artifact_rows),
                "internal_links_match": links_ok,
                "accepted_level_3_e_repro": accepted,
                "metadata_verified_from_source": metadata_ok,
                "upstream_decision_count": len(gate_ids),
                "all_upstream_decisions_passed": (
                    set(thresholds) == set(gate_ids)
                    and len(thresholds) == chain.get("upstream_decision_count")
                    and all(value is True for value in thresholds.values())
                    and result.get("all_thresholds_passed") is True
                ),
            }
        )

    compendium_path = REPO_ROOT / COMPENDIUM_RELATIVE_PATH
    compendium_text = compendium_path.read_text(encoding="utf-8")
    compendium_ok = (
        sha256_path(compendium_path) == COMPENDIUM_SHA256
        and FLAT_EQUATION_ID in compendium_text
        and COVARIANT_EQUATION_ID in compendium_text
    )
    family = {
        "guardrail_schema_matches": guardrail.get("schema_id") == GUARDRAIL_SCHEMA_ID,
        "guardrail_hash_matches": guardrail_hash_ok,
        "source_chain_count": len(chains),
        "bound_artifact_count": len(all_artifacts),
        "chain_order_matches": chain_ids == list(CHAIN_ORDER),
        "artifact_paths_unique": paths_unique,
        "source_hashes_passed": source_hashes_passed,
        "canonical_source_json_passed": canonical_source_json_passed,
        "internal_links_passed": internal_links_passed,
        "all_values_finite": True,
        "chain_records": chain_records,
        "artifact_binding_contract": {
            chain["chain_id"]: [
                {
                    "artifact_role": artifact["artifact_role"],
                    "path": artifact["path"],
                    "sha256": artifact["sha256"],
                }
                for artifact in chain["artifacts"]
            ]
            for chain in chains
        },
        "background_comparison_rows": background_rows,
        "comparable_rows": comparable_rows,
        "qualified_source_decisions": source_decisions,
        "source_local_on_shell_policy_rows": on_shell_rows,
        "applicability_typed_local_check_rows": local_checks,
        "control_instances": controls,
        "identity_sources_passed": identity_sources_passed,
        "compendium_boundary_passed": compendium_ok,
        "warped_2plus1_degeneracy_language_isolated": warped_language_isolated,
        "comparison_policy": {
            "family_envelopes_allowed": [
                "dimensionless_second_order_convergence_p_min",
                "within_background_dimensionless_off_shell_relative_identity_error",
            ],
            "forbidden_metric_pooled": False,
            "performance_ranking_performed": False,
            "two_plus_one_grid_N_means_N_by_N": True,
        },
        "synthesis_classification": copy.deepcopy(
            guardrail.get("synthesis_classification", {})
        ),
        "boundary": copy.deepcopy(guardrail.get("boundary", {})),
        "unit_ledger_live": False,
        "execution_candidate_only": True,
        "candidate_claim_level": guardrail.get("claim_ceiling", {}).get(
            "claim_ladder_level"
        ),
        "candidate_primary_label": guardrail.get("claim_ceiling", {}).get(
            "candidate_primary_label"
        ),
        "review_accepted": False,
        "equation_surface_upgraded": False,
    }
    family["family_minimum_p_min"] = min(
        float(row["p_min"]) for row in comparable_rows
    )
    family["family_maximum_off_shell_relative_error"] = max(
        float(row["off_shell_relative_identity_error"]) for row in comparable_rows
    )
    family["all_values_finite"] = _all_finite(family)
    return family


def _contains_key(value: Any, forbidden: set[str]) -> bool:
    if isinstance(value, dict):
        if any(key in forbidden for key in value):
            return True
        return any(_contains_key(item, forbidden) for item in value.values())
    if isinstance(value, list):
        return any(_contains_key(item, forbidden) for item in value)
    return False


def independently_adjudicate(family: dict[str, Any]) -> list[dict[str, Any]]:
    rows = family.get("background_comparison_rows", [])
    chain_records = family.get("chain_records", [])
    comparable = family.get("comparable_rows", [])
    source_decisions = family.get("qualified_source_decisions", [])
    on_shell = family.get("source_local_on_shell_policy_rows", [])
    local_checks = family.get("applicability_typed_local_check_rows", [])
    controls = family.get("control_instances", [])
    comparison = family.get("comparison_policy", {})
    boundary = family.get("boundary", {})

    artifact_integrity = (
        family.get("guardrail_schema_matches") is True
        and family.get("guardrail_hash_matches") is True
        and family.get("source_chain_count") == 4
        and family.get("bound_artifact_count") == 24
        and family.get("chain_order_matches") is True
        and family.get("artifact_paths_unique") is True
        and family.get("source_hashes_passed") is True
        and family.get("canonical_source_json_passed") is True
        and family.get("internal_links_passed") is True
        and family.get("all_values_finite") is True
        and _all_finite(family)
        and all(item.get("artifact_hashes_match") is True for item in chain_records)
        and all(item.get("internal_links_match") is True for item in chain_records)
        and all(
            [
                {
                    "artifact_role": artifact.get("artifact_role"),
                    "path": artifact.get("path"),
                    "sha256": artifact.get("expected_sha256"),
                }
                for artifact in record.get("artifacts", [])
            ]
            == family.get("artifact_binding_contract", {}).get(
                record.get("chain_id")
            )
            and all(
                artifact.get("actual_sha256") == artifact.get("expected_sha256")
                and artifact.get("hash_matches") is True
                for artifact in record.get("artifacts", [])
            )
            for record in chain_records
        )
    )
    review_acceptance = (
        len(chain_records) == 4
        and all(item.get("accepted_level_3_e_repro") is True for item in chain_records)
    )
    identity_mapping = (
        family.get("identity_sources_passed") is True
        and family.get("compendium_boundary_passed") is True
    )
    geometry_coverage = (
        len(rows) == 4
        and {row.get("geometry_class") for row in rows}
        == {value["geometry_class"] for value in CHAIN_EXPECTATIONS.values()}
        and all(row.get("metadata_verified_from_source") is True for row in rows)
    )
    dimension_coverage = (
        {row.get("spacetime_dimension") for row in rows} == {2, 3}
        and {row.get("divergence_component_count") for row in rows} == {2, 3}
    )
    connection_coverage = {row.get("connection_class") for row in rows} == {
        "zero_connection",
        "nonzero_connection",
    }
    curvature_coverage = {
        row.get("curvature_class") for row in rows
    } == {
        "zero_curvature",
        "constant_nonzero_curvature",
        "spatially_varying_signed_curvature_with_zero_crossings",
    }
    profile_coverage = (
        len(rows) == 4
        and {row.get("chain_id") for row in rows} == set(CHAIN_ORDER)
        and next(
            row for row in rows if row.get("chain_id") == "warped_2plus1"
        ).get("divergence_component_count")
        == 3
        and len(comparable) == 5
        and all(
            row.get("profile_component_evidence_verified_from_source") is True
            for row in rows
        )
    )
    upstream = (
        len(source_decisions) == 37
        and len({row.get("qualified_gate_id") for row in source_decisions}) == 37
        and all(row.get("passed") is True for row in source_decisions)
        and [item.get("upstream_decision_count") for item in chain_records]
        == [4, 6, 11, 16]
        and all(item.get("all_upstream_decisions_passed") is True for item in chain_records)
    )
    convergence = (
        len(comparable) == 5
        and math.isfinite(float(family.get("family_minimum_p_min", math.nan)))
        and family.get("family_minimum_p_min") >= 1.8
        and family.get("family_minimum_p_min")
        == min(row.get("p_min") for row in comparable)
    )
    off_shell_error = (
        len(comparable) == 5
        and math.isfinite(
            float(family.get("family_maximum_off_shell_relative_error", math.nan))
        )
        and family.get("family_maximum_off_shell_relative_error") <= 0.02
        and family.get("family_maximum_off_shell_relative_error")
        == max(row.get("off_shell_relative_identity_error") for row in comparable)
    )
    on_shell_policy = (
        len(on_shell) == 4
        and {row.get("chain_id") for row in on_shell} == set(CHAIN_ORDER)
        and all(row.get("policy_passed") is True for row in on_shell)
        and all(
            row.get("relative_error_against_exact_zero_formed") is False
            for row in on_shell
        )
    )
    applicability = len(local_checks) == 4
    if applicability:
        for row in local_checks:
            checks = row.get("checks", [])
            applicability &= len(checks) == 6
            for check in checks:
                status = check.get("status")
                if status in {"not_applicable", "baseline_not_recovery_test"}:
                    applicability &= check.get("value") is None
                elif status == "applicable_passed":
                    applicability &= check.get("value") is True
                else:
                    applicability = False
    control_coverage = (
        len(controls) == 10
        and len({row.get("control_instance_id") for row in controls}) == 10
        and {row.get("mechanism_class") for row in controls} == CONTROL_MECHANISMS
        and all(row.get("detected") is True for row in controls)
        and next(
            row
            for row in controls
            if row.get("control_instance_id") == "conformal_naive_partial"
        ).get("diagnostic_only_without_new_threshold")
        is True
    )
    comparison_policy = (
        comparison.get("family_envelopes_allowed")
        == [
            "dimensionless_second_order_convergence_p_min",
            "within_background_dimensionless_off_shell_relative_identity_error",
        ]
        and comparison.get("forbidden_metric_pooled") is False
        and comparison.get("performance_ranking_performed") is False
        and comparison.get("two_plus_one_grid_N_means_N_by_N") is True
        and all(
            row.get("metric_kind")
            == "within_background_dimensionless_off_shell_relative_identity_error"
            for row in comparable
        )
    )
    boundary_ok = (
        family.get("synthesis_classification", {}).get("new_pde_calculation")
        is False
        and family.get("synthesis_classification", {}).get("statistical_sample")
        is False
        and family.get("synthesis_classification", {}).get(
            "implementation_lineage_independent"
        )
        is False
        and family.get("synthesis_classification", {}).get(
            "arbitrary_background_generalization_allowed"
        )
        is False
        and family.get("warped_2plus1_degeneracy_language_isolated") is True
        and family.get("execution_candidate_only") is True
        and family.get("candidate_claim_level") == 3
        and family.get("candidate_primary_label") == "E-REPRO"
        and family.get("review_accepted") is False
        and family.get("equation_surface_upgraded") is False
        and family.get("unit_ledger_live") is False
        and boundary.get("unit_ledger_status") == "queued_non_live_hard_gate"
        and boundary.get("unit_ledger_target") == SUCCESS_TARGET
        and boundary.get("unit_ledger_required_before_stronger_claims") is True
        and all(boundary.get(key) is False for key in FORBIDDEN_BOUNDARY_TRUE)
    )
    passes = (
        artifact_integrity,
        review_acceptance,
        identity_mapping,
        geometry_coverage,
        dimension_coverage,
        connection_coverage,
        curvature_coverage,
        profile_coverage,
        upstream,
        convergence,
        off_shell_error,
        on_shell_policy,
        applicability,
        control_coverage,
        comparison_policy,
        boundary_ok,
    )
    return [
        {
            "decision_number": number,
            "decision_id": decision_id,
            "passed": bool(passed),
        }
        for number, (decision_id, passed) in enumerate(
            zip(DECISION_IDS, passes), start=1
        )
    ]


def _apply_tamper(control_id: str, family: dict[str, Any]) -> None:
    if control_id == "omitted_background":
        removed = family["chain_records"][-1]["chain_id"]
        family["chain_records"].pop()
        family["background_comparison_rows"] = [
            row
            for row in family["background_comparison_rows"]
            if row["chain_id"] != removed
        ]
        family["comparable_rows"] = [
            row for row in family["comparable_rows"] if row["chain_id"] != removed
        ]
        family["qualified_source_decisions"] = [
            row
            for row in family["qualified_source_decisions"]
            if row["chain_id"] != removed
        ]
        family["source_local_on_shell_policy_rows"] = [
            row
            for row in family["source_local_on_shell_policy_rows"]
            if row["chain_id"] != removed
        ]
        family["applicability_typed_local_check_rows"] = [
            row
            for row in family["applicability_typed_local_check_rows"]
            if row["chain_id"] != removed
        ]
        family["control_instances"] = [
            row
            for row in family["control_instances"]
            if row["chain_id"] != removed
        ]
        family["source_chain_count"] = 3
        family["bound_artifact_count"] = 18
    elif control_id == "swapped_chain_artifacts":
        first = family["chain_records"][0]
        second = family["chain_records"][1]
        first["artifacts"], second["artifacts"] = (
            second["artifacts"],
            first["artifacts"],
        )
    elif control_id == "masked_upstream_failure":
        family["qualified_source_decisions"][0]["passed"] = False
    elif control_id == "inapplicable_zero_fill":
        for row in family["applicability_typed_local_check_rows"]:
            for check in row["checks"]:
                if check["status"] == "not_applicable":
                    check["status"] = "applicable_passed"
                    check["value"] = 0
                    return
    elif control_id == "on_shell_relative_error_injection":
        family["source_local_on_shell_policy_rows"][-1][
            "relative_error_against_exact_zero_formed"
        ] = True
    elif control_id == "raw_absolute_error_substitution":
        family["comparable_rows"][0]["metric_kind"] = "raw_absolute_divergence_error"
    elif control_id == "removed_control_instance":
        family["control_instances"].pop()
    elif control_id in {"input_hash_tamper", "review_hash_tamper", "result_hash_tamper"}:
        target_role = {
            "input_hash_tamper": "guardrail",
            "review_hash_tamper": "independent_review",
            "result_hash_tamper": "calculation_result",
        }[control_id]
        target = next(
            artifact
            for record in family["chain_records"]
            for artifact in record["artifacts"]
            if artifact["artifact_role"] == target_role
        )
        target["expected_sha256"] = "0" * 64
    elif control_id == "nonfinite_injection":
        family["chain_records"][0]["nonfinite_integrity_probe"] = math.nan
    elif control_id == "degeneracy_language_leak":
        family["warped_2plus1_degeneracy_language_isolated"] = False
    elif control_id == "collapsed_curvature_classes":
        for row in family["background_comparison_rows"]:
            if row["curvature_class"] == "spatially_varying_signed_curvature_with_zero_crossings":
                row["curvature_class"] = "constant_nonzero_curvature"
    elif control_id == "forbidden_claim_promotion":
        family["boundary"]["level_4_or_level_5_claimed"] = True
    else:
        raise KeyError(control_id)


def independently_run_tamper_controls(
    family: dict[str, Any]
) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    for control_id, expected_failed in TAMPER_EXPECTATIONS.items():
        candidate = copy.deepcopy(family)
        _apply_tamper(control_id, candidate)
        decisions = independently_adjudicate(candidate)
        failed = [row["decision_id"] for row in decisions if row["passed"] is False]
        records.append(
            {
                "control_id": control_id,
                "expected_failed_decision_id": expected_failed,
                "observed_failed_decision_ids": failed,
                "detected": expected_failed in failed,
            }
        )
    return records


def _same_number(left: Any, right: Any, tolerance: float = 5e-13) -> bool:
    if not isinstance(left, (int, float)) or not isinstance(right, (int, float)):
        return False
    return math.isfinite(float(left)) and math.isfinite(float(right)) and math.isclose(
        float(left), float(right), rel_tol=tolerance, abs_tol=tolerance
    )


def _result_semantic_matches(
    result: dict[str, Any],
    family: dict[str, Any],
    decisions: list[dict[str, Any]],
    tamper_controls: list[dict[str, Any]],
) -> dict[str, bool]:
    expected_decisions = {row["decision_id"]: row["passed"] for row in decisions}
    observed_decisions = {
        row.get("decision_id"): row.get("passed", row.get("pass"))
        for row in result.get("synthesis_decisions", [])
    }
    observed_tamper_rows = result.get("synthesis_tamper_controls", [])
    observed_controls = {
        row.get("control_id"): row
        for row in observed_tamper_rows
        if isinstance(row, dict)
    }
    independent_control_ids = {row["control_id"] for row in tamper_controls}
    tamper_match = (
        set(observed_controls) == independent_control_ids == set(TAMPER_EXPECTATIONS)
        and all(row["detected"] is True for row in tamper_controls)
    )
    if tamper_match:
        for control_id, expected_failed in TAMPER_EXPECTATIONS.items():
            row = observed_controls[control_id]
            tamper_match &= (
                row.get("expected_failed_decision_id") == expected_failed
                and expected_failed in row.get("observed_failed_decision_ids", [])
                and row.get("fresh_deep_copy_used") is True
                and row.get("passed", row.get("detected")) is True
            )
    comparable_contract = result.get("comparable_metric_contract", {})
    convergence_rows = comparable_contract.get("convergence_rows", [])
    error_rows = comparable_contract.get("off_shell_relative_error_rows", [])
    convergence_by_profile = {
        row.get("profile_row_id"): row for row in convergence_rows
    }
    error_by_profile = {row.get("profile_row_id"): row for row in error_rows}
    result_rows = [
        {
            "chain_id": convergence_by_profile[profile_id].get("chain_id"),
            "profile_row_id": profile_id,
            "p_min": convergence_by_profile[profile_id].get("p_min"),
            "off_shell_relative_identity_error": error_by_profile.get(
                profile_id, {}
            ).get("off_shell_relative_identity_error"),
            "metric_kind": error_by_profile.get(profile_id, {}).get(
                "metric_kind"
            ),
        }
        for profile_id in convergence_by_profile
    ]
    expected_by_profile = {
        row["profile_row_id"]: row for row in family["comparable_rows"]
    }
    observed_by_profile = {row.get("profile_row_id"): row for row in result_rows}
    comparable_match = set(observed_by_profile) == set(expected_by_profile)
    if comparable_match:
        for key, expected in expected_by_profile.items():
            observed = observed_by_profile[key]
            comparable_match &= (
                observed.get("chain_id") == expected["chain_id"]
                and _same_number(observed.get("p_min"), expected["p_min"])
                and _same_number(
                    observed.get("off_shell_relative_identity_error"),
                    expected["off_shell_relative_identity_error"],
                )
                and observed.get("metric_kind") == expected["metric_kind"]
            )
    family_min = comparable_contract.get(
        "family_minimum_p_min",
        comparable_contract.get("family_minimum_p_min_reference"),
    )
    family_max = comparable_contract.get(
        "family_maximum_off_shell_relative_error",
        comparable_contract.get(
            "family_maximum_off_shell_relative_identity_error",
            comparable_contract.get(
                "family_maximum_off_shell_relative_error_reference"
            ),
        ),
    )
    return {
        "source_chain_records": _source_chain_rows_match(
            result.get("source_chains", []), family["chain_records"]
        ),
        "background_rows": _background_rows_match(
            result.get("background_comparison_rows", []),
            family["background_comparison_rows"],
        ),
        "comparable_rows_and_envelopes": (
            comparable_match
            and _same_number(family_min, family["family_minimum_p_min"])
            and _same_number(
                family_max, family["family_maximum_off_shell_relative_error"]
            )
        ),
        "thirty_seven_source_decisions": _qualified_decisions_match(
            result.get("qualified_source_decisions", []),
            family["qualified_source_decisions"],
        ),
        "on_shell_policies": _rows_by_chain_match(
            _normalized_on_shell_rows(
                result.get("source_local_on_shell_policy_rows", [])
            ),
            _normalized_on_shell_rows(
                family["source_local_on_shell_policy_rows"]
            ),
            required=(
                "policy_id",
                "policy_passed",
                "relative_error_against_exact_zero_formed",
            ),
        ),
        "applicability": _applicability_matches(
            result.get("applicability_typed_local_check_rows", []),
            family["applicability_typed_local_check_rows"],
        ),
        "controls": _controls_match(
            result.get("control_coverage", {}), family["control_instances"]
        ),
        "sixteen_decisions": observed_decisions == expected_decisions,
        "fourteen_tamper_controls": tamper_match,
    }


def _background_rows_match(observed: list[Any], expected: list[Any]) -> bool:
    keys = (
        "spacetime_dimension",
        "divergence_component_count",
        "geometry_class",
        "connection_class",
        "curvature_class",
        "grid_schedule",
        "grid_meaning",
        "finest_grid_shape",
    )
    observed_by = {
        row.get("chain_id"): row for row in observed if isinstance(row, dict)
    }
    expected_by = {row["chain_id"]: row for row in expected}
    return set(observed_by) == set(expected_by) and all(
        all(observed_by[chain].get(key) == row.get(key) for key in keys)
        for chain, row in expected_by.items()
    )


def _source_chain_rows_match(
    observed: list[Any], expected: list[dict[str, Any]]
) -> bool:
    observed_by = {
        row.get("chain_id"): row for row in observed if isinstance(row, dict)
    }
    expected_by = {row["chain_id"]: row for row in expected}
    if set(observed_by) != set(expected_by) or len(observed_by) != 4:
        return False
    for chain_id, source in expected_by.items():
        expected_artifacts = [
            {
                "artifact_role": artifact["artifact_role"],
                "path": artifact["path"],
                "sha256": artifact["expected_sha256"],
            }
            for artifact in source["artifacts"]
        ]
        observed_row = observed_by[chain_id]
        if (
            observed_row.get("artifacts") != expected_artifacts
            or observed_row.get("artifact_integrity_verified") is not True
            or observed_row.get("accepted") is not True
            or observed_row.get("claim_ceiling_level") != 3
            or observed_row.get("primary_label") != "E-REPRO"
        ):
            return False
    return True


def _qualified_decisions_match(observed: list[Any], expected: list[Any]) -> bool:
    observed_by = {
        row.get("qualified_gate_id"): row.get("passed", row.get("pass"))
        for row in observed
        if isinstance(row, dict)
    }
    expected_by = {row["qualified_gate_id"]: row["passed"] for row in expected}
    return observed_by == expected_by


def _rows_by_chain_match(
    observed: list[Any], expected: list[Any], *, required: Iterable[str]
) -> bool:
    observed_by = {row.get("chain_id"): row for row in observed if isinstance(row, dict)}
    expected_by = {row["chain_id"]: row for row in expected}
    return set(observed_by) == set(expected_by) and all(
        all(observed_by[chain].get(key) == row.get(key) for key in required)
        for chain, row in expected_by.items()
    )


def _normalized_on_shell_rows(rows: list[Any]) -> list[dict[str, Any]]:
    normalized: list[dict[str, Any]] = []
    for row in rows:
        if not isinstance(row, dict):
            continue
        policy = row.get("policy", {})
        normalized.append(
            {
                "chain_id": row.get("chain_id"),
                "policy_id": row.get("policy_id", policy.get("policy_id")),
                "policy_passed": row.get("policy_passed", row.get("passed")),
                "relative_error_against_exact_zero_formed": row.get(
                    "relative_error_against_exact_zero_formed",
                    row.get("relative_error_against_zero_formed"),
                ),
            }
        )
    return normalized


def _applicability_matches(observed: list[Any], expected: list[Any]) -> bool:
    def normalized(rows: list[Any]) -> dict[str, dict[str, tuple[Any, Any]]]:
        result: dict[str, dict[str, tuple[Any, Any]]] = {}
        for row in rows:
            if not isinstance(row, dict):
                continue
            raw_checks = row.get("checks", [])
            if isinstance(raw_checks, dict):
                checks = [
                    {"check_id": check_id, **check}
                    for check_id, check in raw_checks.items()
                ]
            else:
                checks = raw_checks
            result[row.get("chain_id")] = {
                check.get("check_id"): (
                    (
                        "passed"
                        if check.get("status") in {"passed", "applicable_passed"}
                        else check.get("status")
                    ),
                    (
                        None
                        if check.get("status")
                        in {"not_applicable", "baseline_not_recovery_test"}
                        and check.get("value") is None
                        else "present"
                        if check.get("value") is not None
                        else "missing"
                    ),
                )
                for check in checks
                if isinstance(check, dict)
            }
        return result
    return normalized(observed) == normalized(expected)


def _controls_match(observed: Any, expected: list[dict[str, Any]]) -> bool:
    if isinstance(observed, dict):
        rows = observed.get("instances", observed.get("control_instances", []))
    else:
        rows = observed
    observed_by = {
        row.get("control_instance_id"): (
            row.get("mechanism_class"), row.get("detected", row.get("passed"))
        )
        for row in rows
        if isinstance(row, dict)
    }
    expected_by = {
        row["control_instance_id"]: (row["mechanism_class"], row["detected"])
        for row in expected
    }
    return observed_by == expected_by


def _fixed_subprocess_environment() -> dict[str, str]:
    environment = dict(os.environ)
    environment.update(
        {
            "PYTHONUTF8": "1",
            "PYTHONHASHSEED": "0",
            "TZ": "UTC",
            "LC_ALL": "C.UTF-8",
            "LANG": "C.UTF-8",
        }
    )
    return environment


def _run_fresh_execution(directory: Path) -> dict[str, bytes]:
    result = directory / "result.json"
    manifest = directory / "manifest.json"
    execution_report = directory / "execution-report.json"
    diagnostic = directory / "preflight-diagnostic.json"
    environment = _fixed_subprocess_environment()
    calculation = subprocess.run(
        [
            sys.executable,
            "-m",
            (
                "formal.python.toe.calculations."
                "calc_scalar_stress_energy_covariant_divergence_identity_multi_"
                "background_robustness"
            ),
            "--output",
            str(result),
            "--manifest",
            str(manifest),
            "--preflight-diagnostic",
            str(diagnostic),
        ],
        cwd=REPO_ROOT,
        env=environment,
        check=False,
        capture_output=True,
        text=True,
    )
    if calculation.returncode != 0:
        raise RuntimeError(f"fresh synthesis failed: {calculation.stderr}")
    if diagnostic.exists():
        raise RuntimeError("successful fresh synthesis emitted a preflight diagnostic")
    execution = subprocess.run(
        [
            sys.executable,
            "-m",
            (
                "formal.python.tools.scalar_stress_energy_covariant_divergence_"
                "identity_multi_background_robustness_calculation_execution_report"
            ),
            "--guardrail",
            str(GUARDRAIL_PATH),
            "--script",
            str(SCRIPT_PATH),
            "--output",
            str(result),
            "--manifest",
            str(manifest),
            "--out",
            str(execution_report),
        ],
        cwd=REPO_ROOT,
        env=environment,
        check=False,
        capture_output=True,
        text=True,
    )
    if execution.returncode != 0:
        raise RuntimeError(f"fresh execution report failed: {execution.stderr}")
    return {
        "result": result.read_bytes(),
        "manifest": manifest.read_bytes(),
        "execution_report": execution_report.read_bytes(),
    }


def _fresh_subprocess_verification(
    output_path: Path, manifest_path: Path, execution_report_path: Path
) -> dict[str, Any]:
    guardrail = load_strict_json_object(GUARDRAIL_PATH, style="report")
    source_paths = [
        REPO_ROOT / artifact["path"]
        for chain in guardrail["source_chains"]
        for artifact in chain["artifacts"]
    ]
    source_before = {str(path): sha256_path(path) for path in source_paths}
    repository_paths = (
        GUARDRAIL_PATH,
        SCRIPT_PATH,
        output_path,
        manifest_path,
        execution_report_path,
    )
    repository_before = {
        str(path): sha256_path(path) for path in repository_paths
    }
    with tempfile.TemporaryDirectory(prefix="toe-multi-review-a-") as first_name:
        with tempfile.TemporaryDirectory(prefix="toe-multi-review-b-") as second_name:
            first = _run_fresh_execution(Path(first_name))
            second = _run_fresh_execution(Path(second_name))
    source_after = {str(path): sha256_path(path) for path in source_paths}
    repository_after = {
        str(path): sha256_path(path) for path in repository_paths
    }
    repository = {
        "result": output_path.read_bytes(),
        "manifest": manifest_path.read_bytes(),
        "execution_report": execution_report_path.read_bytes(),
    }
    keys = ("result", "manifest", "execution_report")
    return {
        "run_count": 2,
        "distinct_temporary_directories": True,
        "fixed_environment": {
            "PYTHONUTF8": "1",
            "PYTHONHASHSEED": "0",
            "TZ": "UTC",
            "LC_ALL": "C.UTF-8",
            "LANG": "C.UTF-8",
        },
        "run_one_sha256": {key: sha256_bytes(first[key]) for key in keys},
        "run_two_sha256": {key: sha256_bytes(second[key]) for key in keys},
        "both_runs_byte_identical": all(first[key] == second[key] for key in keys),
        "fresh_runs_match_repository_artifacts": all(
            first[key] == repository[key] and second[key] == repository[key]
            for key in keys
        ),
        "all_twenty_four_source_artifacts_unchanged": source_before == source_after,
        "repository_execution_artifacts_unchanged": (
            repository_before == repository_after
        ),
    }


def verify_calculation_result(
    *,
    guardrail_path: Path = GUARDRAIL_PATH,
    script_path: Path = SCRIPT_PATH,
    output_path: Path = OUTPUT_PATH,
    manifest_path: Path = MANIFEST_PATH,
    execution_report_path: Path = EXECUTION_REPORT_PATH,
    expected_hashes: dict[str, str] | None = None,
    run_subprocesses: bool = True,
) -> dict[str, Any]:
    mismatch_codes: list[str] = []
    expected = dict(EXPECTED_EXECUTION_HASHES if expected_hashes is None else expected_hashes)
    paths = {
        "guardrail_sha256": guardrail_path,
        "script_sha256": script_path,
        "output_sha256": output_path,
        "manifest_sha256": manifest_path,
        "execution_report_sha256": execution_report_path,
    }
    hash_codes = {
        "guardrail_sha256": "guardrail_hash_mismatch",
        "script_sha256": "calculation_script_hash_mismatch",
        "output_sha256": "calculation_output_hash_mismatch",
        "manifest_sha256": "calculation_manifest_hash_mismatch",
        "execution_report_sha256": "execution_report_hash_mismatch",
    }
    actual: dict[str, str | None] = {}
    for key, path in paths.items():
        try:
            actual[key] = sha256_path(path)
        except OSError:
            actual[key] = None
            mismatch_codes.append("artifact_missing")
        if expected.get(key) == UNFROZEN_HASH_SENTINEL or key not in expected:
            mismatch_codes.append("expected_execution_hash_not_frozen")
        elif actual[key] != expected.get(key):
            mismatch_codes.append(hash_codes[key])

    artifacts: dict[str, dict[str, Any] | None] = {
        "guardrail": None,
        "result": None,
        "manifest": None,
        "execution_report": None,
    }
    canonical_checks: dict[str, bool] = {}
    for name, path, style in (
        ("guardrail", guardrail_path, "report"),
        ("result", output_path, "compact"),
        ("manifest", manifest_path, "compact"),
        ("execution_report", execution_report_path, "report"),
    ):
        try:
            artifacts[name] = load_strict_json_object(path, style=style)
            canonical_checks[name] = True
        except DuplicateKeyError:
            canonical_checks[name] = False
            mismatch_codes.append("duplicate_json_key")
        except NonFiniteJSONError:
            canonical_checks[name] = False
            mismatch_codes.append("nonfinite_json_value")
        except (UnicodeDecodeError, json.JSONDecodeError):
            canonical_checks[name] = False
            mismatch_codes.append("invalid_json_encoding_or_syntax")
        except (OSError, ValueError):
            canonical_checks[name] = False
            mismatch_codes.append("canonicalization_mismatch")

    guardrail = artifacts["guardrail"]
    result = artifacts["result"]
    manifest = artifacts["manifest"]
    execution = artifacts["execution_report"]
    schema_match = bool(
        guardrail
        and result
        and manifest
        and execution
        and guardrail.get("schema_id") == GUARDRAIL_SCHEMA_ID
        and result.get("schema_id") == RESULT_SCHEMA_ID
        and set(result) == RESULT_KEYS
        and manifest.get("schema_id") == MANIFEST_SCHEMA_ID
        and set(manifest) == MANIFEST_KEYS
        and execution.get("schema_id") == EXECUTION_SCHEMA_ID
        and set(execution) == EXECUTION_KEYS
        and all(
            item.get("calculation_id") == CALCULATION_ID
            for item in (guardrail, result, manifest, execution)
        )
    )
    if not schema_match:
        mismatch_codes.append("schema_or_required_field_mismatch")

    manifest_links = bool(
        manifest
        and manifest.get("guardrail_path") == GUARDRAIL_RELATIVE_PATH
        and manifest.get("guardrail_sha256") == actual["guardrail_sha256"]
        and manifest.get("script_path") == SCRIPT_RELATIVE_PATH
        and manifest.get("script_sha256") == actual["script_sha256"]
        and manifest.get("output_path") == OUTPUT_RELATIVE_PATH
        and manifest.get("output_sha256") == actual["output_sha256"]
        and manifest.get("execution_report_path") == EXECUTION_REPORT_RELATIVE_PATH
    )
    if not manifest_links:
        mismatch_codes.append("manifest_hash_or_identity_link_mismatch")
    execution_links = bool(
        execution
        and execution.get("guardrail_path") == GUARDRAIL_RELATIVE_PATH
        and execution.get("guardrail_sha256") == actual["guardrail_sha256"]
        and execution.get("calculation_script_path") == SCRIPT_RELATIVE_PATH
        and execution.get("calculation_script_sha256") == actual["script_sha256"]
        and execution.get("calculation_output_path") == OUTPUT_RELATIVE_PATH
        and execution.get("calculation_output_sha256") == actual["output_sha256"]
        and execution.get("calculation_manifest_path") == MANIFEST_RELATIVE_PATH
        and execution.get("calculation_manifest_sha256") == actual["manifest_sha256"]
        and execution.get("execution_report_path") == EXECUTION_REPORT_RELATIVE_PATH
    )
    if not execution_links:
        mismatch_codes.append("execution_report_hash_or_identity_link_mismatch")

    scientific_input_links = False
    if guardrail is not None and manifest is not None and execution is not None:
        expected_inputs = [
            {
                "chain_id": chain["chain_id"],
                "artifact_role": artifact["artifact_role"],
                "path": artifact["path"],
                "sha256": artifact["sha256"],
            }
            for chain in guardrail.get("source_chains", [])
            for artifact in chain.get("artifacts", [])
        ]
        scientific_input_links = (
            len(expected_inputs) == 24
            and manifest.get("scientific_input_artifacts") == expected_inputs
            and execution.get("scientific_input_artifacts") == expected_inputs
            and manifest.get("source_chain_count") == 4
            and manifest.get("bound_artifact_count") == 24
            and execution.get("source_chain_count") == 4
            and execution.get("bound_artifact_count") == 24
        )
    if not scientific_input_links:
        mismatch_codes.append("twenty_four_scientific_input_link_mismatch")

    family: dict[str, Any] | None = None
    decisions: list[dict[str, Any]] = []
    tamper_controls: list[dict[str, Any]] = []
    section_matches: dict[str, bool] = {}
    execution_report_section_matches: dict[str, bool] = {}
    try:
        family = independent_reconstruct_source_family(guardrail_path)
        decisions = independently_adjudicate(family)
        tamper_controls = independently_run_tamper_controls(family)
    except DuplicateKeyError:
        mismatch_codes.append("source_artifact_duplicate_json_key")
        mismatch_codes.append("independent_source_reconstruction_failed")
    except NonFiniteJSONError:
        mismatch_codes.append("source_artifact_nonfinite_json_value")
        mismatch_codes.append("independent_source_reconstruction_failed")
    except (OSError, UnicodeError, json.JSONDecodeError, ValueError, KeyError):
        mismatch_codes.append("source_artifact_integrity_or_schema_mismatch")
        mismatch_codes.append("independent_source_reconstruction_failed")
    except Exception:
        mismatch_codes.append("independent_source_reconstruction_failed")
    if family is not None and result is not None:
        section_matches = _result_semantic_matches(
            result, family, decisions, tamper_controls
        )
        if execution is not None:
            execution_report_section_matches = _result_semantic_matches(
                execution, family, decisions, tamper_controls
            )
        mismatch_by_section = {
            "source_chain_records": "source_chain_record_mismatch",
            "background_rows": "background_comparison_mismatch",
            "comparable_rows_and_envelopes": "comparable_metric_envelope_mismatch",
            "thirty_seven_source_decisions": "source_decision_inventory_mismatch",
            "on_shell_policies": "on_shell_policy_or_zero_reference_mismatch",
            "applicability": "applicability_typing_mismatch",
            "controls": "control_coverage_or_masking_mismatch",
            "sixteen_decisions": "sixteen_synthesis_decision_mismatch",
            "fourteen_tamper_controls": "fourteen_tamper_control_mismatch",
        }
        for section, matches in section_matches.items():
            if not matches:
                mismatch_codes.append(mismatch_by_section[section])
        for section, matches in execution_report_section_matches.items():
            if not matches:
                mismatch_codes.append(
                    f"execution_report_{mismatch_by_section[section]}"
                )
    else:
        mismatch_codes.append("execution_result_semantic_comparison_unavailable")

    independent_all_decisions = (
        len(decisions) == 16 and all(row["passed"] for row in decisions)
    )
    independent_all_controls = (
        len(tamper_controls) == 14 and all(row["detected"] for row in tamper_controls)
    )
    if not independent_all_decisions:
        mismatch_codes.append("independent_synthesis_decision_failure")
        mismatch_codes.extend(
            f"independent_decision_failed__{row['decision_id']}"
            for row in decisions
            if row["passed"] is False
        )
    if not independent_all_controls:
        mismatch_codes.append("independent_tamper_control_failure")

    lifecycle_match = bool(
        result
        and manifest
        and execution
        and result.get("calculation_status")
        == "executed_candidate_e_repro_pending_independent_review"
        and result.get("selected_next_target") == REVIEW_TARGET
        and result.get("result_review") == {"status": "pending", "target": REVIEW_TARGET}
        and result.get("claim", {}).get("primary_label") == "E-REPRO"
        and result.get("claim", {}).get("claim_ceiling_level") == 3
        and result.get("claim", {}).get("review_accepted") is False
        and manifest.get("result_review_target") == REVIEW_TARGET
        and manifest.get("selected_next_target") == REVIEW_TARGET
        and execution.get("status")
        == "executed_candidate_e_repro_pending_independent_review"
        and execution.get("selected_next_target") == REVIEW_TARGET
        and execution.get("claim", {}).get("review_accepted") is False
        and result.get("source_chain_count") == 4
        and result.get("bound_artifact_count") == 24
        and result.get("synthesis_decision_count") == 16
        and result.get("synthesis_tamper_control_count") == 14
        and result.get("all_decisions_passed") is True
        and result.get("all_thresholds_passed") is True
        and manifest.get("calculation_status")
        == "executed_candidate_e_repro_pending_independent_review"
        and manifest.get("claim_label") == "E-REPRO"
        and manifest.get("claim_ceiling_level") == 3
        and manifest.get("all_decisions_passed") is True
        and manifest.get("all_thresholds_passed") is True
        and manifest.get("ambient_repository_state_serialized") is False
        and manifest.get("execution_commit_hash_serialized") is False
        and execution.get("five_artifact_chain_prepared_for_independent_review")
        is True
        and execution.get("all_decisions_passed") is True
        and execution.get("all_thresholds_passed") is True
        and execution.get("equation_compendium_edited") is False
        and execution.get("ambient_repository_state_serialized") is False
        and execution.get("execution_commit_hash_serialized") is False
        and execution.get("full_ToeFormal_aggregate_run_or_upgraded") is False
        and guardrail is not None
        and result.get("boundary")
        == manifest.get("boundary")
        == execution.get("boundary")
        == guardrail.get("boundary")
    )
    if not lifecycle_match:
        mismatch_codes.append("execution_lifecycle_or_claim_boundary_mismatch")

    subprocess_evidence: dict[str, Any] = {
        "run_count": 0,
        "both_runs_byte_identical": False,
        "fresh_runs_match_repository_artifacts": False,
        "all_twenty_four_source_artifacts_unchanged": False,
        "repository_execution_artifacts_unchanged": False,
    }
    if run_subprocesses:
        try:
            subprocess_evidence = _fresh_subprocess_verification(
                output_path, manifest_path, execution_report_path
            )
        except (OSError, RuntimeError, subprocess.SubprocessError):
            mismatch_codes.append("fresh_subprocess_execution_failed")
        else:
            if not subprocess_evidence["both_runs_byte_identical"]:
                mismatch_codes.append("fresh_subprocess_byte_mismatch")
            if not subprocess_evidence["fresh_runs_match_repository_artifacts"]:
                mismatch_codes.append("fresh_subprocess_repository_mismatch")
            if not subprocess_evidence[
                "all_twenty_four_source_artifacts_unchanged"
            ]:
                mismatch_codes.append("fresh_subprocess_source_artifact_mutation")
            if not subprocess_evidence[
                "repository_execution_artifacts_unchanged"
            ]:
                mismatch_codes.append("fresh_subprocess_execution_artifact_mutation")
    else:
        mismatch_codes.append("fresh_subprocess_verification_not_run")

    if run_subprocesses:
        try:
            post_family = independent_reconstruct_source_family(guardrail_path)
            post_integrity = independently_adjudicate(post_family)[0]["passed"]
        except Exception:
            post_integrity = False
        if not post_integrity:
            mismatch_codes.append("post_reproduction_source_integrity_mismatch")
        try:
            post_execution_hashes = {
                key: sha256_path(path) for key, path in paths.items()
            }
        except OSError:
            post_execution_hashes = {}
        if post_execution_hashes != actual:
            mismatch_codes.append("post_reproduction_execution_artifact_mutation")

    mismatch_codes = list(dict.fromkeys(mismatch_codes))
    accepted = not mismatch_codes
    return {
        "accepted": accepted,
        "primary_claim_label": "E-REPRO" if accepted else "B-BLOCKED",
        "claim_status": (
            "accepted_level_3_scoped_e_repro_exact_four_case_family_only"
            if accepted
            else "blocked_reproducibility_mismatch"
        ),
        "mismatch_codes": mismatch_codes,
        "expected_hashes": expected,
        "actual_hashes": actual,
        "all_five_artifact_hashes_match": actual == expected,
        "canonical_byte_checks": canonical_checks,
        "all_canonical_bytes_match": bool(canonical_checks) and all(canonical_checks.values()),
        "schema_and_required_fields_match": schema_match,
        "manifest_hash_and_identity_links_match": manifest_links,
        "execution_report_hash_and_identity_links_match": execution_links,
        "twenty_four_scientific_input_links_match": scientific_input_links,
        "independent_reconstruction_implementation": (
            "review-local chain-specific source adapters, source hash/link checks, "
            "family envelopes, decision adjudication, and isolated tamper controls"
        ),
        "execution_self_adjudication_trusted": False,
        "independent_family_sha256": (
            sha256_bytes(canonical_json_bytes(family)) if family is not None else None
        ),
        "independent_summary": (
            {
                "source_chain_count": family["source_chain_count"],
                "bound_artifact_count": family["bound_artifact_count"],
                "background_comparison_row_count": len(
                    family["background_comparison_rows"]
                ),
                "comparable_convergence_row_count": len(
                    family["comparable_rows"]
                ),
                "comparable_off_shell_relative_error_row_count": len(
                    family["comparable_rows"]
                ),
                "qualified_source_decision_count": len(
                    family["qualified_source_decisions"]
                ),
                "source_local_on_shell_policy_row_count": len(
                    family["source_local_on_shell_policy_rows"]
                ),
                "applicability_typed_local_check_row_count": len(
                    family["applicability_typed_local_check_rows"]
                ),
                "control_instance_count": len(family["control_instances"]),
                "control_mechanism_count": len(
                    {
                        row["mechanism_class"]
                        for row in family["control_instances"]
                    }
                ),
                "synthesis_decision_count": len(decisions),
                "synthesis_tamper_control_count": len(tamper_controls),
                "family_minimum_p_min": family["family_minimum_p_min"],
                "family_maximum_off_shell_relative_identity_error": family[
                    "family_maximum_off_shell_relative_error"
                ],
            }
            if family is not None
            else None
        ),
        "independent_section_matches": section_matches,
        "execution_report_independent_section_matches": (
            execution_report_section_matches
        ),
        "independent_synthesis_decisions": decisions,
        "all_sixteen_independent_synthesis_decisions_pass": independent_all_decisions,
        "independent_synthesis_tamper_controls": tamper_controls,
        "all_fourteen_independent_tamper_controls_detected": independent_all_controls,
        "execution_lifecycle_and_claim_boundary_match": lifecycle_match,
        "fresh_subprocess_reproduction": subprocess_evidence,
        "selected_next_target": SUCCESS_TARGET if accepted else FAILURE_TARGET,
        "selection_basis": SUCCESS_SELECTION_BASIS if accepted else None,
    }


def build_review_report(**verification_arguments: Any) -> dict[str, Any]:
    verification = verify_calculation_result(**verification_arguments)
    accepted = verification["accepted"]
    return {
        "schema_id": REVIEW_SCHEMA_ID,
        "review_id": REVIEW_ID,
        "calculation_id": CALCULATION_ID,
        "status": (
            "accepted_level_3_scoped_e_repro"
            if accepted
            else "blocked_reproducibility_mismatch"
        ),
        "primary_label": "E-REPRO" if accepted else "B-BLOCKED",
        "accepted_e_repro": accepted,
        "captured_at_utc": CAPTURED_AT_UTC,
        "consumed_target": REVIEW_TARGET,
        "consumed_target_kind": REVIEW_TARGET_KIND,
        "execution_commit": EXECUTION_COMMIT,
        "selected_next_target": verification["selected_next_target"],
        "selected_next_target_kind": (
            SUCCESS_TARGET_KIND if accepted else FAILURE_TARGET_KIND
        ),
        "selection_basis": SUCCESS_SELECTION_BASIS if accepted else None,
        "packet_result": REVIEW_OUTCOME if accepted else "B-BLOCKED",
        "strict_packet_result": REVIEW_STRICT_OUTCOME if accepted else "B-BLOCKED",
        "review_result": REVIEW_OUTCOME if accepted else "B-BLOCKED",
        "strict_review_result": REVIEW_STRICT_OUTCOME if accepted else "B-BLOCKED",
        "five_artifact_chain": {
            "guardrail_path": GUARDRAIL_RELATIVE_PATH,
            "calculation_script_path": SCRIPT_RELATIVE_PATH,
            "calculation_output_path": OUTPUT_RELATIVE_PATH,
            "calculation_manifest_path": MANIFEST_RELATIVE_PATH,
            "execution_report_path": EXECUTION_REPORT_RELATIVE_PATH,
            "expected_hashes": verification["expected_hashes"],
            "all_hashes_match": verification["all_five_artifact_hashes_match"],
        },
        "verification": verification,
        "mismatch_codes": verification["mismatch_codes"],
        "claim": {
            "primary_label": "E-REPRO" if accepted else "B-BLOCKED",
            "claim_status": verification["claim_status"],
            "claim_ceiling_level": 3,
            "claim_scope": (
                "reproducible robustness across the exact four enumerated "
                "fixed-background evidence chains"
            ),
            "review_accepted": accepted,
            "not_a_theorem": True,
            "not_a_statistical_generalization": True,
            "not_arbitrary_background_validity": True,
            "not_independent_code_replication": True,
        },
        "boundary": {
            "closed_enumerated_family": True,
            "fixed_backgrounds": True,
            "fixed_coordinate_systems": True,
            "shared_implementation_lineage": True,
            "all_background_validity_claimed": False,
            "formal_proof_claimed": False,
            "statistical_success_probability_claimed": False,
            "independent_code_replication_claimed": False,
            "new_pde_solve_performed": False,
            "gravity_evolution_claimed": False,
            "einstein_source_compatibility_claimed": False,
            "bianchi_compatibility_claimed": False,
            "qft_gr_seam_admissibility_claimed": False,
            "qft_gr_seam_closure_claimed": False,
            "scalar_qft_pillar_recovery_claimed": False,
            "level_4_or_level_5_claimed": False,
            "quantum_or_renormalized_stress_energy_claimed": False,
            "ccft_resumed": False,
            "C_k_dynamics_claimed": False,
            "C_k_action_embedding_authorized": False,
            "master_action_promoted": False,
            "new_physics_claimed": False,
            "unit_ledger_target": SUCCESS_TARGET,
            "unit_ledger_status_during_review": "queued_non_live_hard_gate",
            "full_ToeFormal_aggregate_run_or_upgraded": False,
        },
        "failure_preservation": {
            "review_artifact_written_on_failure": True,
            "execution_commit_remains_immutable": True,
            "source_or_execution_artifacts_amended": False,
            "diagnostic_authority_rotation_required": not accepted,
        },
        "determinism": {
            "ambient_branch_head_or_dirty_state_serialized": False,
            "wall_clock_time_serialized": False,
            "temporary_paths_serialized": False,
            "fresh_subprocess_count": verification[
                "fresh_subprocess_reproduction"
            ]["run_count"],
            "fixed_capture_time": CAPTURED_AT_UTC,
            "report_encoding": (
                "UTF-8 without BOM; sorted indented JSON; exactly one LF"
            ),
        },
    }


def write_review_report(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(report_json_bytes(payload))


def review_report_main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Independently review the closed four-case scalar multi-background "
            "robustness synthesis."
        )
    )
    parser.add_argument("--guardrail", type=Path, default=GUARDRAIL_PATH)
    parser.add_argument("--script", type=Path, default=SCRIPT_PATH)
    parser.add_argument("--output", type=Path, default=OUTPUT_PATH)
    parser.add_argument("--manifest", type=Path, default=MANIFEST_PATH)
    parser.add_argument("--execution-report", type=Path, default=EXECUTION_REPORT_PATH)
    parser.add_argument("--out", type=Path, default=REVIEW_REPORT_PATH)
    args = parser.parse_args(argv)
    payload = build_review_report(
        guardrail_path=args.guardrail,
        script_path=args.script,
        output_path=args.output,
        manifest_path=args.manifest,
        execution_report_path=args.execution_report,
    )
    # The failed report is intentionally preserved before returning nonzero.
    write_review_report(args.out, payload)
    print(
        json.dumps(
            {
                "accepted": payload["accepted_e_repro"],
                "claim_label": payload["primary_label"],
                "mismatch_codes": payload["mismatch_codes"],
                "selected_next_target": payload["selected_next_target"],
                "review_report": REVIEW_REPORT_RELATIVE_PATH,
            },
            sort_keys=True,
        )
    )
    return 0 if payload["accepted_e_repro"] else 1


if __name__ == "__main__":
    raise SystemExit(review_report_main())
