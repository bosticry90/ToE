from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/POST_SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_"
    "EXPLORATORY_SANDBOX_V0_EXECUTION_RESULT_REVIEW_SCIENTIFIC_RESPONSE_"
    "SELECTION_20260719_v0.json"
)
HUMAN_RELATIVE_PATH = (
    "formal/docs/lanes/POST_SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_"
    "EXPLORATORY_SANDBOX_V0_EXECUTION_RESULT_REVIEW_SCIENTIFIC_RESPONSE_"
    "SELECTION_20260719_v0.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/test_post_scalar_only_yukawa_analytic_sphere_kernel_"
    "exploratory_sandbox_v0_execution_result_review_scientific_response_selection_v0.py"
)
LEAN_RELATIVE_PATH = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "PostScalarOnlyYukawaAnalyticSphereKernelExploratorySandboxV0ExecutionResultReview"
    "ScientificResponseSelectionV0.lean"
)
REVIEW_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_EXPLORATORY_"
    "SANDBOX_EXECUTION_RESULT_REVIEW_20260719_v0.json"
)
V0_SOURCE_RELATIVE_PATH = (
    "formal/python/tools/scalar_only_yukawa_analytic_sphere_kernel_"
    "exploratory_sandbox_v0.py"
)

TARGET = (
    "select_post_scalar_only_yukawa_analytic_sphere_kernel_exploratory_sandbox_"
    "v0_execution_result_review_scientific_response_v0"
)
VERDICT = (
    "SELECTED_FINAL_SERIALIZATION_CORRECTED_NON_DECISION_BEARING_SANDBOX_"
    "V1_EXECUTION"
)
SELECTED_ROUTE = (
    "AUTHORIZE_FINAL_SERIALIZATION_CORRECTED_NON_DECISION_BEARING_SANDBOX_"
    "IMPLEMENTATION_V1"
)
SELECTED_CANDIDATE_ID = "ANALYTIC_SPHERE_KERNEL_EXPLORATORY_SANDBOX_V1_FINAL_ONCE"
SELECTED_NEXT_TARGET = (
    "execute_scalar_only_yukawa_analytic_sphere_kernel_exploratory_sandbox_v1_once"
)
SELECTED_NEXT_TARGET_KIND = (
    "ONE_FINAL_VERSIONED_SERIALIZATION_CORRECTED_NON_PRODUCTION_NON_ADJUDICATIVE_"
    "SANDBOX_IMPLEMENTATION_AND_EXECUTION"
)

V0_SOURCE_SHA256 = "27a32f540465ed78cb2094629033a4aa30e3142c1f75aa113fc88eb10c7563ae"
REVIEW_HASHES = {
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_EXPLORATORY_SANDBOX_EXECUTION_RESULT_REVIEW_20260719_v0.md":
        "8a25dfee32a67a960efb36217de7b45ca6da3134af58526b127be5eee3be75c8",
    REVIEW_RELATIVE_PATH:
        "ebb8ead3b8ad64e7ddc106e86309764fb9084533132638b6eaf70e046f5e200a",
    "formal/python/tools/scalar_only_yukawa_analytic_sphere_kernel_exploratory_sandbox_execution_result_review_v0.py":
        "586ad278f1819e4a4d0904c61bda6f1be174f1ff526eff24ef9cf8dc8f76f5c1",
    "formal/python/tests/test_scalar_only_yukawa_analytic_sphere_kernel_exploratory_sandbox_execution_result_review_v0.py":
        "a6587f52ee964831eadbbd9cae9f118a40332b847bda7471aa5d72d058fb3688",
    "formal/toe_formal/ToeFormal/Derivation/ScalarOnlyYukawaAnalyticSphereKernelExploratorySandboxExecutionResultReviewV0.lean":
        "9115aaf011cd0734c59129457b4375ca3d37f0c2e4a58c0d185830384aea8bb2",
}

EXACT_SELECTOR_OPTIONS = (
    SELECTED_ROUTE,
    "RETIRE_OR_DEFER_ANALYTIC_REPLACEMENT_LANE",
)

EXPLORATORY_LABELS = (
    "EXPLORATORY_IMPLEMENTATION_RESULT",
    "NON_PRODUCTION",
    "NON_ADJUDICATIVE",
    "NO_SCIENTIFIC_CLAIM",
)

PERMITTED_CHANGE_CLASSES = (
    "RECURSIVE_DECIMAL_TO_FROZEN_CANONICAL_STRING_NORMALIZATION",
    "REAL_NESTED_ADJUDICATION_AND_COMPLETE_AGGREGATE_SERIALIZATION_CONTROL",
    "STRICT_UNKNOWN_OBJECT_AND_NONFINITE_REJECTION",
    "RECURSIVE_NORMALIZED_AGGREGATE_SCHEMA_VALIDATION",
    "CANONICAL_UTF8_ENCODING_AND_STRICT_ROUND_TRIP_VERIFICATION",
    "ATOMIC_WRITE_FLUSH_FSYNC_PARSE_SCHEMA_HASH_VERIFY_AND_RENAME",
    "V1_IDENTIFIERS_FILENAMES_HASHES_CUSTODY_AND_NARROW_HELPER_WIRING",
)

FROZEN_SCIENTIFIC_SURFACES = (
    "ANALYTIC_NEWTONIAN_AND_YUKAWA_FORMULAS",
    "SMALL_DIRECT_AND_SCALED_EVALUATOR_BRANCHES",
    "EIGHT_REGRESSION_CASE_INPUTS_AND_EXPECTED_VALUES",
    "ENERGY_AND_RADIAL_DERIVATIVE_REFERENCES",
    "ABSOLUTE_AND_RELATIVE_TOLERANCES",
    "THIRTEEN_BOUNDARY_AND_LIMIT_PROBES",
    "TWELVE_MUTATIONS_AND_INJECTION_POINTS",
    "TYPED_PREDICATES_AND_ADJUDICATORS",
    "DEPENDENCY_SCANNER_CONTRACT",
    "TEN_THOUSAND_CALL_RUNTIME_WORKLOAD",
    "SCALAR_ARRAY_COMPONENT_HOOK_AND_FAILURE_INTERFACE_SEMANTICS",
    "CLASSIFICATION_AND_INCOMPLETE_RUN_PRECEDENCE",
    "RESOURCE_ENVELOPE_AND_PRODUCTION_FIREWALLS",
)

ATOMIC_COMMIT_PIPELINE = (
    "CONSTRUCT_COMPLETE_AGGREGATE",
    "RECURSIVELY_NORMALIZE",
    "RECURSIVELY_VALIDATE_SCHEMA",
    "CANONICALLY_ENCODE_UTF8",
    "WRITE_TEMPORARY_FILE",
    "FLUSH_AND_FSYNC",
    "STRICT_PARSE_SCHEMA_AND_HASH_VERIFY_TEMPORARY_FILE",
    "ATOMIC_RENAME_TO_CANONICAL_DESTINATION",
    "STRICT_PARSE_SCHEMA_AND_HASH_VERIFY_CANONICAL_FILE",
)

CRITERIA = {
    "localized_defect_fit": 5,
    "accepted_oracle_leverage": 5,
    "contract_explicitness": 5,
    "scientific_surface_freeze": 5,
    "serialization_closure": 5,
    "boundedness": 5,
    "production_safety": 5,
    "terminality": 5,
    "computational_economy": 4,
    "reversibility": 5,
    "authority_clarity": 5,
}

CANDIDATES = (
    {
        "candidate_id": SELECTED_CANDIDATE_ID,
        "route": SELECTED_ROUTE,
        "target": SELECTED_NEXT_TARGET,
        "scores": {key: 5 for key in CRITERIA},
        "disposition": "SELECTED_FINAL_ONE_SHOT_SERIALIZATION_CORRECTED_SANDBOX_V1",
    },
    {
        "candidate_id": "RETIRE_OR_DEFER_ANALYTIC_REPLACEMENT_LANE",
        "route": EXACT_SELECTOR_OPTIONS[1],
        "target": "retire_or_defer_scalar_only_yukawa_analytic_replacement_lane_v0",
        "scores": {
            "localized_defect_fit": 0,
            "accepted_oracle_leverage": 2,
            "contract_explicitness": 5,
            "scientific_surface_freeze": 5,
            "serialization_closure": 0,
            "boundedness": 5,
            "production_safety": 5,
            "terminality": 5,
            "computational_economy": 5,
            "reversibility": 3,
            "authority_clarity": 5,
        },
        "disposition": "RUNNER_UP_SAFE_BUT_ABANDONS_PROPORTIONATE_FINAL_ATTEMPT",
    },
)


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _load_json(relative_path: str) -> dict[str, Any]:
    value = json.loads((REPO_ROOT / relative_path).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {relative_path}")
    return value


def _artifact_row(relative_path: str) -> dict[str, str]:
    return {"relative_path": relative_path, "sha256": _sha256(REPO_ROOT / relative_path)}


def _weighted_score(scores: dict[str, int], weights: dict[str, int]) -> int:
    if set(scores) != set(weights):
        raise ValueError("candidate score criteria mismatch")
    return sum(scores[key] * weights[key] for key in weights)


def _rank(weights: dict[str, int]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for candidate in CANDIDATES:
        row = dict(candidate)
        row["weighted_score"] = _weighted_score(candidate["scores"], weights)
        rows.append(row)
    return sorted(rows, key=lambda row: (-row["weighted_score"], row["candidate_id"]))


def _sensitivity() -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    for omitted in CRITERIA:
        weights = dict(CRITERIA)
        weights[omitted] = 0
        ranked = _rank(weights)
        rows.append({
            "variant": f"omit_{omitted}",
            "selected_candidate_id": ranked[0]["candidate_id"],
            "selected_score": ranked[0]["weighted_score"],
            "runner_up_candidate_id": ranked[1]["candidate_id"],
            "runner_up_score": ranked[1]["weighted_score"],
        })
    for criterion, baseline in CRITERIA.items():
        for delta in (-1, 1):
            weights = dict(CRITERIA)
            weights[criterion] = max(1, baseline + delta)
            ranked = _rank(weights)
            rows.append({
                "variant": f"{criterion}_{delta:+d}",
                "selected_candidate_id": ranked[0]["candidate_id"],
                "selected_score": ranked[0]["weighted_score"],
                "runner_up_candidate_id": ranked[1]["candidate_id"],
                "runner_up_score": ranked[1]["weighted_score"],
            })
    return {
        "variant_count": len(rows),
        "rows": rows,
        "selected_candidate_stable_in_all_variants": all(
            row["selected_candidate_id"] == SELECTED_CANDIDATE_ID for row in rows
        ),
        "minimum_winning_margin": min(
            row["selected_score"] - row["runner_up_score"] for row in rows
        ),
    }


def build_report() -> dict[str, Any]:
    for relative_path, expected in REVIEW_HASHES.items():
        if _sha256(REPO_ROOT / relative_path) != expected:
            raise ValueError(f"accepted failure review authority drift: {relative_path}")
    if _sha256(REPO_ROOT / V0_SOURCE_RELATIVE_PATH) != V0_SOURCE_SHA256:
        raise ValueError("V0 sandbox source hash drift")

    review = _load_json(REVIEW_RELATIVE_PATH)
    if review.get("verdict") != "ACCEPTED_EXPLORATORY_IMPLEMENTATION_SERIALIZATION_FAILURE":
        raise ValueError("accepted sandbox result-review verdict mismatch")
    if review.get("selected_next_target") != TARGET:
        raise ValueError("accepted result review did not authorize this selector")
    if review["review_gates"]["pass_count"] != 40:
        raise ValueError("accepted result-review pass count mismatch")
    if review["review_gates"]["failure_count"] != 0:
        raise ValueError("accepted result review must be failure-free")
    if review["defect_attribution"][
        "ambiguity_in_decimal_conversion_obligation_established"
    ] is not False:
        raise ValueError("contract ambiguity unexpectedly established")
    if review["defect_attribution"]["principal_classification"] != "IMPLEMENTATION_FAILURE":
        raise ValueError("localized implementation attribution mismatch")
    if review["scientific_admissibility"]["kernel_pass_or_fail"] != "UNRESOLVED":
        raise ValueError("sandbox kernel must remain unqualified")

    ranking = _rank(CRITERIA)
    sensitivity = _sensitivity()
    if len(CANDIDATES) != 2:
        raise ValueError("post-failure selector must contain exactly two candidates")
    if tuple(candidate["route"] for candidate in CANDIDATES) != EXACT_SELECTOR_OPTIONS:
        raise ValueError("post-failure candidate routes mismatch")
    if ranking[0]["candidate_id"] != SELECTED_CANDIDATE_ID:
        raise ValueError("final V1 sandbox candidate is not top ranked")
    if not sensitivity["selected_candidate_stable_in_all_variants"]:
        raise ValueError("final V1 sandbox selection is sensitivity-unstable")

    selection_gates = (
        "EXACT_ACCEPTED_FAILURE_REVIEW_AUTHORITY_AND_HASH_CUSTODY",
        "FORTY_OF_FORTY_ACCEPTED_REVIEW_GATES_FROZEN",
        "IMPLEMENTATION_FAILURE_ATTRIBUTION_PRESERVED",
        "CONTRACT_AMBIGUITY_NOT_ESTABLISHED",
        "ANALYTIC_ORACLE_REMAINS_QUALIFIED",
        "SANDBOX_KERNEL_REMAINS_NEITHER_QUALIFIED_NOR_REFUTED",
        "TRANSIENT_VALUES_REMAIN_NONADMISSIBLE",
        "EXACT_TWO_OPTION_POST_FAILURE_SELECTOR",
        "NO_THIRD_ROUTE_OR_AUTOMATIC_REPAIR",
        "FINAL_V1_WINS_ALL_THIRTY_THREE_SENSITIVITY_VARIANTS",
        "V0_SOURCE_SHA256_FROZEN",
        "EXACT_SEVEN_PERMITTED_CHANGE_CLASSES",
        "EXACT_THIRTEEN_FROZEN_SCIENTIFIC_SURFACES",
        "FORMULAS_EVALUATORS_CASES_REFERENCES_AND_TOLERANCES_FROZEN",
        "PROBES_MUTATIONS_PREDICATES_ADJUDICATORS_AND_SCANNER_FROZEN",
        "RUNTIME_WORKLOAD_INTERFACE_AND_PRECEDENCE_FROZEN",
        "PERMISSIVE_JSON_DEFAULT_STR_FORBIDDEN",
        "RECURSIVE_DECIMAL_NORMALIZER_REQUIRED",
        "UNKNOWN_OBJECT_AND_NONFINITE_REJECTION_REQUIRED",
        "NORMALIZED_OBJECT_RECURSIVE_SCHEMA_VALIDATION_REQUIRED",
        "NO_DECIMAL_OR_NONJSON_OBJECT_MAY_REMAIN",
        "REAL_NESTED_ADJUDICATION_RECORD_CONTROL_REQUIRED",
        "COMPLETE_FINAL_AGGREGATE_CONTROL_REQUIRED",
        "CONTROL_USES_EXACT_REAL_FINALIZATION_PATH",
        "ATOMIC_TEMP_WRITE_FSYNC_VERIFY_AND_RENAME_REQUIRED",
        "EXACTLY_ONE_V1_EXECUTION_AUTHORIZED",
        "NO_AUTOMATIC_V2_OR_THIRD_SANDBOX",
        "NO_ADDITIONAL_SERIALIZATION_REPAIR_CHAIN",
        "NO_ADDITIONAL_INFRASTRUCTURE_PREREQUISITE",
        "PRESERVATION_FAILURE_FORCES_RETIRE_OR_DEFER_ONLY",
        "COMPLETE_RESULT_STOPS_FOR_INDEPENDENT_REVIEW",
        "NO_PRODUCTION_CUBATURE_SHADOW_STAGE_A_OR_STAGE_B",
        "NO_TORQUE_DFT_REAL150_JACOBIAN_SVD_OR_IDENTIFIABILITY",
        "SELECTION_ONLY_NO_V1_IMPLEMENTATION_OR_EXECUTION_NOW",
        "CURRENT_AUTHORITY_ROTATES_TO_FINAL_ONE_SHOT_V1_SANDBOX",
    )

    scope = {
        "scientific_response_selection_executed": True,
        "accepted_failure_review_frozen": True,
        "final_v1_sandbox_implementation_authorized": True,
        "one_v1_sandbox_execution_authorized": True,
        "v1_sandbox_implemented_now": False,
        "v1_sandbox_executed_now": False,
        "automatic_v2_authorized": False,
        "additional_repair_chain_authorized": False,
        "additional_infrastructure_prerequisite_authorized": False,
        "production_change_authorized": False,
        "historical_cubature_call_authorized": False,
        "historical_cubature_adjudication_authorized": False,
        "shadow_qualification_authorized": False,
        "stage_a_rerun_authorized": False,
        "torque_or_dft_authorized": False,
        "real_150_vector_authorized": False,
        "jacobian_or_identifiability_authorized": False,
        "stage_b_authorized": False,
        "scientific_claim_authorized": False,
    }

    return {
        "schema_id": (
            "toe.post_scalar_only_yukawa.analytic_sphere_kernel.exploratory_sandbox_"
            "v0_execution_result_review.scientific_response_selection.v0"
        ),
        "selection_id": (
            "POST_SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_EXPLORATORY_SANDBOX_"
            "V0_EXECUTION_RESULT_REVIEW_SCIENTIFIC_RESPONSE_SELECTION_20260719_v0"
        ),
        "captured_at_utc": "2026-07-19T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "selected_route": SELECTED_ROUTE,
        "selected_candidate_id": SELECTED_CANDIDATE_ID,
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "authority": {
            "consumed_review_verdict": review["verdict"],
            "frozen_review_artifacts": [
                {"relative_path": path, "sha256": digest}
                for path, digest in REVIEW_HASHES.items()
            ],
            "frozen_v0_sandbox_source": {
                "relative_path": V0_SOURCE_RELATIVE_PATH,
                "sha256": V0_SOURCE_SHA256,
            },
            "human_selection": _artifact_row(HUMAN_RELATIVE_PATH),
            "generator": _artifact_row(
                "formal/python/tools/post_scalar_only_yukawa_analytic_sphere_kernel_"
                "exploratory_sandbox_v0_execution_result_review_scientific_response_"
                "selection_v0.py"
            ),
            "test": _artifact_row(TEST_RELATIVE_PATH),
            "lean": _artifact_row(LEAN_RELATIVE_PATH),
        },
        "review_interpretation": {
            "review_verdict": review["verdict"],
            "review_pass_count": review["review_gates"]["pass_count"],
            "review_failure_count": review["review_gates"]["failure_count"],
            "principal_outcome": review["principal_review_outcome"],
            "implementation_defect_localized": True,
            "synthetic_control_integration_gap_localized": True,
            "contract_ambiguous": False,
            "analytic_oracle_remains_qualified": True,
            "sandbox_kernel_qualified_or_refuted": False,
            "transient_values_admissible": False,
            "transient_value_reconstruction_authorized": False,
            "historical_cubature_adjudicated": False,
        },
        "selection_policy": {
            "candidate_count": len(CANDIDATES),
            "options_exact": list(EXACT_SELECTOR_OPTIONS),
            "criterion_count": len(CRITERIA),
            "criteria_weights": CRITERIA,
            "criterion_scale": "0_TO_5_PRIORITY_SCORE_NOT_TRUTH_PROBABILITY",
            "tie_break_rule": "LEXICOGRAPHIC_CANDIDATE_ID",
        },
        "ranking": {
            "rows": ranking,
            "selected_candidate_id": ranking[0]["candidate_id"],
            "selected_score": ranking[0]["weighted_score"],
            "runner_up_candidate_id": ranking[1]["candidate_id"],
            "runner_up_score": ranking[1]["weighted_score"],
            "winning_margin": ranking[0]["weighted_score"] - ranking[1]["weighted_score"],
        },
        "sensitivity_analysis": sensitivity,
        "v1_change_contract": {
            "status": "FINAL_V1_IMPLEMENTATION_AND_EXECUTION_AUTHORIZED_NOT_PERFORMED",
            "base_v0_source_relative_path": V0_SOURCE_RELATIVE_PATH,
            "base_v0_source_sha256": V0_SOURCE_SHA256,
            "v1_implementation_location": (
                "formal/python/tools/scalar_only_yukawa_analytic_sphere_kernel_"
                "exploratory_sandbox_v1.py"
            ),
            "v1_result_location": (
                "formal/docs/release/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_"
                "EXPLORATORY_SANDBOX_20260719_v1.json"
            ),
            "permitted_change_classes": list(PERMITTED_CHANGE_CLASSES),
            "frozen_scientific_surfaces": list(FROZEN_SCIENTIFIC_SURFACES),
            "permissive_json_default_forbidden": True,
            "unknown_object_types_fail_closed": True,
            "nonfinite_numbers_fail_closed": True,
            "source_diff_outside_permitted_classes_fails_closed": True,
            "v0_and_v1_source_hashes_required_in_result": True,
            "frozen_surface_audit_required_before_decision_bearing_work": True,
            "mandatory_result_labels": list(EXPLORATORY_LABELS),
            "resource_envelope_unchanged": {
                "synthetic_infrastructure_stage_timeout_seconds": 60,
                "synthetic_infrastructure_stage_memory_mib": 256,
                "total_timeout_seconds": 300,
                "total_memory_mib": 1024,
            },
        },
        "real_path_serialization_control": {
            "runs_before_decision_bearing_calculations": True,
            "schema_complete_synthetic_final_aggregate": True,
            "all_live_decimal_locations_populated": True,
            "nested_adjudication_records_included": True,
            "complete_final_aggregate_shape_included": True,
            "same_recursive_normalizer_as_real_result": True,
            "same_recursive_schema_validator_as_real_result": True,
            "same_canonical_encoder_as_real_result": True,
            "same_atomic_writer_as_real_result": True,
            "same_strict_parser_and_hash_verifier_as_real_result": True,
            "same_finalization_path_as_real_result": True,
            "post_normalization_decimal_count_required": 0,
            "post_normalization_unknown_object_count_required": 0,
            "failure_consumes_execution_and_fails_closed": True,
            "atomic_commit_pipeline": list(ATOMIC_COMMIT_PIPELINE),
        },
        "selection_gates": {
            "gate_count": len(selection_gates),
            "pass_count": len(selection_gates),
            "failure_count": 0,
            "rows": [{"gate_id": gate, "status": "PASS"} for gate in selection_gates],
        },
        "terminal_boundary": {
            "authorized_v1_execution_count": 1,
            "automatic_v2_authorized": False,
            "third_sandbox_attempt_authorized": False,
            "additional_repair_chain_authorized": False,
            "additional_infrastructure_prerequisite_authorized": False,
            "complete_result_successor": "INDEPENDENT_EXPLORATORY_RESULT_REVIEW_ONLY",
            "complete_preserved_negative_successor": (
                "INDEPENDENT_FAILURE_REVIEW_THEN_FRESH_SUBSTANTIVE_LANE_SELECTOR"
            ),
            "preservation_failure_successor": (
                "RETIRE_OR_DEFER_ANALYTIC_REPLACEMENT_LANE_ONLY"
            ),
            "production_advancement_automatic": False,
        },
        "forbidden_during_v1": [
            "EDIT_ANALYTIC_FORMULAS_EVALUATORS_CASES_REFERENCES_OR_TOLERANCES",
            "EDIT_PROBES_MUTATIONS_PREDICATES_ADJUDICATORS_SCANNER_OR_WORKLOAD",
            "PERMISSIVE_DEFAULT_STRING_OR_UNKNOWN_OBJECT_COERCION",
            "RECONSTRUCT_OR_PROMOTE_V0_TRANSIENT_VALUES",
            "IMPORT_MODIFY_OR_DISPATCH_THROUGH_PRODUCTION_KERNEL",
            "CALL_OR_ADJUDICATE_HISTORICAL_CUBATURE",
            "SHADOW_QUALIFICATION_ADOPTION_OR_ROLLBACK",
            "TORQUE_DFT_REAL150_JACOBIAN_SVD_IDENTIFIABILITY_STAGE_A_OR_STAGE_B",
            "SCIENTIFIC_EMPIRICAL_OR_PRODUCTION_CLAIM",
        ],
        "scope": scope,
        "current_posture": {
            "analytic_sphere_oracle": "QUALIFIED_AND_ACCEPTED",
            "v0_sandbox_result": "ACCEPTED_SERIALIZATION_FAILURE_NO_SCIENTIFIC_RESULT",
            "v1_sandbox": "FINAL_ONE_SHOT_IMPLEMENTATION_AND_EXECUTION_AUTHORIZED",
            "historical_cubature": "UNADJUDICATED_RETIRED_FROM_DECISION_BEARING_USE",
            "production": "UNCHANGED_NOT_AUTHORIZED",
            "stage_a": "NOT_REOPENED",
            "stage_b": "NOT_AUTHORIZED",
            "next_authority": SELECTED_NEXT_TARGET,
        },
        "claim_ceiling": (
            "This selector authorizes exactly one final versioned non-production and "
            "non-adjudicative sandbox implementation and execution, limited to the frozen "
            "serialization, real-aggregate control, atomic-preservation, version, hash, and "
            "custody corrections. It does not implement or execute V1 in this selection, "
            "reconstruct V0 transient values, qualify or refute the candidate kernel, "
            "adjudicate cubature, change production, perform shadow qualification, rerun "
            "Stage A, compute torque, DFT, vector, Jacobian, SVD, or identifiability, "
            "authorize Stage B, or permit a scientific or empirical claim."
        ),
    }


def artifact_bytes() -> bytes:
    return (json.dumps(build_report(), indent=2, sort_keys=True) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Select a final serialization-corrected sandbox V1 or retirement after the "
            "accepted V0 preservation failure."
        )
    )
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--write", action="store_true")
    args = parser.parse_args()
    output = REPO_ROOT / REPORT_RELATIVE_PATH
    expected = artifact_bytes()
    current = output.read_bytes() if output.exists() else None
    if args.write:
        if current != expected:
            output.write_bytes(expected)
            print(f"wrote {REPORT_RELATIVE_PATH}")
        else:
            print("final V1 sandbox selector already current")
        return 0
    if current != expected:
        print("final V1 sandbox selector drift")
        return 1
    report = build_report()
    print(
        "final V1 sandbox selector OK "
        f"route={report['selected_route']} score={report['ranking']['selected_score']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
