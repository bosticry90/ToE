from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_PRODUCTION_CUBATURE_VS_ANALYTIC_"
    "ORACLE_COMPARISON_PACKET_20260719_v1.json"
)
HUMAN_RELATIVE_PATH = (
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_PRODUCTION_CUBATURE_VS_ANALYTIC_"
    "ORACLE_COMPARISON_PACKET_20260719_v1.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/test_scalar_only_yukawa_production_cubature_vs_analytic_"
    "oracle_comparison_packet_v1.py"
)
LEAN_RELATIVE_PATH = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "ScalarOnlyYukawaProductionCubatureVsAnalyticOracleComparisonPacketV1.lean"
)
V0_REPORT_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_PRODUCTION_CUBATURE_VS_ANALYTIC_"
    "ORACLE_COMPARISON_PACKET_20260719_v0.json"
)
SELECTOR_RELATIVE_PATH = (
    "formal/docs/release/POST_SCALAR_ONLY_YUKAWA_PRODUCTION_CUBATURE_VS_ANALYTIC_"
    "ORACLE_COMPARISON_PACKET_REVIEW_SCIENTIFIC_RESPONSE_SELECTION_20260719_v0.json"
)

TARGET = (
    "prepare_scalar_only_yukawa_production_cubature_vs_analytic_oracle_"
    "comparison_packet_v1"
)
VERDICT = (
    "PREPARED_SCALAR_ONLY_YUKAWA_PRODUCTION_CUBATURE_VS_ANALYTIC_ORACLE_"
    "COMPARISON_PACKET_V1"
)
SELECTED_NEXT_TARGET = (
    "review_scalar_only_yukawa_production_cubature_vs_analytic_oracle_"
    "comparison_packet_v1_result"
)
SELECTED_NEXT_TARGET_KIND = "INDEPENDENT_PACKET_REVIEW_ONLY_NO_COMPARISON_EXECUTION"

SELECTOR_HASHES = {
    "formal/docs/lanes/POST_SCALAR_ONLY_YUKAWA_PRODUCTION_CUBATURE_VS_ANALYTIC_ORACLE_COMPARISON_PACKET_REVIEW_SCIENTIFIC_RESPONSE_SELECTION_20260719_v0.md":
        "c290298752ba076543146884ac107527707814510bb522ecc9d5203ba06c9da5",
    SELECTOR_RELATIVE_PATH:
        "122fe8d12036f73c43e100e38511998d6e1f23adc4b5e18a0d10a5b3d1bae1a2",
    "formal/python/tools/post_scalar_only_yukawa_production_cubature_vs_analytic_oracle_comparison_packet_review_scientific_response_selection_v0.py":
        "fc89fb19cc8fc00584afb075513cc9dd28d53ed874a1609e12ac22c0968b45ca",
    "formal/python/tests/test_post_scalar_only_yukawa_production_cubature_vs_analytic_oracle_comparison_packet_review_scientific_response_selection_v0.py":
        "7d3e34c46222f6ad9f3fb2a5d08ef2206d0c05f9106d836d8b066821e541c9a0",
    "formal/toe_formal/ToeFormal/Derivation/PostScalarOnlyYukawaProductionCubatureVsAnalyticOracleComparisonPacketReviewScientificResponseSelectionV0.lean":
        "cf4b49ee62ca0bf27e29b93be760284756fd6371a3e99af237212a5c5b8da9da",
}

V0_PACKET_HASHES = {
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_PRODUCTION_CUBATURE_VS_ANALYTIC_ORACLE_COMPARISON_PACKET_20260719_v0.md":
        "255208335825d75616f27cd76df09f7743092ffc2b8a766e484d041c89acea1c",
    V0_REPORT_RELATIVE_PATH:
        "e8a3a610b60749386758c7b666cd20f3f80dd96fb3571a99250055fedb7062a7",
    "formal/python/tools/scalar_only_yukawa_production_cubature_vs_analytic_oracle_comparison_packet_v0.py":
        "87313c439a7841af21828b26483a74daa00d25e4487c4c9765de7c58aed09193",
    "formal/python/tests/test_scalar_only_yukawa_production_cubature_vs_analytic_oracle_comparison_packet_v0.py":
        "52558c1d185698800260f45e2401342763872da36bd9807621faf5242a65ef29",
    "formal/toe_formal/ToeFormal/Derivation/ScalarOnlyYukawaProductionCubatureVsAnalyticOracleComparisonPacketV0.lean":
        "67a5ae19cc0c300bd6d47546f14f073f514962147cd96cd010fb46b10acf11a8",
}

ORDERS = (8, 16, 24, 32, 40, 48)
FINAL_ORDERS = (32, 40, 48)
FIT_ORDERS = (16, 24, 32, 40, 48)
FIT_TAIL_ORDERS = (24, 32, 40, 48)
LEGACY_CASE_IDS = (
    "LEGACY_STAGE_A_00_LARGE_X",
    "LEGACY_STAGE_A_01_TRANSITION",
    "LEGACY_STAGE_A_02_LONG_RANGE",
)
MIRROR_EXTENSION_CASE_IDS = (
    "SMALL_X_UNEQUAL_WIDE",
    "MIXED_X_UNEQUAL",
    "SMALL_GAP_LARGE_X",
    "EXTREME_X_1000_UNEQUAL",
    "LONG_RANGE_UNEQUAL_WIDE",
)
CASE_IDS = LEGACY_CASE_IDS + MIRROR_EXTENSION_CASE_IDS
COMPONENTS = ("NEWTONIAN", "YUKAWA")

SCIENTIFIC_LABELS = (
    "FIXED_ORDER_CUBATURE_INADEQUATE",
    "IMPLEMENTATION_OR_NORMALIZATION_DEFECT_INDICATED",
    "NEAR_CONTACT_OR_TRANSITION_REGIME_UNDERSAMPLED",
    "PRODUCTION_COMPARISON_TIMEOUT",
    "PRODUCTION_CUBATURE_VALIDATED_ON_TESTED_CASES",
    "PRODUCTION_FAILURE_NOT_LOCALIZED",
    "REGIME_DEPENDENT_PRODUCTION_FAILURE",
    "SLOW_BUT_CONVERGENT_AND_ECONOMICALLY_INFERIOR",
    "YUKAWA_SPECIFIC_IMPLEMENTATION_DEFECT_INDICATED",
)
REPAIRED_REVIEW_GATES = (
    "R12_HISTORICAL_AND_MIRROR_ACCUMULATION_IDENTICAL",
    "R13_HISTORICAL_AND_MIRROR_DECISION_SCOPE_SEPARATED",
    "R14_LEGACY_EQUIVALENCE_RULE_EXECUTABLE",
    "R24_SLOW_CONVERGENCE_FIT_AND_COST_RULE_EXECUTABLE",
    "R25_SYSTEMATIC_BIAS_AND_FINGERPRINT_RULES_EXECUTABLE",
    "R31_CONTROL_CASE_ORDER_AND_TOLERANCE_ROUTING",
    "R36_INCOMPLETE_RECORDS_SUPPRESS_SCIENTIFIC_CLASSIFICATION",
)
PACKET_REVIEW_OUTCOMES = (
    "PRODUCTION_COMPARISON_CONTRACT_READY",
    "BLOCKED_PRODUCTION_PATH_IDENTITY",
    "BLOCKED_METRIC_OR_CLASSIFICATION_CONTRACT",
    "BLOCKED_MUTATION_ROUTING",
    "BLOCKED_INCOMPLETE_RECORD_PRECEDENCE",
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


def _route(
    control_id: str,
    case_ids: tuple[str, ...],
    orders: tuple[int, ...],
    components: tuple[str, ...],
    execution_order: str,
    injection_point: str,
    acceptance_rule: str,
    required_detection: str,
    **extra: Any,
) -> dict[str, Any]:
    failure = (
        "BLOCKED_PRODUCTION_PATH_IDENTITY_AND_STOP_BEFORE_MUTATIONS_OR_96_CELLS"
        if control_id == "C00_HISTORICAL_MIRROR_EQUIVALENCE"
        else "BLOCKED_PRODUCTION_COMPARISON_CONTROLS_AND_SUPPRESS_ALL_SCIENTIFIC_LABELS"
    )
    return {
        "control_id": control_id,
        "case_ids": list(case_ids),
        "orders": list(orders),
        "components": list(components),
        "execution_order": execution_order,
        "injection_point": injection_point,
        "acceptance_rule": acceptance_rule,
        "required_detection": required_detection,
        "failure_consequence": failure,
        **extra,
    }


def _control_routes() -> list[dict[str, Any]]:
    case_then_order = "CASE_ORDER_AS_LISTED_THEN_ASCENDING_ORDER"
    case_order_component = case_then_order + "_THEN_COMPONENT_ORDER"
    four_bias_cases = LEGACY_CASE_IDS + ("SMALL_X_UNEQUAL_WIDE",)
    return [
        _route(
            "C00_HISTORICAL_MIRROR_EQUIVALENCE",
            LEGACY_CASE_IDS,
            (8, 16, 24),
            ("YUKAWA",),
            case_then_order + ";_HISTORICAL_FIRST_THEN_MIRROR_ORDINARY",
            "NONE",
            "ABS(H-M)<=1E-36+5E-14*MAX(ABS(H),ABS(M))_FOR_ALL_NINE_PAIRS",
            "EXACT_HISTORICAL_TO_MIRROR_ORDINARY_EQUIVALENCE",
            kind="MANDATORY_PATH_IDENTITY_PREFLIGHT_NOT_ONE_OF_TEN_MUTATIONS",
            historical_function="reduced_four_dimensional_density_integral_yukawa_energy",
            mirror_function="_fixed_density_integral(summation='ORDINARY')",
            absolute_tolerance_J=1e-36,
            relative_tolerance=5e-14,
        ),
        _route(
            "C01_POINT_EQUIVALENT_NEWTONIAN",
            ("SMALL_X_UNEQUAL_WIDE",),
            FINAL_ORDERS,
            ("NEWTONIAN",),
            "ASCENDING_ORDER",
            "NONE_MIRROR_NEWTONIAN_COMPANION_PATH",
            "ALL_THREE_RECORDS_PASS_FROZEN_ACCURACY_RULE",
            "POINT_EQUIVALENT_NEWTONIAN_ACCURACY",
            kind="FROZEN_V0_CONTROL",
        ),
        _route(
            "C02_MISSING_A_Y_ONE_THIRD",
            CASE_IDS,
            FINAL_ORDERS,
            ("YUKAWA",),
            case_then_order,
            "SET_A_Y_FROM_1_OVER_3_TO_1_IMMEDIATELY_AFTER_RAW_YUKAWA_DENSITY_INTEGRAL",
            "ALL_24_MUTATED_TO_UNMUTATED_RATIOS_EQUAL_3_WITH_ABS_REL_TOL_1E-12_AND_FINGERPRINT_LENGTH_24",
            "YUKAWA_SPECIFIC_IMPLEMENTATION_DEFECT_INDICATED_ON_CONTROL_FIXTURE",
            kind="FROZEN_V0_CONTROL",
            absolute_tolerance=1e-12,
            relative_tolerance=1e-12,
        ),
        _route(
            "C03_GAP_FOR_CENTER_DISTANCE",
            ("LEGACY_STAGE_A_01_TRANSITION", "SMALL_GAP_LARGE_X"),
            (24, 48),
            COMPONENTS,
            case_order_component,
            "REPLACE_D_WITH_G_AT_KERNEL_DENOMINATOR_AND_EXPONENTIAL_ARGUMENT",
            "EVERY_MUTATED_RECORD_DIFFERS_FROM_UNMUTATED_BY_RELATIVE_AT_LEAST_1E-3",
            "IMPLEMENTATION_OR_NORMALIZATION_DEFECT_INDICATED_ON_CONTROL_FIXTURE",
            kind="FROZEN_V0_CONTROL",
            minimum_relative_change=1e-3,
        ),
        _route(
            "C04_RADIUS_AS_DIAMETER",
            ("LEGACY_STAGE_A_02_LONG_RANGE", "SMALL_X_UNEQUAL_WIDE"),
            (16, 32),
            COMPONENTS,
            case_order_component,
            "REPLACE_EACH_RADIUS_R_WITH_2R_BEFORE_NODE_AND_VOLUME_WEIGHT_CONSTRUCTION",
            "STRICT_NONOVERLAP_RECHECK_PASSES_AND_EVERY_MUTATED_RECORD_CHANGES_BY_RELATIVE_AT_LEAST_0P1",
            "IMPLEMENTATION_OR_NORMALIZATION_DEFECT_INDICATED_ON_CONTROL_FIXTURE",
            kind="FROZEN_V0_CONTROL",
            minimum_relative_change=0.1,
        ),
        _route(
            "C05_ONE_DIMENSION_UNREFINED",
            ("LEGACY_STAGE_A_00_LARGE_X", "SMALL_GAP_LARGE_X"),
            (24, 32, 40, 48),
            COMPONENTS,
            case_order_component,
            "SET_MU2_ORDER_TO_8_WHILE_R1_MU1_R2_USE_RECORDED_ORDER",
            "EXECUTED_DIMENSION_VECTOR_EQUALS_[N,N,N,8]_AND_CLASSIFIER_EMITS_FIXED_ORDER_CUBATURE_INADEQUATE",
            "FIXED_ORDER_CUBATURE_INADEQUATE_ON_CONTROL_FIXTURE",
            kind="FROZEN_V0_CONTROL",
            metadata_tolerance="EXACT",
        ),
        _route(
            "C06_WEIGHT_NORMALIZATION_BIAS",
            four_bias_cases,
            FINAL_ORDERS,
            COMPONENTS,
            case_order_component,
            "MULTIPLY_ACCUMULATED_QUADRATURE_WEIGHT_PRODUCT_BY_1P01_BEFORE_G_AND_A_Y",
            "ALL_24_MUTATED_TO_UNMUTATED_RATIOS_EQUAL_1P01_WITH_ABS_REL_TOL_1E-12_AND_BOTH_COMPONENT_GROUPS_TRIGGER_SYSTEMATIC_BIAS",
            "IMPLEMENTATION_OR_NORMALIZATION_DEFECT_INDICATED_ON_CONTROL_FIXTURE",
            kind="FROZEN_V0_CONTROL",
            absolute_tolerance=1e-12,
            relative_tolerance=1e-12,
        ),
        _route(
            "C07_COMPONENT_CHANNEL_SWAP",
            ("LEGACY_STAGE_A_01_TRANSITION",),
            (16,),
            COMPONENTS,
            "NEWTONIAN_THEN_YUKAWA",
            "SWAP_COMPONENT_IDS_AT_ATOMIC_RECORD_SERIALIZATION",
            "COMPONENT_SOURCE_AND_ORACLE_COMPONENT_HASH_MISMATCH_REJECTS_RECORD_BEFORE_METRICS",
            "CHANNEL_IDENTITY_FIREWALL",
            kind="FROZEN_V0_CONTROL",
            tolerance="EXACT_HASH_AND_ENUM_IDENTITY",
        ),
        _route(
            "C08_ORDER_METADATA_OVERCLAIM",
            ("LEGACY_STAGE_A_01_TRANSITION",),
            (40,),
            COMPONENTS,
            "NEWTONIAN_THEN_YUKAWA",
            "WRITE_RECORDED_ORDER_48_AFTER_EXECUTING_ORDER_40",
            "EXECUTED_NODE_COUNT_AND_RULE_HASH_MISMATCH_REJECTS_RECORD_BEFORE_COMMIT",
            "ORDER_CUSTODY_FIREWALL",
            kind="FROZEN_V0_CONTROL",
            tolerance="EXACT_INTEGER_AND_SHA256_IDENTITY",
        ),
        _route(
            "C09_ORACLE_OVERWRITE",
            ("LEGACY_STAGE_A_01_TRANSITION",),
            (16,),
            COMPONENTS,
            "NEWTONIAN_THEN_YUKAWA",
            "ATTEMPT_TO_WRITE_PRODUCTION_VALUE_INTO_READ_ONLY_ORACLE_FIELD_AT_SERIALIZATION",
            "PRE_AND_POST_ORACLE_ARTIFACT_AND_VALUE_HASH_MISMATCH_REJECTS_WRITE_AND_RECORD",
            "ORACLE_IMMUTABILITY_FIREWALL",
            kind="FROZEN_V0_CONTROL",
            tolerance="EXACT_SHA256_IDENTITY",
        ),
        _route(
            "C10_CONSTANT_MULTIPLICATIVE_BIAS",
            four_bias_cases,
            FINAL_ORDERS,
            COMPONENTS,
            case_order_component,
            "MULTIPLY_PRODUCTION_COMPONENT_BY_1P02_AFTER_INTEGRATION_BEFORE_METRICS",
            "ALL_24_MUTATED_TO_UNMUTATED_RATIOS_EQUAL_1P02_WITH_ABS_REL_TOL_1E-12_AND_BOTH_COMPONENT_GROUPS_TRIGGER_SYSTEMATIC_BIAS",
            "IMPLEMENTATION_OR_NORMALIZATION_DEFECT_INDICATED_ON_CONTROL_FIXTURE",
            kind="FROZEN_V0_CONTROL",
            absolute_tolerance=1e-12,
            relative_tolerance=1e-12,
        ),
    ]


def build_report() -> dict[str, Any]:
    for relative_path, expected_hash in SELECTOR_HASHES.items():
        if _sha256(REPO_ROOT / relative_path) != expected_hash:
            raise ValueError(f"selector authority drift: {relative_path}")
    for relative_path, expected_hash in V0_PACKET_HASHES.items():
        if _sha256(REPO_ROOT / relative_path) != expected_hash:
            raise ValueError(f"frozen V0 packet drift: {relative_path}")

    selector = _load_json(SELECTOR_RELATIVE_PATH)
    v0 = _load_json(V0_REPORT_RELATIVE_PATH)
    if selector.get("selected_next_target") != TARGET:
        raise ValueError("selector did not authorize V1 packet preparation")
    if selector.get("selected_candidate_id") != "SEVEN_GATE_COMPARISON_CONTRACT_REPAIR_V1":
        raise ValueError("selector candidate mismatch")
    if selector.get("scope", {}).get("comparison_execution_performed") is not False:
        raise ValueError("selector unexpectedly performed comparison execution")

    domain = v0.get("comparison_domain", {})
    if tuple(domain.get("case_ids", [])) != CASE_IDS:
        raise ValueError("V0 case order drift")
    if tuple(domain.get("orders", [])) != ORDERS:
        raise ValueError("V0 order ladder drift")
    if tuple(domain.get("components", [])) != COMPONENTS:
        raise ValueError("V0 component order drift")
    if domain.get("required_atomic_scientific_cells") != 96:
        raise ValueError("V0 atomic-cell count drift")
    if set(v0.get("classification_contract", {}).get("predicates", {})) != set(SCIENTIFIC_LABELS):
        raise ValueError("V0 scientific-label set drift")

    source_rows = []
    for case_id in CASE_IDS:
        for order in ORDERS:
            for component in COMPONENTS:
                if case_id in LEGACY_CASE_IDS and component == "YUKAWA":
                    source = "EXACT_HISTORICAL_STAGE_A_YUKAWA_FUNCTION"
                    evidence_scope = "HISTORICAL_STAGE_A_YUKAWA"
                elif component == "NEWTONIAN":
                    source = "PARAMETERIZED_MIRROR_PAIRWISE_NEWTONIAN"
                    evidence_scope = "MIRROR_NEWTONIAN_COMPANION"
                else:
                    source = "PARAMETERIZED_MIRROR_PAIRWISE_YUKAWA"
                    evidence_scope = "PARAMETERIZED_MIRROR_YUKAWA_EXTENSION"
                source_rows.append({
                    "case_id": case_id,
                    "order": order,
                    "component": component,
                    "production_source": source,
                    "evidence_scope": evidence_scope,
                })
    scopes = (
        "HISTORICAL_STAGE_A_YUKAWA",
        "MIRROR_NEWTONIAN_COMPANION",
        "PARAMETERIZED_MIRROR_YUKAWA_EXTENSION",
    )
    source_counts = {
        scope: sum(row["evidence_scope"] == scope for row in source_rows)
        for scope in scopes
    }

    controls = _control_routes()
    v0_controls = [row["control_id"] for row in v0["controls"]["rows"]]
    if [row["control_id"] for row in controls[1:]] != v0_controls:
        raise ValueError("ten frozen V0 controls changed identity or order")
    preserved_predicates = {
        key: value
        for key, value in v0["classification_contract"]["predicates"].items()
        if key not in {
            "IMPLEMENTATION_OR_NORMALIZATION_DEFECT_INDICATED",
            "SLOW_BUT_CONVERGENT_AND_ECONOMICALLY_INFERIOR",
            "YUKAWA_SPECIFIC_IMPLEMENTATION_DEFECT_INDICATED",
        }
    }

    packet_gates = (
        "SELECTOR_AUTHORITY_HASHES_MATCH",
        "V0_PACKET_HASHES_MATCH",
        "EXACT_THIRTY_THREE_ACCEPTED_REVIEW_GATES_FROZEN",
        "EXACT_SEVEN_FAILED_REVIEW_GATES_REPAIRED_ONLY",
        "EIGHT_CASES_UNCHANGED",
        "SIX_ORDERS_UNCHANGED",
        "TWO_COMPONENTS_UNCHANGED",
        "NINETY_SIX_SCIENTIFIC_CELLS_UNCHANGED",
        "ORACLE_CUSTODY_UNCHANGED",
        "BASE_METRICS_AND_ACCURACY_UNCHANGED",
        "RESOURCE_ENVELOPE_UNCHANGED",
        "HISTORICAL_YUKAWA_FUNCTION_DIRECT_FOR_EIGHTEEN_CELLS",
        "NEWTONIAN_COMPANION_SCOPE_EXPLICIT_FOR_FORTY_EIGHT_CELLS",
        "MIRROR_YUKAWA_EXTENSION_SCOPE_EXPLICIT_FOR_THIRTY_CELLS",
        "EXACT_SOURCE_MAP_FOR_ALL_NINETY_SIX_CELLS",
        "LEGACY_EQUIVALENCE_CASES_ORDERS_AND_SEQUENCE_FROZEN",
        "LEGACY_EQUIVALENCE_TOLERANCE_FROZEN",
        "LEGACY_EQUIVALENCE_FAILURE_STOPS_BEFORE_SCIENCE",
        "MIRROR_ONLY_RESULTS_CANNOT_SUPPORT_HISTORICAL_CLAIMS",
        "SLOW_ERROR_FIT_FAMILY_AND_ORDER_SUBSETS_FROZEN",
        "SLOW_FIT_NONMONOTONE_AND_ZERO_HANDLING_FROZEN",
        "SLOW_FIT_STABILITY_THRESHOLDS_FROZEN",
        "RUNTIME_FIT_AND_REQUIRED_ORDER_FORMULAE_FROZEN",
        "ECONOMIC_INFERIORITY_THRESHOLD_FROZEN",
        "SYSTEMATIC_BIAS_GROUPING_PER_COMPONENT_FROZEN",
        "SYSTEMATIC_BIAS_RATIO_VECTOR_AND_SPREAD_FROZEN",
        "YUKAWA_FINGERPRINT_VECTOR_ORDER_FROZEN",
        "YUKAWA_FINGERPRINT_DISTANCE_AND_TOLERANCE_FROZEN",
        "TEN_V0_MUTATION_CONTROLS_PRESERVED",
        "ONE_MANDATORY_PATH_IDENTITY_PREFLIGHT_ADDED",
        "ALL_ELEVEN_CONTROL_CASE_ROUTES_EXACT",
        "ALL_ELEVEN_CONTROL_ORDER_ROUTES_EXACT",
        "ALL_ELEVEN_INJECTION_POINTS_EXACT",
        "ALL_ELEVEN_ACCEPTANCE_RULES_EXACT",
        "ALL_ELEVEN_FAILURE_CONSEQUENCES_EXACT",
        "FULL_NINETY_SIX_CELL_COMPLETENESS_REQUIRED",
        "ALL_MANDATORY_CONTROLS_REQUIRED",
        "ADMINISTRATIVE_OUTCOME_PRECEDENCE_FROZEN",
        "PARTIAL_CELLS_CANNOT_SUPPORT_SCIENTIFIC_LABELS",
        "EXACT_NINE_SCIENTIFIC_LABELS_PRESERVED",
        "NO_PACKET_EXECUTION_NOW",
        "NO_KERNEL_REPAIR_OR_REPLACEMENT",
        "NO_TORQUE_DFT_VECTOR_OR_IDENTIFIABILITY",
        "NO_STAGE_A_RERUN_OR_STAGE_B",
        "INDEPENDENT_V1_PACKET_REVIEW_REQUIRED",
        "AUTOMATIC_V2_PROHIBITED",
    )

    scope = {
        "v1_packet_prepared": True,
        "selector_authority_verified": True,
        "v0_packet_hash_frozen": True,
        "thirty_three_accepted_review_gates_frozen": True,
        "seven_failed_review_gates_repaired_in_contract": True,
        "independent_v1_packet_review_authorized": True,
        "v1_packet_review_performed": False,
        "comparison_contract_accepted": False,
        "comparison_execution_authorized": False,
        "comparison_execution_performed": False,
        "scientific_comparison_cells_computed": False,
        "production_cubature_adjudicated": False,
        "production_kernel_repair_authorized": False,
        "production_kernel_replacement_authorized": False,
        "torque_or_dft_authorized": False,
        "final_real_150_vector_authorized": False,
        "jacobian_or_identifiability_authorized": False,
        "stage_a_rerun_authorized": False,
        "stage_b_authorized": False,
        "automatic_v2_authorized": False,
    }

    return {
        "schema_id": "toe.scalar_only_yukawa.production_cubature_vs_analytic_oracle.comparison_packet.v1",
        "packet_id": "SCALAR_ONLY_YUKAWA_PRODUCTION_CUBATURE_VS_ANALYTIC_ORACLE_COMPARISON_PACKET_20260719_v1",
        "captured_at_utc": "2026-07-19T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "status": "PREPARED_PENDING_INDEPENDENT_REVIEW_NO_EXECUTION",
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "authority": {
            "consumed_selector_verdict": selector["verdict"],
            "frozen_selector_artifacts": [
                {"relative_path": path, "sha256": digest}
                for path, digest in SELECTOR_HASHES.items()
            ],
            "frozen_v0_packet_artifacts": [
                {"relative_path": path, "sha256": digest}
                for path, digest in V0_PACKET_HASHES.items()
            ],
            "human_packet": _artifact_row(HUMAN_RELATIVE_PATH),
            "generator": _artifact_row(
                "formal/python/tools/scalar_only_yukawa_production_cubature_vs_"
                "analytic_oracle_comparison_packet_v1.py"
            ),
            "test": _artifact_row(TEST_RELATIVE_PATH),
            "lean": _artifact_row(LEAN_RELATIVE_PATH),
        },
        "frozen_v0_surfaces": {
            "accepted_review_gate_count": 33,
            "accepted_inputs": v0["accepted_inputs"],
            "comparison_domain": v0["comparison_domain"],
            "oracle_path_identity": v0["oracle_path_identity"],
            "metric_contract": v0["metric_contract"],
            "resource_and_custody_contract": v0["resource_and_custody_contract"],
            "scientific_label_set": list(SCIENTIFIC_LABELS),
            "ten_mutation_control_ids": v0_controls,
            "semantic_change": "FORBIDDEN",
        },
        "v1_repair_scope": {
            "repaired_review_gate_count": len(REPAIRED_REVIEW_GATES),
            "repaired_review_gates": list(REPAIRED_REVIEW_GATES),
            "all_other_review_gates": "FROZEN",
            "automatic_v2": "PROHIBITED",
        },
        "production_source_and_attribution_contract": {
            "execution_order": "CASE_ORDER_AS_FROZEN_THEN_ASCENDING_ORDER_THEN_NEWTONIAN_BEFORE_YUKAWA",
            "source_rows": source_rows,
            "source_counts": source_counts,
            "historical_decision_bearing_case_ids": list(LEGACY_CASE_IDS),
            "historical_decision_bearing_component": "YUKAWA_ONLY",
            "historical_function_called_directly": True,
            "mirror_extension_case_ids": list(MIRROR_EXTENSION_CASE_IDS),
            "mirror_default_summation": "PAIRWISE_NUMPY_BINARY64",
            "newtonian_historical_claim": "FORBIDDEN_COMPANION_DIAGNOSTIC_ONLY",
            "unequal_radius_historical_claim": "FORBIDDEN",
            "full_matrix_claim": "HYBRID_CONTRACT_SCOPE_NOT_RETROACTIVE_STAGE_A_OUTPUT",
            "every_scientific_label_must_serialize_evidence_scope": True,
        },
        "historical_path_equivalence_contract": controls[0],
        "classification_contract_v1": {
            "scientific_labels_exact": list(SCIENTIFIC_LABELS),
            "preserved_predicates": preserved_predicates,
            "slow_convergence_fit": {
                "candidate_prerequisite": "FAILS_ACCURACY_AT_ORDER48_AND_ERRORS_POSITIVE_FINITE_STRICTLY_DECREASE_AT_16_24_32_40_48_AND_EVERY_Q_LT_0P95",
                "zero_error_behavior": "NOT_A_SLOW_FIT_CANDIDATE_ALREADY_ACCURATE_AT_THAT_ORDER",
                "nonfinite_or_nonpositive_error_behavior": "FIT_INVALID_PRODUCTION_FAILURE_NOT_LOCALIZED",
                "nonmonotone_error_behavior": "SLOW_LABEL_FORBIDDEN_EVALUATE_OTHER_FROZEN_LABELS",
                "error_fit_family": "OLS_NATURAL_LOG_ERROR_EQUALS_A_MINUS_P_NATURAL_LOG_ORDER",
                "full_fit_orders": list(FIT_ORDERS),
                "tail_fit_orders": list(FIT_TAIL_ORDERS),
                "minimum_r_squared_each_fit": 0.98,
                "required_positive_exponent_each_fit": True,
                "maximum_relative_exponent_difference": 0.20,
                "required_order_formula": "CEIL(EXP((A_FULL-LOG(1E-36+1E-6*ABS(U_ORACLE)))/P_FULL))",
                "minimum_required_order_for_label": 49,
                "maximum_admissible_extrapolated_order": 192,
                "outside_extrapolation_behavior": "SLOW_LABEL_FORBIDDEN_PRODUCTION_FAILURE_NOT_LOCALIZED_UNLESS_ANOTHER_LABEL_HOLDS",
                "runtime_fit_family": "PER_CASE_OLS_NATURAL_LOG_SECONDS_EQUALS_B_PLUS_S_NATURAL_LOG_ORDER",
                "runtime_fit_orders": list(FIT_ORDERS),
                "runtime_fit_positive_finite_required": True,
                "runtime_fit_minimum_r_squared": 0.95,
                "runtime_fit_positive_exponent_required": True,
                "per_case_projected_seconds_formula": "EXP(B_CASE+S_CASE*LOG(MAX_REQUIRED_COMPONENT_ORDER_FOR_CASE))",
                "already_accurate_case_runtime": "MEASURED_ORDER48_SECONDS",
                "projected_total_seconds_formula": "SUM_OVER_8_CASES_OF_PER_CASE_PROJECTED_SECONDS_WITH_COMPONENTS_NOT_DOUBLE_COUNTED",
                "economic_inferiority_rule": "ANY_PROJECTED_CASE_SECONDS_GT_60_OR_PROJECTED_TOTAL_SECONDS_GT_1200",
                "label_rule": "ALL_CANDIDATE_AND_FIT_STABILITY_RULES_PASS_AND_ECONOMIC_INFERIORITY_RULE_TRUE",
                "near_threshold_behavior": "PRODUCTION_FAILURE_NOT_LOCALIZED_NO_FAVORABLE_ROUNDING",
            },
            "systematic_bias": {
                "grouping": "SEPARATELY_PER_COMPONENT_NEVER_MIX_NEWTONIAN_AND_YUKAWA",
                "orders": list(FINAL_ORDERS),
                "qualifying_case_rule": "CASE_FAILS_ACCURACY_AT_ALL_THREE_FINAL_ORDERS",
                "minimum_qualifying_cases_per_component": 4,
                "ratio_vector_order": "FROZEN_CASE_ORDER_THEN_32_40_48",
                "ratio_entry": "U_PRODUCTION/U_ORACLE",
                "finite_and_oracle_floor_required": True,
                "location": "MEDIAN_OF_ALL_COMPONENT_GROUP_RATIO_ENTRIES",
                "relative_spread": "(MAX_RATIO-MIN_RATIO)/MAX(ABS(MEDIAN_RATIO),1E-300)",
                "maximum_relative_spread": 0.005,
                "minimum_absolute_median_bias": 0.001,
                "same_sign_required": True,
                "label": "IMPLEMENTATION_OR_NORMALIZATION_DEFECT_INDICATED",
                "historical_scope_limitation": "CANNOT_TRIGGER_FROM_THREE_LEGACY_CASES_ALONE_MINIMUM_IS_FOUR",
            },
            "yukawa_mutation_fingerprint": {
                "observed_component": "YUKAWA",
                "reference_control": "C02_MISSING_A_Y_ONE_THIRD",
                "case_order": list(CASE_IDS),
                "order_within_case": list(FINAL_ORDERS),
                "vector_length": 24,
                "entry": "SIGNED_RATIO_MINUS_1",
                "all_entries_finite_required": True,
                "reference_l2_norm_minimum": 1e-3,
                "relative_l2_distance": "NORM2(F_OBS-F_C02)/MAX(NORM2(F_C02),1E-300)",
                "maximum_relative_l2_distance": 0.05,
                "maximum_entrywise_absolute_difference": 0.10,
                "minimum_nonzero_sign_agreement_count": 23,
                "required_sign_comparison_count": 24,
                "newtonian_prerequisite": "NEWTONIAN_PASSES_ALL_8_CASES_AT_32_40_48",
                "yukawa_prerequisite": "AT_LEAST_ONE_YUKAWA_CASE_FAILS_ALL_32_40_48",
                "label": "YUKAWA_SPECIFIC_IMPLEMENTATION_DEFECT_INDICATED",
                "unmatched_behavior": "YUKAWA_SPECIFIC_LABEL_FORBIDDEN_EVALUATE_OTHER_FROZEN_LABELS",
            },
            "evidence_scope_rules": {
                "historical_claim": "ONLY_HISTORICAL_STAGE_A_YUKAWA_ROWS",
                "newtonian_claim": "MIRROR_NEWTONIAN_COMPANION_ONLY",
                "extension_claim": "PARAMETERIZED_MIRROR_YUKAWA_EXTENSION_ONLY",
                "full_matrix_label": "MUST_SAY_HYBRID_96_CELL_COMPARISON_SCOPE",
                "scope_omission": "BLOCKED_METRIC_OR_CLASSIFICATION_CONTRACT",
            },
            "post_result_change": "FORBIDDEN",
            "favorable_rounding": "FORBIDDEN",
        },
        "mandatory_control_contract": {
            "path_identity_preflight_count": 1,
            "frozen_mutation_control_count": 10,
            "total_mandatory_control_count": 11,
            "rows": controls,
            "all_use_live_record_metric_classifier_or_firewall_path": True,
            "control_records_are_not_part_of_96_scientific_cells": True,
            "any_failure_suppresses_scientific_classification": True,
        },
        "completion_and_precedence_contract": {
            "required_unique_scientific_cells": 96,
            "required_source_count_by_scope": source_counts,
            "required_mandatory_controls": 11,
            "duplicate_cell_behavior": "BLOCKED_INCOMPLETE_RECORD_PRECEDENCE",
            "missing_or_nonfinite_cell_behavior": "PRODUCTION_COMPARISON_TIMEOUT",
            "partial_atomic_cells": "CUSTODY_EVIDENCE_ONLY_NOT_SCIENTIFIC_EVIDENCE",
            "scientific_classification_precondition": "EXACTLY_96_UNIQUE_COMPLETE_FINITE_SOURCE_VALID_CELLS_AND_ALL_11_CONTROLS_PASS_AND_ALL_CUSTODY_GATES_PASS",
            "exclusive_precedence": [
                {"priority": 1, "condition": "CUSTODY_OR_ORACLE_HASH_OR_C00_PATH_IDENTITY_FAILURE", "exclusive_outcome": "BLOCKED_PRODUCTION_PATH_IDENTITY_OR_CUSTODY"},
                {"priority": 2, "condition": "ANY_TIMEOUT_WORK_CAP_MISSING_DUPLICATE_OR_NONFINITE_SCIENTIFIC_CELL", "exclusive_outcome": "PRODUCTION_COMPARISON_TIMEOUT"},
                {"priority": 3, "condition": "ANY_OF_C01_THROUGH_C10_FAILS", "exclusive_outcome": "BLOCKED_PRODUCTION_COMPARISON_CONTROLS"},
                {"priority": 4, "condition": "ALL_PRECONDITIONS_PASS", "exclusive_outcome": "EVALUATE_EXACT_NINE_SCIENTIFIC_LABELS"},
            ],
            "scientific_labels_on_priority_1_2_or_3": "FORBIDDEN_EMPTY_LIST_REQUIRED",
            "completed_subset_classification": "FORBIDDEN",
        },
        "packet_review_outcomes": list(PACKET_REVIEW_OUTCOMES),
        "final_attempt_boundary": {
            "v1_is_last_automatic_comparison_contract_repair": True,
            "automatic_v2_authorized": False,
            "new_foundational_review_block_requires_fresh_selector": True,
        },
        "packet_gates": {
            "gate_count": len(packet_gates),
            "pass_count": len(packet_gates),
            "failure_count": 0,
            "rows": [{"gate_id": gate, "status": "PASS"} for gate in packet_gates],
        },
        "scope": scope,
        "claim_ceiling": (
            "This V1 artifact prepares a comparison contract for independent review only. "
            "It computes no production or oracle energy, executes none of the 96 cells or "
            "eleven controls, adjudicates no cubature, changes no kernel, computes no torque, "
            "DFT, real-150 vector, Jacobian, SVD, or identifiability result, reruns no Stage A "
            "execution, and authorizes no Stage B activity."
        ),
    }


def artifact_bytes() -> bytes:
    return (json.dumps(build_report(), indent=2, sort_keys=True) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Prepare the seven-gate V1 comparison contract.")
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
            print("comparison packet V1 already current")
        return 0
    if current != expected:
        print("comparison packet V1 drift")
        return 1
    report = build_report()
    print(
        "comparison packet V1 OK "
        f"cells={len(report['production_source_and_attribution_contract']['source_rows'])} "
        f"controls={report['mandatory_control_contract']['total_mandatory_control_count']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
