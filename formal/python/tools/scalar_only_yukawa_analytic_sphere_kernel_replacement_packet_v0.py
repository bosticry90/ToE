from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_"
    "REPLACEMENT_PACKET_20260719_v0.json"
)
HUMAN_RELATIVE_PATH = (
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_"
    "REPLACEMENT_PACKET_20260719_v0.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/test_scalar_only_yukawa_analytic_sphere_kernel_"
    "replacement_packet_v0.py"
)
LEAN_RELATIVE_PATH = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "ScalarOnlyYukawaAnalyticSphereKernelReplacementPacketV0.lean"
)
SELECTOR_RELATIVE_PATH = (
    "formal/docs/release/POST_SCALAR_ONLY_YUKAWA_PRODUCTION_CUBATURE_VS_ANALYTIC_"
    "ORACLE_COMPARISON_PACKET_V1_REVIEW_SCIENTIFIC_RESPONSE_SELECTION_20260719_v0.json"
)
ORACLE_REVIEW_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_ORACLE_"
    "QUALIFICATION_EXECUTION_RESULT_REVIEW_20260719_v0.json"
)
ORACLE_EXECUTION_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_ORACLE_"
    "QUALIFICATION_EXECUTION_20260719_v0.json"
)

TARGET = "prepare_scalar_only_yukawa_analytic_sphere_kernel_replacement_packet_v0"
VERDICT = "PREPARED_SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_REPLACEMENT_PACKET_V0"
SELECTED_NEXT_TARGET = (
    "review_scalar_only_yukawa_analytic_sphere_kernel_replacement_packet_v0_result"
)
SELECTED_NEXT_TARGET_KIND = (
    "INDEPENDENT_PRE_IMPLEMENTATION_PACKET_REVIEW_ONLY_NO_KERNEL_IMPLEMENTATION_OR_ADOPTION"
)

SELECTOR_HASHES = {
    "formal/docs/lanes/POST_SCALAR_ONLY_YUKAWA_PRODUCTION_CUBATURE_VS_ANALYTIC_ORACLE_COMPARISON_PACKET_V1_REVIEW_SCIENTIFIC_RESPONSE_SELECTION_20260719_v0.md":
        "d211eb8d91c0d2bc1496afcc052d6bb603d5051aca5ce04ba49a31c7044c557e",
    SELECTOR_RELATIVE_PATH:
        "a6b9aaefcd2b3a3759ab26a991eeed0fed5e4568fc2a8f290b40ec2f9cea4ba7",
    "formal/python/tools/post_scalar_only_yukawa_production_cubature_vs_analytic_oracle_comparison_packet_v1_review_scientific_response_selection_v0.py":
        "c89a2fb88296d7ae4d679dc4a1da098f7b63c63c9767fa05bb513fa7947087b3",
    "formal/python/tests/test_post_scalar_only_yukawa_production_cubature_vs_analytic_oracle_comparison_packet_v1_review_scientific_response_selection_v0.py":
        "cd816808dba420e9d6dbaac66aa0dabae36d6acd69534feb4474e7716558fd69",
    "formal/toe_formal/ToeFormal/Derivation/PostScalarOnlyYukawaProductionCubatureVsAnalyticOracleComparisonPacketV1ReviewScientificResponseSelectionV0.lean":
        "d83f546eeccfdb15313ab6a09681bf678e30189de9a91fac6fe6ffb8753a2c9a",
}

ORACLE_HASHES = {
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_ORACLE_QUALIFICATION_EXECUTION_RESULT_REVIEW_20260719_v0.md":
        "077f3d3e01e3bb4809790bf7d9b9266d7f1a3cd0258af5c697f7880a4b9c3d93",
    ORACLE_REVIEW_RELATIVE_PATH:
        "e963c033514e47e374cb6caced1ab533ed6ea08792f964c04e079e7b67088868",
    "formal/python/tools/scalar_only_yukawa_analytic_sphere_oracle_qualification_execution_result_review_v0.py":
        "49d0f59e9a52777ab1a41bdf448dca58ba14401dab4da84e403c8f6000f4668b",
    "formal/python/tests/test_scalar_only_yukawa_analytic_sphere_oracle_qualification_execution_result_review_v0.py":
        "4bf64e2b0da2b36d038811157008bb846c2ecdfa3b861533b71ac84c6f25dc18",
    "formal/toe_formal/ToeFormal/Derivation/ScalarOnlyYukawaAnalyticSphereOracleQualificationExecutionResultReviewV0.lean":
        "d7b36f5bc4b2cc85d7afb5509ce2a319c83a741531d0a738598a068314d46ce6",
    ORACLE_EXECUTION_RELATIVE_PATH:
        "d2527fd3c03a107734b3b55920c35f73185cbbf0f6c13132ff94c40ec447676d",
    "formal/output/scalar_only_yukawa_analytic_sphere_oracle_qualification_v0/execution_result.json":
        "d2527fd3c03a107734b3b55920c35f73185cbbf0f6c13132ff94c40ec447676d",
    "formal/output/scalar_only_yukawa_analytic_sphere_oracle_qualification_v0/worker_scientific_payload.json":
        "f05b58ba4911e260750615c93a12d71050c08679243b5667c36502bd2d9ad25c",
}

HISTORICAL_INTERFACE_HASHES = {
    "formal/python/tools/scalar_only_yukawa_torsion_balance_production_v1.py":
        "4995c467f766466583c53c7904e2f1bb35b7c02970aece4a20e2315403ed8cac",
    "formal/python/tools/scalar_only_yukawa_deterministic_torsion_balance_forward_model_validation_v1.py":
        "ec0209a433027d8e8523d9e0f21ba3662ccec559de33ea042cb0a765b64571ae",
    "formal/docs/release/SCALAR_ONLY_YUKAWA_DETERMINISTIC_TORSION_BALANCE_FORWARD_MODEL_VALIDATION_EXECUTION_20260719_v1.json":
        "86d9c3a2b93ccf3ec480264522d532e9c3924536459e897fc74bf154abd64a13",
}

PACKET_REVIEW_OUTCOMES = (
    "ANALYTIC_KERNEL_REPLACEMENT_CONTRACT_READY",
    "BLOCKED_REPLACEMENT_INTERFACE_IDENTITY",
    "BLOCKED_REPLACEMENT_DOMAIN_COVERAGE",
    "BLOCKED_REPLACEMENT_VALIDATION_INDEPENDENCE",
    "BLOCKED_REPLACEMENT_FIREWALL",
)

REQUIRED_CASE_IDS = (
    "LEGACY_STAGE_A_00_LARGE_X",
    "LEGACY_STAGE_A_01_TRANSITION",
    "LEGACY_STAGE_A_02_LONG_RANGE",
    "SMALL_X_UNEQUAL_WIDE",
    "MIXED_X_UNEQUAL",
    "SMALL_GAP_LARGE_X",
    "EXTREME_X_1000_UNEQUAL",
    "LONG_RANGE_UNEQUAL_WIDE",
)

MUTATION_IDS = (
    "M01_GAP_SUBSTITUTED_FOR_CENTER_DISTANCE",
    "M02_MISSING_SECOND_SPHERE_FACTOR",
    "M03_MISSING_A_Y_ONE_THIRD",
    "M04_REVERSED_ATTRACTIVE_SIGN",
    "M05_WRONG_RADIAL_DERIVATIVE_SIGN",
    "M06_DIRECT_LARGE_X_HYPERBOLIC_OVERFLOW",
    "M07_DIRECT_SMALL_X_CANCELLATION",
    "M08_TOUCHING_OR_OVERLAPPING_INPUT_ACCEPTED",
    "M09_NONPOSITIVE_YUKAWA_RANGE_ACCEPTED",
    "M10_X_ABOVE_QUALIFIED_MAXIMUM_ACCEPTED",
    "M11_OUTPUT_SHAPE_OR_DTYPE_CHANGED",
    "M12_REFERENCE_HELPER_SHARED_WITH_CANDIDATE",
)


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _artifact_row(relative_path: str) -> dict[str, str]:
    return {"relative_path": relative_path, "sha256": _sha256(REPO_ROOT / relative_path)}


def _load_json(relative_path: str) -> dict[str, Any]:
    value = json.loads((REPO_ROOT / relative_path).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {relative_path}")
    return value


def _verify_hashes(rows: dict[str, str], label: str) -> None:
    for relative_path, expected in rows.items():
        path = REPO_ROOT / relative_path
        if not path.exists() or _sha256(path) != expected:
            raise ValueError(f"{label} drift: {relative_path}")


def _frozen_regression_rows(execution: dict[str, Any]) -> list[dict[str, Any]]:
    rows = execution["scientific_payload"]["radial_cross_check_gate"]["case_rows"]
    if [row["case_id"] for row in rows] != list(REQUIRED_CASE_IDS):
        raise ValueError("accepted oracle case order or identity drift")
    return [
        {
            "case_id": row["case_id"],
            "newtonian_reference_J_decimal": row["newtonian_analytic_J"],
            "yukawa_reference_J_decimal": row["yukawa_radial_reference_J"],
            "accepted_binary64_yukawa_J": row["yukawa_analytic_stable_J"],
            "accepted_regime_1": row["analytic_regime_1"],
            "accepted_regime_2": row["analytic_regime_2"],
            "reference_precision_decimal_digits": row["radial_precision_digits"],
        }
        for row in rows
    ]


def build_report() -> dict[str, Any]:
    _verify_hashes(SELECTOR_HASHES, "selector authority")
    _verify_hashes(ORACLE_HASHES, "accepted oracle")
    _verify_hashes(HISTORICAL_INTERFACE_HASHES, "historical interface")

    selector = _load_json(SELECTOR_RELATIVE_PATH)
    if selector.get("verdict") != "SELECTED_ANALYTIC_SPHERE_KERNEL_REPLACEMENT_PACKET_PREPARATION":
        raise ValueError("selector verdict mismatch")
    if selector.get("selected_next_target") != TARGET:
        raise ValueError("selector did not authorize this packet")
    if selector.get("selected_route") != (
        "RETIRE_OLD_CUBATURE_COMPARISON_AND_PREPARE_ANALYTIC_KERNEL_REPLACEMENT"
    ):
        raise ValueError("selector route mismatch")
    if selector.get("scope", {}).get("production_kernel_replacement_performed") is not False:
        raise ValueError("selector unexpectedly replaced the production kernel")

    oracle_review = _load_json(ORACLE_REVIEW_RELATIVE_PATH)
    oracle_execution = _load_json(ORACLE_EXECUTION_RELATIVE_PATH)
    if oracle_review.get("verdict") != "ACCEPTED_ANALYTIC_SPHERE_ORACLE_QUALIFIED":
        raise ValueError("accepted oracle review verdict mismatch")
    if oracle_execution.get("principal_result") != "ANALYTIC_SPHERE_ORACLE_QUALIFIED":
        raise ValueError("accepted oracle execution result mismatch")
    regressions = _frozen_regression_rows(oracle_execution)

    phases = [
        {
            "phase_id": "P0_PRE_IMPLEMENTATION_CONTRACT",
            "status_now": "PREPARED_PENDING_INDEPENDENT_REVIEW",
            "authorized_now": True,
            "may_change_production_code": False,
        },
        {
            "phase_id": "P1_SHADOW_IMPLEMENTATION_AND_QUALIFICATION",
            "status_now": "NOT_AUTHORIZED",
            "authorized_now": False,
            "may_change_production_code": False,
        },
        {
            "phase_id": "P2_INDEPENDENT_QUALIFICATION_RESULT_REVIEW",
            "status_now": "NOT_AUTHORIZED",
            "authorized_now": False,
            "may_change_production_code": False,
        },
        {
            "phase_id": "P3_FRESH_PRODUCTION_ADOPTION_SELECTOR_AND_PACKET",
            "status_now": "NOT_AUTHORIZED",
            "authorized_now": False,
            "may_change_production_code": False,
        },
        {
            "phase_id": "P4_VERSIONED_ADOPTION_WITH_ROLLBACK",
            "status_now": "NOT_AUTHORIZED",
            "authorized_now": False,
            "may_change_production_code": True,
        },
    ]

    packet_gates = (
        "EXACT_SELECTOR_AUTHORITY_AND_ROUTE",
        "ACCEPTED_ORACLE_REVIEW_AND_EXECUTION_HASH_FROZEN",
        "HISTORICAL_STAGE_A_INTERFACE_HASH_FROZEN",
        "OLD_COMPARISON_RETIRED_WITHOUT_CUBATURE_ADJUDICATION",
        "LIVE_ENERGY_ENTRYPOINT_DISTINGUISHED_FROM_CUBATURE_HELPER",
        "PRE_IMPLEMENTATION_ONLY_NO_SOURCE_CHANGE",
        "NEWTONIAN_FORMULA_AND_DERIVATIVE_FROZEN",
        "YUKAWA_FORMULA_TWO_FACTORS_AND_A_Y_FROZEN",
        "CENTER_DISTANCE_AND_SURFACE_GAP_SEMANTICS_FROZEN",
        "SI_UNITS_ATTRACTIVE_SIGN_AND_COMPONENT_SUM_FROZEN",
        "EQUAL_AND_UNEQUAL_RADIUS_HANDLING_FROZEN",
        "POINT_PARTICLE_COMPATIBILITY_LIMIT_FROZEN",
        "STRICT_NONOVERLAP_AND_MACHINE_RESOLVABLE_GAP_FROZEN",
        "POSITIVE_RANGE_REQUIRED_FOR_YUKAWA_OR_TOTAL",
        "NEWTONIAN_ZERO_RANGE_SENTINEL_COMPATIBILITY_ISOLATED",
        "FINITE_MASS_RADIUS_DISTANCE_AND_AMPLITUDE_GUARDS_FROZEN",
        "QUALIFIED_X_DOMAIN_ZERO_THROUGH_ONE_THOUSAND_FROZEN",
        "SMALL_MODERATE_AND_LARGE_X_REGIMES_FROZEN",
        "SCALED_SURFACE_GAP_IDENTITY_FROZEN",
        "NO_DIRECT_LARGE_X_HYPERBOLIC_EVALUATION",
        "NO_SILENT_UNDERFLOW_OR_OVERFLOW",
        "NEAR_CONTACT_LIMIT_AND_TOUCHING_REJECTION_FROZEN",
        "LARGE_SEPARATION_LIMIT_AND_UNDERFLOW_FAILURE_FROZEN",
        "LONG_RANGE_POINT_KERNEL_LIMIT_FROZEN",
        "SMALL_COUPLING_LINEARITY_AND_ZERO_LIMIT_FROZEN",
        "EXISTING_CALLER_ARGUMENT_SCHEMA_FROZEN",
        "OUTPUT_SHAPE_DTYPE_COMPONENT_AND_DERIVATIVE_SCHEMA_FROZEN",
        "VALIDATION_ONLY_MUTATION_HOOKS_SEPARATED_FROM_PRODUCTION",
        "EIGHT_ACCEPTED_REGRESSION_ROWS_COPIED_WITHOUT_RECOMPUTATION",
        "SIX_ACCEPTED_OVERLAP_PROBES_AND_TOLERANCES_FROZEN",
        "X_ONE_THOUSAND_NO_OVERFLOW_TEST_REQUIRED",
        "EXCHANGE_SYMMETRY_AND_EQUAL_UNEQUAL_CASES_REQUIRED",
        "INDEPENDENT_RADIAL_REFERENCE_CUSTODY_REQUIRED",
        "CANDIDATE_MAY_NOT_IMPORT_OR_CALL_ORACLE_EVALUATOR",
        "CANDIDATE_MAY_NOT_IMPORT_OR_CALL_OLD_CUBATURE",
        "TWELVE_LIVE_PATH_MUTATIONS_FROZEN",
        "DETERMINISTIC_SERIALIZATION_AND_KERNEL_ID_REQUIRED",
        "QUALIFICATION_RUNTIME_AND_MEMORY_BOUNDS_FROZEN",
        "PROCESS_GROUP_AND_ATOMIC_EVIDENCE_CUSTODY_FROZEN",
        "ISOLATED_SHADOW_MODULE_REQUIRED_BEFORE_ADOPTION",
        "NO_IN_PLACE_HISTORICAL_SOURCE_OVERWRITE",
        "PRODUCTION_ADOPTION_REQUIRES_FRESH_SELECTOR_AND_PACKET",
        "ROLLBACK_IS_OPERATIONAL_NOT_SCIENTIFIC_VALIDATION",
        "NO_MIXING_OUTPUTS_ACROSS_KERNEL_IDENTITIES",
        "TORQUE_AND_DFT_REMAIN_SEPARATE_VALIDATION_BURDENS",
        "NO_REAL_150_VECTOR_JACOBIAN_SVD_OR_IDENTIFIABILITY",
        "NO_STAGE_A_RERUN_OR_STAGE_B",
        "FIVE_PACKET_REVIEW_OUTCOMES_EXACT",
        "PACKET_FAILURE_REQUIRES_FRESH_SELECTOR_NO_AUTOMATIC_REPAIR",
        "CURRENT_AUTHORITY_ROTATES_ONLY_TO_INDEPENDENT_PACKET_REVIEW",
    )

    scope = {
        "replacement_packet_prepared": True,
        "selector_authority_consumed": True,
        "accepted_oracle_custody_frozen": True,
        "historical_interface_inspected_read_only": True,
        "independent_packet_review_authorized": True,
        "shadow_candidate_module_created": False,
        "analytic_kernel_implemented": False,
        "analytic_kernel_executed": False,
        "production_dispatch_changed": False,
        "production_kernel_replaced": False,
        "old_cubature_called": False,
        "old_cubature_adjudicated": False,
        "comparison_v2_authorized": False,
        "torque_or_dft_authorized": False,
        "real_150_vector_authorized": False,
        "jacobian_svd_or_identifiability_authorized": False,
        "stage_a_rerun_authorized": False,
        "stage_b_authorized": False,
        "automatic_packet_repair_authorized": False,
    }

    return {
        "schema_id": "toe.scalar_only_yukawa.analytic_sphere_kernel.replacement_packet.v0",
        "packet_id": "SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_REPLACEMENT_PACKET_20260719_v0",
        "captured_at_utc": "2026-07-19T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "status": "PREPARED_PENDING_INDEPENDENT_REVIEW_NO_IMPLEMENTATION",
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "authority": {
            "consumed_selector_verdict": selector["verdict"],
            "consumed_selector_route": selector["selected_route"],
            "frozen_selector_artifacts": [
                {"relative_path": path, "sha256": digest}
                for path, digest in SELECTOR_HASHES.items()
            ],
            "frozen_accepted_oracle_artifacts": [
                {"relative_path": path, "sha256": digest}
                for path, digest in ORACLE_HASHES.items()
            ],
            "frozen_historical_interface_artifacts": [
                {"relative_path": path, "sha256": digest}
                for path, digest in HISTORICAL_INTERFACE_HASHES.items()
            ],
            "human_packet": _artifact_row(HUMAN_RELATIVE_PATH),
            "generator": _artifact_row(
                "formal/python/tools/scalar_only_yukawa_analytic_sphere_kernel_"
                "replacement_packet_v0.py"
            ),
            "test": _artifact_row(TEST_RELATIVE_PATH),
            "lean": _artifact_row(LEAN_RELATIVE_PATH),
        },
        "controlling_state": {
            "analytic_sphere_oracle": "QUALIFIED_AND_ACCEPTED",
            "old_cubature_comparison_path": "RETIRED_FROM_AUTOMATIC_REPAIR",
            "old_cubature_scientific_status": "UNADJUDICATED_NEITHER_VALIDATED_NOR_INVALIDATED",
            "kernel_replacement": "NOT_IMPLEMENTED_NOT_AUTHORIZED",
            "stage_a": "BLOCKED_PRODUCTION_KERNEL_VALIDATION_NOT_REOPENED",
            "stage_b": "NOT_AUTHORIZED",
        },
        "historical_path_identity": {
            "live_stage_a_energy_entrypoint": "pair_energy_and_radial_derivative",
            "live_entrypoint_source": "formal/python/tools/scalar_only_yukawa_torsion_balance_production_v1.py",
            "fixed_tensor_cubature_helper": "reduced_four_dimensional_density_integral_yukawa_energy",
            "paths_are_distinct": True,
            "live_entrypoint_already_contains_a_related_form_factor_implementation": True,
            "packet_interpretation": (
                "A future replacement is a versioned oracle-qualified hardening of the "
                "sphere energy evaluator and its validation basis; it is not evidence that "
                "the cubature helper was the live production energy path."
            ),
            "old_cubature_source_disposition": "READ_ONLY_HISTORICAL_NOT_CALLED_OR_ADJUDICATED",
        },
        "analytic_kernel_contract": {
            "scope": "NONOVERLAPPING_HOMOGENEOUS_SPHERE_PAIR_ENERGY_AND_DU_DD_ONLY",
            "mass_if_derived_from_density": "M_i=(4*pi/3)*rho_i*R_i^3",
            "center_distance": "D",
            "surface_gap": "g=D-R1-R2",
            "dimensionless_radii": "x_i=R_i/lambda",
            "newtonian_energy": "U_N=-G*M1*M2/D",
            "newtonian_radial_derivative": "dU_N/dD=G*M1*M2/D^2",
            "sphere_form_factor": "F(x)=3*(x*cosh(x)-sinh(x))/x^3",
            "yukawa_amplitude_production_exact": "1/3",
            "yukawa_energy": (
                "U_Y=-A_Y*G*M1*M2*F(x1)*F(x2)*exp(-D/lambda)/D"
            ),
            "yukawa_radial_derivative": (
                "dU_Y/dD=A_Y*G*M1*M2*F(x1)*F(x2)*exp(-D/lambda)*"
                "(1/D^2+1/(lambda*D))"
            ),
            "scaled_factor": "H(x)=exp(-x)*F(x)",
            "stable_pair_identity": (
                "F(x1)*F(x2)*exp(-D/lambda)=H(x1)*H(x2)*exp(-g/lambda)"
            ),
            "total_energy": "U_TOTAL=U_N+U_Y",
            "total_radial_derivative": "dU_TOTAL/dD=dU_N/dD+dU_Y/dD",
            "units": {"input_lengths": "m", "input_masses": "kg", "energy": "J", "radial_derivative": "J/m=N"},
            "signs_for_positive_A_Y": {"U_N": "NEGATIVE", "U_Y": "NEGATIVE", "dU_N_dD": "POSITIVE", "dU_Y_dD": "POSITIVE"},
            "sphere_exchange_symmetry_required": True,
            "equal_and_unequal_radii_supported": True,
        },
        "numerical_evaluator_contract": {
            "H_at_zero_exact": 1.0,
            "small_x": {
                "domain": "0<=x<=0.1",
                "formula": "H=exp(-x)*(1+x^2/10+x^4/280+x^6/15120+x^8/1330560)",
            },
            "moderate_x": {
                "domain": "0.1<x<=40",
                "formula": "H=exp(-x)*3*(x*cosh(x)-sinh(x))/x^3",
            },
            "large_x": {
                "domain": "40<x<=1000",
                "formula": "H=3*((x-1)+(x+1)*exp(-2*x))/(2*x^3)",
                "direct_sinh_or_cosh_forbidden": True,
            },
            "qualified_x_interval": "0<=x<=1000",
            "x_above_1000": "REJECT_OUTSIDE_NUMERICALLY_QUALIFIED_DOMAIN",
            "pair_evaluation": "USE_EXP_MINUS_G_OVER_LAMBDA_TIMES_H1_TIMES_H2",
            "log_abs_energy_preflight_required": True,
            "silent_overflow_or_underflow": "FORBIDDEN",
            "unrepresentable_nonzero_output": "RAISE_FLOATING_POINT_ERROR_WITH_LOG_ABS_VALUE",
            "regime_boundaries_post_result_change": "FORBIDDEN",
            "overlap_probes": [
                {"overlap_id": "SMALL_DIRECT", "x_values": [0.05, 0.1, 0.2], "absolute_tolerance_H": 5e-14, "relative_tolerance_H": 5e-11},
                {"overlap_id": "DIRECT_SCALED", "x_values": [20.0, 32.0, 40.0], "absolute_tolerance_H": 5e-15, "relative_tolerance_H": 5e-13},
            ],
        },
        "domain_and_limit_contract": {
            "finite_required": ["D", "R1", "R2", "M1", "M2", "lambda", "A_Y"],
            "production_physical_domain": "D>R1+R2; R1>=0; R2>=0; M1>0; M2>0; lambda>0; A_Y=1/3",
            "machine_resolvable_gap_rule": "g=fsum(D,-R1,-R2)>=16*ulp(max(D,R1+R2))",
            "positive_but_unresolvable_gap": "REJECT_UNRESOLVED_NONOVERLAP",
            "touching_or_overlap": "REJECT",
            "negative_radius_mass_or_amplitude": "REJECT",
            "point_particle_compatibility": "R_i=0_IS_ALLOWED_WITH_H(0)=1_AND_EXPLICIT_MASS",
            "newtonian_lambda_zero_compatibility": (
                "ONLY_COMPONENT_NEWTONIAN_MAY_USE_THE_HISTORICAL_LAMBDA_ZERO_SENTINEL; "
                "THE_YUKAWA_CORE_IS_NOT_CALLED"
            ),
            "nonpositive_lambda_for_yukawa_or_total": "REJECT",
            "near_contact_limit": "AS_g_TO_0_PLUS_PAIR_FACTOR_TENDS_TO_H1*H2_AND_REMAINS_FINITE",
            "large_separation_limit": "AS_D_TO_INFINITY_U_Y_TENDS_TO_ZERO_FROM_BELOW_AND_DU_DD_TENDS_TO_ZERO_FROM_ABOVE",
            "long_range_limit": "AS_lambda_TO_INFINITY_F_TO_ONE_AND_U_Y_TENDS_TO_MINUS_A_Y_G_M1_M2_OVER_D",
            "point_particle_limit": "AS_R1_R2_TO_ZERO_U_Y_TENDS_TO_MINUS_A_Y_G_M1_M2_EXP_MINUS_D_OVER_LAMBDA_OVER_D",
            "small_coupling_limit": "U_Y_AND_DU_Y_DD_ARE_LINEAR_IN_A_Y_AND_EQUAL_EXACT_ZERO_AT_A_Y_ZERO",
            "production_amplitude_variation": "FORBIDDEN_FIXED_ONE_THIRD; NONDEFAULT_VALUES_ARE_VALIDATION_CONTROLS_ONLY",
        },
        "caller_interface_contract": {
            "public_compatibility_entrypoint": "pair_energy_and_radial_derivative",
            "distance_argument": "distance_m: scalar_or_numpy_float64_array",
            "lambda_argument": "lambda_m: scalar_float",
            "keyword_arguments_in_order": [
                "mass_d_kg", "mass_a_kg", "radius_d_m", "radius_a_m",
                "yukawa_amplitude", "component", "yukawa_sign", "remove_attractor_form_factor",
            ],
            "components": ["newtonian", "yukawa", "total"],
            "production_defaults": {"yukawa_amplitude": "1/3", "yukawa_sign": 1.0, "remove_attractor_form_factor": False},
            "mutation_only_arguments": ["yukawa_sign", "remove_attractor_form_factor", "nondefault_yukawa_amplitude"],
            "return_schema": "tuple(numpy_float64_array_energy_J,numpy_float64_array_dU_dD_J_per_m)",
            "return_shape": "EXACTLY_MATCH_NP_ASARRAY_DISTANCE_M_SHAPE_INCLUDING_ZERO_DIMENSIONAL_SCALAR_ARRAY",
            "component_total_order": "COMPUTE_COMPONENTS_SEPARATELY_THEN_NEWTONIAN_PLUS_YUKAWA",
            "broadcasting": "DISTANCE_ONLY; MASSES_RADII_LAMBDA_AND_AMPLITUDE_ARE_SCALARS",
            "exception_types": {
                "domain": "ValueError",
                "numeric_overflow_or_underflow": "FloatingPointError",
                "unknown_component": "ValueError",
            },
            "torque_or_angular_semantics": "NOT_PART_OF_THIS_INTERFACE_QUALIFICATION",
        },
        "accepted_oracle_regression_contract": {
            "case_count": len(regressions),
            "case_order": list(REQUIRED_CASE_IDS),
            "rows": regressions,
            "reference_values_copied_not_recomputed_during_packet_preparation": True,
            "newtonian_tolerance": "abs(delta)<=1e-38 J+5e-12*abs(reference)",
            "yukawa_tolerance": "abs(delta)<=1e-38 J+5e-12*abs(reference)",
            "accepted_binary64_values_are_custody_witnesses_not_the_independent_reference": True,
            "candidate_result_bitwise_identity_required": False,
            "all_eight_cases_required": True,
            "missing_case_or_nonfinite_result": "FAIL_CLOSED",
        },
        "validation_independence_contract": {
            "candidate_shadow_module_future_path": (
                "formal/python/tools/scalar_only_yukawa_analytic_sphere_kernel_candidate_v0.py"
            ),
            "candidate_may_import_accepted_oracle_evaluator": False,
            "candidate_may_import_old_cubature_helper": False,
            "candidate_may_call_old_cubature": False,
            "reference_source": "FROZEN_120_DIGIT_RADIAL_VALUES_IN_ACCEPTED_EXECUTION_ARTIFACT",
            "reference_parser_may_not_compute_form_factor": True,
            "validation_required": [
                "ALL_EIGHT_NEWTONIAN_AND_YUKAWA_REGRESSIONS",
                "ALL_SIX_EVALUATOR_OVERLAP_PROBES",
                "POINT_PARTICLE_AND_LONG_RANGE_LIMITS",
                "SPHERE_EXCHANGE_SYMMETRY",
                "EQUAL_AND_UNEQUAL_RADIUS_CASES",
                "MACHINE_RESOLVABLE_NEAR_CONTACT_CASE_AND_TOUCHING_REJECTION",
                "X_1000_NO_OVERFLOW",
                "SMALL_COUPLING_EXACT_ZERO_AND_LINEARITY",
                "OUTPUT_SHAPE_DTYPE_AND_COMPONENT_ROUTING",
                "ALL_DOMAIN_GUARDS_AND_EXCEPTION_TYPES",
                "NO_ORACLE_OR_CUBATURE_IMPORT",
                "DETERMINISTIC_SERIALIZATION_AND_RUNTIME",
            ],
            "validation_mutations": [
                {"mutation_id": mutation_id, "required_result": "DETECTED_BY_LIVE_CANDIDATE_AND_ADJUDICATOR"}
                for mutation_id in MUTATION_IDS
            ],
            "metadata_only_mutation_detection": "FORBIDDEN",
        },
        "future_shadow_qualification_contract": {
            "authorized_by_this_preparation": False,
            "authorization_if_packet_review_ready": (
                "ONE_ISOLATED_SHADOW_IMPLEMENTATION_AND_QUALIFICATION_EXECUTION_ONLY"
            ),
            "production_import_or_dispatch_change": "FORBIDDEN",
            "total_wall_clock_seconds_max": 300,
            "memory_mib_max": 1024,
            "stage_rows": [
                {"stage_id": "K1_CUSTODY_AND_SOURCE_INDEPENDENCE", "seconds_max": 30},
                {"stage_id": "K2_INTERFACE_AND_DOMAIN_GUARDS", "seconds_max": 60},
                {"stage_id": "K3_ORACLE_REGRESSION_AND_LIMITS", "seconds_max": 90},
                {"stage_id": "K4_MUTATIONS_SERIALIZATION_AND_RUNTIME", "seconds_max": 90},
                {"stage_id": "K5_ATOMIC_FINALIZATION", "seconds_max": 30},
            ],
            "deterministic_runtime_probe": "TEN_THOUSAND_FIXED_SCALAR_PAIR_EVALUATIONS_AFTER_ONE_WARMUP",
            "runtime_probe_seconds_max": 5.0,
            "runtime_trials": 5,
            "runtime_adjudicator": "MEDIAN_OF_FIVE_WITH_NO_PARALLELISM",
            "process_group_termination": "MANDATORY",
            "raw_launcher_transcript": "PRESERVED",
            "stage_atomic_status": "REQUIRED",
            "zero_surviving_processes": "MANDATORY",
            "terminal_outcomes": [
                "ANALYTIC_SPHERE_KERNEL_SHADOW_QUALIFIED",
                "BLOCKED_KERNEL_INTERFACE_PARITY",
                "BLOCKED_KERNEL_DOMAIN_OR_NUMERIC_STABILITY",
                "BLOCKED_KERNEL_ORACLE_REGRESSION",
                "BLOCKED_KERNEL_VALIDATION_INDEPENDENCE",
                "BLOCKED_KERNEL_RUNTIME_OR_CUSTODY",
            ],
        },
        "implementation_adoption_and_rollback_contract": {
            "phase_rows": phases,
            "historical_source_in_place_edit_during_shadow_qualification": "FORBIDDEN",
            "production_adoption_preconditions": [
                "ANALYTIC_SPHERE_KERNEL_SHADOW_QUALIFIED",
                "INDEPENDENT_QUALIFICATION_RESULT_REVIEW_ACCEPTED",
                "FRESH_PRODUCTION_ADOPTION_SELECTOR_SELECTED",
                "SEPARATE_VERSIONED_ADOPTION_PACKET_ACCEPTED",
                "EXPLICIT_DISPATCH_SEAM_AND_KERNEL_ID_FROZEN",
                "ROLLBACK_DRILL_PASSED_BEFORE_SCIENTIFIC_EXECUTION",
            ],
            "adoption_may_not_be_inferred_from_shadow_qualification": True,
            "old_source_retention": "HASH_PINNED_READ_ONLY_ROLLBACK_TARGET",
            "rollback_mechanism": "RESTORE_EXPLICIT_DISPATCH_TO_HASH_PINNED_HISTORICAL_ENTRYPOINT",
            "rollback_result": (
                "OPERATIONAL_RESTORATION_ONLY; STAGE_A_REMAINS_BLOCKED_AND_OLD_CUBATURE_REMAINS_UNADJUDICATED"
            ),
            "mixed_kernel_outputs_in_one_scientific_record": "FORBIDDEN",
            "every_future_output_must_record": ["kernel_id", "kernel_source_sha256", "oracle_reference_sha256"],
            "automatic_fallback_after_candidate_failure": "FORBIDDEN",
        },
        "separation_of_obligations": {
            "analytic_derivation": "ALREADY_ACCEPTED_ORACLE_EVIDENCE_HASH_FROZEN_NOT_REDERIVED_OR_CHANGED_HERE",
            "numerical_implementation": "FUTURE_ISOLATED_SHADOW_CANDIDATE_NOT_CREATED_HERE",
            "production_adoption": "FUTURE_SEPARATE_SELECTOR_AND_PACKET_NOT_AUTHORIZED_HERE",
            "torque_and_dft": "FUTURE_SEPARATE_VALIDATION_AFTER_ANY_ACCEPTED_ADOPTION",
            "stage_a_rerun": "FUTURE_FRESH_AUTHORITY_ONLY_AFTER_KERNEL_TORQUE_AND_DFT_VALIDATION",
        },
        "packet_review_outcomes": list(PACKET_REVIEW_OUTCOMES),
        "review_consequence": {
            "ready_outcome": "MAY_AUTHORIZE_ONE_ISOLATED_SHADOW_IMPLEMENTATION_AND_QUALIFICATION_ONLY",
            "blocked_outcome": "FRESH_SCIENTIFIC_RESPONSE_SELECTOR_REQUIRED",
            "automatic_packet_v1_or_comparison_v2": "PROHIBITED",
            "production_adoption_on_ready_review": "NOT_AUTHORIZED",
        },
        "packet_gates": {
            "gate_count": len(packet_gates),
            "pass_count": len(packet_gates),
            "failure_count": 0,
            "rows": [{"gate_id": gate, "status": "PASS"} for gate in packet_gates],
        },
        "scope": scope,
        "claim_ceiling": (
            "This packet freezes a pre-implementation analytic sphere-kernel replacement "
            "contract for independent review. It copies accepted oracle evidence without "
            "recalculation, creates or executes no candidate kernel, calls or adjudicates no "
            "old cubature, changes no production dispatch, computes no torque, DFT, real-150 "
            "vector, Jacobian, SVD, identifiability result, or Stage B forecast, and does not "
            "authorize a Stage A rerun or production adoption."
        ),
    }


def artifact_bytes() -> bytes:
    return (json.dumps(build_report(), indent=2, sort_keys=True) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Prepare the analytic sphere-kernel replacement contract V0."
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
            print("analytic sphere-kernel replacement packet already current")
        return 0
    if current != expected:
        print("analytic sphere-kernel replacement packet drift")
        return 1
    report = build_report()
    print(
        "analytic sphere-kernel replacement packet OK "
        f"cases={report['accepted_oracle_regression_contract']['case_count']} "
        f"gates={report['packet_gates']['pass_count']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
