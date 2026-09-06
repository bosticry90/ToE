"""Frozen C03/RV v1 roots and cumulative challenge policy.

This module contains contracts only.  It imports no historical runner or
candidate implementation, and therefore cannot manufacture scientific values.
"""
from __future__ import annotations

from typing import Any, Mapping, Sequence

from .challenges import ChallengeSpecV1, validate_registry
from .contracts import AlgebraicFieldV1, DimensionSystemV1, PhysicsProfileV1, QMCPolicyV1, VerificationPolicyV1
from .c03_rv_operation_contracts import C03_RV_PHYSICS_OPERATIONS, DERIVED_SIGNATURES, SOURCE_SIGNATURES
from .milestones import C03_RV_ROOTS


FREEZE_TIMESTAMP = "2026-09-05T23:59:59Z"
ACCEPTED_HISTORICAL_FALSIFIER_IDS = (
    "ALL_DERIVED_INTERMEDIATE_CORRUPTION",
    "SOURCE_LOCATOR_MUST_RESOLVE",
    "UNKNOWN_OPERATION_FAILS_CLOSED",
    "PARENT_BYPASS_REJECTED",
    "STALE_EDGE_REJECTED",
    "OUTPUT_BINDING_CORRUPTION_REJECTED",
    "RV03_PHASE_SENSITIVITY",
    "C03_N7_SOURCE_BOUNDARY",
    "C03_N8_SOURCE_BOUNDARY",
    "EVALUATED_ZERO_IS_NOT_UNEVALUATED",
)


def _spec(identity: str, target: Mapping[str, Any], mutation: Mapping[str, Any], invariant: str, origin: str) -> ChallengeSpecV1:
    return ChallengeSpecV1(
        identity, target, mutation, invariant, "VERIFIER_REJECTS", {"roots": "ANCESTRY"},
        "FROZEN_BASELINE_DESCENDANTS_ONLY", {"kind": "DERIVED_FROM_BASELINE"}, origin,
        "2026-09-05T00:00:00Z", True,
    )


def mandatory_challenge_specs() -> tuple[ChallengeSpecV1, ...]:
    return (
        _spec("ALL_DERIVED_INTERMEDIATE_CORRUPTION", {"kind": "DERIVED"}, {"kind": "PERTURB_EXACT_VALUE_BY_ONE"}, "Every derived value is independently recomputed", "C03 complete intermediate-corruption controls and subsequent fine-profile expansion"),
        _spec("SOURCE_LOCATOR_MUST_RESOLVE", {"operation": "SOURCE_DECODE"}, {"kind": "CORRUPT_SOURCE_LOCATOR"}, "Typed source references resolve an actual hash-bound value", "Pass-0281 and post-audit nonexistent-locator failures"),
        _spec("UNKNOWN_OPERATION_FAILS_CLOSED", {"kind": "DERIVED"}, {"kind": "REPLACE_OPERATION", "operation": "UNDECLARED_TARGET_LOOKUP"}, "Unknown operations cannot reach verified status", "Pass-0281 unknown-operation falsifier"),
        _spec("PARENT_BYPASS_REJECTED", {"node_id": "C03.DERIVED.COMMON_NORMALIZED_COEFFICIENT"}, {"kind": "BYPASS_FIRST_PARENT"}, "Output ancestry cannot bypass an authorized transformation", "C03 parent-bypass controls"),
        _spec("STALE_EDGE_REJECTED", {"node_id": "C03.DERIVED.COMMON_NORMALIZED_COEFFICIENT"}, {"kind": "REMOVE_FIRST_PARENT_STALE_EDGE"}, "Parent lists and edge lists must be identical", "C03 stale-edge controls"),
        _spec("OUTPUT_BINDING_CORRUPTION_REJECTED", {"kind": "OUTPUT"}, {"kind": "PERTURB_OUTPUT_ONLY"}, "Emitted roots equal verified root-node values", "RV output-binding and C03 emitted-output controls"),
        _spec("RV03_PHASE_SENSITIVITY", {"node_id": "RV03.PHASE"}, {"kind": "PERTURB_EXACT_VALUE_BY_ONE"}, "RV03 remains sensitive to its phase ancestry", "RV03 phase-sensitivity control"),
        _spec("C03_N7_SOURCE_BOUNDARY", {"node_id": "C03.NATIVE.RELATIONS"}, {"kind": "PERTURB_EXACT_VALUE_BY_ONE"}, "N7 relation data remain source-bound and active", "Post-Pass-0281 N7 boundary control"),
        _spec("C03_N8_SOURCE_BOUNDARY", {"node_id": "C03.NATIVE.QUOTIENT"}, {"kind": "PERTURB_EXACT_VALUE_BY_ONE"}, "N8 quotient projection remains source-bound and active", "Post-Pass-0281 N8 boundary control"),
        _spec("EVALUATED_ZERO_IS_NOT_UNEVALUATED", {"node_id": "RV06.STATE"}, {"kind": "REPLACE_OPERATION", "operation": "UNDECLARED_UNEVALUATED_STATE"}, "Evaluated-zero evidence cannot be replaced by an unevaluated label", "Explicit evaluated-zero semantic controls"),
    )


def challenge_registry_census() -> dict[str, Any]:
    specs = mandatory_challenge_specs()
    return validate_registry(specs, FREEZE_TIMESTAMP, ACCEPTED_HISTORICAL_FALSIFIER_IDS)


def physics_profile(source_declarations: Sequence[Mapping[str, Any]]) -> PhysicsProfileV1:
    algebraic_field = AlgebraicFieldV1(
        "SQRT2_SQRT3_I_COMMON_FIELD", "alpha",
        ("144", "0", "192", "0", "88", "0", "-16", "0", "1"),
        {"kind": "COMPLEX_RECTANGLE", "real_lower": "3", "real_upper": "4", "imag_lower": "1/2", "imag_upper": "3/2"},
        ("1", "alpha", "alpha^2", "alpha^3", "alpha^4", "alpha^5", "alpha^6", "alpha^7"),
    )
    semantic_types = tuple(sorted(set(SOURCE_SIGNATURES.values()) | {row["semantic_type"] for row in DERIVED_SIGNATURES.values()}))
    return PhysicsProfileV1(
        "C03_RV_SU5_EXACT_PROFILE_v1",
        # ``d`` remains symbolic in the admitted BMHV/native-E coordinate
        # vector.  It is part of the exact language, not an implicit runtime
        # symbol supplied by SymPy.
        ("C_duue", "d", "g1", "g2", "g3", "xi1", "xi2", "xi3"),
        algebraic_field,
        DimensionSystemV1(("MASS", "LENGTH", "TIME"), "RATIONAL", (("1", "1", "0"), ("1", "0", "1"))),
        ("SU5_NATURAL_HBAR_C_1",),
        semantic_types,
        {"NATIVE_E": 14},
        ("SU5", "BMHV", "WARSAW", "NATIVE_E"),
        tuple(dict(row) for row in source_declarations),
        tuple(sorted({"SOURCE_DECODE", *C03_RV_PHYSICS_OPERATIONS})),
        C03_RV_ROOTS,
        {root: root.replace(".OUTPUT.", ".claim.") for root in C03_RV_ROOTS},
    )


def verification_policy() -> VerificationPolicyV1:
    specs = mandatory_challenge_specs()
    return VerificationPolicyV1(
        "C03_RV_VERIFICATION_POLICY_v1", FREEZE_TIMESTAMP,
        "python-verified-calculator-v1", "julia-nemo-verified-calculator-v1", "lean-runtime-certificate-v1",
        tuple(sorted(row.spec_hash for row in specs)),
        {
            "exact_language": "CANONICAL_MATH_V1_RATIONAL_FUNCTIONS",
            "enclosure_promotion": "INDEPENDENT_CERTIFICATE_REQUIRED",
            "floating_agreement_ceiling": "CROSSCHECKED_NUMERICAL",
            "trusted_ode_rhs": "DECLARATIVE_IR_ONLY",
            "ode_python_methods": ["DOP853", "RK45", "Radau"],
            "ode_julia_method": "Vern9",
            "ode_rtol_ceiling": "1/1000",
            "ode_atol_ceiling": "1/1000",
            "uncertainty_semantics": ["GUARANTEED_RANGE", "LOCAL_LINEAR_COVARIANCE", "SAMPLED_DISTRIBUTION_ESTIMATE"],
        },
        QMCPolicyV1("SOBOL", "VPC_SOBOL_UINT32_V1", "VPC_SOBOL_2D_BRATLEY_FOX_BASE_V1", "DIGITAL_XOR_SHA256_V1", "GRAY_CODE_INDEX_ORDER", "FIRST_N_FROM_INDEX_ZERO"),
    )
