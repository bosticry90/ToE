from __future__ import annotations

from formal.python.tools.bounded_program_governance import QUADRATIC_PROGRAM_ID
from formal.python.tools.qft_gr_quadratic_hyperbolicity_common import (
    REPO_ROOT,
    QuadraticHyperbolicityError,
    read_json,
    sha256_path,
    write_or_check,
)


CAPTURED_AT_UTC = "2026-07-29T00:00:00Z"
EXECUTION_TARGET = (
    "select_qft_gr_quadratic_toe_role_after_generic_frozen_result_v0"
)
SELECTED_NEXT_TARGET = "authorize_toe_native_surrogate_v0_bounded_program"
NATIVE_STAGE_1_TARGET = "select_toe_native_coherence_representation_v0"
NATIVE_V0_CLOSE_TARGET = (
    "close_toe_native_surrogate_v0_after_bounded_result_v0"
)
NATIVE_HYPOTHESIS_SELECTOR_TARGET = (
    "select_next_native_toe_hypothesis_for_bounded_adjudication_v0"
)
NATIVE_COHERENCE_PROGRAM_PREPARATION_TARGET = (
    "prepare_toe_native_coherence_ontology_and_representation_"
    "bounded_program_v0"
)
REGISTRY_PATH = REPO_ROOT / "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json"
STAGE_3_RESULT_PATH = REPO_ROOT / (
    "formal/output/CALC-QFT-GR-QUADRATIC-EXACT-GENERIC-FROZEN-"
    "COMPANION-OPERATOR-v1.json"
)
STAGE_3_REVIEW_PATH = REPO_ROOT / (
    "formal/docs/release/QFT_GR_QUADRATIC_EXACT_GENERIC_FROZEN_"
    "COMPANION_OPERATOR_V1_RESULT_REVIEW_20260729_v0.json"
)
COMPARISON_ORIGIN_PATH = REPO_ROOT / (
    "formal/toe_formal/ToeFormal/Derivation/"
    "ExploratoryNativeGravitationalRequirementsFamilySurveyResultReviewV0.lean"
)
COMPARISON_REVIEW_PATH = REPO_ROOT / (
    "formal/toe_formal/ToeFormal/Derivation/"
    "SharedLinearizedQuadraticGravitySourceAndSpectrumComparisonResultReviewV0.lean"
)
OUTPUT_PATH = REPO_ROOT / (
    "formal/output/CALC-QFT-GR-QUADRATIC-TOE-ROLE-AFTER-"
    "GENERIC-FROZEN-RESULT-v0.json"
)


def build_calculation() -> dict:
    registry = read_json(REGISTRY_PATH)
    projection = registry["current_projection_v0"]
    program = registry["bounded_programs_v1"][QUADRATIC_PROGRAM_ID]
    stage_3 = read_json(STAGE_3_RESULT_PATH)
    review = read_json(STAGE_3_REVIEW_PATH)
    if projection["current_target"] not in {
        EXECUTION_TARGET,
        SELECTED_NEXT_TARGET,
        NATIVE_STAGE_1_TARGET,
        NATIVE_V0_CLOSE_TARGET,
        NATIVE_HYPOTHESIS_SELECTOR_TARGET,
        NATIVE_COHERENCE_PROGRAM_PREPARATION_TARGET,
    }:
        raise QuadraticHyperbolicityError(
            "quadratic role gate is neither authoritative nor the accepted predecessor"
        )
    if not (
        program["state"] == "CLOSED"
        and program["blocked_stage_id"] == "EXACT_FROZEN_COMPANION_OPERATOR"
        and program["last_closed_attempt_number"] == 3
        and program["repair_attempt_count"] == 0
    ):
        raise QuadraticHyperbolicityError("bounded quadratic program is not closed")
    if not (
        stage_3["terminal_result"] == "BLOCKED"
        and review["accepted"] is True
        and review["terminal_outcome"] == "GENERIC_BACKGROUND_OPERATOR_NOT_CLOSED"
    ):
        raise QuadraticHyperbolicityError("accepted Stage 3 block changed")

    origin_text = COMPARISON_ORIGIN_PATH.read_text(encoding="utf-8")
    comparison_text = COMPARISON_REVIEW_PATH.read_text(encoding="utf-8")
    historical_checks = {
        "entered_as_shared_comparison_packet": (
            "prepare_shared_linearized_quadratic_gravity_source_and_spectrum_comparison_packet_v0"
            in origin_text
        ),
        "comparison_family_adoption_was_false": (
            "def comparisonFamilyAdoptionAuthorized : Bool := false"
            in origin_text
        ),
        "native_gravitational_principle_was_not_identified": (
            "def nativeGravitationalPrincipleIdentified : Bool := false"
            in comparison_text
        ),
        "comparison_action_was_not_selected": (
            "def comparisonActionSelected : Bool := false" in comparison_text
        ),
        "review_kind_excluded_theory_adoption": (
            "SCIENTIFIC_RESPONSE_SELECTION_ONLY_NO_THEORY_ADOPTION"
            in comparison_text
        ),
    }
    if not all(historical_checks.values()):
        raise QuadraticHyperbolicityError(
            "quadratic comparison-role evidence is incomplete"
        )

    return {
        "schema_id": (
            "CALC_QFT_GR_QUADRATIC_TOE_ROLE_AFTER_GENERIC_FROZEN_RESULT_v0"
        ),
        "calculation_id": (
            "CALC-QFT-GR-QUADRATIC-TOE-ROLE-AFTER-GENERIC-FROZEN-RESULT-v0"
        ),
        "captured_at_utc": CAPTURED_AT_UTC,
        "execution_target": EXECUTION_TARGET,
        "consumed_bounded_result": {
            "path": STAGE_3_RESULT_PATH.relative_to(REPO_ROOT).as_posix(),
            "sha256": sha256_path(STAGE_3_RESULT_PATH),
            "terminal_result": "BLOCKED",
            "terminal_outcome": "GENERIC_BACKGROUND_OPERATOR_NOT_CLOSED",
        },
        "consumed_review": {
            "path": STAGE_3_REVIEW_PATH.relative_to(REPO_ROOT).as_posix(),
            "sha256": sha256_path(STAGE_3_REVIEW_PATH),
        },
        "bounded_program_closeout": {
            "program_id": QUADRATIC_PROGRAM_ID,
            "authorized_stage_count": 5,
            "attempted_stage_count": 3,
            "attempted_stage_ids": program["attempted_stage_ids"],
            "blocked_stage_id": program["blocked_stage_id"],
            "repair_attempt_count": program["repair_attempt_count"],
            "unattempted_stage_ids": [
                "CONSTRAINT_TANGENT_AND_PHYSICAL_QUOTIENT",
                "SUBPRINCIPAL_PROPAGATOR_GROWTH",
            ],
            "subsidiary_scientific_targets_created": 0,
        },
        "historical_role_evidence": {
            "origin_path": COMPARISON_ORIGIN_PATH.relative_to(REPO_ROOT).as_posix(),
            "origin_sha256": sha256_path(COMPARISON_ORIGIN_PATH),
            "comparison_review_path": COMPARISON_REVIEW_PATH.relative_to(
                REPO_ROOT
            ).as_posix(),
            "comparison_review_sha256": sha256_path(COMPARISON_REVIEW_PATH),
            "checks": historical_checks,
        },
        "role_decision": {
            "toe_role": "REFERENCE_CONTROL_ONLY",
            "control_result": "UNRESOLVED_AFTER_BOUNDED_ATTEMPT",
            "native_action_evidence_found": False,
            "coefficient_origin_from_native_toe_principle_found": False,
            "effective_limit_derivation_found": False,
            "rejection_as_native_candidate_claimed": False,
            "reason": (
                "The lineage explicitly introduced quadratic gravity as a "
                "shared comparison family, prohibited theory adoption, selected "
                "no comparison action or coefficients, and identified no native "
                "gravitational principle. The bounded closeout then blocked "
                "before an exact generic companion or finite-loss result."
            ),
        },
        "claim_boundary": {
            "quadratic_gravity_native_toe_sector": False,
            "quadratic_gravity_derived_effective_limit": False,
            "quadratic_gravity_rejected_toe_candidate": False,
            "generic_finite_loss_established": False,
            "generic_finite_loss_refuted": False,
            "generic_frozen_status_unresolved": True,
            "further_quadratic_work_authorized": False,
            "native_surrogate_program_authorized_here": False,
        },
        "selected_next_target": SELECTED_NEXT_TARGET,
        "terminal_outcome": (
            "REFERENCE_CONTROL_ONLY_WITH_UNRESOLVED_AFTER_BOUNDED_ATTEMPT"
        ),
        "verdict": (
            "QUADRATIC_GRAVITY_CLASSIFIED_REFERENCE_CONTROL_ONLY_"
            "GENERIC_FROZEN_RESULT_UNRESOLVED_AFTER_BOUNDED_ATTEMPT_"
            "NO_FURTHER_QUADRATIC_STAGE_OR_REPAIR"
        ),
    }


def main() -> int:
    return write_or_check(
        path=OUTPUT_PATH,
        build=build_calculation,
        description="quadratic-gravity ToE role gate",
    )


if __name__ == "__main__":
    raise SystemExit(main())
