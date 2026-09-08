from __future__ import annotations

from formal.python.tools.bounded_program_governance import scope_hash
from formal.python.tools.qft_gr_quadratic_hyperbolicity_common import (
    REPO_ROOT,
    QuadraticHyperbolicityError,
    read_json,
    sha256_path,
    write_or_check,
)


CAPTURED_AT_UTC = "2026-07-29T00:00:00Z"
PROGRAM_ID = "TOE_NATIVE_COHERENCE_ONTOLOGY_AND_REPRESENTATION_V0"
HYPOTHESIS_ID = "HYP_TOE_COHERENCE_OPERATIONAL_REPRESENTABILITY_v0"
CURRENT_TARGET = (
    "prepare_toe_native_coherence_ontology_and_representation_"
    "bounded_program_v0"
)
MANDATORY_EXIT = (
    "close_toe_native_coherence_ontology_and_representation_"
    "v0_after_bounded_result_v0"
)
EXPECTED_PREPARATION_OUTCOME = (
    "COHERENCE_ONTOLOGY_AND_REPRESENTATION_BOUNDED_PROGRAM_"
    "PREPARED_NOT_INSTALLED_OR_OPEN"
)
EXPECTED_STRICT_OUTCOME = (
    "PROGRAM_PROPOSAL_COMPLETE_NO_REPRESENTATION_FIELD_ACTION_SEAM_"
    "PILLAR_OBSERVABLE_OR_EMPIRICAL_CLAIM"
)
EXPECTED_STAGE_IDS = [
    "CONTROLLED_COHERENCE_CLAIM_INVENTORY",
    "COHERENCE_OPERATIONAL_DEFINITION_TEST",
    "COHERENCE_REPRESENTATION_COMPARISON",
    "COHERENCE_OPERATIONAL_REPRESENTABILITY_DECISION",
    "MINIMAL_NATIVE_FIELD_HANDOFF",
]
EXPECTED_TARGETS = [
    "inventory_toe_native_controlled_coherence_claims_v0",
    "test_toe_native_coherence_claim_operational_definition_v0",
    "compare_toe_native_coherence_representation_families_v0",
    "select_toe_native_coherence_operational_representation_v0",
    (
        "prepare_toe_native_minimal_field_content_after_"
        "coherence_representation_v0"
    ),
]
EXPECTED_PROGRAM_OUTCOMES = [
    "COHERENCE_OPERATIONALLY_REPRESENTABLE",
    "COHERENCE_REPRESENTABLE_ONLY_AS_BOUNDED_SURROGATE",
    "COHERENCE_BETTER_TREATED_AS_DERIVED_FUNCTIONAL",
    "EXISTING_COHERENCE_CLAIMS_INSUFFICIENTLY_DEFINED",
    "NO_ADMISSIBLE_REPRESENTATION_FOUND",
]
EXPECTED_REPRESENTATION_FAMILIES = [
    "REAL_SCALAR",
    "COMPLEX_ORDER_PARAMETER",
    "PHASE_FIELD",
    "DENSITY_AND_CURRENT",
    "VECTOR_OR_TENSOR_ORDER_PARAMETER",
    "ROTOR_OR_GEOMETRIC_ALGEBRA_OBJECT",
    "STATISTICAL_FUNCTIONAL",
    "NONLOCAL_RELATION",
    "NO_INDEPENDENT_FIELD",
]
EXPECTED_NOT_CLAIMED = [
    "CCFT_VALIDATION",
    "COHERENCE_IS_FUNDAMENTAL",
    "COHERENCE_IS_A_FIELD",
    "MASTER_ACTION_DERIVATION",
    "QFT_GR_CLOSURE",
    "UNIQUE_OBSERVABLE",
    "EMPIRICAL_CONFIRMATION",
    "FULL_TOE",
]

CALCULATION_PATH = REPO_ROOT / (
    "formal/output/"
    "CALC-TOE-NATIVE-COHERENCE-ONTOLOGY-AND-REPRESENTATION-"
    "BOUNDED-PROGRAM-PREPARATION-v0.json"
)
REGISTRY_PATH = REPO_ROOT / "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json"
OUTPUT_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "TOE_NATIVE_COHERENCE_ONTOLOGY_AND_REPRESENTATION_"
    "BOUNDED_PROGRAM_PREPARATION_RESULT_REVIEW_20260729_v0.json"
)


def _independent_checks(calculation: dict, registry: dict) -> dict[str, bool]:
    proposal = calculation["program_proposal"]
    stages = proposal["semantic_stages_proposed"]
    stage_ids = [stage["semantic_stage_id"] for stage in stages]
    targets = [stage["canonical_target"] for stage in stages]
    evidence_hashes_match = all(
        (REPO_ROOT / record["path"]).is_file()
        and sha256_path(REPO_ROOT / record["path"]) == record["sha256"]
        for record in calculation["evidence"].values()
    )
    scope_hashes_match = all(
        stage["canonical_scope_hash"] == scope_hash(stage["canonical_scope"])
        for stage in stages
    )
    open_scopes_are_preoutput = all(
        stage["proposed_open_event_scope"]["event_type"] == "ATTEMPT_OPEN"
        and stage["proposed_open_event_scope"][
            "substantive_stage_output_allowed"
        ]
        is False
        and stage["proposed_open_event_scope"][
            "producer_may_run_before_open_commit"
        ]
        is False
        for stage in stages
    )
    close_scopes_are_result_bound = all(
        stage["proposed_close_event_scope"]["event_type"] == "ATTEMPT_CLOSE"
        and stage["proposed_close_event_scope"][
            "block_or_failure_requires_mandatory_exit"
        ]
        is True
        and "independent_result_review"
        in stage["proposed_close_event_scope"]["required_atomic_contents"]
        for stage in stages
    )
    boundary = calculation["claim_boundary"]
    closed = registry["bounded_programs_v1"]
    return {
        "current_target_authorizes_preparation_only": (
            registry["current_projection_v0"]["current_target"] == CURRENT_TARGET
            and calculation["execution_target"] == CURRENT_TARGET
        ),
        "hypothesis_identity_is_exact": (
            calculation["native_hypothesis_tested"] == HYPOTHESIS_ID
        ),
        "evidence_hashes_recompute": evidence_hashes_match,
        "proposal_is_not_installed_authorized_or_open": (
            proposal["proposal_only"] is True
            and proposal["installed"] is False
            and proposal["authorized"] is False
            and proposal["open_event_created"] is False
            and proposal["attempt_count"] == 0
        ),
        "five_stage_zero_repair_cap_is_exact": (
            proposal["authorized_stage_count_proposed"] == 5
            and len(stages) == 5
            and proposal["repair_attempt_count_proposed"] == 0
            and proposal["no_subsidiary_scientific_targets_proposed"] is True
        ),
        "stage_identity_and_order_are_exact": (
            stage_ids == EXPECTED_STAGE_IDS
            and targets == EXPECTED_TARGETS
            and [stage["stage_number"] for stage in stages]
            == [1, 2, 3, 4, 5]
            and len(stage_ids) == len(set(stage_ids))
            and len(targets) == len(set(targets))
        ),
        "canonical_scope_hashes_recompute": scope_hashes_match,
        "open_event_scopes_are_preoutput_only": open_scopes_are_preoutput,
        "close_event_scopes_bind_result_review_and_exit": (
            close_scopes_are_result_bound
        ),
        "stage_1_selects_one_claim_or_closes": (
            "exactly_one_claim_selected_for_stage_2_or_failed_closed"
            in stages[0]["canonical_scope"]["required_outputs"]
            and proposal["stage_transition_rules"][
                "stage_1_selects_exactly_one_claim_or_closes"
            ]
            is True
        ),
        "stage_2_tests_operational_distinctions": (
            "standard_quantity_distinction_matrix"
            in stages[1]["canonical_scope"]["required_outputs"]
            and "candidate_measurement_operation"
            in stages[1]["canonical_scope"]["required_outputs"]
        ),
        "stage_3_compares_without_preselection": (
            proposal["representation_families_to_compare"]
            == EXPECTED_REPRESENTATION_FAMILIES
            and "representation promotion before comparative review"
            in stages[2]["canonical_scope"]["prohibited_claims"]
        ),
        "stage_4_uses_exact_terminal_vocabulary": (
            proposal["program_terminal_outcomes"]
            == EXPECTED_PROGRAM_OUTCOMES
            and stages[3]["canonical_scope"]["terminal_outcome_vocabulary"]
            == EXPECTED_PROGRAM_OUTCOMES
        ),
        "stage_5_is_conditional_handoff_only": (
            stages[4]["conditional"] is True
            and proposal["stage_transition_rules"][
                "stage_5_is_optional_and_requires_positive_stage_4_result"
            ]
            is True
            and "action construction"
            in stages[4]["canonical_scope"]["prohibited_claims"]
        ),
        "mandatory_exit_is_exact": (
            proposal["mandatory_exit_target_proposed"] == MANDATORY_EXIT
            and proposal["stage_transition_rules"][
                "any_block_or_failure_closes_without_repair"
            ]
            is True
        ),
        "anti_overclaim_vocabulary_is_exact": (
            proposal["not_claimed"] == EXPECTED_NOT_CLAIMED
        ),
        "no_representation_or_physics_was_selected": (
            boundary["coherence_defined"] is False
            and boundary["coherence_representation_selected"] is False
            and boundary["coherence_field_selected"] is False
            and boundary["native_action_selected"] is False
            and boundary["native_seam_executed"] is False
            and boundary["native_pillar_executed"] is False
            and boundary["observable_selected"] is False
            and boundary["empirical_claim_made"] is False
        ),
        "no_program_lifecycle_state_was_created": (
            boundary["program_installed"] is False
            and boundary["program_authorized"] is False
            and boundary["attempt_opened"] is False
            and PROGRAM_ID not in closed
        ),
        "closed_program_outcomes_remain_exact": (
            closed["QFT_GR_QUADRATIC_BOUNDED_CLOSEOUT_V0"]["state"]
            == "CLOSED"
            and closed["QFT_GR_QUADRATIC_BOUNDED_CLOSEOUT_V0"]["toe_role"]
            == "REFERENCE_CONTROL_ONLY"
            and closed["QFT_GR_QUADRATIC_BOUNDED_CLOSEOUT_V0"][
                "control_result"
            ]
            == "UNRESOLVED_AFTER_BOUNDED_ATTEMPT"
            and closed["TOE_NATIVE_SURROGATE_V0"]["state"] == "CLOSED"
            and closed["TOE_NATIVE_SURROGATE_V0"]["blocked_stage_id"]
            == "COHERENCE_REPRESENTATION"
            and closed["TOE_NATIVE_SURROGATE_V0"][
                "v0_discriminator_result"
            ]
            == "NO_UNIQUE_TOE_DISCRIMINATOR_V0"
        ),
        "separate_governance_and_science_authority_are_required": (
            calculation["prospective_governance_prerequisite"]["status"]
            == "BLOCKED_PENDING_LIFECYCLE_SAFE_GOVERNANCE_ENABLEMENT"
            and calculation["prospective_governance_prerequisite"][
                "maintenance_enablement_is_scientific_authorization"
            ]
            is False
            and calculation["prospective_governance_prerequisite"][
                "scientific_authority_still_required_after_enablement"
            ]
            is True
        ),
        "exhaustive_python_debt_is_not_called_a_pass": (
            calculation["validation_debt_boundary"][
                "exhaustive_python_passage_established"
            ]
            is False
        ),
        "no_automatic_successor_was_selected": (
            calculation["automatic_successor_selected"] is False
            and calculation["separate_authority_decision_required"] is True
        ),
        "preparation_terminal_outcomes_are_exact": (
            calculation["terminal_outcome"] == EXPECTED_PREPARATION_OUTCOME
            and calculation["strict_terminal_outcome"]
            == EXPECTED_STRICT_OUTCOME
        ),
    }


def build_review() -> dict:
    calculation = read_json(CALCULATION_PATH)
    registry = read_json(REGISTRY_PATH)
    checks = _independent_checks(calculation, registry)
    failed = sorted(name for name, value in checks.items() if not value)
    if failed:
        raise QuadraticHyperbolicityError(
            f"coherence program preparation review failed: {failed}"
        )
    return {
        "schema_id": (
            "toe.native_coherence_ontology_and_representation."
            "bounded_program_preparation_result_review.v0"
        ),
        "captured_at_utc": CAPTURED_AT_UTC,
        "reviewed_calculation": CALCULATION_PATH.relative_to(
            REPO_ROOT
        ).as_posix(),
        "reviewed_calculation_sha256": sha256_path(CALCULATION_PATH),
        "program_id": PROGRAM_ID,
        "native_hypothesis_tested": HYPOTHESIS_ID,
        "accepted": True,
        "checks": checks,
        "failed_checks": failed,
        "program_proposal_status": "PREPARED_NOT_INSTALLED_AUTHORIZED_OR_OPEN",
        "scientific_execution_authorized": False,
        "representation_selected": False,
        "field_selected": False,
        "action_selected": False,
        "automatic_successor_selected": False,
        "separate_authority_decision_required": True,
        "validation_debt_status": (
            "EXHAUSTIVE_PYTHON_PASSAGE_NOT_ESTABLISHED_SEPARATE_DEBT_"
            "CLASSIFICATION_REQUIRED"
        ),
        "terminal_outcome": EXPECTED_PREPARATION_OUTCOME,
        "strict_terminal_outcome": EXPECTED_STRICT_OUTCOME,
        "verdict": (
            "COHERENCE_ONTOLOGY_AND_REPRESENTATION_BOUNDED_PROGRAM_"
            "PREPARATION_ACCEPTED_NO_PROGRAM_INSTALLATION_OR_NATIVE_MODEL"
        ),
    }


def main() -> int:
    return write_or_check(
        path=OUTPUT_PATH,
        build=build_review,
        description=(
            "ToE native coherence ontology and representation bounded "
            "program preparation result review"
        ),
    )


if __name__ == "__main__":
    raise SystemExit(main())
