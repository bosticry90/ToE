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
EXECUTION_TARGET = (
    "prepare_toe_native_coherence_ontology_and_representation_"
    "bounded_program_v0"
)
PROGRAM_ID = "TOE_NATIVE_COHERENCE_ONTOLOGY_AND_REPRESENTATION_V0"
HYPOTHESIS_ID = "HYP_TOE_COHERENCE_OPERATIONAL_REPRESENTABILITY_v0"
MANDATORY_EXIT_TARGET = (
    "close_toe_native_coherence_ontology_and_representation_"
    "v0_after_bounded_result_v0"
)
PREPARATION_OUTCOME = (
    "COHERENCE_ONTOLOGY_AND_REPRESENTATION_BOUNDED_PROGRAM_"
    "PREPARED_NOT_INSTALLED_OR_OPEN"
)
STRICT_OUTCOME = (
    "PROGRAM_PROPOSAL_COMPLETE_NO_REPRESENTATION_FIELD_ACTION_SEAM_"
    "PILLAR_OBSERVABLE_OR_EMPIRICAL_CLAIM"
)

REGISTRY_PATH = REPO_ROOT / "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json"
SELECTOR_RESULT_PATH = REPO_ROOT / (
    "formal/output/CALC-TOE-NATIVE-HYPOTHESIS-FRONTIER-SELECTION-v0.json"
)
SELECTOR_REVIEW_PATH = REPO_ROOT / (
    "formal/docs/release/TOE_NATIVE_HYPOTHESIS_FRONTIER_SELECTION_"
    "RESULT_REVIEW_20260729_v0.json"
)
COHERENCE_HYPOTHESIS_PATH = REPO_ROOT / (
    "formal/docs/paper/TOE_COHERENCE_ADMISSIBILITY_BRIDGE_HYPOTHESIS_v0.md"
)
OBJECT_CROSSWALK_PATH = REPO_ROOT / (
    "formal/docs/paper/CCFT_TO_TOE_OBJECT_CROSSWALK_v0.md"
)
MASTER_ACTION_PATH = REPO_ROOT / (
    "formal/docs/paper/TOE_CANDIDATE_MASTER_ACTION_v0.md"
)
VARIATIONAL_PROGRAM_PATH = REPO_ROOT / (
    "formal/docs/paper/CCFT_FULL_VARIATIONAL_ACTION_PROGRAM_v0.md"
)
DISCRIMINATOR_MAP_PATH = REPO_ROOT / (
    "formal/docs/paper/CCFT_EMPIRICAL_DISCRIMINATOR_CANDIDATE_MAP_v0.md"
)
READINESS_PATH = REPO_ROOT / (
    "formal/docs/release/SCIENCE_FIRST_PILLAR_SEAM_READINESS_v0.json"
)
REAL_SCALAR_REVIEW_PATH = REPO_ROOT / (
    "formal/docs/release/TOE_NATIVE_COHERENCE_REPRESENTATION_"
    "V0_RESULT_REVIEW_20260729_v0.json"
)
NATIVE_CLOSEOUT_PATH = REPO_ROOT / (
    "formal/output/CALC-TOE-NATIVE-SURROGATE-V0-BOUNDED-CLOSEOUT-v0.json"
)
GOVERNANCE_VALIDATOR_PATH = REPO_ROOT / (
    "formal/python/tools/bounded_program_governance.py"
)
QUADRATIC_MANIFEST_PATH = REPO_ROOT / (
    "formal/docs/release/bounded_program_manifests/"
    "QFT_GR_QUADRATIC_BOUNDED_CLOSEOUT_V0_MANIFEST_v1.json"
)
NATIVE_MANIFEST_PATH = REPO_ROOT / (
    "formal/docs/release/bounded_program_manifests/"
    "TOE_NATIVE_SURROGATE_V0_MANIFEST_v1.json"
)
OUTPUT_PATH = REPO_ROOT / (
    "formal/output/"
    "CALC-TOE-NATIVE-COHERENCE-ONTOLOGY-AND-REPRESENTATION-"
    "BOUNDED-PROGRAM-PREPARATION-v0.json"
)

EVIDENCE_PATHS = {
    "frontier_selection": SELECTOR_RESULT_PATH,
    "frontier_selection_review": SELECTOR_REVIEW_PATH,
    "coherence_admissibility_hypothesis": COHERENCE_HYPOTHESIS_PATH,
    "ccft_to_toe_object_crosswalk": OBJECT_CROSSWALK_PATH,
    "candidate_master_action": MASTER_ACTION_PATH,
    "ccft_variational_program": VARIATIONAL_PROGRAM_PATH,
    "ccft_discriminator_map": DISCRIMINATOR_MAP_PATH,
    "pillar_seam_readiness": READINESS_PATH,
    "closed_real_scalar_review": REAL_SCALAR_REVIEW_PATH,
    "closed_native_surrogate": NATIVE_CLOSEOUT_PATH,
    "bounded_governance_validator": GOVERNANCE_VALIDATOR_PATH,
    "quadratic_closed_program_manifest": QUADRATIC_MANIFEST_PATH,
    "native_surrogate_closed_program_manifest": NATIVE_MANIFEST_PATH,
}

CLAIM_CLASSIFICATIONS = [
    "PHYSICAL_ONTOLOGY_CLAIM",
    "MATHEMATICAL_STRUCTURE_CLAIM",
    "EFFECTIVE_MODEL_CLAIM",
    "ANALOGY_OR_HEURISTIC",
    "OBSERVATIONAL_CLAIM",
    "UNRESOLVED_LANGUAGE",
]

REPRESENTATION_FAMILIES = [
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

PROGRAM_TERMINAL_OUTCOMES = [
    "COHERENCE_OPERATIONALLY_REPRESENTABLE",
    "COHERENCE_REPRESENTABLE_ONLY_AS_BOUNDED_SURROGATE",
    "COHERENCE_BETTER_TREATED_AS_DERIVED_FUNCTIONAL",
    "EXISTING_COHERENCE_CLAIMS_INSUFFICIENTLY_DEFINED",
    "NO_ADMISSIBLE_REPRESENTATION_FOUND",
]

PROGRAM_NOT_CLAIMED = [
    "CCFT_VALIDATION",
    "COHERENCE_IS_FUNDAMENTAL",
    "COHERENCE_IS_A_FIELD",
    "MASTER_ACTION_DERIVATION",
    "QFT_GR_CLOSURE",
    "UNIQUE_OBSERVABLE",
    "EMPIRICAL_CONFIRMATION",
    "FULL_TOE",
]


def _scope(
    *,
    semantic_stage_id: str,
    question: str,
    authorized_inputs: list[str],
    required_outputs: list[str],
    prohibited_claims: list[str],
    dependencies: list[str],
    outcomes: list[str],
) -> dict:
    return {
        "semantic_stage_id": semantic_stage_id,
        "normalized_scientific_question": question,
        "authorized_inputs": authorized_inputs,
        "required_outputs": required_outputs,
        "prohibited_claims": prohibited_claims,
        "dependency_artifact_ids": dependencies,
        "terminal_outcome_vocabulary": outcomes,
    }


def _stage(
    *,
    number: int,
    semantic_stage_id: str,
    target: str,
    question: str,
    authorized_inputs: list[str],
    required_outputs: list[str],
    prohibited_claims: list[str],
    dependencies: list[str],
    outcomes: list[str],
    conditional: bool = False,
) -> dict:
    canonical_scope = _scope(
        semantic_stage_id=semantic_stage_id,
        question=question,
        authorized_inputs=authorized_inputs,
        required_outputs=required_outputs,
        prohibited_claims=prohibited_claims,
        dependencies=dependencies,
        outcomes=outcomes,
    )
    return {
        "stage_number": number,
        "semantic_stage_id": semantic_stage_id,
        "canonical_target": target,
        "canonical_scope": canonical_scope,
        "canonical_scope_hash": scope_hash(canonical_scope),
        "conditional": conditional,
        "proposed_open_event_scope": {
            "event_type": "ATTEMPT_OPEN",
            "required_atomic_contents": [
                "immutable_OPEN_event",
                "registry_projection_update",
                "generated_authority_surfaces",
                "Lean_authority_mirrors",
            ],
            "substantive_stage_output_allowed": False,
            "producer_may_run_before_open_commit": False,
        },
        "proposed_close_event_scope": {
            "event_type": "ATTEMPT_CLOSE",
            "required_atomic_contents": [
                "stage_result_or_failed_closed_result",
                "independent_result_review",
                "immutable_CLOSE_event",
                "registry_and_authority_transition",
                "validation_record",
            ],
            "terminal_outcomes": outcomes,
            "block_or_failure_requires_mandatory_exit": True,
        },
    }


def _stages() -> list[dict]:
    common_prohibitions = [
        "CCFT validation",
        "coherence fundamentality",
        "coherence field selection before Stage 4",
        "master-action derivation",
        "QFT-GR closure",
        "unique observable",
        "empirical confirmation",
        "completed ToE",
    ]
    return [
        _stage(
            number=1,
            semantic_stage_id="CONTROLLED_COHERENCE_CLAIM_INVENTORY",
            target="inventory_toe_native_controlled_coherence_claims_v0",
            question=(
                "Which preserved ToE and CCFT coherence statements are serious "
                "candidate claims, what do they mean in their own source, and "
                "which single claim—if any—may advance to operational testing?"
            ),
            authorized_inputs=list(EVIDENCE_PATHS),
            required_outputs=[
                "source_bound_claim_inventory",
                "claim_classification_table",
                "provenance_and_conflict_ledger",
                "symbolic_similarity_meaning_transport_firewall",
                "exactly_one_claim_selected_for_stage_2_or_failed_closed",
                "legacy_UEFM_context_admissibility_record",
            ],
            prohibited_claims=[
                *common_prohibitions,
                "representation selection",
                "symbolic similarity as evidence of physical identity",
            ],
            dependencies=["frontier_selection_review"],
            outcomes=[
                "CONTROLLED_COHERENCE_CLAIM_INVENTORY_COMPLETE",
                "NO_SERIOUS_COHERENCE_CLAIM_SURVIVES_INVENTORY",
                "COHERENCE_CLAIM_PROVENANCE_BLOCKED",
            ],
        ),
        _stage(
            number=2,
            semantic_stage_id="COHERENCE_OPERATIONAL_DEFINITION_TEST",
            target="test_toe_native_coherence_claim_operational_definition_v0",
            question=(
                "Does the one Stage-1-selected claim define a possessor, "
                "change, zero, scale, preparation or destruction operation, "
                "units, and a measurement-sensitive distinction from standard "
                "correlation, order, entanglement, synchronization, entropy, "
                "phase alignment, and field amplitude?"
            ),
            authorized_inputs=[
                "CONTROLLED_COHERENCE_CLAIM_INVENTORY",
                "exactly_one_selected_coherence_claim",
            ],
            required_outputs=[
                "operational_definition_contract",
                "physical_possessor_and_change_ledger",
                "zero_and_scale_semantics",
                "preparation_transport_destruction_operations",
                "units_or_dimension_classification",
                "standard_quantity_distinction_matrix",
                "candidate_measurement_operation",
            ],
            prohibited_claims=[
                *common_prohibitions,
                "representation selection",
                "observable validation",
            ],
            dependencies=["CONTROLLED_COHERENCE_CLAIM_INVENTORY"],
            outcomes=[
                "COHERENCE_OPERATIONAL_DEFINITION_ACCEPTED",
                "EXISTING_COHERENCE_CLAIMS_INSUFFICIENTLY_DEFINED",
                "COHERENCE_OPERATIONAL_DEFINITION_BLOCKED",
            ],
        ),
        _stage(
            number=3,
            semantic_stage_id="COHERENCE_REPRESENTATION_COMPARISON",
            target="compare_toe_native_coherence_representation_families_v0",
            question=(
                "Which candidate mathematical representation families preserve "
                "the accepted operational claim, and what meaning, symmetry, "
                "degree-of-freedom, locality, conservation, background, and "
                "information-loss costs does each impose?"
            ),
            authorized_inputs=[
                "COHERENCE_OPERATIONAL_DEFINITION_TEST",
                *REPRESENTATION_FAMILIES,
            ],
            required_outputs=[
                "representation_family_comparison_matrix",
                "component_meaning_and_units_ledger",
                "symmetry_and_degree_of_freedom_ledger",
                "locality_and_relativistic_transformation_ledger",
                "conservation_exchange_and_background_requirements",
                "CCFT_information_loss_ledger",
                "standard_quantity_renaming_audit",
                "mathematical_and_experimental_tractability_assessment",
            ],
            prohibited_claims=[
                *common_prohibitions,
                "representation promotion before comparative review",
                "field assumption from terminology alone",
            ],
            dependencies=["COHERENCE_OPERATIONAL_DEFINITION_TEST"],
            outcomes=[
                "COHERENCE_REPRESENTATION_COMPARISON_COMPLETE",
                "NO_ADMISSIBLE_REPRESENTATION_FOUND",
                "COHERENCE_REPRESENTATION_COMPARISON_BLOCKED",
            ],
        ),
        _stage(
            number=4,
            semantic_stage_id="COHERENCE_OPERATIONAL_REPRESENTABILITY_DECISION",
            target="select_toe_native_coherence_operational_representation_v0",
            question=(
                "Is the frozen operational coherence claim representable, only "
                "surrogately representable, better treated as a derived "
                "functional, insufficiently defined, or unsupported by every "
                "admissible representation?"
            ),
            authorized_inputs=[
                "COHERENCE_REPRESENTATION_COMPARISON",
                "COHERENCE_OPERATIONAL_DEFINITION_TEST",
            ],
            required_outputs=[
                "exact_preserved_claim_represented_or_blocked",
                "selected_mathematical_type_or_nonfield_classification",
                "controlled_physical_meaning",
                "omitted_structure_ledger",
                "enabled_later_calculation",
                "representation_adequacy_falsifier",
                "terminal_representability_decision",
            ],
            prohibited_claims=[
                *common_prohibitions,
                "nature_contains_selected_object",
                "automatic action or interaction authorization",
            ],
            dependencies=[
                "COHERENCE_REPRESENTATION_COMPARISON",
                "COHERENCE_OPERATIONAL_DEFINITION_TEST",
            ],
            outcomes=PROGRAM_TERMINAL_OUTCOMES,
        ),
        _stage(
            number=5,
            semantic_stage_id="MINIMAL_NATIVE_FIELD_HANDOFF",
            target=(
                "prepare_toe_native_minimal_field_content_after_"
                "coherence_representation_v0"
            ),
            question=(
                "After a positive Stage-4 representation result only, what "
                "minimal native field-content or nonfield-content decision may "
                "be prepared for a separately authorized future program?"
            ),
            authorized_inputs=[
                "COHERENCE_OPERATIONAL_REPRESENTABILITY_DECISION",
                "positive_stage_4_representation_result_only",
            ],
            required_outputs=[
                "minimal_content_handoff_contract",
                "representation_to_content_dependency_map",
                "explicit_omission_and_nonclaim_boundary",
                "separate_future_authority_requirement",
            ],
            prohibited_claims=[
                *common_prohibitions,
                "field content execution",
                "action construction",
                "interaction construction",
                "seam calculation",
                "pillar recovery",
            ],
            dependencies=["COHERENCE_OPERATIONAL_REPRESENTABILITY_DECISION"],
            outcomes=[
                "MINIMAL_NATIVE_CONTENT_HANDOFF_PREPARED",
                "MINIMAL_NATIVE_CONTENT_HANDOFF_NOT_APPLICABLE",
                "MINIMAL_NATIVE_CONTENT_HANDOFF_BLOCKED",
            ],
            conditional=True,
        ),
    ]


def _evidence() -> dict[str, dict[str, str]]:
    return {
        name: {
            "path": path.relative_to(REPO_ROOT).as_posix(),
            "sha256": sha256_path(path),
        }
        for name, path in EVIDENCE_PATHS.items()
    }


def build_calculation() -> dict:
    registry = read_json(REGISTRY_PATH)
    projection = registry["current_projection_v0"]
    if projection["current_target"] != EXECUTION_TARGET:
        raise QuadraticHyperbolicityError(
            "coherence ontology program preparation is not authoritative"
        )

    selector = read_json(SELECTOR_RESULT_PATH)
    selector_review = read_json(SELECTOR_REVIEW_PATH)
    real_scalar_review = read_json(REAL_SCALAR_REVIEW_PATH)
    native_closeout = read_json(NATIVE_CLOSEOUT_PATH)
    quadratic = registry["bounded_programs_v1"][
        "QFT_GR_QUADRATIC_BOUNDED_CLOSEOUT_V0"
    ]
    native = registry["bounded_programs_v1"]["TOE_NATIVE_SURROGATE_V0"]
    governance_text = GOVERNANCE_VALIDATOR_PATH.read_text(encoding="utf-8")

    checks = {
        "selected_hypothesis_matches_authority": (
            selector["selected_native_hypothesis"]["hypothesis_id"]
            == HYPOTHESIS_ID
            and selector["selected_next_target"] == EXECUTION_TARGET
            and selector_review["accepted"] is True
        ),
        "preparation_is_not_program_execution": (
            selector["program_installation_executed"] is False
            and selector["scientific_calculation_executed"] is False
        ),
        "closed_program_outcomes_are_preserved": (
            quadratic["state"] == "CLOSED"
            and quadratic["toe_role"] == "REFERENCE_CONTROL_ONLY"
            and quadratic["control_result"]
            == "UNRESOLVED_AFTER_BOUNDED_ATTEMPT"
            and native["state"] == "CLOSED"
            and native["blocked_stage_id"] == "COHERENCE_REPRESENTATION"
            and native["v0_discriminator_result"]
            == "NO_UNIQUE_TOE_DISCRIMINATOR_V0"
            and native_closeout["terminal_outcome"]
            == "NO_UNIQUE_TOE_DISCRIMINATOR_V0"
        ),
        "real_scalar_route_remains_closed": (
            real_scalar_review["accepted"] is True
            and real_scalar_review["terminal_result"] == "BLOCKED"
        ),
        "current_validator_has_no_prospective_program_manifest": (
            PROGRAM_ID not in governance_text
            and set(registry["bounded_programs_v1"])
            == {
                "QFT_GR_QUADRATIC_BOUNDED_CLOSEOUT_V0",
                "TOE_NATIVE_SURROGATE_V0",
            }
        ),
    }
    if not all(checks.values()):
        failed = sorted(key for key, value in checks.items() if not value)
        raise QuadraticHyperbolicityError(
            f"program-preparation prerequisites failed: {failed}"
        )

    stages = _stages()
    return {
        "schema_id": (
            "toe.native_coherence_ontology_and_representation."
            "bounded_program_preparation.v0"
        ),
        "calculation_id": (
            "CALC-TOE-NATIVE-COHERENCE-ONTOLOGY-AND-REPRESENTATION-"
            "BOUNDED-PROGRAM-PREPARATION-v0"
        ),
        "captured_at_utc": CAPTURED_AT_UTC,
        "execution_target": EXECUTION_TARGET,
        "native_hypothesis_tested": HYPOTHESIS_ID,
        "preparation_question": (
            "Can at least one preserved ToE or CCFT coherence claim be "
            "translated into an operational physical concept and a suitable "
            "mathematical representation without assuming the representation?"
        ),
        "evidence": _evidence(),
        "evidence_checks": checks,
        "program_proposal": {
            "schema_id": "toe.bounded_program.proposal.v0",
            "program_id": PROGRAM_ID,
            "proposal_only": True,
            "installed": False,
            "authorized": False,
            "open_event_created": False,
            "attempt_count": 0,
            "authorized_stage_count_proposed": 5,
            "repair_attempt_count_proposed": 0,
            "no_subsidiary_scientific_targets_proposed": True,
            "mandatory_exit_target_proposed": MANDATORY_EXIT_TARGET,
            "semantic_stages_proposed": stages,
            "program_terminal_outcomes": PROGRAM_TERMINAL_OUTCOMES,
            "claim_classification_vocabulary": CLAIM_CLASSIFICATIONS,
            "representation_families_to_compare": REPRESENTATION_FAMILIES,
            "not_claimed": PROGRAM_NOT_CLAIMED,
            "stage_transition_rules": {
                "stage_1_selects_exactly_one_claim_or_closes": True,
                "stage_2_requires_stage_1_selected_claim": True,
                "stage_3_requires_accepted_operational_definition": True,
                "stage_4_requires_completed_comparison": True,
                "stage_5_is_optional_and_requires_positive_stage_4_result": True,
                "any_block_or_failure_closes_without_repair": True,
                "new_representation_requires_separately_authorized_v1": True,
            },
            "legacy_UEFM_boundary": (
                "No UEFM artifact is named as an authorized input in this "
                "proposal. Any UEFM material may enter only after a separate "
                "provenance and admissibility record identifies a retained "
                "artifact; terminology alone is not evidence."
            ),
        },
        "prospective_governance_prerequisite": {
            "status": "BLOCKED_PENDING_LIFECYCLE_SAFE_GOVERNANCE_ENABLEMENT",
            "authority_lane": "SEPARATE_MAINTENANCE_AUTHORITY",
            "program_manifest_installed": False,
            "program_registry_record_created": False,
            "attempt_opened": False,
            "maintenance_enablement_is_scientific_authorization": False,
            "scientific_authority_still_required_after_enablement": True,
        },
        "validation_debt_boundary": {
            "exhaustive_python_passage_established": False,
            "reported_pre_final_repair_counts": {
                "passed": 14739,
                "failed": 147,
                "errors": 10,
                "skipped": 598,
            },
            "classification": (
                "DISCLOSED_VALIDATION_DEBT_REQUIRES_SEPARATE_"
                "MAINTENANCE_OR_VALIDATION_PACKET"
            ),
            "coherence_program_displaced_by_debt": False,
            "exception": (
                "A failure directly undermining current authority, proposal "
                "inputs, custody, generation, or native-physics surfaces must "
                "block readiness."
            ),
        },
        "claim_boundary": {
            "coherence_defined": False,
            "coherence_representation_selected": False,
            "coherence_field_selected": False,
            "program_installed": False,
            "program_authorized": False,
            "attempt_opened": False,
            "native_action_selected": False,
            "native_seam_executed": False,
            "native_pillar_executed": False,
            "observable_selected": False,
            "empirical_claim_made": False,
            "closed_program_reopened": False,
        },
        "automatic_successor_selected": False,
        "separate_authority_decision_required": True,
        "terminal_outcome": PREPARATION_OUTCOME,
        "strict_terminal_outcome": STRICT_OUTCOME,
        "verdict": (
            "BOUNDED_COHERENCE_ONTOLOGY_AND_REPRESENTATION_PROGRAM_"
            "PROPOSAL_PREPARED_NO_INSTALLATION_AUTHORIZATION_OR_EXECUTION"
        ),
    }


def main() -> int:
    return write_or_check(
        path=OUTPUT_PATH,
        build=build_calculation,
        description=(
            "ToE native coherence ontology and representation bounded "
            "program preparation"
        ),
    )


if __name__ == "__main__":
    raise SystemExit(main())
