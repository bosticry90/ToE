from __future__ import annotations

from formal.python.tools.qft_gr_quadratic_hyperbolicity_common import (
    REPO_ROOT,
    QuadraticHyperbolicityError,
    read_json,
    sha256_path,
    write_or_check,
)


CAPTURED_AT_UTC = "2026-07-29T00:00:00Z"
CALCULATION_PATH = REPO_ROOT / (
    "formal/output/CALC-TOE-NATIVE-HYPOTHESIS-FRONTIER-SELECTION-v0.json"
)
REGISTRY_PATH = REPO_ROOT / "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json"
AUTHORITY_PATH = REPO_ROOT / (
    "formal/docs/release/TOE_NATIVE_HYPOTHESIS_FRONTIER_SELECTION_"
    "AUTHORITY_PACKET_20260729_v0.json"
)
AUTHORITY_REVIEW_PATH = REPO_ROOT / (
    "formal/docs/release/TOE_NATIVE_HYPOTHESIS_FRONTIER_SELECTION_"
    "AUTHORITY_PACKET_RESULT_REVIEW_20260729_v0.json"
)
NATIVE_CLOSEOUT_PATH = REPO_ROOT / (
    "formal/output/CALC-TOE-NATIVE-SURROGATE-V0-BOUNDED-CLOSEOUT-v0.json"
)
READINESS_PATH = REPO_ROOT / (
    "formal/docs/release/SCIENCE_FIRST_PILLAR_SEAM_READINESS_v0.json"
)
REPRESENTATION_RESULT_PATH = REPO_ROOT / (
    "formal/output/CALC-TOE-NATIVE-COHERENCE-REPRESENTATION-v0.json"
)
REPRESENTATION_REVIEW_PATH = REPO_ROOT / (
    "formal/docs/release/TOE_NATIVE_COHERENCE_REPRESENTATION_"
    "V0_RESULT_REVIEW_20260729_v0.json"
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
MASTER_ACTION_FIREWALL_REVIEW_PATH = REPO_ROOT / (
    "formal/docs/release/TOE_CANDIDATE_MASTER_ACTION_CK_FIREWALL_"
    "AUTHORITY_RECONCILIATION_PACKET_REVIEW_20260717_v0.json"
)
NATIVE_GRAVITY_REVIEW_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "NATIVE_GRAVITATIONAL_PRINCIPLE_REQUIREMENTS_AND_ACTION_SELECTION_"
    "PACKET_REVIEW_20260718_v2.json"
)
PROVISIONAL_MATTER_PATH = REPO_ROOT / (
    "formal/toe_formal/ToeFormal/Derivation/"
    "QFTGRToeMatterSectorCandidateSelectionPacket.lean"
)
BOUNDED_GOVERNANCE_VALIDATOR_PATH = REPO_ROOT / (
    "formal/python/tools/bounded_program_governance.py"
)
QUADRATIC_PROGRAM_MANIFEST_PATH = REPO_ROOT / (
    "formal/docs/release/bounded_program_manifests/"
    "QFT_GR_QUADRATIC_BOUNDED_CLOSEOUT_V0_MANIFEST_v1.json"
)
NATIVE_PROGRAM_MANIFEST_PATH = REPO_ROOT / (
    "formal/docs/release/bounded_program_manifests/"
    "TOE_NATIVE_SURROGATE_V0_MANIFEST_v1.json"
)
OUTPUT_PATH = REPO_ROOT / (
    "formal/docs/release/TOE_NATIVE_HYPOTHESIS_FRONTIER_SELECTION_"
    "RESULT_REVIEW_20260729_v0.json"
)

EXPECTED_NEXT_TARGET = (
    "prepare_toe_native_coherence_ontology_and_representation_"
    "bounded_program_v0"
)
EXPECTED_PROGRAM_ID = "TOE_NATIVE_COHERENCE_ONTOLOGY_AND_REPRESENTATION_V0"
EXPECTED_HYPOTHESIS_ID = "HYP_TOE_COHERENCE_OPERATIONAL_REPRESENTABILITY_v0"
EXPECTED_MANDATORY_EXIT_TARGET = (
    "close_toe_native_coherence_ontology_and_representation_"
    "v0_after_bounded_result_v0"
)
EXPECTED_SEMANTIC_STAGE_IDS = [
    "PRESERVED_COHERENCE_CLAIM_PROVENANCE",
    "COHERENCE_OPERATIONAL_SEMANTICS",
    "COHERENCE_ONTOLOGICAL_ROLE",
    "REPRESENTATION_FAMILY_ADEQUACY",
    "REPRESENTATION_SELECTION_AND_EXIT",
]
EXPECTED_TERMINAL_OUTCOME_VOCABULARY = [
    "NATIVE_COHERENCE_REPRESENTATION_SELECTED",
    "LIMITED_COHERENCE_SURROGATE_SELECTED",
    "COHERENCE_CLASSIFIED_AS_EMERGENT_OR_NONFIELD",
    "EXPLICIT_NATIVE_COHERENCE_POSTULATE_REQUIRED",
    "EXISTING_CCFT_DEFINITION_INSUFFICIENT",
    "NO_ADMISSIBLE_COHERENCE_REPRESENTATION_FOUND",
    "COHERENCE_HYPOTHESIS_REJECTED_IN_FROZEN_SCOPE",
]


def build_review() -> dict:
    calculation = read_json(CALCULATION_PATH)
    registry = read_json(REGISTRY_PATH)
    authority = read_json(AUTHORITY_PATH)
    authority_review = read_json(AUTHORITY_REVIEW_PATH)
    native_closeout = read_json(NATIVE_CLOSEOUT_PATH)
    readiness = read_json(READINESS_PATH)
    representation = read_json(REPRESENTATION_RESULT_PATH)
    representation_review = read_json(REPRESENTATION_REVIEW_PATH)
    native_gravity_review = read_json(NATIVE_GRAVITY_REVIEW_PATH)
    firewall_review = read_json(MASTER_ACTION_FIREWALL_REVIEW_PATH)
    quadratic_manifest = read_json(QUADRATIC_PROGRAM_MANIFEST_PATH)
    native_manifest = read_json(NATIVE_PROGRAM_MANIFEST_PATH)
    coherence_text = COHERENCE_HYPOTHESIS_PATH.read_text(encoding="utf-8")
    crosswalk_text = OBJECT_CROSSWALK_PATH.read_text(encoding="utf-8")
    master_action_text = MASTER_ACTION_PATH.read_text(encoding="utf-8")
    variational_program_text = VARIATIONAL_PROGRAM_PATH.read_text(
        encoding="utf-8"
    )
    discriminator_map_text = DISCRIMINATOR_MAP_PATH.read_text(
        encoding="utf-8"
    )
    provisional_matter_text = PROVISIONAL_MATTER_PATH.read_text(
        encoding="utf-8"
    )
    governance_validator_text = BOUNDED_GOVERNANCE_VALIDATOR_PATH.read_text(
        encoding="utf-8"
    )

    candidate_matrix = calculation["candidate_matrix"]
    selected = [
        row for row in candidate_matrix if row["decision"] == "SELECT"
    ]
    proposal = calculation["future_bounded_program_proposal"]
    boundary = calculation["claim_boundary"]
    bounded_programs = registry["bounded_programs_v1"]
    quadratic = bounded_programs["QFT_GR_QUADRATIC_BOUNDED_CLOSEOUT_V0"]
    native = bounded_programs["TOE_NATIVE_SURROGATE_V0"]
    evidence_hashes_match = all(
        (REPO_ROOT / row["path"]).is_file()
        and sha256_path(REPO_ROOT / row["path"]) == row["sha256"]
        for row in calculation["evidence"].values()
    )
    independent_evidence_checks = {
        "selector_authority_is_current_or_consumed_once": (
            authority["authorized_target"]
            == "select_next_native_toe_hypothesis_for_bounded_adjudication_v0"
            and authority["program_installation_authorized_here"] is False
            and authority["scientific_calculation_authorized_here"] is False
            and authority_review["accepted"] is True
        ),
        "quadratic_program_remains_closed_reference_control": (
            quadratic["state"] == "CLOSED"
            and quadratic["toe_role"] == "REFERENCE_CONTROL_ONLY"
            and quadratic["control_result"]
            == "UNRESOLVED_AFTER_BOUNDED_ATTEMPT"
        ),
        "native_surrogate_v0_remains_closed": (
            native["state"] == "CLOSED"
            and native["blocked_stage_id"] == "COHERENCE_REPRESENTATION"
            and native["stage_2_authorized"] is False
            and native["v0_discriminator_result"]
            == "NO_UNIQUE_TOE_DISCRIMINATOR_V0"
            and native_closeout["terminal_outcome"]
            == "NO_UNIQUE_TOE_DISCRIMINATOR_V0"
        ),
        "real_scalar_route_blocked_without_continuum_crosswalk": (
            representation["terminal_result"] == "BLOCKED"
            and representation["terminal_outcome"]
            == "BLOCKED_CCFT_TO_CONTINUUM_MAP_UNRESOLVED"
            and representation_review["accepted"] is True
            and representation["claim_boundary"][
                "real_scalar_representation_derived"
            ]
            is False
        ),
        "coherence_is_candidate_not_validated": (
            "candidate mesoscopic coherence bridge layer"
            in coherence_text.lower()
            and "does not validate ccft" in coherence_text.lower()
        ),
        "object_crosswalk_is_mapping_only": (
            "maps CCFT objects to possible ToE surfaces" in crosswalk_text
            and "without claiming CCFT validation" in crosswalk_text
        ),
        "master_action_is_noncanonical": (
            "Keep the candidate bounded and non-canonical"
            in master_action_text
            and readiness["master_action_policy"]["canonicalization_allowed"]
            is False
            and readiness["master_action_policy"]["promotion_allowed"] is False
        ),
        "later_ccft_packets_remain_planning_only": (
            "Status: planning packet only." in variational_program_text
            and "Status: planning packet only." in discriminator_map_text
            and "CCFT remains candidate mesoscopic coherence bridge layer only."
            in discriminator_map_text
        ),
        "ck_action_conflict_is_only_schematically_bounded": (
            firewall_review["aggregate_organizing_surface_review"][
                "all_C_k_families_admissibility_only"
            ]
            is True
            and firewall_review["historical_action_review"][
                "contains_displayed_C_k_multiplier_term"
            ]
            is True
            and "schematic working-form" in firewall_review["claim_ceiling"]
            and "no executable native continuum action"
            in firewall_review["claim_ceiling"]
        ),
        "no_seam_is_ready_for_exploratory_entry": (
            readiness["exploratory_seam_entry_eligible_ids"] == []
            and readiness["level_5_seam_admissible_ids"] == []
            and readiness["claim_boundary"]["seam_closure_claimed"] is False
        ),
        "native_gravity_action_is_not_selected": (
            native_gravity_review["retained_results"][
                "native_candidate_readiness"
            ]
            == "BLOCKED_NO_NATIVE_GRAVITATIONAL_PRINCIPLE"
            and native_gravity_review["retained_results"]["native_principle"]
            == "NOT_IDENTIFIED"
            and native_gravity_review["retained_results"][
                "gravitational_action"
            ]
            == "NOT_PROPOSED"
        ),
        "matter_sector_is_provisional_not_native": (
            "provisional_real_scalar_field_test_sector_v0"
            in provisional_matter_text
            and "def toeNativeMatterSectorDefined : Bool := false"
            in provisional_matter_text
        ),
        "proposed_program_not_installed": (
            EXPECTED_PROGRAM_ID not in bounded_programs
        ),
        "prospective_lifecycle_support_is_not_yet_generic": (
            "PROGRAM_MANIFEST_PATHS = {" in governance_validator_text
            and "QFT_GR_QUADRATIC_BOUNDED_CLOSEOUT_V0"
            in governance_validator_text
            and "TOE_NATIVE_SURROGATE_V0" in governance_validator_text
            and EXPECTED_PROGRAM_ID not in governance_validator_text
            and quadratic_manifest["status"]
            == "IMMUTABLE_AUTHORITATIVE_PROGRAM_MANIFEST"
            and quadratic_manifest["program_id"]
            == "QFT_GR_QUADRATIC_BOUNDED_CLOSEOUT_V0"
            and native_manifest["status"]
            == "IMMUTABLE_AUTHORITATIVE_PROGRAM_MANIFEST"
            and native_manifest["program_id"] == "TOE_NATIVE_SURROGATE_V0"
        ),
    }
    checks = {
        "current_target_is_selector_or_accepted_preparation": (
            registry["current_projection_v0"]["current_target"]
            in {
                "select_next_native_toe_hypothesis_for_bounded_adjudication_v0",
                EXPECTED_NEXT_TARGET,
            }
        ),
        "producer_reported_evidence_checks_all_true": all(
            calculation["evidence_checks"].values()
        ),
        "producer_evidence_check_inventory_matches_independent_review": (
            calculation["evidence_checks"] == independent_evidence_checks
        ),
        "independent_decision_evidence_checks_pass": all(
            independent_evidence_checks.values()
        ),
        "all_evidence_paths_and_hashes_match": evidence_hashes_match,
        "four_candidate_paths_compared": (
            {row["candidate_path"] for row in candidate_matrix}
            == {
                "PILLAR_RECOVERY",
                "NATIVE_SEAM_ADJUDICATION",
                "CCFT_COHERENCE_ONTOLOGY_AND_REPRESENTATION",
                "MASTER_ACTION_RECONCILIATION",
            }
        ),
        "exactly_one_path_selected": len(selected) == 1,
        "coherence_path_is_selected": (
            len(selected) == 1
            and selected[0]["candidate_path"]
            == "CCFT_COHERENCE_ONTOLOGY_AND_REPRESENTATION"
        ),
        "hypothesis_identifier_is_exact": (
            calculation["selected_native_hypothesis"]["hypothesis_id"]
            == EXPECTED_HYPOTHESIS_ID
        ),
        "five_evidence_tensions_are_preserved": (
            len(calculation["evidence_tensions"]) == 5
            and {row["tension_id"] for row in calculation["evidence_tensions"]}
            == {
                "MASTER_ACTION_CK_ACTION_FIREWALL_CONFLICT",
                "CCFT_FIELD_ROLE_COLLISION",
                "CCFT_TO_MASTER_ACTION_FIELD_INVENTORY_GAP",
                "CCFT_ROADMAP_POPULATION_METADATA_STALE",
                "ARCHIVED_COMPLEX_FIELD_NOT_ACCEPTED_NATIVE_AUTHORITY",
            }
        ),
        "dependency_order_places_ontology_before_action_and_seams": (
            calculation["dependency_ordering"]["primary_sequence"][:4]
            == [
                "CCFT_COHERENCE_ONTOLOGY_AND_REPRESENTATION",
                "MINIMAL_NATIVE_FIELD_OR_NONFIELD_CONTENT_AND_SYMMETRIES",
                "MASTER_ACTION_RECONCILIATION",
                "NATIVE_SEAM_ADJUDICATION",
            ]
        ),
        "real_scalar_failure_is_not_reversed": (
            representation["terminal_result"] == "BLOCKED"
            and representation["claim_boundary"][
                "real_scalar_representation_derived"
            ]
            is False
            and boundary["coherence_representation_selected"] is False
            and boundary["coherence_field_type_selected"] is False
        ),
        "seam_deferral_is_evidence_bound": (
            readiness["exploratory_seam_entry_eligible_ids"] == []
            and readiness["level_5_seam_admissible_ids"] == []
        ),
        "master_action_deferral_is_evidence_bound": (
            "Keep the candidate bounded and non-canonical"
            in master_action_text
            and readiness["master_action_policy"]["promotion_allowed"] is False
        ),
        "future_program_is_proposal_only": (
            proposal["proposal_status"] == "PROPOSAL_ONLY_NOT_INSTALLED_OR_OPEN"
            and proposal["proposal_only"] is True
            and proposal["installed"] is False
            and proposal["authorized"] is False
            and proposal["open_event_created"] is False
            and proposal["program_id"] == EXPECTED_PROGRAM_ID
            and EXPECTED_PROGRAM_ID not in bounded_programs
        ),
        "future_program_proposal_shape_is_complete": (
            proposal["authorized_stage_count_proposed"] == 5
            and proposal["repair_attempt_count_proposed"] == 0
            and proposal["no_subsidiary_scientific_targets_proposed"] is True
            and proposal["mandatory_exit_target_proposed"]
            == EXPECTED_MANDATORY_EXIT_TARGET
            and len(proposal["semantic_stages_proposed"]) == 5
            and [
                row["stage_number"]
                for row in proposal["semantic_stages_proposed"]
            ]
            == [1, 2, 3, 4, 5]
            and [
                row["semantic_stage_id"]
                for row in proposal["semantic_stages_proposed"]
            ]
            == EXPECTED_SEMANTIC_STAGE_IDS
            and proposal["terminal_outcome_vocabulary_proposed"]
            == EXPECTED_TERMINAL_OUTCOME_VOCABULARY
            and proposal["installation_entry_requirements"]
            == {
                "exactly_one_coherence_claim_frozen": True,
                "support_criterion_required": True,
                "disfavor_criterion_required": True,
                "block_criterion_required": True,
                "failure_to_freeze_one_claim_closes_preparation": True,
                "scientific_authority_required_after_governance_enablement": True,
            }
        ),
        "prospective_governance_is_separate": (
            calculation["prospective_governance_prerequisite"][
                "required_before_program_installation"
            ]
            is True
            and calculation["prospective_governance_prerequisite"][
                "prospective_program_installation_status"
            ]
            == "BLOCKED_PENDING_LIFECYCLE_SAFE_GOVERNANCE_ENABLEMENT"
            and calculation["prospective_governance_prerequisite"][
                "authority_lane"
            ]
            == "SEPARATE_MAINTENANCE_AUTHORITY"
            and calculation["prospective_governance_prerequisite"][
                "program_record_created"
            ]
            is False
            and calculation["prospective_governance_prerequisite"][
                "manifest_installed"
            ]
            is False
            and calculation["prospective_governance_prerequisite"][
                "attempt_opened"
            ]
            is False
            and calculation["prospective_governance_prerequisite"][
                "scientific_program_authorization_still_required_after_maintenance"
            ]
            is True
        ),
        "prospective_governance_limitation_is_hash_bound": (
            {
                "bounded_governance_validator",
                "quadratic_program_manifest",
                "native_surrogate_program_manifest",
            }
            <= set(calculation["evidence"])
        ),
        "closed_programs_are_not_reopened": (
            bounded_programs["QFT_GR_QUADRATIC_BOUNDED_CLOSEOUT_V0"][
                "state"
            ]
            == "CLOSED"
            and bounded_programs["TOE_NATIVE_SURROGATE_V0"]["state"]
            == "CLOSED"
            and boundary["closed_programs_reopened"] is False
        ),
        "no_program_or_physics_execution_is_smuggled_in": (
            boundary["new_bounded_program_installed"] is False
            and boundary["new_attempt_opened"] is False
            and boundary["native_field_content_selected"] is False
            and boundary["native_action_selected"] is False
            and boundary["native_interaction_selected"] is False
            and boundary["pillar_or_seam_calculation_executed"] is False
        ),
        "selected_next_target_is_preparation_only": (
            calculation["selected_next_target"] == EXPECTED_NEXT_TARGET
        ),
        "terminal_outcome_is_authorized": (
            calculation["terminal_outcome"]
            == "SELECT_CCFT_COHERENCE_ONTOLOGY_AND_REPRESENTATION"
        ),
    }
    failed = sorted(name for name, passed in checks.items() if not passed)
    if failed:
        raise QuadraticHyperbolicityError(
            f"native-hypothesis frontier selection review failed: {failed}"
        )

    return {
        "schema_id": (
            "TOE_NATIVE_HYPOTHESIS_FRONTIER_SELECTION_"
            "RESULT_REVIEW_20260729_v0"
        ),
        "captured_at_utc": CAPTURED_AT_UTC,
        "reviewed_calculation": {
            "path": CALCULATION_PATH.relative_to(REPO_ROOT).as_posix(),
            "sha256": sha256_path(CALCULATION_PATH),
        },
        "checks": checks,
        "failed_checks": failed,
        "accepted": True,
        "selection_outcome": (
            "SELECT_CCFT_COHERENCE_ONTOLOGY_AND_REPRESENTATION"
        ),
        "terminal_outcome": (
            "SELECT_CCFT_COHERENCE_ONTOLOGY_AND_REPRESENTATION"
        ),
        "selected_hypothesis_id": EXPECTED_HYPOTHESIS_ID,
        "selected_next_target": EXPECTED_NEXT_TARGET,
        "program_installation_authorized": False,
        "scientific_stage_open_authorized": False,
        "claim_ceiling": (
            "PROGRAM_PREPARATION_ONLY_NO_PROGRAM_INSTALLATION_FIELD_ACTION_"
            "SEAM_PILLAR_OR_EMPIRICAL_CLAIM"
        ),
        "verdict": (
            "NATIVE_HYPOTHESIS_FRONTIER_SELECTION_ACCEPTED_COHERENCE_"
            "ONTOLOGY_AND_REPRESENTATION_PROGRAM_PREPARATION_SELECTED"
        ),
    }


def main() -> int:
    return write_or_check(
        path=OUTPUT_PATH,
        build=build_review,
        description="native-hypothesis frontier selection result review",
    )


if __name__ == "__main__":
    raise SystemExit(main())
