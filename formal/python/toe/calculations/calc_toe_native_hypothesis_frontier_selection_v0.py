from __future__ import annotations

from formal.python.tools.qft_gr_quadratic_hyperbolicity_common import (
    REPO_ROOT,
    QuadraticHyperbolicityError,
    read_json,
    sha256_path,
    write_or_check,
)


CAPTURED_AT_UTC = "2026-07-29T00:00:00Z"
EXECUTION_TARGET = "select_next_native_toe_hypothesis_for_bounded_adjudication_v0"
SELECTED_NEXT_TARGET = (
    "prepare_toe_native_coherence_ontology_and_representation_"
    "bounded_program_v0"
)
SELECTED_HYPOTHESIS_ID = "HYP_TOE_COHERENCE_OPERATIONAL_REPRESENTABILITY_v0"
PROPOSED_PROGRAM_ID = (
    "TOE_NATIVE_COHERENCE_ONTOLOGY_AND_REPRESENTATION_V0"
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
COHERENCE_REPRESENTATION_RESULT_PATH = REPO_ROOT / (
    "formal/output/CALC-TOE-NATIVE-COHERENCE-REPRESENTATION-v0.json"
)
COHERENCE_REPRESENTATION_REVIEW_PATH = REPO_ROOT / (
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
MASTER_ACTION_GAP_REVIEW_PATH = REPO_ROOT / (
    "formal/docs/release/MASTER_ACTION_DEPENDENCY_GAP_PACKET_"
    "RESULT_REVIEW_20260503_v0.json"
)
READINESS_PATH = REPO_ROOT / (
    "formal/docs/release/SCIENCE_FIRST_PILLAR_SEAM_READINESS_v0.json"
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
    "formal/output/CALC-TOE-NATIVE-HYPOTHESIS-FRONTIER-SELECTION-v0.json"
)

EVIDENCE_PATHS = {
    "selector_authority": AUTHORITY_PATH,
    "selector_authority_review": AUTHORITY_REVIEW_PATH,
    "native_surrogate_closeout": NATIVE_CLOSEOUT_PATH,
    "real_scalar_representation_attempt": COHERENCE_REPRESENTATION_RESULT_PATH,
    "real_scalar_representation_review": COHERENCE_REPRESENTATION_REVIEW_PATH,
    "coherence_admissibility_hypothesis": COHERENCE_HYPOTHESIS_PATH,
    "ccft_to_toe_object_crosswalk": OBJECT_CROSSWALK_PATH,
    "ccft_variational_program": VARIATIONAL_PROGRAM_PATH,
    "ccft_discriminator_map": DISCRIMINATOR_MAP_PATH,
    "candidate_master_action": MASTER_ACTION_PATH,
    "master_action_ck_firewall_review": MASTER_ACTION_FIREWALL_REVIEW_PATH,
    "master_action_dependency_gap_review": MASTER_ACTION_GAP_REVIEW_PATH,
    "pillar_seam_readiness": READINESS_PATH,
    "native_gravity_action_selection_review": NATIVE_GRAVITY_REVIEW_PATH,
    "provisional_matter_sector": PROVISIONAL_MATTER_PATH,
    "bounded_governance_validator": BOUNDED_GOVERNANCE_VALIDATOR_PATH,
    "quadratic_program_manifest": QUADRATIC_PROGRAM_MANIFEST_PATH,
    "native_surrogate_program_manifest": NATIVE_PROGRAM_MANIFEST_PATH,
}


def _evidence_records() -> dict[str, dict[str, str]]:
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
    if projection["current_target"] not in {
        EXECUTION_TARGET,
        SELECTED_NEXT_TARGET,
    }:
        raise QuadraticHyperbolicityError(
            "native-hypothesis frontier selector is not authoritative"
        )

    authority = read_json(AUTHORITY_PATH)
    authority_review = read_json(AUTHORITY_REVIEW_PATH)
    native_closeout = read_json(NATIVE_CLOSEOUT_PATH)
    representation_result = read_json(COHERENCE_REPRESENTATION_RESULT_PATH)
    representation_review = read_json(COHERENCE_REPRESENTATION_REVIEW_PATH)
    readiness = read_json(READINESS_PATH)
    native_gravity_review = read_json(NATIVE_GRAVITY_REVIEW_PATH)
    firewall_review = read_json(MASTER_ACTION_FIREWALL_REVIEW_PATH)
    coherence_text = COHERENCE_HYPOTHESIS_PATH.read_text(encoding="utf-8")
    crosswalk_text = OBJECT_CROSSWALK_PATH.read_text(encoding="utf-8")
    master_action_text = MASTER_ACTION_PATH.read_text(encoding="utf-8")
    variational_program_text = VARIATIONAL_PROGRAM_PATH.read_text(
        encoding="utf-8"
    )
    discriminator_map_text = DISCRIMINATOR_MAP_PATH.read_text(
        encoding="utf-8"
    )
    provisional_matter_text = PROVISIONAL_MATTER_PATH.read_text(encoding="utf-8")
    governance_validator_text = BOUNDED_GOVERNANCE_VALIDATOR_PATH.read_text(
        encoding="utf-8"
    )
    quadratic_manifest = read_json(QUADRATIC_PROGRAM_MANIFEST_PATH)
    native_manifest = read_json(NATIVE_PROGRAM_MANIFEST_PATH)

    closed_programs = registry["bounded_programs_v1"]
    quadratic = closed_programs["QFT_GR_QUADRATIC_BOUNDED_CLOSEOUT_V0"]
    native = closed_programs["TOE_NATIVE_SURROGATE_V0"]
    checks = {
        "selector_authority_is_current_or_consumed_once": (
            authority["authorized_target"] == EXECUTION_TARGET
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
            representation_result["terminal_result"] == "BLOCKED"
            and representation_result["terminal_outcome"]
            == "BLOCKED_CCFT_TO_CONTINUUM_MAP_UNRESOLVED"
            and representation_review["accepted"] is True
            and representation_result["claim_boundary"][
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
            "maps CCFT objects to possible ToE surfaces"
            in crosswalk_text
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
            and "schematic working-form"
            in firewall_review["claim_ceiling"]
            and "no executable native continuum action"
            in firewall_review["claim_ceiling"]
        ),
        "no_seam_is_ready_for_exploratory_entry": (
            readiness["exploratory_seam_entry_eligible_ids"] == []
            and readiness["level_5_seam_admissible_ids"] == []
            and readiness["claim_boundary"]["seam_closure_claimed"] is False
        ),
        "native_gravity_action_is_not_selected": (
            native_gravity_review["retained_results"]["native_candidate_readiness"]
            == "BLOCKED_NO_NATIVE_GRAVITATIONAL_PRINCIPLE"
            and native_gravity_review["retained_results"]["native_principle"]
            == "NOT_IDENTIFIED"
            and native_gravity_review["retained_results"]["gravitational_action"]
            == "NOT_PROPOSED"
        ),
        "matter_sector_is_provisional_not_native": (
            "provisional_real_scalar_field_test_sector_v0"
            in provisional_matter_text
            and "def toeNativeMatterSectorDefined : Bool := false"
            in provisional_matter_text
        ),
        "proposed_program_not_installed": (
            PROPOSED_PROGRAM_ID not in closed_programs
        ),
        "prospective_lifecycle_support_is_not_yet_generic": (
            "PROGRAM_MANIFEST_PATHS = {" in governance_validator_text
            and "QFT_GR_QUADRATIC_BOUNDED_CLOSEOUT_V0"
            in governance_validator_text
            and "TOE_NATIVE_SURROGATE_V0" in governance_validator_text
            and PROPOSED_PROGRAM_ID not in governance_validator_text
            and quadratic_manifest["status"]
            == "IMMUTABLE_AUTHORITATIVE_PROGRAM_MANIFEST"
            and quadratic_manifest["program_id"]
            == "QFT_GR_QUADRATIC_BOUNDED_CLOSEOUT_V0"
            and native_manifest["status"]
            == "IMMUTABLE_AUTHORITATIVE_PROGRAM_MANIFEST"
            and native_manifest["program_id"] == "TOE_NATIVE_SURROGATE_V0"
        ),
    }
    failed = sorted(name for name, passed in checks.items() if not passed)
    if failed:
        raise QuadraticHyperbolicityError(
            f"native-hypothesis frontier selection failed: {failed}"
        )

    candidate_matrix = [
        {
            "candidate_path": "CCFT_COHERENCE_ONTOLOGY_AND_REPRESENTATION",
            "decision": "SELECT",
            "selection_status": "SELECTED",
            "native_hypothesis_id": SELECTED_HYPOTHESIS_ID,
            "readiness": "READY_FOR_BOUNDED_ONTOLOGY_ADJUDICATION_ONLY",
            "native_distance": "DIRECT_NATIVE_HYPOTHESIS_ADJUDICATION",
            "evidence_status": (
                "CANDIDATE_OBJECTS_EXIST_BUT_OPERATIONAL_ONTOLOGY_AND_"
                "CROSSWALK_ARE_UNRESOLVED"
            ),
            "reason": (
                "The repository preserves coherence as a distinctive candidate "
                "concept, but the failed real-scalar route shows that its "
                "operational meaning and mathematical type remain the earliest "
                "unresolved native dependency."
            ),
        },
        {
            "candidate_path": "MASTER_ACTION_RECONCILIATION",
            "decision": "DEFER",
            "selection_status": "NOT_SELECTED",
            "readiness": "BLOCKED_BY_NATIVE_OBJECT_AND_PRINCIPLE_SELECTION",
            "native_distance": "DOWNSTREAM_OF_ONTOLOGY",
            "evidence_status": (
                "SCHEMATIC_NONCANONICAL_NONEXECUTABLE_WITH_CK_ROLE_TENSION"
            ),
            "reason": (
                "The candidate master action is explicitly noncanonical, and "
                "neither a native coherence representation nor a native "
                "gravitational principle has been selected."
            ),
        },
        {
            "candidate_path": "NATIVE_SEAM_ADJUDICATION",
            "decision": "DEFER",
            "selection_status": "NOT_SELECTED",
            "readiness": "BLOCKED_BY_UNDEFINED_NATIVE_ENDPOINTS",
            "native_distance": "DOWNSTREAM_OF_ONTOLOGY_AND_ACTION",
            "evidence_status": (
                "ZERO_ELIGIBLE_SEAMS_IN_BOUND_READINESS_SNAPSHOT"
            ),
            "reason": (
                "The bound 2026-07-09 readiness snapshot reports no seam "
                "eligible for exploratory entry, and a native seam cannot be "
                "closed before the native objects on both sides are defined."
            ),
        },
        {
            "candidate_path": "PILLAR_RECOVERY",
            "decision": "SUPPORTING_WORK_ONLY",
            "selection_status": "NOT_SELECTED",
            "readiness": "REFERENCE_BASELINES_AVAILABLE",
            "native_distance": "DOWNSTREAM_OR_CONTROL_SUPPORT",
            "evidence_status": (
                "KNOWN_PHYSICS_CONTROL_AND_PARTIAL_READINESS_AVAILABLE"
            ),
            "reason": (
                "Known-physics pillar controls remain useful, but without a "
                "native field content or action they cannot yet adjudicate what "
                "is distinctive about the ToE."
            ),
        },
    ]
    selected = [
        row for row in candidate_matrix if row["decision"] == "SELECT"
    ]
    if len(selected) != 1:
        raise QuadraticHyperbolicityError(
            "selector must produce exactly one selected native path"
        )

    stages = [
        {
            "stage_number": 1,
            "semantic_stage_id": "PRESERVED_COHERENCE_CLAIM_PROVENANCE",
            "question": (
                "Which single preserved ToE or CCFT coherence claim will be "
                "frozen for bounded native adjudication, and what is its "
                "evidence status?"
            ),
        },
        {
            "stage_number": 2,
            "semantic_stage_id": "COHERENCE_OPERATIONAL_SEMANTICS",
            "question": (
                "What observable or operational distinctions are meant by "
                "coherence, zero coherence, change, transport, and scale?"
            ),
        },
        {
            "stage_number": 3,
            "semantic_stage_id": "COHERENCE_ONTOLOGICAL_ROLE",
            "question": (
                "Is coherence fundamental, emergent, relational, statistical, "
                "effective, or not an independent physical object?"
            ),
        },
        {
            "stage_number": 4,
            "semantic_stage_id": "REPRESENTATION_FAMILY_ADEQUACY",
            "question": (
                "Which representation families can express the frozen semantics "
                "without assuming a field type, action, or interaction in advance?"
            ),
        },
        {
            "stage_number": 5,
            "semantic_stage_id": "REPRESENTATION_SELECTION_AND_EXIT",
            "question": (
                "Select one bounded representation, select a limited surrogate, "
                "classify coherence as nonfield/emergent, or close without one."
            ),
        },
    ]

    return {
        "schema_id": "CALC_TOE_NATIVE_HYPOTHESIS_FRONTIER_SELECTION_v0",
        "calculation_id": (
            "CALC-TOE-NATIVE-HYPOTHESIS-FRONTIER-SELECTION-v0"
        ),
        "captured_at_utc": CAPTURED_AT_UTC,
        "execution_target": EXECUTION_TARGET,
        "native_hypothesis_tested": "NONE_GOVERNANCE_ONLY",
        "scientific_calculation_executed": False,
        "program_installation_executed": False,
        "closed_programs_reopened": False,
        "authority": {
            "path": AUTHORITY_PATH.relative_to(REPO_ROOT).as_posix(),
            "sha256": sha256_path(AUTHORITY_PATH),
            "review_path": AUTHORITY_REVIEW_PATH.relative_to(
                REPO_ROOT
            ).as_posix(),
            "review_sha256": sha256_path(AUTHORITY_REVIEW_PATH),
        },
        "evidence": _evidence_records(),
        "evidence_checks": checks,
        "evidence_findings": {
            "ccft_status": "CANDIDATE_MESOSCOPIC_LINKAGE_LAYER_ONLY",
            "accepted_real_scalar_crosswalk_exists": False,
            "accepted_complex_field_crosswalk_exists": False,
            "coherence_operational_ontology_selected": False,
            "native_matter_sector_selected": False,
            "native_gravitational_principle_selected": False,
            "executable_native_master_action_exists": False,
            "exploratory_seam_entry_eligible_count_in_bound_readiness_snapshot": 0,
            "level_5_seam_admissible_count_in_bound_readiness_snapshot": 0,
        },
        "evidence_tensions": [
            {
                "tension_id": "MASTER_ACTION_CK_ACTION_FIREWALL_CONFLICT",
                "status": "RESOLVED_ONLY_TO_SCHEMATIC_NONEXECUTABLE_STATUS",
                "finding": (
                    "The historical working-form action displays multiplier "
                    "terms for C_k while accepted later policy keeps every C_k "
                    "family admissibility-only and refuses action variation."
                ),
                "selection_effect": (
                    "MASTER_ACTION_RECONCILIATION_IS_DOWNSTREAM_AND_NOT_SELECTED"
                ),
            },
            {
                "tension_id": "CCFT_FIELD_ROLE_COLLISION",
                "status": "UNRESOLVED",
                "finding": (
                    "Historical CCFT candidate prose assigns distinct amplitude "
                    "and phase-gradient roles to a complex field, while the "
                    "repository also uses scalar symbols for provisional matter "
                    "and the failed real-scalar coherence proposal."
                ),
                "selection_effect": (
                    "ONTOLOGY_AND_SYMBOL_ROLE_ADJUDICATION_REQUIRED_BEFORE_"
                    "FIELD_SELECTION"
                ),
            },
            {
                "tension_id": "CCFT_TO_MASTER_ACTION_FIELD_INVENTORY_GAP",
                "status": "UNRESOLVED",
                "finding": (
                    "Candidate CCFT objects do not yet have an accepted transport "
                    "into an executable native master-action field inventory."
                ),
                "selection_effect": (
                    "MASTER_ACTION_RECONCILIATION_MUST_FOLLOW_OBJECT_SELECTION"
                ),
            },
            {
                "tension_id": "CCFT_ROADMAP_POPULATION_METADATA_STALE",
                "status": "STALE_METADATA_ONLY",
                "finding": (
                    "Early roadmap population prose predates later planning "
                    "artifacts and cannot serve as current completion evidence."
                ),
                "selection_effect": (
                    "DO_NOT_USE_EARLY_POPULATION_COUNT_AS_CURRENT_STATUS"
                ),
            },
            {
                "tension_id": "ARCHIVED_COMPLEX_FIELD_NOT_ACCEPTED_NATIVE_AUTHORITY",
                "status": "PROVENANCE_BOUNDARY",
                "finding": (
                    "The preserved complex-field description remains historical "
                    "candidate material and is not native scientific authority."
                ),
                "selection_effect": (
                    "NO_REAL_OR_COMPLEX_FIELD_MAY_BE_SELECTED_BY_THIS_SELECTOR"
                ),
            },
        ],
        "candidate_matrix": candidate_matrix,
        "dependency_ordering": {
            "primary_sequence": [
                "CCFT_COHERENCE_ONTOLOGY_AND_REPRESENTATION",
                "MINIMAL_NATIVE_FIELD_OR_NONFIELD_CONTENT_AND_SYMMETRIES",
                "MASTER_ACTION_RECONCILIATION",
                "NATIVE_SEAM_ADJUDICATION",
                "PILLAR_RECOVERY_AND_BENCHMARKING",
                "OBSERVABLE_AND_DISTINCTIVENESS",
            ],
            "parallel_support_only": [
                "KNOWN_PHYSICS_PILLAR_BASELINE_CATALOG",
                "UNIT_AND_CONVENTION_TOOLING",
                "STANDARD_COMPARATOR_PRESERVATION",
            ],
        },
        "selected_native_hypothesis": {
            "hypothesis_id": SELECTED_HYPOTHESIS_ID,
            "statement": (
                "At least one central preserved ToE coherence claim may admit "
                "a controlled operational meaning and a minimal mathematical "
                "representation, without assuming in advance that coherence is "
                "a scalar, field, fundamental object, or action term."
            ),
            "selected_path": (
                "CCFT_COHERENCE_ONTOLOGY_AND_REPRESENTATION"
            ),
            "selected_as_true": False,
            "representation_selected": False,
            "field_selected": False,
            "action_selected": False,
            "selection_outcome": (
                "SELECT_CCFT_COHERENCE_ONTOLOGY_AND_REPRESENTATION"
            ),
        },
        "future_bounded_program_proposal": {
            "proposal_status": "PROPOSAL_ONLY_NOT_INSTALLED_OR_OPEN",
            "proposal_only": True,
            "installed": False,
            "authorized": False,
            "open_event_created": False,
            "program_id": PROPOSED_PROGRAM_ID,
            "authorized_stage_count_proposed": 5,
            "repair_attempt_count_proposed": 0,
            "no_subsidiary_scientific_targets_proposed": True,
            "mandatory_exit_target_proposed": (
                "close_toe_native_coherence_ontology_and_representation_"
                "v0_after_bounded_result_v0"
            ),
            "semantic_stages_proposed": stages,
            "terminal_outcome_vocabulary_proposed": [
                "NATIVE_COHERENCE_REPRESENTATION_SELECTED",
                "LIMITED_COHERENCE_SURROGATE_SELECTED",
                "COHERENCE_CLASSIFIED_AS_EMERGENT_OR_NONFIELD",
                "EXPLICIT_NATIVE_COHERENCE_POSTULATE_REQUIRED",
                "EXISTING_CCFT_DEFINITION_INSUFFICIENT",
                "NO_ADMISSIBLE_COHERENCE_REPRESENTATION_FOUND",
                "COHERENCE_HYPOTHESIS_REJECTED_IN_FROZEN_SCOPE",
            ],
            "installation_entry_requirements": {
                "exactly_one_coherence_claim_frozen": True,
                "support_criterion_required": True,
                "disfavor_criterion_required": True,
                "block_criterion_required": True,
                "failure_to_freeze_one_claim_closes_preparation": True,
                "scientific_authority_required_after_governance_enablement": True,
            },
        },
        "prospective_governance_prerequisite": {
            "required_before_program_installation": True,
            "prospective_program_installation_status": (
                "BLOCKED_PENDING_LIFECYCLE_SAFE_GOVERNANCE_ENABLEMENT"
            ),
            "maintenance_prerequisite": (
                "PROSPECTIVE_BOUNDED_PROGRAM_LIFECYCLE_ENABLEMENT_REQUIRED"
            ),
            "reason": (
                "The current bounded-program validator enforces the two closed "
                "historical v1 manifests. Installing a new prospective program "
                "first requires separately authorized generic lifecycle-safe "
                "manifest support with immutable predeclared stage envelopes "
                "and Git chronology. That maintenance enablement is necessary "
                "but is not scientific authorization to install or open the "
                "proposed coherence program."
            ),
            "authority_lane": "SEPARATE_MAINTENANCE_AUTHORITY",
            "scientific_authority_preserved_during_maintenance": True,
            "program_record_created": False,
            "manifest_installed": False,
            "attempt_opened": False,
            "scientific_program_authorization_still_required_after_maintenance": (
                True
            ),
        },
        "claim_boundary": {
            "closed_programs_reopened": False,
            "new_bounded_program_installed": False,
            "new_attempt_opened": False,
            "coherence_representation_selected": False,
            "coherence_field_type_selected": False,
            "native_field_content_selected": False,
            "native_action_selected": False,
            "native_interaction_selected": False,
            "pillar_or_seam_calculation_executed": False,
            "ccft_validated": False,
            "master_action_promoted": False,
            "empirical_claim_made": False,
            "full_toe_claim_made": False,
        },
        "nonclaims": [
            "no real or complex coherence field selected",
            "no closed program reopened",
            "no new bounded program installed or opened",
            "no native action or interaction selected",
            "no C_k action embedding or variation",
            "no pillar or seam calculation",
            "no CCFT validation",
            "no master-action promotion",
            "no empirical validation",
            "no unique ToE discriminator",
            "no completed ToE claim",
        ],
        "terminal_outcome": (
            "SELECT_CCFT_COHERENCE_ONTOLOGY_AND_REPRESENTATION"
        ),
        "selected_next_target": SELECTED_NEXT_TARGET,
        "verdict": (
            "SELECTED_CCFT_COHERENCE_ONTOLOGY_AND_REPRESENTATION_"
            "PROGRAM_PREPARATION_ONLY_NO_PROGRAM_INSTALLATION_OR_FIELD_SELECTION"
        ),
    }


def main() -> int:
    return write_or_check(
        path=OUTPUT_PATH,
        build=build_calculation,
        description="ToE native-hypothesis frontier selection",
    )


if __name__ == "__main__":
    raise SystemExit(main())
