from __future__ import annotations

from formal.python.tools.bounded_program_governance import scope_hash
from formal.python.tools.qft_gr_quadratic_hyperbolicity_common import (
    REPO_ROOT,
    read_json,
    sha256_path,
    write_or_check,
)


CAPTURED_AT_UTC = "2026-07-30T00:00:00Z"
EXECUTION_TARGET = (
    "prepare_toe_repository_wide_native_hypothesis_evidence_census_"
    "bounded_program_v0"
)
PROGRAM_ID = "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_EVIDENCE_CENSUS_V0"
MANDATORY_EXIT_TARGET = (
    "close_toe_repository_wide_native_hypothesis_evidence_census_"
    "v0_after_bounded_result_v0"
)
OUTCOME = (
    "REPOSITORY_WIDE_NATIVE_HYPOTHESIS_EVIDENCE_CENSUS_BOUNDED_"
    "PROGRAM_PROPOSAL_PREPARED"
)
STRICT_OUTCOME = (
    "PROPOSAL_ONLY_NOT_INSTALLED_AUTHORIZED_OR_OPEN_NO_ARCHIVE_ADOPTION_"
    "HYPOTHESIS_PROMOTION_FIELD_ACTION_SEAM_OBSERVABLE_OR_AUTOMATIC_SUCCESSOR"
)

SCOPE_RESULT_PATH = REPO_ROOT / (
    "formal/output/"
    "CALC-TOE-NATIVE-COHERENCE-AUTHORIZED-EVIDENCE-SCOPE-"
    "QUALIFICATION-v0.json"
)
SCOPE_REVIEW_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "TOE_NATIVE_COHERENCE_AUTHORIZED_EVIDENCE_SCOPE_QUALIFICATION_"
    "RESULT_REVIEW_20260730_v0.json"
)
ARCHIVE_INDEX_PATH = REPO_ROOT / "formal/output/archive_intake_index.json"
ARCHIVE_RANKING_PATH = REPO_ROOT / "formal/output/archive_candidate_ranking.json"
ARCHIVE_TOOL_PATH = REPO_ROOT / "formal/python/tools/archive_intake_index.py"
ARCHIVE_POLICY_PATH = REPO_ROOT / (
    "formal/docs/release/SR_M5_ARCHIVE_RETENTION_POLICY_v0.md"
)
PREINSTALLATION_CONTROLS_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_EVIDENCE_CENSUS_"
    "PREINSTALLATION_CONTROLS_20260730_v0.json"
)
OUTPUT_PATH = REPO_ROOT / (
    "formal/output/"
    "CALC-TOE-REPOSITORY-WIDE-NATIVE-HYPOTHESIS-EVIDENCE-CENSUS-"
    "BOUNDED-PROGRAM-PREPARATION-v0.json"
)

EVIDENCE_PATHS = {
    "coherence_scope_qualification": SCOPE_RESULT_PATH,
    "coherence_scope_qualification_review": SCOPE_REVIEW_PATH,
    "archive_intake_index": ARCHIVE_INDEX_PATH,
    "archive_candidate_ranking": ARCHIVE_RANKING_PATH,
    "archive_intake_tool": ARCHIVE_TOOL_PATH,
    "archive_retention_policy": ARCHIVE_POLICY_PATH,
    "preinstallation_controls": PREINSTALLATION_CONTROLS_PATH,
}

SOURCE_AUTHORITY_VOCABULARY = [
    "CURRENT_CANONICAL",
    "CURRENT_NONCANONICAL",
    "HISTORICAL_AUTHORITATIVE_AT_TIME",
    "SUPERSEDED",
    "REJECTED",
    "QUARANTINED",
    "SPECULATIVE_NOTE",
    "GENERATED_SUMMARY",
    "DUPLICATE",
    "EXTERNAL_EVIDENCE",
    "UNKNOWN_PROVENANCE",
]

CLAIM_DOMAINS = [
    "ONTOLOGY",
    "PILLARS",
    "SEAMS",
    "CCFT",
    "MASTER_ACTION",
    "BRIDGE_CONDITIONS",
    "GRAVITY",
    "MATTER",
    "QUANTUM_STRUCTURE",
    "EMERGENCE",
    "THERMODYNAMICS",
    "SCALE_HIERARCHY",
    "OBSERVABLES",
    "PREDICTIONS",
    "FALSIFICATION",
]

SEAM_CLASSES = [
    "CONCEPTUAL_RELATION",
    "ADMISSIBILITY_CONDITION",
    "SOURCE_MAP",
    "LIMITING_PROCEDURE",
    "VARIATIONAL_COUPLING",
    "EQUIVALENCE_THEOREM",
    "COMPUTED_BRIDGE",
    "UNRESOLVED_PROPOSAL",
]

FRONTIER_CLASSES = [
    "READY_FOR_BOUNDED_TEST",
    "READY_AFTER_ONE_DEFINITION",
    "READY_AFTER_ONE_DERIVATION",
    "HISTORICAL_ONLY",
    "CONTROL_MODEL_ONLY",
    "BLOCKED_BY_CONFLICT",
    "BLOCKED_BY_MISSING_EVIDENCE",
    "REJECTED",
]

ARCHIVE_ASSESSMENT_OUTCOMES = [
    "ARCHIVE_CONTAINS_NEW_OPERATIONAL_COHERENCE_EVIDENCE",
    "ARCHIVE_CONTAINS_RELEVANT_BUT_STILL_NONOPERATIONAL_MATERIAL",
    "ARCHIVE_CONTAINS_ONLY_DUPLICATE_OR_SUPERSEDED_CLAIMS",
    "ARCHIVE_CENSUS_INCOMPLETE",
    "NO_NEW_MATERIAL_EVIDENCE_FOUND",
]

SUPPLEMENTAL_ARCHIVE_ROOTS = [
    {
        "path": "archive/ToE_Project",
        "intake_status": "PRESENT_LOCALLY_PENDING_CANONICAL_REINDEX",
        "scientific_status": "UNADJUDICATED",
    },
    {
        "path": "archive/ToE_Project_Starter_2025-09-24",
        "intake_status": "PRESENT_LOCALLY_PENDING_CANONICAL_REINDEX",
        "scientific_status": "UNADJUDICATED",
    },
]

PROGRAM_TERMINAL_OUTCOMES = [
    "NATIVE_HYPOTHESIS_GRAPH_AND_FRONTIER_READY",
    "EVIDENCE_FOUND_BUT_RECONCILIATION_BLOCKED",
    "REPOSITORY_WIDE_EVIDENCE_CENSUS_INCOMPLETE",
    "NO_TEST_READY_NATIVE_HYPOTHESIS_FOUND",
]


def _scope(
    stage_id: str,
    question: str,
    inputs: list[str],
    outputs: list[str],
    prohibited: list[str],
    dependencies: list[str],
    outcomes: list[str],
) -> dict:
    return {
        "semantic_stage_id": stage_id,
        "normalized_scientific_question": question,
        "authorized_inputs": inputs,
        "required_outputs": outputs,
        "prohibited_claims": prohibited,
        "dependency_artifact_ids": dependencies,
        "terminal_outcome_vocabulary": outcomes,
    }


def _stage(
    number: int,
    stage_id: str,
    target: str,
    question: str,
    outputs: list[str],
    outcomes: list[str],
) -> dict:
    common_inputs = [
        "current_tracked_repository",
        "archive_tree_read_only",
        "archive/ToE_Project_read_only_pending_canonical_reindex",
        (
            "archive/ToE_Project_Starter_2025-09-24_"
            "read_only_pending_canonical_reindex"
        ),
        "current_canonical_authority_surfaces",
        "preinstallation_controls_v0",
        "formal_outputs_and_release_records",
        "calculation_and_validation_sources",
        "Lean_modules",
        "quarantine_dossiers",
        "monographs_theory_specifications_and_historical_notes",
    ]
    common_prohibited = [
        "automatic archive adoption",
        "authority promotion without independent review",
        "claim truth from repetition or symbolic similarity",
        "field or representation selection",
        "master-action construction",
        "seam execution",
        "empirical validation",
        "completed ToE",
    ]
    canonical_scope = _scope(
        stage_id,
        question,
        common_inputs,
        outputs,
        common_prohibited,
        list(EVIDENCE_PATHS),
        outcomes,
    )
    return {
        "stage_number": number,
        "semantic_stage_id": stage_id,
        "canonical_target": target,
        "canonical_scope": canonical_scope,
        "canonical_scope_hash": scope_hash(canonical_scope),
        "proposed_open_event_scope": {
            "event_type": "ATTEMPT_OPEN",
            "substantive_stage_output_allowed": False,
            "producer_may_run_before_open_commit": False,
            "required_atomic_contents": [
                "immutable_OPEN_event",
                "registry_projection_update",
                "generated_authority_surfaces",
                "Lean_authority_mirrors",
            ],
        },
        "proposed_close_event_scope": {
            "event_type": "ATTEMPT_CLOSE",
            "block_or_failure_requires_mandatory_exit": True,
            "required_atomic_contents": [
                "stage_result_or_failed_closed_result",
                "independent_result_review",
                "immutable_CLOSE_event",
                "registry_and_authority_transition",
                "validation_record",
            ],
            "terminal_outcomes": outcomes,
        },
    }


def _stages() -> list[dict]:
    return [
        _stage(
            1,
            "REPOSITORY_WIDE_SOURCE_CENSUS",
            "inventory_toe_repository_wide_native_hypothesis_sources_v0",
            (
                "Which repository and archive files may contain substantive "
                "native-ToE hypotheses, derivations, bridge claims, or "
                "predictions, and what are their custody and authority states?"
            ),
            [
                "path_hash_date_provenance_authority_catalog",
                "domain_relevance_scores",
                "machine_generated_and_binary_exclusion_ledger",
                "deep_review_candidate_set_selected_by_explicit_gates",
                "archive_specific_evidence_assessment",
            ],
            [
                "REPOSITORY_WIDE_SOURCE_CENSUS_COMPLETE",
                "REPOSITORY_WIDE_SOURCE_CENSUS_COMPLETE_WITH_GAPS",
                (
                    "REPOSITORY_WIDE_SOURCE_CENSUS_COMPLETE_WITH_"
                    "LOCAL_CUSTODY_LIMITATIONS"
                ),
                "SOURCE_ROOT_SNAPSHOT_STABLE",
                "SOURCE_ROOT_MUTATED_DURING_CENSUS",
                "REPOSITORY_WIDE_SOURCE_CENSUS_INCOMPLETE",
                "SOURCE_ROOT_UNAVAILABLE",
                "SOURCE_DISCOVERY_OR_PROVENANCE_BLOCKED",
                "CUSTODY_OR_PROVENANCE_BLOCKED",
                "DETERMINISTIC_INDEX_GENERATION_FAILED",
            ],
        ),
        _stage(
            2,
            "DEDUPLICATION_AND_LINEAGE_RECONSTRUCTION",
            "reconstruct_toe_native_hypothesis_source_lineages_v0",
            (
                "Which candidate sources are duplicates, revisions, generated "
                "copies, summaries, superseded descendants, parallel lineages, "
                "or contradictory descendants?"
            ),
            [
                "exact_and_near_duplicate_groups",
                "revision_and_derivation_lineages",
                "source_to_summary_provenance_edges",
                "supersession_and_contradiction_ledger",
                "independent_source_count",
            ],
            [
                "SOURCE_LINEAGES_RECONSTRUCTED",
                "SOURCE_LINEAGES_RECONSTRUCTED_WITH_AMBIGUITIES",
                "SOURCE_LINEAGE_RECONSTRUCTION_BLOCKED",
            ],
        ),
        _stage(
            3,
            "NATIVE_CLAIM_EXTRACTION_AND_CLASSIFICATION",
            "extract_and_classify_toe_repository_wide_native_hypothesis_claims_v0",
            (
                "What source-bound native ontology, pillar, seam, action, "
                "bridge, gravity, matter, emergence, thermodynamic, prediction, "
                "and falsification claims are contained in the gated sources?"
            ),
            [
                "source_bound_claim_records",
                "claim_domain_and_authority_classification",
                "pillar_and_seam_ledgers",
                "master_action_term_and_origin_ledger",
                "Ck_meaning_disambiguation_ledger",
                "prediction_and_falsification_ledger",
            ],
            [
                "NATIVE_CLAIM_EXTRACTION_COMPLETE",
                "NATIVE_CLAIM_EXTRACTION_COMPLETE_WITH_CONFLICTS",
                "BOUNDED_DEEP_REVIEW_COMPLETE_WITH_UNREVIEWED_OVERFLOW",
                "NATIVE_CLAIM_EXTRACTION_BLOCKED",
            ],
        ),
        _stage(
            4,
            "CURRENT_HYPOTHESIS_RECONCILIATION",
            "reconcile_toe_current_native_hypothesis_evidence_v0",
            (
                "Which claims support, conflict with, supersede, or depend on "
                "one another, which have mathematical or only philosophical "
                "support, and which extracted claims merit proposed canonical "
                "promotion under independent review?"
            ),
            [
                "native_hypothesis_graph",
                "support_conflict_dependency_and_supersession_edges",
                "mathematical_backing_and_missing_definition_ledger",
                "candidate_canonical_promotion_dossiers",
                "independent_review_for_each_proposed_promotion",
            ],
            [
                "CURRENT_HYPOTHESIS_RECONCILIATION_COMPLETE",
                "CURRENT_HYPOTHESIS_RECONCILIATION_COMPLETE_WITH_CONFLICTS",
                "CURRENT_HYPOTHESIS_RECONCILIATION_BLOCKED",
            ],
        ),
        _stage(
            5,
            "NATIVE_FRONTIER_DECISION",
            "select_toe_native_frontier_after_repository_wide_evidence_census_v0",
            (
                "Which currently supportable native hypothesis is strongest "
                "for a separate bounded adjudication, or why is no hypothesis "
                "ready?"
            ),
            [
                "frontier_classification_for_each_candidate",
                "ranked_native_frontier_map",
                "selected_next_hypothesis_or_explicit_no_selection",
                "decision_rationale_and_missing_prerequisite_count",
                "separate_next_program_preparation_target_if_selected",
            ],
            PROGRAM_TERMINAL_OUTCOMES,
        ),
    ]


def build() -> dict:
    scope_result = read_json(SCOPE_RESULT_PATH)
    archive_index = read_json(ARCHIVE_INDEX_PATH)
    controls = read_json(PREINSTALLATION_CONTROLS_PATH)
    if not isinstance(archive_index.get("files"), list):
        raise ValueError("archive intake index must contain a files array")
    evidence = {
        key: {
            "path": path.relative_to(REPO_ROOT).as_posix(),
            "sha256": sha256_path(path),
        }
        for key, path in EVIDENCE_PATHS.items()
    }
    stages = _stages()
    prepared_identifiers = [
        {
            "stage_number": stage["stage_number"],
            "semantic_stage_id": stage["semantic_stage_id"],
            "canonical_target": stage["canonical_target"],
        }
        for stage in stages
    ]
    if (
        controls["canonical_identifier_contract"]["semantic_stages"]
        != prepared_identifiers
    ):
        raise ValueError("preinstallation controls changed canonical stage identifiers")
    if (
        controls["canonical_identifier_contract"]["mandatory_exit_target"]
        != MANDATORY_EXIT_TARGET
    ):
        raise ValueError("preinstallation controls changed mandatory exit target")
    return {
        "schema_id": (
            "toe.repository_wide_native_hypothesis_evidence_census."
            "bounded_program_preparation.v0"
        ),
        "calculation_id": (
            "CALC-TOE-REPOSITORY-WIDE-NATIVE-HYPOTHESIS-EVIDENCE-CENSUS-"
            "BOUNDED-PROGRAM-PREPARATION-v0"
        ),
        "captured_at_utc": CAPTURED_AT_UTC,
        "execution_target": EXECUTION_TARGET,
        "native_hypothesis_tested": "NONE_DIRECTLY_CONTROL_MODEL",
        "native_relevance": {
            "kind": "ONE_PREREQUISITE_FROM_NATIVE_CALCULATION",
            "statement": (
                "Recovers and reconciles the repository's native-hypothesis "
                "evidence before another physical representation, action, "
                "seam, or calculation is selected."
            ),
        },
        "prerequisite_scope": "AUTHORIZED_PROGRAM_ONLY",
        "evidence": evidence,
        "triggering_scope_result": {
            "authorized_evidence_sufficiency": scope_result[
                "scope_qualification"
            ]["authorized_evidence_sufficiency"],
            "repository_wide_evidence_sufficiency": scope_result[
                "scope_qualification"
            ]["repository_wide_evidence_sufficiency"],
            "legacy_archive_indexed_file_count_before_supplemental_roots": len(
                archive_index["files"]
            ),
            "legacy_archive_index_is_complete_for_current_local_archive": False,
            "supplemental_archive_roots": SUPPLEMENTAL_ARCHIVE_ROOTS,
            "supplemental_archive_root_count": len(SUPPLEMENTAL_ARCHIVE_ROOTS),
            "supplemental_archive_scientific_content_adjudicated": False,
            "closed_coherence_program_reopened": False,
        },
        "preinstallation_control_contract": {
            "artifact_id": controls["artifact_id"],
            "status": controls["status"],
            "canonical_identifiers_preserved": True,
            "workload_budgets_frozen": True,
            "completion_statuses_separated": True,
            "two_pass_source_snapshot_frozen": True,
            "deterministic_deep_review_selection_frozen": True,
            "passive_parser_contract_frozen": True,
            "byte_identity_and_cache_contract_frozen": True,
            "atomic_close_batch_contract_frozen": True,
            "terminal_state_map_frozen": True,
            "promotion_remains_outside_program": True,
            "maintenance_infrastructure_executed": False,
            "scientific_census_executed": False,
        },
        "program_proposal": {
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
            "source_authority_vocabulary": SOURCE_AUTHORITY_VOCABULARY,
            "claim_domains": CLAIM_DOMAINS,
            "seam_classes": SEAM_CLASSES,
            "frontier_classifications": FRONTIER_CLASSES,
            "archive_assessment_outcomes": ARCHIVE_ASSESSMENT_OUTCOMES,
            "program_terminal_outcomes": PROGRAM_TERMINAL_OUTCOMES,
            "workload_budgets": controls["workload_budgets"],
            "completion_status_contract": controls[
                "completion_status_contract"
            ],
            "source_root_snapshot_contract": controls[
                "source_root_snapshot_contract"
            ],
            "deep_review_selection_contract": controls[
                "deep_review_selection_contract"
            ],
            "parser_contract_artifact": controls["artifact_id"],
            "byte_identity_and_cache_contract": controls[
                "byte_identity_and_cache_contract"
            ],
            "index_schema": controls["index_schema"],
            "batch_and_atomic_close_contract": controls[
                "batch_and_atomic_close_contract"
            ],
            "duplicate_contract": controls["duplicate_contract"],
            "promotion_contract": controls["promotion_contract"],
            "terminal_state_map": controls["terminal_state_map"],
            "terminal_state_qualifiers": controls[
                "terminal_state_qualifiers"
            ],
            "repository_exclusion_contract": controls[
                "repository_exclusion_contract"
            ],
            "discovery_strategy": {
                "broad_automated_discovery_first": True,
                "metadata_and_hash_classification_before_deep_read": True,
                "deep_review_requires_relevance_and_provenance_gate": True,
                "deep_read_all_archive_files_required": False,
                "binary_generated_cache_and_dependency_trees_excluded_by_rule": True,
                "supplemental_archive_roots_require_stage_1_reindex": True,
                "vendored_virtual_environments_are_not_scientific_evidence": True,
                "generated_outputs_are_classified_before_evidence_use": True,
                "keyword_only_discovery_is_sufficient": False,
            },
            "custody_contract": {
                "archive_is_read_only": True,
                "supplemental_archive_roots_are_read_only": True,
                "supplemental_archive_roots_are_explicit_stage_1_inputs": True,
                "supplemental_archive_roots_are_not_adopted_evidence": True,
                "original_paths_and_hashes_preserved": True,
                "provenance_and_licensing_recorded_where_available": True,
                "source_documents_distinguished_from_generated_summaries": True,
                "claims_extracted_into_new_custody_dossiers": True,
                "whole_documents_not_promoted_automatically": True,
                "independent_review_required_for_canonical_promotion": True,
                "discovery_is_separate_from_scientific_adoption": True,
            },
            "native_hypothesis_graph_schema": [
                "source",
                "claim",
                "assumption",
                "mathematical_object",
                "derivation",
                "result",
                "seam_or_pillar",
                "observable",
                "authority_status",
            ],
            "transition_rules": {
                "each_stage_consumes_only_accepted_prior_outputs": True,
                "any_block_or_failure_exits_without_repair": True,
                "stage_5_selects_but_does_not_execute_next_hypothesis": True,
                "positive_archive_finding_does_not_select_representation": True,
                "separate_installation_authority_required": True,
                "separate_stage_1_open_authority_required": True,
                "no_automatic_successor": True,
            },
        },
        "claim_boundary": {
            "coherence_closeout_scope_qualified": True,
            "repository_wide_census_performed": False,
            "supplemental_archive_root_census_performed": False,
            "supplemental_archive_root_claims_extracted": False,
            "archive_material_adopted": False,
            "canonical_evidence_promoted": False,
            "native_hypothesis_selected": False,
            "representation_selected": False,
            "field_selected": False,
            "action_selected": False,
            "seam_executed": False,
            "observable_selected": False,
            "program_installed": False,
            "stage_1_opened": False,
            "scientific_claim_made": False,
            "preinstallation_controls_frozen": True,
            "maintenance_index_or_cache_generated": False,
        },
        "prohibited_claims": [
            "repository-wide source exhaustion",
            "archive evidence adequacy",
            "archive material authority",
            "supplemental archive root scientific adequacy",
            "CCFT validation or rejection",
            "native ontology selection",
            "master-action selection",
            "pillar or seam closure",
            "unique empirical discriminator",
            "completed ToE",
        ],
        "terminal_outcome": OUTCOME,
        "strict_terminal_outcome": STRICT_OUTCOME,
        "verdict": (
            "PROGRAM_PROPOSAL_PREPARED_AWAITING_SEPARATE_INSTALLATION_AUTHORITY"
        ),
    }


def main() -> int:
    return write_or_check(
        path=OUTPUT_PATH,
        build=build,
        description=(
            "repository-wide native-hypothesis evidence-census bounded "
            "program preparation"
        ),
    )


if __name__ == "__main__":
    raise SystemExit(main())
