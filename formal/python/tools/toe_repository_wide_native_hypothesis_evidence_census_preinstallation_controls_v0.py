from __future__ import annotations

from formal.python.tools.qft_gr_quadratic_hyperbolicity_common import (
    REPO_ROOT,
    write_or_check,
)


CAPTURED_AT_UTC = "2026-07-30T00:00:00Z"
OUTPUT_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_EVIDENCE_CENSUS_"
    "PREINSTALLATION_CONTROLS_20260730_v0.json"
)

PROGRAM_ID = "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_EVIDENCE_CENSUS_V0"
MANDATORY_EXIT_TARGET = (
    "close_toe_repository_wide_native_hypothesis_evidence_census_"
    "v0_after_bounded_result_v0"
)

STAGES = [
    {
        "stage_number": 1,
        "semantic_stage_id": "REPOSITORY_WIDE_SOURCE_CENSUS",
        "canonical_target": (
            "inventory_toe_repository_wide_native_hypothesis_sources_v0"
        ),
    },
    {
        "stage_number": 2,
        "semantic_stage_id": "DEDUPLICATION_AND_LINEAGE_RECONSTRUCTION",
        "canonical_target": (
            "reconstruct_toe_native_hypothesis_source_lineages_v0"
        ),
    },
    {
        "stage_number": 3,
        "semantic_stage_id": "NATIVE_CLAIM_EXTRACTION_AND_CLASSIFICATION",
        "canonical_target": (
            "extract_and_classify_toe_repository_wide_"
            "native_hypothesis_claims_v0"
        ),
    },
    {
        "stage_number": 4,
        "semantic_stage_id": "CURRENT_HYPOTHESIS_RECONCILIATION",
        "canonical_target": "reconcile_toe_current_native_hypothesis_evidence_v0",
    },
    {
        "stage_number": 5,
        "semantic_stage_id": "NATIVE_FRONTIER_DECISION",
        "canonical_target": (
            "select_toe_native_frontier_after_repository_wide_"
            "evidence_census_v0"
        ),
    },
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

TERMINAL_STATE_MAP = {
    "REPOSITORY_WIDE_SOURCE_CENSUS_COMPLETE": "PASS",
    "REPOSITORY_WIDE_SOURCE_CENSUS_COMPLETE_WITH_GAPS": "PASS",
    "REPOSITORY_WIDE_SOURCE_CENSUS_COMPLETE_WITH_LOCAL_CUSTODY_LIMITATIONS": (
        "PASS"
    ),
    "SOURCE_ROOT_SNAPSHOT_STABLE": "PASS",
    "SOURCE_ROOT_MUTATED_DURING_CENSUS": "BLOCKED",
    "REPOSITORY_WIDE_SOURCE_CENSUS_INCOMPLETE": "BLOCKED",
    "SOURCE_ROOT_UNAVAILABLE": "BLOCKED",
    "SOURCE_DISCOVERY_OR_PROVENANCE_BLOCKED": "BLOCKED",
    "CUSTODY_OR_PROVENANCE_BLOCKED": "BLOCKED",
    "DETERMINISTIC_INDEX_GENERATION_FAILED": "FAILED",
    "SOURCE_LINEAGES_RECONSTRUCTED": "PASS",
    "SOURCE_LINEAGES_RECONSTRUCTED_WITH_AMBIGUITIES": "PASS",
    "SOURCE_LINEAGE_RECONSTRUCTION_BLOCKED": "BLOCKED",
    "NATIVE_CLAIM_EXTRACTION_COMPLETE": "PASS",
    "NATIVE_CLAIM_EXTRACTION_COMPLETE_WITH_CONFLICTS": "PASS",
    "BOUNDED_DEEP_REVIEW_COMPLETE_WITH_UNREVIEWED_OVERFLOW": "PASS",
    "NATIVE_CLAIM_EXTRACTION_BLOCKED": "BLOCKED",
    "CURRENT_HYPOTHESIS_RECONCILIATION_COMPLETE": "PASS",
    "CURRENT_HYPOTHESIS_RECONCILIATION_COMPLETE_WITH_CONFLICTS": "PASS",
    "CURRENT_HYPOTHESIS_RECONCILIATION_BLOCKED": "BLOCKED",
    "NATIVE_HYPOTHESIS_GRAPH_AND_FRONTIER_READY": "PASS",
    "EVIDENCE_FOUND_BUT_RECONCILIATION_BLOCKED": "BLOCKED",
    "REPOSITORY_WIDE_EVIDENCE_CENSUS_INCOMPLETE": "BLOCKED",
    "NO_TEST_READY_NATIVE_HYPOTHESIS_FOUND": "PASS",
}


def _parser(
    parser_id: str,
    formats: list[str],
    max_file_bytes: int,
    max_text_bytes: int,
    timeout_seconds: int,
    memory_bytes: int,
    *,
    page_or_sheet_limit: int | None = None,
    nesting_limit: int | None = None,
    record_limit: int | None = None,
) -> dict:
    return {
        "parser_id": parser_id,
        "parser_version": "v1",
        "formats": formats,
        "max_file_bytes": max_file_bytes,
        "max_extracted_text_bytes": max_text_bytes,
        "timeout_seconds": timeout_seconds,
        "memory_limit_bytes": memory_bytes,
        "maximum_page_or_worksheet_count": page_or_sheet_limit,
        "maximum_nesting_or_recursion_depth": nesting_limit,
        "maximum_record_or_cell_count": record_limit,
        "embedded_object_policy": "NEVER_ACTIVATE_OR_EXTRACT_RECURSIVELY",
        "macro_policy": "DISABLED",
        "network_policy": "DENY",
        "failure_classification": "PARSER_FAILURE_PRESERVED",
    }


def build() -> dict:
    return {
        "schema_id": (
            "toe.repository_wide_native_hypothesis_evidence_census."
            "preinstallation_controls.v0"
        ),
        "artifact_id": (
            "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_EVIDENCE_CENSUS_"
            "PREINSTALLATION_CONTROLS_20260730_v0"
        ),
        "captured_at_utc": CAPTURED_AT_UTC,
        "status": "PREINSTALLATION_CONTROLS_FROZEN_NOT_EXECUTED",
        "program_id": PROGRAM_ID,
        "canonical_identifier_contract": {
            "semantic_stages": STAGES,
            "mandatory_exit_target": MANDATORY_EXIT_TARGET,
            "identifiers_may_change_only_by_reviewed_proposal_amendment": True,
        },
        "workload_budgets": {
            "budget_scope": (
                "ELIGIBLE_CORPUS_AFTER_DETERMINISTIC_VENDOR_CACHE_TEMP_AND_"
                "UNSUPPORTED_ACTIVE_CONTENT_SEGREGATION"
            ),
            "maximum_eligible_deep_review_files": 640,
            "maximum_eligible_deep_review_bytes": 1_073_741_824,
            "maximum_files_per_hypothesis_domain": 64,
            "maximum_files_per_source_lineage": 8,
            "maximum_extracted_claims": 4096,
            "maximum_claims_per_file": 32,
            "maximum_unresolved_lineage_relationships": 512,
            "maximum_parser_failures": 128,
            "maximum_unsupported_format_files": 1024,
            "maximum_total_extracted_text_bytes": 268_435_456,
            "overflow_terminal_outcome": (
                "BOUNDED_DEEP_REVIEW_COMPLETE_WITH_UNREVIEWED_OVERFLOW"
            ),
            "overflow_is_not_repository_claim_exhaustion": True,
        },
        "completion_status_contract": {
            "declared_root_discovery_status": [
                "DECLARED_ROOT_METADATA_DISCOVERY_COMPLETE",
                "DECLARED_ROOT_METADATA_DISCOVERY_INCOMPLETE",
            ],
            "custody_inventory_status": [
                "CUSTODY_INVENTORY_COMPLETE",
                "CUSTODY_INVENTORY_COMPLETE_WITH_LOCAL_LIMITATIONS",
                "CUSTODY_INVENTORY_BLOCKED",
            ],
            "bounded_deep_review_status": [
                "BOUNDED_DEEP_REVIEW_COMPLETE",
                "BOUNDED_DEEP_REVIEW_COMPLETE_WITH_UNREVIEWED_OVERFLOW",
                "BOUNDED_DEEP_REVIEW_BLOCKED",
            ],
            "claim_exhaustion_status": [
                "REPOSITORY_CLAIM_EXHAUSTION_NOT_ESTABLISHED"
            ],
        },
        "source_root_snapshot_contract": {
            "passes": [
                "INITIAL_SOURCE_ROOT_SCAN",
                "FINAL_SOURCE_ROOT_SCAN",
                "MUTATION_COMPARISON",
            ],
            "recorded_fields": [
                "source_root_id",
                "normalized_root_relative_path_inventory",
                "initial_file_count",
                "initial_aggregate_byte_count",
                "final_file_count",
                "final_aggregate_byte_count",
                "initial_snapshot_tuple_hash",
                "final_snapshot_tuple_hash",
                "files_added_during_execution",
                "files_removed_during_execution",
                "files_changed_during_execution",
            ],
            "tuple_fields": [
                "normalized_relative_path",
                "file_type",
                "size",
                "sha256",
                "custody_classification",
            ],
            "tuple_sort": "UTF8_BYTES_OF_NORMALIZED_RELATIVE_PATH",
            "snapshot_serialization": "RFC8785_AFTER_DECLARED_SET_NORMALIZATION",
            "snapshot_hash": "SHA-256",
            "absolute_paths_in_snapshot_hash": False,
            "timestamps_in_snapshot_hash": False,
            "stable_outcome": "SOURCE_ROOT_SNAPSHOT_STABLE",
            "mutated_outcome": "SOURCE_ROOT_MUTATED_DURING_CENSUS",
            "material_mutation_blocks_stage": True,
            "excluded_cache_mutation_exception": (
                "ALLOWED_ONLY_WHEN_OUTSIDE_AUTHORITATIVE_INVENTORY_AND_"
                "QUANTIFIED_IN_EXCLUSION_LEDGER"
            ),
        },
        "deep_review_selection_contract": {
            "priority_order": [
                "CURRENT_CANONICAL_PRIMARY_SOURCES",
                "ARCHIVED_PRIMARY_LINEAGE_HEADS",
                "EARLIEST_PRIMARY_SOURCE_PER_LINEAGE",
                "UNIQUE_DEFINITIONS_EQUATIONS_OR_PREDICTIONS",
                "SOURCES_REPRESENTING_KNOWN_CONFLICTS",
                "DERIVED_SUMMARY_WHEN_PRIMARY_UNAVAILABLE",
                "DETERMINISTIC_STRATIFIED_OVERFLOW_SAMPLE",
            ],
            "domain_order": CLAIM_DOMAINS,
            "minimum_slots_per_nonempty_domain_before_global_fill": 16,
            "maximum_files_per_domain": 64,
            "maximum_files_per_lineage": 8,
            "conflict_allocation": (
                "INCLUDE_BOTH_CONFLICT_ENDPOINTS_BEFORE_LOWER_PRIORITY_SOURCES"
            ),
            "primary_domain_assignment": (
                "FIRST_MATCH_IN_FROZEN_DOMAIN_ORDER_AFTER_SOURCE_BOUND_TAGGING"
            ),
            "tie_breaking_order": [
                "source_root_id",
                "normalized_relative_path_utf8_bytes",
                "sha256",
            ],
            "overflow_sampling": (
                "ROUND_ROBIN_OVER_DOMAIN_BY_SOURCE_CLASS_STRATA_SORTED_BY_"
                "FROZEN_DOMAIN_AND_SOURCE_CLASS_ORDER"
            ),
            "manual_preference_permitted": False,
            "overflow_population_and_unreviewed_counts_recorded": True,
        },
        "parser_contract": {
            "contract_version": "v1",
            "archived_active_content_is_untrusted": True,
            "never_execute_import_compile_or_activate_archived_content": True,
            "network_access": "DENY",
            "external_url_fetch": "DENY",
            "recursive_archive_expansion": "DENY",
            "compressed_or_decompression_bombs": "REJECT_AND_PRESERVE_METADATA",
            "symlink_junction_reparse_policy": (
                "DO_NOT_FOLLOW_RECORD_METADATA_AND_BLOCK_ANY_ROOT_ESCAPE"
            ),
            "special_file_policy": (
                "DEVICE_PIPE_SOCKET_OR_OTHER_SPECIAL_OBJECT_METADATA_ONLY"
            ),
            "path_traversal_policy": "REJECT",
            "filename_normalization_collision_policy": (
                "PRESERVE_RAW_NAMES_RECORD_COLLISION_AND_BLOCK_AMBIGUOUS_INTAKE"
            ),
            "unsupported_file_status": "UNSUPPORTED_FORMAT_PRESERVED",
            "unsupported_is_not_irrelevant": True,
            "handlers": [
                _parser(
                    "PASSIVE_TEXT_SOURCE_V1",
                    [
                        "md",
                        "txt",
                        "py",
                        "lean",
                        "tex",
                        "rst",
                        "ps1",
                        "sh",
                        "cfg",
                        "ini",
                    ],
                    16_777_216,
                    4_194_304,
                    30,
                    536_870_912,
                    nesting_limit=32,
                ),
                _parser(
                    "PASSIVE_STRUCTURED_TEXT_V1",
                    ["json", "yaml", "yml", "toml"],
                    16_777_216,
                    4_194_304,
                    30,
                    536_870_912,
                    nesting_limit=64,
                ),
                _parser(
                    "PASSIVE_TABULAR_V1",
                    ["csv", "tsv"],
                    268_435_456,
                    8_388_608,
                    60,
                    1_073_741_824,
                    record_limit=2_000_000,
                ),
                _parser(
                    "PASSIVE_PDF_V1",
                    ["pdf"],
                    134_217_728,
                    8_388_608,
                    120,
                    1_073_741_824,
                    page_or_sheet_limit=1000,
                ),
                _parser(
                    "PASSIVE_OFFICE_V1",
                    ["docx", "xlsx", "pptx", "odt", "ods", "odp"],
                    134_217_728,
                    8_388_608,
                    120,
                    1_073_741_824,
                    page_or_sheet_limit=1000,
                ),
                _parser(
                    "PASSIVE_NOTEBOOK_V1",
                    ["ipynb"],
                    67_108_864,
                    8_388_608,
                    60,
                    1_073_741_824,
                    nesting_limit=64,
                    record_limit=10_000,
                ),
                _parser(
                    "METADATA_ONLY_MEDIA_V1",
                    ["png", "jpg", "jpeg", "gif", "svg", "wav", "mp3", "mp4"],
                    1_073_741_824,
                    0,
                    30,
                    536_870_912,
                ),
                _parser(
                    "METADATA_ONLY_BINARY_DATA_V1",
                    ["npy", "npz", "bin", "exe", "dll", "whl"],
                    1_073_741_824,
                    0,
                    30,
                    536_870_912,
                ),
                _parser(
                    "CONTAINER_METADATA_ONLY_V1",
                    ["zip", "tar", "gz", "7z", "rar"],
                    1_073_741_824,
                    0,
                    30,
                    536_870_912,
                    nesting_limit=0,
                ),
            ],
            "execution_enforcement_required_before_stage_1_open": True,
            "parser_failures_separate_from_irrelevant_counts": True,
        },
        "byte_identity_and_cache_contract": {
            "tracked_primary_identity": "COMMITTED_GIT_BLOB_BYTES",
            "tracked_blob_read_method": "git cat-file blob",
            "tracked_sha256_cache_key": [
                "git_object_format",
                "git_object_id",
                "hashing_schema_version",
            ],
            "effective_attributes_recorded_separately": True,
            "worktree_sha256_recorded_separately_when_relevant": True,
            "local_metadata_is_change_detection_hint_only": True,
            "local_final_manifest_requires_verified_sha256": True,
            "cache_status": "LOCAL_REGENERABLE_NONAUTHORITATIVE",
            "cache_path": ".toe_cache/native_hypothesis_census_v1.sqlite3",
            "cache_schema_version": 1,
            "cache_transactions_are_atomic": True,
            "cache_never_replaces_final_hash_verification": True,
            "new_versioned_index_required": True,
            "historical_index_must_not_be_overwritten": (
                "formal/output/archive_intake_index.json"
            ),
        },
        "index_schema": {
            "schema_version": 1,
            "index_id": "TOE_NATIVE_HYPOTHESIS_CENSUS_INDEX_V1",
            "file_record_fields": [
                "source_root_id",
                "custody_relative_path",
                "git_or_filesystem_status",
                "git_object_id",
                "committed_blob_sha256",
                "worktree_sha256",
                "local_verified_sha256",
                "file_size",
                "date_metadata_with_kind_and_confidence",
                "file_type",
                "content_fingerprint",
                "duplicate_group_candidate",
                "source_classification",
                "content_extraction_status",
                "domain_tags",
                "source_lineage",
                "provenance_status",
                "licensing_or_redistribution_concern",
                "custody_class",
                "eligibility_for_deeper_review",
                "exclusion_reason",
                "source_snapshot_id",
                "indexer_schema_version",
                "parser_contract_version",
            ],
            "source_snapshot_fields": [
                "source_root_id",
                "initial_snapshot_tuple_hash",
                "final_snapshot_tuple_hash",
                "stability_status",
            ],
            "generated_index_path_pattern": (
                "formal/output/native_hypothesis_census_v1/"
                "{stage_id}/{batch_id}.json"
            ),
        },
        "batch_and_atomic_close_contract": {
            "working_cache_status": "LOCAL_REGENERABLE_NONAUTHORITATIVE",
            "intermediate_substantive_batch_commits_permitted": False,
            "final_close_commit_contains": [
                "final_batch_manifests",
                "aggregate_manifest",
                "index_schema_and_tool_versions",
                "source_root_snapshot_records",
                "stage_result",
                "independent_review",
                "validation_record",
                "immutable_CLOSE_event",
                "registry_and_authority_transition",
            ],
            "aggregate_manifest_binds_each_batch_hash": True,
            "batch_union_equals_declared_inventory": True,
            "batch_overlap_permitted": False,
            "batch_omission_permitted": False,
            "no_batch_is_a_subsidiary_scientific_target": True,
        },
        "duplicate_contract": {
            "stage_1_exact_hash_grouping_is_candidate_only": True,
            "every_duplicate_path_remains_in_custody_inventory": True,
            "stage_1_classes": [
                "EXACT_CONTENT_DUPLICATE",
                "SUSPECTED_NEAR_DUPLICATE",
                "DERIVED_SUMMARY_CANDIDATE",
                "PENDING_LINEAGE_REVIEW",
            ],
            "near_duplicate_similarity_is_nonauthoritative": True,
            "scientific_lineage_and_supersession_are_stage_2_only": True,
        },
        "promotion_contract": {
            "census_may_emit": "PROMOTION_CANDIDATE_DOSSIER",
            "census_may_promote_claims": False,
            "promotion_requires_separate_post_census_authority": True,
        },
        "terminal_state_map": TERMINAL_STATE_MAP,
        "terminal_state_qualifiers": {
            "REPOSITORY_WIDE_SOURCE_CENSUS_COMPLETE_WITH_GAPS": (
                "PASS_ONLY_WHEN_EVERY_DECLARED_ROOT_IS_INVENTORIED_AND_ALL_"
                "GAPS_ARE_QUANTIFIED_NONMATERIAL_LOCAL_PORTABILITY_OR_"
                "DETERMINISTIC_EXCLUSION_LIMITATIONS"
            ),
            "SOURCE_LINEAGES_RECONSTRUCTED_WITH_AMBIGUITIES": (
                "PASS_ONLY_WHEN_AMBIGUITIES_ARE_WITHIN_FROZEN_BUDGET_AND_"
                "PRESERVED_WITHOUT_SUPERSESSION_OR_AUTHORITY_INFERENCE"
            ),
            "BOUNDED_DEEP_REVIEW_COMPLETE_WITH_UNREVIEWED_OVERFLOW": (
                "PASS_REQUIRES_DETERMINISTIC_SELECTION_OVERFLOW_COUNTS_AND_"
                "REPOSITORY_CLAIM_EXHAUSTION_NOT_ESTABLISHED"
            ),
        },
        "repository_exclusion_contract": {
            "tracked_gitignore_rules": [
                "/archive/ToE_Project/",
                "/archive/ToE_Project_Starter_2025-09-24/",
                "/archive/custody_bundles/",
                "/.toe_cache/native_hypothesis_census_v1.sqlite3",
            ],
            "broad_archive_ignore_prohibited": True,
            "curated_dossier_root": (
                "formal/docs/release/native_hypothesis_evidence_dossiers/"
            ),
            "curated_dossiers_must_not_be_ignored": True,
            "ignore_rule_removal_requires_maintenance_authority": True,
        },
        "authority_boundary": {
            "program_installed": False,
            "stage_1_opened": False,
            "archive_scientifically_traversed": False,
            "source_classification_performed": False,
            "claims_extracted": False,
            "evidence_promoted": False,
            "native_hypothesis_selected": False,
            "index_or_cache_generated": False,
            "next_valid_decision_after_acceptance": (
                "AUTHORIZE_CENSUS_PROGRAM_INSTALLATION"
            ),
        },
    }


def main() -> int:
    return write_or_check(
        path=OUTPUT_PATH,
        build=build,
        description=(
            "repository-wide native-hypothesis evidence-census "
            "preinstallation controls"
        ),
    )


if __name__ == "__main__":
    raise SystemExit(main())
