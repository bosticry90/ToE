from __future__ import annotations

from formal.python.tools.bounded_program_governance import scope_hash
from formal.python.tools.qft_gr_quadratic_hyperbolicity_common import (
    REPO_ROOT,
    read_json,
    sha256_path,
    write_or_check,
)


CAPTURED_AT_UTC = "2026-07-30T00:00:00Z"
CURRENT_TARGET = (
    "prepare_toe_repository_wide_native_hypothesis_evidence_census_"
    "bounded_program_v0"
)
CALC_PATH = REPO_ROOT / (
    "formal/output/"
    "CALC-TOE-REPOSITORY-WIDE-NATIVE-HYPOTHESIS-EVIDENCE-CENSUS-"
    "BOUNDED-PROGRAM-PREPARATION-v0.json"
)
REGISTRY_PATH = REPO_ROOT / "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json"
OUTPUT_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_EVIDENCE_CENSUS_"
    "BOUNDED_PROGRAM_PREPARATION_RESULT_REVIEW_20260730_v0.json"
)
EXPECTED_STAGES = [
    "REPOSITORY_WIDE_SOURCE_CENSUS",
    "DEDUPLICATION_AND_LINEAGE_RECONSTRUCTION",
    "NATIVE_CLAIM_EXTRACTION_AND_CLASSIFICATION",
    "CURRENT_HYPOTHESIS_RECONCILIATION",
    "NATIVE_FRONTIER_DECISION",
]


def build() -> dict:
    calc = read_json(CALC_PATH)
    registry = read_json(REGISTRY_PATH)
    proposal = calc["program_proposal"]
    stages = proposal["semantic_stages_proposed"]
    evidence_ok = all(
        (REPO_ROOT / item["path"]).is_file()
        and sha256_path(REPO_ROOT / item["path"]) == item["sha256"]
        for item in calc["evidence"].values()
    )
    checks = {
        "current_target_is_preparation_only": (
            calc["execution_target"] == CURRENT_TARGET
            and registry["current_projection_v0"]["current_target"]
            == CURRENT_TARGET
        ),
        "evidence_hashes_recompute": evidence_ok,
        "scope_qualification_is_dependency": (
            "coherence_scope_qualification" in calc["evidence"]
            and calc["triggering_scope_result"][
                "repository_wide_evidence_sufficiency"
            ]
            == "NOT_TESTED"
        ),
        "preinstallation_controls_are_hash_bound_and_nonexecuting": (
            "preinstallation_controls" in calc["evidence"]
            and calc["preinstallation_control_contract"]["status"]
            == "PREINSTALLATION_CONTROLS_FROZEN_NOT_EXECUTED"
            and calc["preinstallation_control_contract"][
                "canonical_identifiers_preserved"
            ]
            is True
            and calc["preinstallation_control_contract"][
                "workload_budgets_frozen"
            ]
            is True
            and calc["preinstallation_control_contract"][
                "two_pass_source_snapshot_frozen"
            ]
            is True
            and calc["preinstallation_control_contract"][
                "deterministic_deep_review_selection_frozen"
            ]
            is True
            and calc["preinstallation_control_contract"][
                "passive_parser_contract_frozen"
            ]
            is True
            and calc["preinstallation_control_contract"][
                "maintenance_infrastructure_executed"
            ]
            is False
            and calc["preinstallation_control_contract"][
                "scientific_census_executed"
            ]
            is False
        ),
        "supplemental_archive_roots_are_explicit_and_unadjudicated": (
            calc["triggering_scope_result"]["supplemental_archive_root_count"] == 2
            and [
                item["path"]
                for item in calc["triggering_scope_result"][
                    "supplemental_archive_roots"
                ]
            ]
            == [
                "archive/ToE_Project",
                "archive/ToE_Project_Starter_2025-09-24",
            ]
            and all(
                item["intake_status"]
                == "PRESENT_LOCALLY_PENDING_CANONICAL_REINDEX"
                and item["scientific_status"] == "UNADJUDICATED"
                for item in calc["triggering_scope_result"][
                    "supplemental_archive_roots"
                ]
            )
            and calc["triggering_scope_result"][
                "legacy_archive_index_is_complete_for_current_local_archive"
            ]
            is False
            and calc["triggering_scope_result"][
                "supplemental_archive_scientific_content_adjudicated"
            ]
            is False
        ),
        "proposal_is_not_installed_authorized_or_open": (
            proposal["proposal_only"] is True
            and proposal["installed"] is False
            and proposal["authorized"] is False
            and proposal["open_event_created"] is False
            and proposal["attempt_count"] == 0
        ),
        "five_stage_zero_repair_cap_is_exact": (
            proposal["authorized_stage_count_proposed"] == 5
            and proposal["repair_attempt_count_proposed"] == 0
            and proposal["no_subsidiary_scientific_targets_proposed"] is True
            and len(stages) == 5
        ),
        "workload_and_claim_exhaustion_boundaries_are_exact": (
            proposal["workload_budgets"][
                "maximum_eligible_deep_review_files"
            ]
            == 640
            and proposal["workload_budgets"][
                "maximum_eligible_deep_review_bytes"
            ]
            == 1_073_741_824
            and proposal["workload_budgets"][
                "overflow_is_not_repository_claim_exhaustion"
            ]
            is True
            and proposal["completion_status_contract"][
                "claim_exhaustion_status"
            ]
            == ["REPOSITORY_CLAIM_EXHAUSTION_NOT_ESTABLISHED"]
        ),
        "semantic_stage_order_is_exact": (
            [stage["semantic_stage_id"] for stage in stages]
            == EXPECTED_STAGES
            and [stage["stage_number"] for stage in stages] == [1, 2, 3, 4, 5]
        ),
        "scope_hashes_recompute": all(
            stage["canonical_scope_hash"] == scope_hash(stage["canonical_scope"])
            for stage in stages
        ),
        "open_scopes_precede_substantive_outputs": all(
            stage["proposed_open_event_scope"][
                "substantive_stage_output_allowed"
            ]
            is False
            and stage["proposed_open_event_scope"][
                "producer_may_run_before_open_commit"
            ]
            is False
            for stage in stages
        ),
        "close_scopes_bind_result_and_independent_review": all(
            "stage_result_or_failed_closed_result"
            in stage["proposed_close_event_scope"]["required_atomic_contents"]
            and "independent_result_review"
            in stage["proposed_close_event_scope"]["required_atomic_contents"]
            and stage["proposed_close_event_scope"][
                "block_or_failure_requires_mandatory_exit"
            ]
            is True
            for stage in stages
        ),
        "archive_is_discovered_but_not_adopted": (
            proposal["custody_contract"]["archive_is_read_only"] is True
            and proposal["custody_contract"][
                "supplemental_archive_roots_are_read_only"
            ]
            is True
            and proposal["custody_contract"][
                "supplemental_archive_roots_are_explicit_stage_1_inputs"
            ]
            is True
            and proposal["custody_contract"][
                "supplemental_archive_roots_are_not_adopted_evidence"
            ]
            is True
            and proposal["custody_contract"][
                "whole_documents_not_promoted_automatically"
            ]
            is True
            and calc["claim_boundary"]["archive_material_adopted"] is False
        ),
        "snapshot_parser_identity_and_close_contracts_fail_closed": (
            proposal["source_root_snapshot_contract"][
                "material_mutation_blocks_stage"
            ]
            is True
            and proposal["deep_review_selection_contract"][
                "manual_preference_permitted"
            ]
            is False
            and proposal["byte_identity_and_cache_contract"][
                "tracked_primary_identity"
            ]
            == "COMMITTED_GIT_BLOB_BYTES"
            and proposal["batch_and_atomic_close_contract"][
                "intermediate_substantive_batch_commits_permitted"
            ]
            is False
            and proposal["promotion_contract"]["census_may_promote_claims"]
            is False
            and proposal["terminal_state_map"][
                "SOURCE_ROOT_MUTATED_DURING_CENSUS"
            ]
            == "BLOCKED"
            and proposal["terminal_state_map"][
                "DETERMINISTIC_INDEX_GENERATION_FAILED"
            ]
            == "FAILED"
            and proposal["terminal_state_qualifiers"][
                "BOUNDED_DEEP_REVIEW_COMPLETE_WITH_UNREVIEWED_OVERFLOW"
            ].endswith("REPOSITORY_CLAIM_EXHAUSTION_NOT_ESTABLISHED")
        ),
        "broad_first_gated_deep_review_is_exact": (
            proposal["discovery_strategy"]["broad_automated_discovery_first"]
            is True
            and proposal["discovery_strategy"][
                "deep_review_requires_relevance_and_provenance_gate"
            ]
            is True
            and proposal["discovery_strategy"][
                "deep_read_all_archive_files_required"
            ]
            is False
            and proposal["discovery_strategy"][
                "supplemental_archive_roots_require_stage_1_reindex"
            ]
            is True
            and proposal["discovery_strategy"][
                "vendored_virtual_environments_are_not_scientific_evidence"
            ]
            is True
        ),
        "source_authority_vocabulary_is_explicit": (
            len(proposal["source_authority_vocabulary"]) == 11
            and "CURRENT_CANONICAL"
            in proposal["source_authority_vocabulary"]
            and "UNKNOWN_PROVENANCE"
            in proposal["source_authority_vocabulary"]
        ),
        "native_graph_has_complete_provenance_chain": (
            proposal["native_hypothesis_graph_schema"]
            == [
                "source",
                "claim",
                "assumption",
                "mathematical_object",
                "derivation",
                "result",
                "seam_or_pillar",
                "observable",
                "authority_status",
            ]
        ),
        "stage_5_selects_without_execution": (
            proposal["transition_rules"][
                "stage_5_selects_but_does_not_execute_next_hypothesis"
            ]
            is True
            and proposal["transition_rules"]["no_automatic_successor"] is True
        ),
        "no_scientific_model_or_claim_selected": all(
            calc["claim_boundary"][key] is False
            for key in [
                "repository_wide_census_performed",
                "supplemental_archive_root_census_performed",
                "supplemental_archive_root_claims_extracted",
                "archive_material_adopted",
                "canonical_evidence_promoted",
                "native_hypothesis_selected",
                "representation_selected",
                "field_selected",
                "action_selected",
                "seam_executed",
                "observable_selected",
                "program_installed",
                "stage_1_opened",
                "scientific_claim_made",
                "maintenance_index_or_cache_generated",
            ]
        ),
    }
    failed = sorted(name for name, passed in checks.items() if not passed)
    return {
        "schema_id": (
            "toe.repository_wide_native_hypothesis_evidence_census."
            "bounded_program_preparation_review.v0"
        ),
        "artifact_id": (
            "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_EVIDENCE_CENSUS_"
            "BOUNDED_PROGRAM_PREPARATION_RESULT_REVIEW_20260730_v0"
        ),
        "captured_at_utc": CAPTURED_AT_UTC,
        "reviewed_result": {
            "path": CALC_PATH.relative_to(REPO_ROOT).as_posix(),
            "sha256": sha256_path(CALC_PATH),
        },
        "checks": checks,
        "failed_checks": failed,
        "accepted": not failed,
        "proposal_only": True,
        "program_installed": False,
        "program_authorized": False,
        "stage_1_opened": False,
        "scientific_result_claimed": False,
        "verdict": (
            "ACCEPT_PROGRAM_PROPOSAL_AWAIT_SEPARATE_INSTALLATION_AUTHORITY"
            if not failed
            else "REJECT_PROGRAM_PREPARATION_REVIEW_FAILED"
        ),
    }


def main() -> int:
    return write_or_check(
        path=OUTPUT_PATH,
        build=build,
        description=(
            "repository-wide native-hypothesis evidence-census program "
            "preparation result review"
        ),
    )


if __name__ == "__main__":
    raise SystemExit(main())
