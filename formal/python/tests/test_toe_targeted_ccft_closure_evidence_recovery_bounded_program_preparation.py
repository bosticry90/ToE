from __future__ import annotations

import hashlib
import json
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
RELEASE = REPO_ROOT / "formal/docs/release"
RESULT = RELEASE / "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_BOUNDED_PROGRAM_PREPARATION_RESULT_v0.json"
REVIEW = RELEASE / "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_BOUNDED_PROGRAM_PREPARATION_RESULT_REVIEW_v0.json"
PROGRAM_ID = "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_V0"


def read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_authority_and_all_source_bindings_reproduce() -> None:
    value = read(RESULT)
    authority = value["authority_binding"]
    assert sha(REPO_ROOT / authority["authority_path"]) == authority["authority_sha256"]
    assert sha(REPO_ROOT / authority["authority_review_path"]) == authority["authority_review_sha256"]
    for source in value["source_bindings"]:
        assert sha(REPO_ROOT / source["path"]) == source["sha256"]


def test_exact_roots_and_search_gate_are_frozen_without_execution() -> None:
    value = read(RESULT)
    assert len(value["authorized_source_roots_proposed"]) == 8
    ids = {row["source_root_id"] for row in value["authorized_source_roots_proposed"]}
    assert "LOCAL_ARCHIVE_TOE_PROJECT" in ids
    assert "LOCAL_ARCHIVE_TOE_PROJECT_STARTER_2025_09_24" in ids
    assert value["root_and_content_exclusions"]["reddit_excluded"] is True
    search = value["deterministic_search_contract"]
    assert len(search["branch_terms"]["CP_NLSE"]) == 8
    assert len(search["branch_terms"]["LCRD_V3"]) == 7
    assert search["manual_preference_or_desired_model_may_affect_selection"] is False
    assert search["selected_content_is_extracted_once_and_reused_by_later_stages"] is True


def test_program_is_four_stage_one_pass_zero_repair_and_numerically_bounded() -> None:
    controls = read(RESULT)["program_controls"]
    assert controls["authorized_stage_count_proposed"] == 4
    assert controls["maximum_attempt_count_proposed"] == 4
    assert controls["one_attempt_per_stage"] is True
    assert controls["targeted_content_search_pass_limit"] == 1
    assert controls["repair_attempt_count"] == 0
    assert controls["automatic_second_search"] is False
    assert controls["maximum_metadata_candidates"] == 256
    assert controls["maximum_deep_review_files"] == 96
    assert controls["maximum_deep_review_files_per_branch"] == 48
    assert controls["maximum_total_deep_review_bytes"] == 536870912
    assert controls["maximum_source_root_mutations"] == 0


def test_parser_duplicate_snapshot_and_hostile_content_controls_are_frozen() -> None:
    value = read(RESULT)
    parser = value["passive_parser_and_hostile_content_contract"]
    assert parser["recursive_archive_expansion_depth"] == 0
    assert parser["macros_executed"] is False
    assert parser["archived_code_imported_compiled_or_executed"] is False
    assert parser["network_access_from_parsers"] is False
    assert parser["symlink_junction_reparse_or_path_escape_allowed"] is False
    assert value["duplicate_and_lineage_contract"]["no_source_gains_authority_from_recency_or_copy_count"] is True
    assert value["root_snapshot_contract"]["material_root_mutation_blocks_the_program"] is True


def test_contract_checklists_and_seven_evidence_classes_are_exact() -> None:
    value = read(RESULT)
    assert len(value["missing_contract_checklists"]["CP_NLSE"]) == 10
    assert len(value["missing_contract_checklists"]["LCRD_V3"]) == 8
    assert value["evidence_strength_vocabulary"] == [
        "EXACT_SOURCE_BOUND_CONTRACT_RECOVERED",
        "PARTIAL_CONTRACT_RECOVERED",
        "CONFLICTING_SOURCE_CONTRACTS",
        "DERIVED_SUMMARY_WITH_PRIMARY_SOURCE_MISSING",
        "NUMERICAL_DEFAULT_ONLY",
        "HEURISTIC_NOT_A_CONTRACT",
        "NO_RELEVANT_EVIDENCE",
    ]
    admissibility = value["positive_recovery_admissibility_rule"]
    assert admissibility["minimum_exact_recovered_contract_count"] == 1
    assert admissibility["must_materially_close_a_previously_missing_contract"] is True
    assert admissibility["unresolved_conflict_disqualifies_positive_credit_for_that_contract"] is True


def test_four_stages_two_scientific_outcomes_and_handoff_are_frozen() -> None:
    value = read(RESULT)
    stages = value["stages"]
    assert [row["stage_number"] for row in stages] == [1, 2, 3, 4]
    assert [row["semantic_stage_id"] for row in stages] == [
        "TARGETED_CCFT_CLOSURE_SOURCE_DISCOVERY_AND_CUSTODY",
        "TARGETED_CCFT_CLOSURE_CONTRACT_EXTRACTION",
        "TARGETED_CCFT_CONTRACT_COMPLETENESS_AND_CONFLICT_ADJUDICATION",
        "TARGETED_CCFT_RECOVERY_RESULT_AND_CONSTRUCTION_HANDOFF",
    ]
    assert value["program_scientific_terminal_outcomes"] == [
        "TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERED",
        "NO_ADDITIONAL_CCFT_CLOSURE_EVIDENCE_FOUND",
    ]
    assert value["mandatory_exit_target_proposed"] == "close_toe_targeted_ccft_closure_evidence_recovery_v0_after_bounded_result_v0"
    handoff = value["required_post_outcome_handoff"]
    assert handoff["applies_after_either_scientific_terminal_outcome"] is True
    assert handoff["target"] == "prepare_bounded_ccft_v0_theory_construction_program"
    assert handoff["preparation_authorized_by_recovery_program"] is False
    assert handoff["additional_historical_recovery_after_handoff"] is False


def test_proposal_is_uninstalled_unopened_and_nonexecuting() -> None:
    value = read(RESULT)
    assert value["proposed_program_id"] == PROGRAM_ID
    assert value["status"] == "PROGRAM_PROPOSAL_PREPARED_AWAITING_SEPARATE_INSTALLATION_AUTHORITY"
    assert value["terminal_outcome"] == "TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_PROGRAM_PROPOSAL_PREPARED"
    assert all(item is False for item in value["nonclaim_boundary"].values())


def test_independent_review_accepts_only_the_uninstalled_proposal() -> None:
    review = read(REVIEW)
    assert review["reviewed_result"]["sha256"] == sha(RESULT)
    assert review["accepted"] is True
    assert review["proposal_only"] is True
    assert review["program_installed"] is False
    assert review["scientific_stage_opened"] is False
    assert review["archive_search_executed"] is False
    assert review["failed_checks"] == []
    assert all(review["checks"].values())
