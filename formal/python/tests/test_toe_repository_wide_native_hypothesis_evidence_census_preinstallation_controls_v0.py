from __future__ import annotations

import subprocess
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_repository_wide_native_hypothesis_evidence_census_preinstallation_controls_v0 import (
    MANDATORY_EXIT_TARGET,
    STAGES,
    build,
)


REPO_ROOT = find_repo_root(Path(__file__))


def _git(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["git", *args],
        cwd=REPO_ROOT,
        check=False,
        capture_output=True,
        text=True,
    )


def test_canonical_identifiers_and_exit_are_preserved() -> None:
    result = build()
    contract = result["canonical_identifier_contract"]
    assert contract["semantic_stages"] == STAGES
    assert contract["mandatory_exit_target"] == MANDATORY_EXIT_TARGET
    assert [item["semantic_stage_id"] for item in STAGES] == [
        "REPOSITORY_WIDE_SOURCE_CENSUS",
        "DEDUPLICATION_AND_LINEAGE_RECONSTRUCTION",
        "NATIVE_CLAIM_EXTRACTION_AND_CLASSIFICATION",
        "CURRENT_HYPOTHESIS_RECONCILIATION",
        "NATIVE_FRONTIER_DECISION",
    ]


def test_workload_and_selection_are_numerically_bounded() -> None:
    result = build()
    budgets = result["workload_budgets"]
    selection = result["deep_review_selection_contract"]
    assert budgets["maximum_eligible_deep_review_files"] == 640
    assert budgets["maximum_eligible_deep_review_bytes"] == 1_073_741_824
    assert budgets["maximum_files_per_hypothesis_domain"] == 64
    assert budgets["maximum_files_per_source_lineage"] == 8
    assert budgets["maximum_extracted_claims"] == 4096
    assert budgets["maximum_claims_per_file"] == 32
    assert budgets["maximum_total_extracted_text_bytes"] == 268_435_456
    assert selection["manual_preference_permitted"] is False
    assert selection["overflow_population_and_unreviewed_counts_recorded"] is True
    assert selection["tie_breaking_order"] == [
        "source_root_id",
        "normalized_relative_path_utf8_bytes",
        "sha256",
    ]


def test_snapshot_parser_and_cache_contracts_fail_closed() -> None:
    result = build()
    snapshot = result["source_root_snapshot_contract"]
    parser = result["parser_contract"]
    cache = result["byte_identity_and_cache_contract"]
    assert snapshot["material_mutation_blocks_stage"] is True
    assert snapshot["absolute_paths_in_snapshot_hash"] is False
    assert snapshot["timestamps_in_snapshot_hash"] is False
    assert parser["never_execute_import_compile_or_activate_archived_content"] is True
    assert parser["network_access"] == "DENY"
    assert parser["recursive_archive_expansion"] == "DENY"
    assert parser["unsupported_file_status"] == "UNSUPPORTED_FORMAT_PRESERVED"
    assert cache["tracked_primary_identity"] == "COMMITTED_GIT_BLOB_BYTES"
    assert cache["local_metadata_is_change_detection_hint_only"] is True
    assert cache["local_final_manifest_requires_verified_sha256"] is True
    assert cache["historical_index_must_not_be_overwritten"] == (
        "formal/output/archive_intake_index.json"
    )


def test_atomic_close_and_terminal_state_mapping_are_explicit() -> None:
    result = build()
    close = result["batch_and_atomic_close_contract"]
    state_map = result["terminal_state_map"]
    assert close["intermediate_substantive_batch_commits_permitted"] is False
    assert close["aggregate_manifest_binds_each_batch_hash"] is True
    assert close["batch_union_equals_declared_inventory"] is True
    assert close["batch_overlap_permitted"] is False
    assert close["batch_omission_permitted"] is False
    assert state_map["REPOSITORY_WIDE_SOURCE_CENSUS_COMPLETE"] == "PASS"
    assert state_map["SOURCE_ROOT_MUTATED_DURING_CENSUS"] == "BLOCKED"
    assert state_map["SOURCE_ROOT_UNAVAILABLE"] == "BLOCKED"
    assert state_map["DETERMINISTIC_INDEX_GENERATION_FAILED"] == "FAILED"
    assert result["terminal_state_qualifiers"][
        "BOUNDED_DEEP_REVIEW_COMPLETE_WITH_UNREVIEWED_OVERFLOW"
    ].endswith("REPOSITORY_CLAIM_EXHAUSTION_NOT_ESTABLISHED")


def test_exact_repository_ignore_policy_is_active_and_narrow() -> None:
    result = build()
    rules = result["repository_exclusion_contract"]["tracked_gitignore_rules"]
    gitignore = (REPO_ROOT / ".gitignore").read_text(encoding="utf-8")
    for rule in rules:
        assert rule in gitignore.splitlines()
    assert "/archive/**" not in gitignore.splitlines()
    assert "archive/**" not in gitignore.splitlines()

    intended = [
        "archive/ToE_Project/README.md",
        "archive/ToE_Project_Starter_2025-09-24/README.md",
        "archive/custody_bundles/example.bundle",
    ]
    for path in intended:
        checked = _git("check-ignore", "-v", "--no-index", path)
        assert checked.returncode == 0, (path, checked.stdout, checked.stderr)

    curated = _git(
        "check-ignore",
        "--no-index",
        "formal/docs/release/native_hypothesis_evidence_dossiers/example.json",
    )
    assert curated.returncode == 1

    tracked_under_roots = _git(
        "ls-files",
        "--",
        "archive/ToE_Project",
        "archive/ToE_Project_Starter_2025-09-24",
    )
    assert tracked_under_roots.returncode == 0
    assert tracked_under_roots.stdout.strip() == ""

    dry_run = _git("add", "-A", "--dry-run")
    assert dry_run.returncode == 0, dry_run.stderr
    assert "archive/ToE_Project/" not in dry_run.stdout
    assert "archive/ToE_Project_Starter_2025-09-24/" not in dry_run.stdout


def test_authority_boundary_remains_unopened_and_nonexecuting() -> None:
    boundary = build()["authority_boundary"]
    assert all(
        boundary[key] is False
        for key in [
            "program_installed",
            "stage_1_opened",
            "archive_scientifically_traversed",
            "source_classification_performed",
            "claims_extracted",
            "evidence_promoted",
            "native_hypothesis_selected",
            "index_or_cache_generated",
        ]
    )
    assert (
        boundary["next_valid_decision_after_acceptance"]
        == "AUTHORIZE_CENSUS_PROGRAM_INSTALLATION"
    )
