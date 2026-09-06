from __future__ import annotations

import json
from pathlib import Path

import pytest

from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_executor_custody_v1
    as custody,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_executor_v1
    as executor,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_numerical_freeze_packet_review_v1
    as review,
)


ROOT = review.REPO_ROOT


@pytest.fixture(scope="module")
def report() -> dict:
    return review.build_report()


def test_review_artifact_is_current_deterministic_and_blocked(report: dict) -> None:
    raw = review.canonical_json_bytes(report)
    assert (ROOT / review.REPORT_RELATIVE_PATH).read_bytes() == raw
    assert review.artifact_bytes() == raw
    assert report["target"] == review.TARGET
    assert report["verdict"] == "BLOCK_INPUT_HASH_RECONSTRUCTION"
    assert report["selected_next_target"].endswith(
        "instrumented_r13_mechanism_experiment_numerical_freeze_packet_v2"
    )
    assert report["authority_rotation"]["execution_authorized"] is False
    assert report["authority_rotation"]["versioned_freeze_v2_correction_authorized"] is True


def test_committed_closure_breaks_all_six_frozen_input_hashes(report: dict) -> None:
    audit = report["input_hash_reconstruction_audit"]
    assert audit["positive_inclusion_record_count"] == 6
    assert audit["frozen_stored_core_reconstruction_count"] == 6
    assert audit["current_committed_closure_reconstruction_count"] == 0
    assert audit["closure_digest_changed_after_source_commit_binding"] is True
    assert audit["frozen_null_source_commit_count"] == 6
    assert audit["all_runtime_bytes_and_blob_ids_exact"] is True
    assert audit["all_frozen_source_commits_exact"] is False
    assert audit["preparation_generator_check_passed"] is False
    assert audit["stale_artifact_paths"] == list(review.STALE_ARTIFACT_PATHS)


def test_twenty_mutations_reject_but_promised_diagnostics_do_not_match(
    report: dict,
) -> None:
    audit = report["executor_and_adversarial_audit"]
    assert audit["public_execution_parameters"] == ["repo_root"]
    assert audit["caller_can_supply_matrix_or_identity"] is False
    assert audit["strict_matrix_self_validation_diagnostics"] == []
    assert audit["identity_mutation_count"] == 20
    assert audit["identity_mutation_rejection_count"] == 20
    assert audit["identity_mutation_exact_diagnostic_count"] == 0
    assert audit["full_adversarial_registry_count"] == 41
    assert audit["full_adversarial_registry_unique_count"] == 41
    assert all(item["rejected"] for item in audit["mutation_results"])
    assert all(not item["exact_registered_diagnostic"] for item in audit["mutation_results"])


def test_remaining_scientific_and_custody_boundaries_are_preserved(
    report: dict,
) -> None:
    failed = set(report["failed_acceptance_ids"])
    assert failed == {
        "six_positive_inclusion_input_hashes_reconstruct",
        "run_id_only_executor_and_twenty_exact_mutation_diagnostics",
        "eight_loaded_modules_match_frozen_committed_files",
        "forty_one_controls_are_atomic_and_have_exact_outcomes",
    }
    assert report["passed_acceptance_check_count"] == 7
    assert report["failed_acceptance_check_count"] == 4
    custody_report = report["canonical_custody"]
    assert custody_report["file_count"] == 205
    assert custody_report["mechanism_output_root_absent_before_and_after_review"] is True
    assert not (ROOT / custody.EXPERIMENT_OUTPUT_ROOT_RELATIVE_PATH).exists()
    assert report["reviewer_independence"]["simulation_invocation_count"] == 0
    assert report["preserved_scientific_core"]["canonical_robustness"] == "NUMERICALLY_BLOCKED"
    assert report["preserved_scientific_core"]["R13_root_mechanism"] == "UNRESOLVED"
    assert report["preserved_scientific_core"]["new_E_REPRO"] == "NONE"


def test_blocked_review_anchor_fails_closed_before_output_creation() -> None:
    anchor = json.loads((ROOT / review.REPORT_RELATIVE_PATH).read_text(encoding="utf-8"))
    assert executor._validate_freeze_anchor(anchor) == ["REVIEW_ANCHOR_NOT_ACCEPTED"]
    with pytest.raises(executor.RuntimeCustodyError, match="REVIEW_ANCHOR_NOT_ACCEPTED"):
        executor.preflight_frozen_execution(ROOT)
    assert not (ROOT / custody.EXPERIMENT_OUTPUT_ROOT_RELATIVE_PATH).exists()
