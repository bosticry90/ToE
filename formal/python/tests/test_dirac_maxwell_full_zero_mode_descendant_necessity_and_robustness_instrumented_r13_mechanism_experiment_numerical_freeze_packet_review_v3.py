from __future__ import annotations

import json
from functools import lru_cache
from pathlib import Path
from typing import Any

import pytest

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_numerical_freeze_packet_review_v3
    as review,
)


ROOT = find_repo_root(Path(__file__))


@lru_cache(maxsize=1)
def _raw() -> bytes:
    return review.artifact_bytes()


@lru_cache(maxsize=1)
def _report() -> dict[str, Any]:
    value = json.loads(_raw().decode("utf-8"))
    assert isinstance(value, dict)
    return value


def test_review_anchor_regenerates_exactly_and_deterministically() -> None:
    raw = _raw()
    assert (ROOT / review.REPORT_RELATIVE_PATH).read_bytes() == raw
    assert review.artifact_bytes() == raw


def test_all_twelve_independent_acceptance_checks_pass() -> None:
    report = _report()
    assert report["verdict"] == review.ACCEPT_VERDICT
    assert report["acceptance_check_count"] == 12
    assert report["passed_acceptance_check_count"] == 12
    assert report["failed_acceptance_check_count"] == 0
    assert report["failed_acceptance_ids"] == []
    assert report["blocking_outcomes"] == []
    assert all(item["passed"] for item in report["acceptance_checks"])


def test_artifact_freshness_and_blocked_predecessor_history_are_exact() -> None:
    audit = _report()["artifact_and_predecessor_history_audit"]
    assert audit["artifact_count"] == audit["exact_artifact_count"] == 5
    assert audit["stored_sha256"] == audit["expected_sha256"]
    assert audit["subprocess_regeneration_sha256"] == audit["expected_sha256"]
    assert audit["subprocess_regeneration_byte_exact"] is True
    assert audit["cross_bindings_exact"] is True
    assert audit["v1_remains_stale"] is True
    assert audit["v1_stale_path_count"] > 0
    assert audit["v2_review_verdict"] == "BLOCK_EXECUTOR_PREFLIGHT_CONFIGURATION"
    assert audit["v2_historical_preflight_validates_unresolved_template"] is True


def test_role_resolved_values_are_transitively_bound_and_deterministic() -> None:
    audit = _report()["independent_identity_and_resolution_audit"]
    assert audit["scientific_input_reconstruction_count"] == 6
    assert audit["unique_scientific_input_count"] == 3
    assert audit["complete_execution_identity_reconstruction_count"] == 6
    assert audit["unique_complete_execution_identity_count"] == 6
    assert audit["resolved_configuration_reconstruction_count"] == 6
    assert audit["all_resolution_rows_pass"] is True
    assert audit["transitive_identity_probe_count"] == 3
    assert audit["all_role_resolved_values_transitively_bound"] is True
    assert {item["probe_id"] for item in audit["transitive_identity_probes"]} == {
        "block_floor",
        "block_scale",
        "role",
    }
    assert all(
        item["complete_execution_identity_changed"]
        for item in audit["transitive_identity_probes"]
    )


def test_all_three_pairs_match_after_resolution() -> None:
    audit = _report()["independent_identity_and_resolution_audit"]
    assert audit["pair_count"] == 3
    assert audit["all_pair_integrity_checks_pass"] is True
    for pair in audit["pair_rows"]:
        assert pair["physical_core_equal"] is True
        assert pair["resolved_metric_configuration_equal"] is True
        assert pair["block_floors_equal"] is True
        assert pair["block_scales_equal"] is True
        assert pair["complete_execution_identity_distinct"] is True


def test_prior_and_v3_mutations_are_atomic_exact_and_preexecution() -> None:
    report = _report()
    prior = report["prior_identity_mutation_audit"]
    assert prior["registered_mutation_count"] == 20
    assert prior["executed_mutation_count"] == 20
    assert prior["atomic_mutation_count"] == 20
    assert prior["exact_first_diagnostic_count"] == 20
    assert prior["rejected_before_simulation_count"] == 20
    assert prior["output_creation_count"] == 0
    v3 = report["v3_resolution_diagnostic_audit"]
    assert v3["registered_control_count"] == 8
    assert v3["executed_control_count"] == 8
    assert v3["atomic_control_count"] == 8
    assert v3["exact_diagnostic_count"] == 8
    assert v3["plan_construction_count"] == 0
    assert v3["simulation_entry_count"] == 0
    assert v3["output_creation_count"] == 0


def test_final_fixed_anchor_real_preflight_is_repeatable_and_read_only(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    for key, value in review.implementation_v0.REQUIRED_EXECUTION_ENVIRONMENT.items():
        monkeypatch.setenv(key, value)
    output_root = ROOT / review.custody_v3.EXPERIMENT_OUTPUT_ROOT_RELATIVE_PATH
    canonical_before = review.canonical_v0.canonical_root_digest()
    tree_before = review.canonical_v0.canonical_directory_tree_sha256()
    executor_before = review._global_configuration_digest(review.executor_v3)
    implementation_before = review._global_configuration_digest(
        review.implementation_v0
    )
    first = review.executor_v3.preflight_frozen_execution(ROOT)
    second = review.executor_v3.preflight_frozen_execution(ROOT)
    assert first == second
    assert first["all_passed"] is True
    assert first["read_only_execution_plan_count"] == 6
    assert len(first["read_only_execution_plans"]) == 6
    assert first["simulation_entry_count"] == 0
    assert first["execution_invoked"] is False
    assert first["output_root_absent"] is True
    assert not output_root.exists()
    assert review.canonical_v0.canonical_root_digest() == canonical_before
    assert review.canonical_v0.canonical_directory_tree_sha256() == tree_before
    assert review._global_configuration_digest(review.executor_v3) == executor_before
    assert review._global_configuration_digest(
        review.implementation_v0
    ) == implementation_before


def test_authority_is_one_execution_only_and_claims_remain_blocked() -> None:
    report = _report()
    authority = report[review.custody_v3.REVIEW_AUTHORITY_FIELD]
    assert review.executor_v3._validate_freeze_anchor(report) == []
    assert authority["execution_authorized"] is True
    assert authority["one_execution_only"] is True
    assert authority["automatic_retries_authorized"] is False
    assert authority["exact_run_ids"] == list(review.custody_v3.EXACT_RUN_IDS)
    assert report["selected_next_target"] == review.ACCEPTED_NEXT_TARGET
    rotation = report["authority_rotation"]
    assert rotation["one_time_execution_count_authorized"] == 1
    assert rotation["exact_authorized_run_count"] == 6
    assert rotation["rerun_authorized"] is False
    assert rotation["substitution_authorized"] is False
    assert rotation["result_acceptance_authorized"] is False
    preserved = report["preserved_scientific_core"]
    assert preserved["fourteen_row_robustness"] == "NUMERICALLY_BLOCKED"
    assert preserved["R13_root_mechanism"] == "UNRESOLVED"
    assert preserved["new_E_REPRO"] == "NONE"
    assert not (
        ROOT / review.custody_v3.EXPERIMENT_OUTPUT_ROOT_RELATIVE_PATH
    ).exists()
