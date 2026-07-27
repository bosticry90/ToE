from __future__ import annotations

import json
from functools import lru_cache
from pathlib import Path
from typing import Any

import pytest

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_executor_v2
    as executor_v2,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_numerical_freeze_packet_review_v2
    as review,
)


ROOT = find_repo_root(Path(__file__))


@lru_cache(maxsize=1)
def _raw() -> bytes:
    return review.artifact_bytes()


@lru_cache(maxsize=1)
def _report() -> dict[str, Any]:
    return json.loads(_raw().decode("utf-8"))


def test_review_artifact_is_current_and_deterministic() -> None:
    raw = _raw()
    assert (ROOT / review.REPORT_RELATIVE_PATH).read_bytes() == raw
    assert review.artifact_bytes() == raw


def test_independent_review_blocks_only_the_executor_preflight_configuration() -> None:
    report = _report()
    assert report["verdict"] == "BLOCK_EXECUTOR_PREFLIGHT_CONFIGURATION"
    assert report["acceptance_check_count"] == 11
    assert report["passed_acceptance_check_count"] == 10
    assert report["failed_acceptance_check_count"] == 1
    assert report["failed_acceptance_ids"] == [
        "executor_anchor_API_and_read_only_preflight_are_exact"
    ]
    finding = report["blocking_findings"][0]
    assert finding["finding_id"] == (
        "B_V2_EXECUTOR_PREFLIGHT_REJECTS_FROZEN_METRIC_TEMPLATE"
    )
    assert finding["observed_first_diagnostic"] == (
        "ValueError:metric_configuration missing block_floors"
    )


def test_all_v2_identity_freshness_runtime_and_mutation_repairs_pass_review() -> None:
    report = _report()
    freshness = report["reviewed_artifact_freshness"]
    assert freshness["artifact_count"] == freshness["exact_artifact_count"] == 5
    assert freshness["v2_subprocess_regeneration_byte_exact"] is True
    assert freshness["v1_remains_stale"] is True
    assert freshness["v1_stale_diagnostic_preserved"] is True

    identities = report["independent_identity_reconstruction_audit"]
    assert identities["scientific_input_reconstruction_count"] == 6
    assert identities["unique_scientific_input_count"] == 3
    assert identities["complete_execution_identity_reconstruction_count"] == 6
    assert identities["unique_complete_execution_identity_count"] == 6
    assert identities["all_three_pairs_scientifically_identical"] is True
    assert identities["all_three_pair_execution_identities_distinct"] is True

    runtime = report["runtime_source_closure_audit"]
    assert runtime["frozen_module_count"] == runtime["loaded_module_count"] == 8
    assert runtime["all_loaded_paths_bytes_and_loaders_exact"] is True
    assert runtime["hostile_same_name_wrong_path_rejected"] is True
    assert runtime["wrong_frozen_bytes_rejected"] is True
    assert runtime["wrong_loader_rejected"] is True

    mutations = report["identity_mutation_audit"]
    assert mutations["executed_mutation_count"] == 20
    assert mutations["atomic_mutation_count"] == 20
    assert mutations["rejected_before_simulation_count"] == 20
    assert mutations["exact_first_diagnostic_count"] == 20
    assert mutations["exact_final_block_decision_count"] == 20
    assert mutations["output_creation_count"] == 0


def test_role_resolved_configs_are_valid_but_raw_template_breaks_preflight() -> None:
    audit = _report()["executor_authority_audit"]
    assert audit["accepted_authority_diagnostics"] == []
    assert audit["resolved_role_configuration_valid_count"] == 6
    assert audit["unresolved_metric_template_validation_passed"] is False
    assert audit["executor_preflight_validates_unresolved_template"] is True
    assert audit["accepted_anchor_can_complete_read_only_preflight"] is False


def test_instrumentation_is_registered_read_only_but_not_yet_observed() -> None:
    audit = _report()["instrumentation_registration_audit"]
    assert audit["pair_count"] == 3
    assert audit["all_pair_physics_and_initial_states_exact"] is True
    assert audit["all_instrumentation_registered_read_only"] is True
    assert audit["step_observer_cannot_write_physical_state"] is True
    assert audit["role_instrumentation_cannot_write_physical_state"] is True
    assert audit["stopping_test_is_independent_of_observer"] is True
    assert audit["actual_nonperturbation_result_evaluated"] is False


def test_blocked_review_anchor_cannot_authorize_preflight_or_output() -> None:
    output_root = ROOT / review.custody_v2.EXPERIMENT_OUTPUT_ROOT_RELATIVE_PATH
    assert not output_root.exists()
    with pytest.raises(executor_v2.RuntimeCustodyError, match="REVIEW_ANCHOR_NOT_ACCEPTED"):
        executor_v2.preflight_frozen_execution(ROOT)
    assert not output_root.exists()


def test_authority_rotates_only_to_versioned_v3_correction() -> None:
    report = _report()
    assert report["selected_next_target"] == review.BLOCKED_NEXT_TARGET
    assert "runtime_execution_authority" not in report
    authority = report["authority_rotation"]
    assert authority["numerical_freeze_v2_accepted"] is False
    assert authority["execution_authorized"] is False
    assert authority["one_time_execution_count_authorized"] == 0
    assert authority["exact_authorized_run_count"] == 0
    assert authority["rerun_authorized"] is False
    canonical = report["canonical_custody"]
    assert canonical["canonical_inventory_exact"] is True
    assert canonical["canonical_tree_exact"] is True
    assert canonical["experiment_output_root_absent"] is True
    assert canonical["canonical_robustness"] == "NUMERICALLY_BLOCKED"
    assert canonical["R13_root_mechanism"] == "UNRESOLVED"
