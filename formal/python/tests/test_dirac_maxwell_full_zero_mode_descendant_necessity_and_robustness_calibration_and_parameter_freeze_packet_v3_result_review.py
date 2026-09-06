from __future__ import annotations

import json
import subprocess
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_calibration_and_parameter_freeze_packet_v3_result_review
    as review,
)


ROOT = find_repo_root(Path(__file__))
REPORT_PATH = ROOT / review.REPORT_RELATIVE_PATH


def _report() -> dict:
    return json.loads(REPORT_PATH.read_text(encoding="utf-8"))


def test_independent_review_artifact_is_current() -> None:
    assert REPORT_PATH.read_bytes() == review.artifact_bytes()


def test_preparation_commit_and_all_seven_v3_inputs_are_exact() -> None:
    assert subprocess.check_output(["git", "rev-parse", f"{review.PREPARATION_COMMIT}^"], cwd=ROOT).decode().strip() == review.PREPARATION_PARENT
    for path, digest in review.V3_INPUT_HASHES.items():
        assert review.sha256_path(ROOT / path) == digest
        assert review.sha256_bytes(review.git_bytes(review.PREPARATION_COMMIT, path)) == digest


def test_preserved_v2_scientific_contract_is_reconstructed_not_inferred() -> None:
    audit = _report()["independent_scientific_freeze_audit"]
    assert audit["scientific_rows"] == 14
    assert audit["scientific_records"] == 182
    assert audit["control_records"] == 21
    assert audit["total_records"] == audit["identity_records"] == 203
    assert audit["threshold_count"] == 22
    assert audit["convergence_classes"] == {
        "FIRST_ORDER_WILSON_AFFECTED_SPATIAL": 0.8,
        "SECOND_ORDER_TEMPORAL": 1.5,
        "SECOND_ORDER_ENERGY_ERROR": 1.5,
    }
    assert audit["materiality_gates"] == {"material_R_perp_gate": 0.1, "descendant_dominated_R_perp_gate": 0.5}
    assert audit["all_fourteen_rows_have_thirteen_records"] is True
    assert audit["run_ids_unique"] is True
    assert audit["matrix_identity_run_ids_equal"] is True


def test_baseline_is_independently_rebuilt_from_v2_inputs() -> None:
    bundle = review.load_json(review.V3_BUNDLE_RELATIVE_PATH)
    rebuilt = review.reconstruct_passing_baseline()
    assert rebuilt == bundle["baseline_fixture"]
    assert review.sha256_bytes(review.canonical_json_bytes(rebuilt)) == bundle["baseline_fixture_hash"]
    result = review.independently_classify_fixture(rebuilt)
    assert result["decision"] == review.BASELINE_DECISION
    assert result["first_diagnostic"] == "BASELINE_ACCEPTED"


def test_review_does_not_import_the_v3_preparation_module_or_use_combined_flags() -> None:
    source = (ROOT / review.SCRIPT_RELATIVE_PATH).read_text(encoding="utf-8")
    imports = source.split("REPO_ROOT =", 1)[0]
    assert "calibration_and_parameter_freeze_packet_v3 as" not in imports
    independence = _report()["reviewer_independence"]
    assert independence["v3_preparation_module_imported"] is False
    assert independence["v3_mutation_constructors_shared"] is False
    assert independence["preparation_combined_pass_flags_used"] is False


def test_all_twenty_three_mutations_are_replayed_from_fresh_fixtures() -> None:
    audit = _report()["independent_mutation_audit"]
    assert audit["registered_mutation_count"] == audit["independently_replayed_count"] == 23
    assert audit["all_changed_exactly_one_premise"] is True
    assert audit["all_registered_old_and_new_values_confirmed"] is True
    assert audit["all_expected_first_diagnostics_reproduced"] is True
    assert audit["all_expected_decision_deltas_reproduced"] is True
    assert audit["preparation_execution_result_agreement"] is True
    assert all(item["fresh_fixture_used"] for item in audit["reconstructions"])
    assert all(item["preparation_combined_pass_flag_used"] is False for item in audit["reconstructions"])
    assert all(item["independent_changed_field_count"] == 1 for item in audit["reconstructions"])


def test_registered_pointer_old_new_diagnostic_and_decision_are_exact() -> None:
    bundle = review.load_json(review.V3_BUNDLE_RELATIVE_PATH)
    baseline = review.reconstruct_passing_baseline()
    baseline_hash = review.sha256_bytes(review.canonical_json_bytes(baseline))
    for contract in bundle["mutation_registry"]:
        if contract["old_value"] != review.ABSENT:
            assert review.independent_pointer_read(baseline, contract["target_field_locator"]) == contract["old_value"]
        result = review.independently_replay_mutation(contract, baseline, baseline_hash)
        assert result["independent_first_diagnostic"] == contract["expected_first_diagnostic"]
        assert result["independent_decision_after"] == contract["expected_decision_after"]
        assert result["independent_diff_pointer"] == contract["target_field_locator"]


def test_all_five_v2_defects_are_semantically_repaired() -> None:
    audit = _report()["independent_five_defect_audit"]
    assert audit and all(audit.values())


def test_six_preparation_meta_regressions_and_review_decision_probe_discriminate() -> None:
    audit = _report()["independent_meta_regression_audit"]
    assert audit["preparation_meta_regression_count"] == 6
    assert audit["independently_reconstructed_preparation_meta_regressions"] == 6
    assert audit["reviewer_only_decision_delta_probe_count"] == 1
    assert audit["all_seven_review_probes_passed"] is True
    assert len(audit["probes"]) == 7
    assert {item["observed_diagnostic"] for item in audit["probes"]} >= {
        "MUTATION_DIRECTION_MISMATCH",
        "MUTATION_TARGET_FEATURE_CLASS_MISMATCH",
        "MUTATION_NONATOMIC_CHANGED_FIELD_COUNT_2",
        "B-BLOCKED_DIAGNOSTIC_PRECEDENCE",
        "MUTATION_RAW_FAILURE_NOT_REALIZED",
        "B-BLOCKED_DECISION_DELTA",
    }


def test_committed_configuration_custody_is_independently_reproduced() -> None:
    custody = _report()["independent_committed_input_custody_audit"]
    assert custody["record_count"] == 4
    assert custody["all_records_exact"] is True
    assert custody["v3_paths_have_LF_custody_in_preparation_commit"] is True
    assert custody["generator_reads_authoritative_config_with_git_show"] is True
    assert custody["generator_does_not_read_worktree_config_as_authority"] is True
    assert all(item["git_blob_oid_exact"] and item["committed_sha256_exact"] for item in custody["records"])
    assert all(item["working_tree_hash_not_regeneration_input"] for item in custody["records"])


def test_acceptance_authorizes_only_one_exact_execution() -> None:
    report = _report()
    assert report["verdict"] == "ACCEPT_FREEZE"
    assert report["selected_next_target"] == review.EXECUTION_TARGET
    authority = report["authority_rotation"]
    assert authority["freeze_v3_independently_accepted"] is True
    assert authority["exact_203_record_execution_authorized_once"] is True
    assert authority["dynamic_run_generation_or_exclusion_authorized"] is False
    assert authority["additional_pilot_authorized"] is False
    assert authority["threshold_or_classifier_change_authorized"] is False
    assert authority["interpretation_driven_rerun_authorized"] is False
    assert authority["execution_may_award_final_scientific_verdict"] is False
    assert authority["independent_canonical_result_review_required"] is True
    assert authority["new_scientific_claim_authorized"] is False


def test_historical_boundaries_and_prompt_are_preserved() -> None:
    report = _report()
    boundary = report["historical_validation_boundary"]
    assert boundary["freeze_v2_report_rewritten"] is False
    assert boundary["two_historical_worktree_sensitive_regeneration_tests_remain_documented"] is True
    assert boundary["historical_repository_wide_Lean"]["status"] == "INCOMPLETE_TIMEOUT"
    assert boundary["repository_wide_green_claim"] is False
    assert review.PROMPT_DEPENDENCY_ROLE == "DEMOTE_TO_NONBLOCKING_PROVENANCE"
