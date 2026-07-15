from __future__ import annotations

import json
import subprocess
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_calibration_and_parameter_freeze_packet_v3
    as freeze,
)


ROOT = find_repo_root(Path(__file__))


def _load(relative_path: str) -> dict:
    return json.loads((ROOT / relative_path).read_text(encoding="utf-8"))


def test_generated_v3_artifacts_are_current() -> None:
    expected = freeze.artifact_bytes()
    assert all((ROOT / path).read_bytes() == raw for path, raw in expected.items())


def test_v3_is_bounded_to_the_v2_mutation_and_configuration_custody_blockers() -> None:
    packet = _load(freeze.PACKET_RELATIVE_PATH)
    assert packet["verdict"] == "PREPARED_PENDING_INDEPENDENT_REVIEW"
    assert packet["bounded_v3_correction_scope"] == {
        "corrected_only": [
            "mutation causal contracts",
            "fresh-fixture atomicity",
            "first-diagnostic precedence",
            "committed-configuration custody",
        ],
        "scientific_design_changed": False,
        "pilot_changed_or_reopened": False,
        "classifier_changed": False,
        "threshold_values_changed": False,
        "canonical_run_matrix_changed": False,
        "additional_pilot_required": False,
    }
    assert packet["selected_next_target"] == freeze.REVIEW_TARGET
    assert packet["authority_boundary"]["canonical_203_record_execution_authorized"] is False
    assert packet["authority_boundary"]["new_E_REPRO_claim"] is False


def test_v2_scientific_contract_is_byte_preserved() -> None:
    packet = _load(freeze.PACKET_RELATIVE_PATH)
    preserved = packet["preserved_v2_contract"]
    assert preserved["scientific_rows"] == 14
    assert preserved["scientific_records"] == 182
    assert preserved["positive_controls"] == 8
    assert preserved["negative_controls"] == 13
    assert preserved["total_canonical_records"] == 203
    assert preserved["numerical_threshold_values"] == 22
    assert preserved["convergence_classes"] == {
        "FIRST_ORDER_WILSON_AFFECTED_SPATIAL": 0.8,
        "SECOND_ORDER_TEMPORAL": 1.5,
        "SECOND_ORDER_ENERGY_ERROR": 1.5,
    }
    assert preserved["materiality_gates"] == {"materially_influential": 0.1, "descendant_dominated": 0.5}
    for path, digest in freeze.PRESERVED_INPUT_HASHES.items():
        assert freeze.sha256_path(ROOT / path) == digest


def test_baseline_fixture_is_fresh_complete_and_admissible() -> None:
    bundle = _load(freeze.BUNDLE_RELATIVE_PATH)
    baseline = bundle["baseline_fixture"]
    assert bundle["baseline_fixture_hash"] == freeze.sha256_bytes(freeze.canonical_json_bytes(baseline))
    assert len(baseline["declared_expected_run_ids"]) == 203
    assert len(baseline["output_payloads"]) == 203
    assert freeze._classify(baseline)["decision"] == freeze.BASELINE_DECISION
    assert bundle["canonical_scientific_execution_record_count_change"] == 0


def test_all_twenty_three_mutations_have_the_closed_causal_schema() -> None:
    bundle = _load(freeze.BUNDLE_RELATIVE_PATH)
    registry = bundle["mutation_registry"]
    required = {
        "mutation_id", "mutation_title", "baseline_fixture_id", "baseline_fixture_hash", "baseline_expected_verdict",
        "target_artifact_id", "target_record_id", "target_field_locator", "target_feature_class", "premise_class",
        "old_value", "new_value", "changed_field_count", "expected_first_diagnostic", "expected_decision_before",
        "expected_decision_after", "expected_eligibility_delta", "expected_materiality_delta", "forbidden_prior_diagnostics",
        "forbidden_unrelated_decision_changes", "mutation_constructor_id", "fresh_fixture_required", "atomicity_assertion",
        "derived_rebindings", "raw_failure_contract",
    }
    assert len(registry) == len({item["mutation_id"] for item in registry}) == 23
    assert all(set(item) == required for item in registry)
    assert all(item["changed_field_count"] == 1 for item in registry)
    assert all(item["fresh_fixture_required"] is True for item in registry)
    assert all(item["target_field_locator"].startswith("/") for item in registry)


def test_all_mutations_rebuild_fresh_fixture_and_change_exactly_one_premise() -> None:
    bundle = _load(freeze.BUNDLE_RELATIVE_PATH)
    baseline = bundle["baseline_fixture"]
    reconstructed = [freeze.execute_mutation(contract, baseline) for contract in bundle["mutation_registry"]]
    assert len(reconstructed) == 23
    assert all(item["passed"] for item in reconstructed)
    assert all(item["changed_field_count"] == 1 for item in reconstructed)
    assert all(item["canonical_diff_pointers"] for item in reconstructed)
    assert reconstructed == bundle["mutation_execution_results"]


def test_five_v2_nonatomic_findings_are_repaired_semantically() -> None:
    bundle = _load(freeze.BUNDLE_RELATIVE_PATH)
    registry = {item["mutation_id"]: item for item in bundle["mutation_registry"]}

    comparator = registry["M_V3_COMPARATOR_THRESHOLD_APPLIED_TO_PRIMARY"]
    assert comparator["old_value"] == ["INTENTIONALLY_NONINVARIANT_COMPARATOR"]
    assert comparator["new_value"] == ["INTENTIONALLY_NONINVARIANT_COMPARATOR", "FULL_MODEL"]
    assert comparator["expected_first_diagnostic"] == "THRESHOLD_SCOPE_MODEL_CLASS_MISMATCH"

    phase = registry["M_V3_PHASE_CONTROL_ON_PHASE_TRIVIAL_ROW"]
    assert phase["target_record_id"] == "PHASE_EXCHANGE_SIGN_CONTROL"
    assert phase["target_feature_class"] == "DELTA_THETA_PSI_NONTRIVIAL"
    assert phase["expected_first_diagnostic"] == "CONTROL_REQUIRED_PHASE_FEATURE_ABSENT"

    holonomy = registry["M_V3_HOLONOMY_CONTROL_ON_TRIVIAL_ROW"]
    assert holonomy["target_record_id"] == "NONTRIVIAL_HOLONOMY_CONTROL"
    assert holonomy["target_feature_class"] == "THETA_W_NONTRIVIAL"
    assert holonomy["expected_first_diagnostic"] == "CONTROL_REQUIRED_HOLONOMY_FEATURE_ABSENT"

    materiality = registry["M_V3_MATERIALITY_AFTER_NUMERICAL_BLOCK"]
    assert materiality["target_field_locator"].endswith("/series/gauss_residual/1")
    assert materiality["expected_decision_after"] == "NUMERICALLY_BLOCKED"
    assert materiality["expected_materiality_delta"] == "DESCENDANT_CLASS_TO_NOT_EVALUATED_NUMERICAL_BLOCK"

    supplied_pass = registry["M_V3_SUPPLIED_PASS_TRUE_WITH_RAW_FAILURE"]
    assert supplied_pass["target_field_locator"].endswith("/series/solver_residual/1")
    assert supplied_pass["new_value"] == 1.0
    assert supplied_pass["raw_failure_contract"] != "NOT_APPLICABLE"


def test_six_mutation_system_meta_regressions_discriminate_exactly() -> None:
    bundle = _load(freeze.BUNDLE_RELATIVE_PATH)
    results = bundle["mutation_system_meta_regressions"]
    assert len(results) == 6
    assert all(item["passed"] for item in results)
    assert {item["observed_diagnostic"] for item in results} == {
        "MUTATION_DIRECTION_MISMATCH",
        "MUTATION_TARGET_FEATURE_CLASS_MISMATCH",
        "MUTATION_NONATOMIC_CHANGED_FIELD_COUNT_2",
        "MUTATION_EXPECTED_DIAGNOSTIC_NOT_FIRST",
        "MUTATION_RAW_FAILURE_NOT_REALIZED",
    }


def test_committed_configuration_custody_uses_git_bytes_not_worktree_bytes() -> None:
    packet = _load(freeze.PACKET_RELATIVE_PATH)
    custody = packet["committed_configuration_custody"]
    assert custody["source_commit"] == freeze.SOURCE_REVIEW_COMMIT
    assert custody["all_authoritative_hashes_use_committed_bytes"] is True
    assert {item["path"] for item in custody["records"]} == set(freeze.COMMITTED_CONFIGURATION_PATHS)
    for record in custody["records"]:
        raw = subprocess.check_output(["git", "show", f"{freeze.SOURCE_REVIEW_COMMIT}:{record['path']}"], cwd=ROOT)
        oid = subprocess.check_output(["git", "rev-parse", f"{freeze.SOURCE_REVIEW_COMMIT}:{record['path']}"], cwd=ROOT).decode().strip()
        assert record["git_blob_oid"] == oid
        assert record["sha256_of_committed_bytes"] == freeze.sha256_bytes(raw)
        assert record["working_tree_hash_is_regeneration_input"] is False
        assert record["working_tree_sha256_at_preparation"] == freeze.WORKING_TREE_SHA256_AT_PREPARATION[record["path"]]


def test_historical_v2_validation_limitation_is_preserved_without_rewriting_v2() -> None:
    packet = _load(freeze.PACKET_RELATIVE_PATH)
    correction = packet["historical_validation_correction"]
    assert correction["freeze_v2_report_rewritten"] is False
    assert correction["freeze_v2_post_commit_99_test_assertion_fully_reproducible"] is False
    assert correction["committed_v2_artifact_identities_remain_exact"] is True
    assert correction["v3_authoritative_configuration_hashes_use_git_show_committed_bytes"] is True


def test_prompt_and_claim_boundary_remain_unchanged() -> None:
    packet = _load(freeze.PACKET_RELATIVE_PATH)
    assert freeze.sha256_path(ROOT / freeze.PROMPT_RELATIVE_PATH) == freeze.PROMPT_SHA256
    assert packet["authority_boundary"]["robustness_classification_assigned"] is False
    assert packet["authority_boundary"]["descendant_materiality_classification_assigned"] is False
    assert packet["historical_repository_wide_Lean"]["status"] == "INCOMPLETE_TIMEOUT"
    assert packet["historical_repository_wide_Lean"]["repository_wide_green_claim"] is False
