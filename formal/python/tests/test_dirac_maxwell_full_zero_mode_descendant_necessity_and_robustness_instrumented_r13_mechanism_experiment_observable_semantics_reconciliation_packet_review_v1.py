from __future__ import annotations

import json
from functools import lru_cache
from pathlib import Path
from typing import Any

import pytest

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_implementation_v0
    as implementation_v0,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_observable_semantics_reconciliation_packet_review_v1
    as review_v1,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_observable_semantics_reconciliation_v1
    as reconciliation_v1,
)


ROOT = find_repo_root(Path(__file__))


@lru_cache(maxsize=1)
def _raw() -> bytes:
    return review_v1.artifact_bytes()


@lru_cache(maxsize=1)
def _review() -> dict[str, Any]:
    value = json.loads(_raw().decode("utf-8"))
    assert isinstance(value, dict)
    return value


def test_review_regenerates_exactly_and_deterministically() -> None:
    raw = _raw()
    assert (ROOT / review_v1.REPORT_RELATIVE_PATH).read_bytes() == raw
    assert review_v1.artifact_bytes() == raw


def test_packet_custody_semantics_and_field_foundation_pass_all_checks() -> None:
    accepted = _review()["accepted_foundation"]
    assert accepted["status"] == "ACCEPTED_WITHIN_PACKET_REVIEW"
    assert accepted["passed_check_count"] == accepted["check_count"] == 14
    assert all(accepted["checks"].values())
    assert accepted["source_output_file_count"] == 14
    assert accepted["historical_semantics_count"] == 2
    assert accepted["ordered_vector_count"] == 224
    assert accepted["field_count"] == 1792
    assert accepted["block_count"] == 8


def test_both_historical_reductions_reconstruct_independently() -> None:
    audit = _review()["independent_semantics_audit"]
    assert audit["fixture_count"] == 3
    assert audit["producer_formula_exact_for_all_fixtures"] is True
    assert audit["verifier_formula_exact_for_all_fixtures"] is True
    assert audit["at_least_one_fixture_diverges"] is True


def test_candidate_aggregate_contract_is_exactly_reconstructed() -> None:
    audit = _review()["aggregate_contract_audit"]
    assert audit["multiple_hypotheses_may_be_supported"] is True
    assert audit["multiple_support_aggregate"] == "MULTIPLE_SUPPORTED_MECHANISMS"
    assert audit["H_E_not_supported_when_A_through_D_nonempty"] is True
    assert audit["empty_support_aggregate"] == (
        "MECHANISM_UNRESOLVED_COMPLETE_EVIDENCE"
    )
    assert audit["H_E_supported_only_after_empty_A_through_D"] is True
    assert audit["incomplete_evidence_is_not_false_predicates"] is True
    assert audit["same_aggregate_function_called_by_both_semantics"] is True


def test_role_level_dominant_block_mutation_is_undetected() -> None:
    probe = _review()["decision_contract_audit"][
        "dominant_block_mutation_probe"
    ]
    assert probe["control_id"] == "ROLE_LEVEL_DOMINANT_BLOCK_IDENTITY_MUTATION"
    assert probe["changed_premise"] == (
        "block_dominance_metrics.R13_LOOSE.dominant_block_id"
    )
    assert probe["producer_value"] == "THETA_KINEMATIC"
    assert probe["verifier_value"] == "P_LONGITUDINAL_MAXWELL"
    assert probe["observed_threshold_decision_change_count"] == 0
    assert probe["observed_hypothesis_predicate_change_count"] == 0
    assert probe["observed_final_candidate_classification_changed"] is False
    assert probe["mutation_undetected"] is True
    assert probe["first_diagnostic"] == (
        "ROLE_LEVEL_DOMINANT_BLOCK_CHANGE_NOT_GATED"
    )


def test_all_four_required_decision_contract_checks_fail() -> None:
    audit = _review()["decision_contract_audit"]
    assert audit["passed_check_count"] == 0
    assert audit["check_count"] == 4
    assert set(audit["failed_check_ids"]) == {
        "role_level_dominant_block_identity_is_gated",
        "decision_relevant_ordering_has_independent_gate",
        "terminal_classification_is_materialized",
        "one_two_and_larger_ulp_counts_are_materialized",
    }
    assert not any(audit["checks"].values())


def test_review_blocks_v1_with_exact_first_diagnostic() -> None:
    review = _review()
    assert review["verdict"] == "BLOCKED_DECISION_INVARIANCE_GATE_INCOMPLETE"
    assert review["first_diagnostic"] == (
        "ROLE_LEVEL_DOMINANT_BLOCK_CHANGE_NOT_GATED"
    )
    findings = review["blocking_findings"]
    assert len(findings) == 4
    assert findings[0]["severity"] == "DECISIVE"
    assert findings[0]["diagnostic"] == review["first_diagnostic"]


def test_blocked_review_anchor_cannot_authorize_calculation() -> None:
    source_root = ROOT / review_v1.SOURCE_OUTPUT_ROOT_RELATIVE_PATH
    before = implementation_v0.directory_tree_sha256(source_root)
    with pytest.raises(
        reconciliation_v1.ReconciliationError,
        match="RECONCILIATION_REVIEW_NOT_ACCEPTED",
    ) as captured:
        reconciliation_v1.preflight_authorized_calculation(ROOT)
    assert captured.value.diagnostic == "RECONCILIATION_REVIEW_NOT_ACCEPTED"
    assert implementation_v0.directory_tree_sha256(source_root) == before
    assert not (ROOT / reconciliation_v1.RESULT_OUTPUT_ROOT_RELATIVE_PATH).exists()


def test_v2_authority_is_narrow_and_adds_no_arithmetic_route() -> None:
    correction = _review()["required_v2_correction"]
    assert correction["scope"] == "DECISION_GATE_AND_RESULT_SCHEMA_ONLY"
    assert correction["must_compare_role_level_dominant_block_ids"] is True
    assert correction["must_define_and_compare_decision_relevant_ordering_and_ties"] is True
    assert correction["must_emit_exactly_one_of"] == [
        "PREDICATE_INVARIANT",
        "BLOCKED_OBSERVABLE_DECISION_INSTABILITY",
    ]
    assert correction["must_fail_if_field_count_is_not_1792"] is True
    assert correction["must_add_atomic_mutation_for_role_dominant_block"] is True
    assert correction["must_not_add_reduction_semantics"] is True
    assert correction["must_not_run_simulation"] is True


def test_scientific_and_execution_boundaries_remain_closed() -> None:
    review = _review()
    boundary = review["authority_boundary"]
    assert boundary["packet_v1_accepted"] is False
    assert boundary["calculation_authorized"] is False
    assert boundary["derived_output_authorized"] is False
    assert boundary["simulation_authorized"] is False
    assert boundary["historical_output_modification_authorized"] is False
    assert boundary["H_A_through_H_E_evaluation_authorized"] is False
    assert boundary["canonical_semantics_selection_authorized"] is False
    assert boundary["packet_v2_narrow_preparation_authorized"] is True
    preserved = review["preserved_scientific_core"]
    assert preserved["fourteen_row_robustness"] == "NUMERICALLY_BLOCKED"
    assert preserved["R13_root_mechanism"] == (
        "UNRESOLVED_EVIDENCE_SEMANTICS_BLOCK"
    )
    assert preserved["new_E_REPRO"] == "NONE"


def test_authority_rotates_only_to_narrow_v2_preparation() -> None:
    review = _review()
    assert review["selected_next_target"] == review_v1.SELECTED_NEXT_TARGET
    assert review["selected_next_target"].endswith(
        "observable_semantics_reconciliation_packet_v2"
    )

