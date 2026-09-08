from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.tools import (
    native_gravitational_principle_requirements_and_action_selection_packet_review_v0 as review,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = REPO_ROOT / review.REPORT_RELATIVE_PATH


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_review_regenerates_exactly_and_deterministically() -> None:
    assert review.artifact_bytes() == review.artifact_bytes() == REPORT_PATH.read_bytes()


def test_review_preserves_every_frozen_authority_and_packet_byte() -> None:
    before = {
        path: _sha256(REPO_ROOT / path)
        for path in review.AUTHORITY_AND_PACKET_HASHES
    }
    review.build_review()
    after = {
        path: _sha256(REPO_ROOT / path)
        for path in review.AUTHORITY_AND_PACKET_HASHES
    }
    assert before == after == review.AUTHORITY_AND_PACKET_HASHES


def test_review_consumes_packet_target_and_blocks_v0() -> None:
    report = _report()
    assert report["target"] == review.TARGET
    assert report["verdict"] == review.VERDICT
    assert report["primary_diagnostic"] == review.PRIMARY_DIAGNOSTIC
    assert report["selected_next_target"] == review.SELECTED_NEXT_TARGET
    assert report["authority"]["reviewed_packet_verdict"] == (
        "PREPARED_PENDING_INDEPENDENT_REVIEW"
    )


def test_all_ten_requirement_sources_pass_without_scope_promotion() -> None:
    audit = _report()["requirement_source_audit"]
    assert audit["requirement_count"] == audit["pass_count"] == 10
    assert [row["requirement_id"] for row in audit["rows"]] == (
        review.EXPECTED_REQUIREMENT_IDS
    )
    assert all(row["scope_boundary_present"] is True for row in audit["rows"])
    assert all(row["status"] == "PASS" for row in audit["rows"])


def test_per_row_statement_class_binding_is_missing_for_all_requirements() -> None:
    audit = _report()["statement_class_audit"]
    assert audit["requirement_count"] == 10
    assert audit["valid_bound_statement_class_count"] == 0
    assert audit["missing_statement_class_count"] == 10
    assert audit["authority_status_is_statement_class"] is False
    assert audit["status"] == "FAIL"
    assert audit["diagnostic"] == "REQUIREMENT_STATEMENT_CLASS_BINDING_MISSING"


def test_family_envelope_standard_oracle_and_equivalence_are_retained() -> None:
    report = _report()
    family = report["family_envelope_audit"]
    assert family["family_count"] == 7
    assert family["adequate_for_first_selection_power_test"] is True
    assert family["exhaustive_claimed"] is False
    assert family["family_adopted_count"] == 0
    assert family["status"] == "PASS"
    isolation = report["standard_GR_isolation_audit"]
    assert isolation["oracle_role"] == "COMPARISON_ORACLE_ONLY"
    assert isolation["Einstein_equation_used_as_selection_premise"] is False
    assert isolation["comparator_activated"] is False
    equivalence = report["equivalence_audit"]
    assert equivalence["local_bulk_scope_preserved"] is True
    assert equivalence["physically_distinct_dynamics_merged"] is False


def test_matrix_vocabulary_cannot_encode_completed_undecidability() -> None:
    audit = _report()["matrix_vocabulary_audit"]
    assert audit["required_completed_analysis_state"] == (
        "NOT_DECIDABLE_FROM_REQUIREMENT"
    )
    assert audit["required_state_present"] is False
    assert audit["not_evaluated_is_equivalent_to_undecidable"] is False
    assert audit["survives_is_equivalent_to_undecidable"] is False
    assert audit["status"] == "FAIL"
    assert audit["diagnostic"] == "MATRIX_UNDECIDABLE_STATE_MISSING"


def test_unique_nondistinctive_eh_witness_matches_two_outcomes() -> None:
    audit = _report()["outcome_overlap_audit"]
    assert audit["witness"] == {
        "consistent": True,
        "project_specific_distinctiveness_demonstrated": False,
        "supplied_uniqueness_assumption_used": False,
        "unique_survivor": "F_EH",
    }
    assert audit["matching_outcome_count"] == 2
    assert audit["matching_outcomes"] == [
        "NATIVE_PRINCIPLE_SET_SELECTS_ACTION_FAMILY",
        "CURRENT_REQUIREMENTS_COLLAPSE_TO_STANDARD_GR",
    ]
    assert audit["first_match_result_under_v0_order"] == (
        "NATIVE_PRINCIPLE_SET_SELECTS_ACTION_FAMILY"
    )
    assert audit["status"] == "FAIL"


def test_eight_declared_controls_have_no_shared_executable_path() -> None:
    audit = _report()["control_path_audit"]
    assert audit["declared_control_count"] == 8
    assert audit["recognized_analysis_entry_points"] == []
    assert audit["end_to_end_control_count"] == 0
    assert audit["status"] == "FAIL"
    assert audit["diagnostic"] == "CONTROL_ANALYSIS_PATH_NOT_EXECUTABLE"


def test_review_gate_counts_and_findings_are_exact() -> None:
    report = _report()
    gates = report["review_gates"]
    assert gates["gate_count"] == len(gates["rows"]) == 10
    assert gates["pass_count"] == 6
    assert gates["failure_count"] == 4
    findings = report["findings"]
    assert findings["finding_count"] == findings["blocking_count"] == 4
    assert [row["diagnostic"] for row in findings["rows"]] == [
        "REQUIREMENT_STATEMENT_CLASS_BINDING_MISSING",
        "MATRIX_UNDECIDABLE_STATE_MISSING",
        "OUTCOME_PREDICATE_OVERLAP",
        "CONTROL_ANALYSIS_PATH_NOT_EXECUTABLE",
    ]


def test_review_controls_are_atomic_and_reproduce_each_finding() -> None:
    controls = _report()["review_controls"]
    assert controls["control_count"] == len(controls["rows"]) == 4
    assert controls["all_single_mutation"] is True
    assert all(row["mutation_count"] == 1 for row in controls["rows"])
    assert [row["observed_diagnostic"] for row in controls["rows"]] == [
        row["diagnostic"] for row in _report()["findings"]["rows"]
    ]


def test_v1_repairs_are_narrow_and_do_not_execute_science() -> None:
    repairs = _report()["required_v1_repairs"]
    assert len(repairs) == 5
    joined = " ".join(repairs)
    for token in (
        "statement_class",
        "NOT_DECIDABLE_FROM_REQUIREMENT",
        "disjoint",
        "table-analysis entry point",
        "preserve all ten sources",
    ):
        assert token in joined


def test_retained_results_keep_upstream_scientific_blocks() -> None:
    retained = _report()["retained_results"]
    assert retained["requirement_source_bindings"] == "10_OF_10_RETAINED"
    assert retained["comparison_family_envelope"] == "7_OF_7_RETAINED"
    assert retained["standard_GR_isolation"] == "RETAINED"
    assert retained["local_bulk_equivalence_scope"] == "RETAINED"
    assert retained["native_candidate_readiness"] == (
        "BLOCKED_NO_NATIVE_GRAVITATIONAL_PRINCIPLE"
    )


def test_review_records_block_only_and_creates_no_scientific_result_or_tooling() -> None:
    scope = _report()["scope"]
    assert scope["independent_review_executed"] is True
    assert scope["packet_block_recorded"] is True
    for key, value in scope.items():
        if key not in {"independent_review_executed", "packet_block_recorded"}:
            assert value is False, key
    claim = _report()["claim_ceiling"]
    for token in (
        "No survivor analysis",
        "family judgment",
        "principle",
        "postulate",
        "action",
        "variation",
        "tooling lane",
        "automation",
    ):
        assert token in claim


def test_human_review_contains_verdict_findings_and_nonclaims() -> None:
    text = (REPO_ROOT / review.REVIEW_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        review.VERDICT,
        review.PRIMARY_DIAGNOSTIC,
        "MATRIX_UNDECIDABLE_STATE_MISSING",
        "OUTCOME_PREDICATE_OVERLAP",
        "CONTROL_ANALYSIS_PATH_NOT_EXECUTABLE",
        "No scientific family-survival",
        review.SELECTED_NEXT_TARGET,
    ):
        assert token in text
