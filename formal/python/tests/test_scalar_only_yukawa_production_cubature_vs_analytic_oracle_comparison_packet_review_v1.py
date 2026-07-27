from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import (
    scalar_only_yukawa_production_cubature_vs_analytic_oracle_comparison_packet_review_v1
    as review,
)


ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = ROOT / review.REPORT_RELATIVE_PATH


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_review_regenerates_and_freezes_v1_packet() -> None:
    assert review.artifact_bytes() == REPORT_PATH.read_bytes()
    report = _report()
    assert report["target"] == review.TARGET
    assert report["verdict"] == review.VERDICT
    assert report["principal_review_outcome"] == review.PRINCIPAL_OUTCOME
    assert {
        row["relative_path"]: row["sha256"]
        for row in report["authority"]["frozen_packet_artifacts"]
    } == review.PACKET_HASHES


def test_accepted_surfaces_remain_preserved() -> None:
    accepted = _report()["accepted_surfaces"]
    assert accepted["frozen_review_gates"] == "33_PRESERVED"
    assert accepted["analytic_oracle"] == "QUALIFIED_AND_ACCEPTED"
    assert accepted["case_order_component_and_96_cell_accounting"] == "ACCEPTED"
    assert accepted["historical_mirror_source_partition"] == "ACCEPTED"
    assert accepted["historical_identity_preflight"] == "ACCEPTED_AS_EXECUTABLE"
    assert accepted["slow_fit_and_economic_rules"] == "ACCEPTED_AS_EXECUTABLE"
    assert accepted["overall_comparison_contract"] == "NOT_READY"


def test_c03_and_c04_required_labels_are_unreachable() -> None:
    audit = _report()["independent_control_reachability_audit"]
    rows = audit["unreachable_general_defect_controls"]
    assert [row["control_id"] for row in rows] == [
        "C03_GAP_FOR_CENTER_DISTANCE",
        "C04_RADIUS_AS_DIAMETER",
    ]
    assert audit["systematic_classifier_minimum_case_count"] == 4
    assert audit["systematic_classifier_required_orders"] == [32, 40, 48]
    assert all(row["case_count"] == 2 for row in rows)
    assert all(row["reachable"] is False for row in rows)


def test_c02_lacks_its_newtonian_classifier_prerequisite() -> None:
    audit = _report()["independent_control_reachability_audit"]
    assert audit["c02_routes_newtonian_prerequisite"] is False
    assert audit["c02_routes_all_fingerprint_cases"] is True
    assert audit["c02_routes_all_fingerprint_orders"] is True


def test_c06_and_c10_detection_depends_on_unknown_baseline() -> None:
    rows = _report()["independent_control_reachability_audit"][
        "baseline_dependent_systematic_controls"
    ]
    assert [row["control_id"] for row in rows] == [
        "C06_WEIGHT_NORMALIZATION_BIAS",
        "C10_CONSTANT_MULTIPLICATIVE_BIAS",
    ]
    assert [row["multiplier"] for row in rows] == [1.01, 1.02]
    assert all(row["unknown_baseline_spread_can_prevent_required_label"] for row in rows)
    assert not any(row["detection_independent_of_scientific_baseline"] for row in rows)


def test_duplicate_record_has_two_conflicting_outcomes() -> None:
    audit = _report()["independent_completion_precedence_audit"]
    assert audit["duplicate_declared_behavior"] == "BLOCKED_INCOMPLETE_RECORD_PRECEDENCE"
    assert audit["duplicate_priority2_behavior"] == "PRODUCTION_COMPARISON_TIMEOUT"
    assert audit["duplicate_outcome_unique"] is False


def test_timeout_namespace_is_contradictory() -> None:
    audit = _report()["independent_completion_precedence_audit"]
    assert audit["timeout_token"] == "PRODUCTION_COMPARISON_TIMEOUT"
    assert audit["timeout_in_scientific_label_set"] is True
    assert audit["priority2_requires_empty_scientific_label_list"] is True
    assert audit["timeout_namespace_unambiguous"] is False
    assert audit["partial_subset_classification_forbidden"] is True


def test_exact_five_review_gates_fail() -> None:
    gates = _report()["review_gates"]
    assert gates["gate_count"] == 48
    assert gates["pass_count"] == 43
    assert gates["failure_count"] == 5
    assert gates["failed_gate_ids"] == list(review.FAILED_GATE_IDS)


def test_final_attempt_rotates_only_to_fresh_selector() -> None:
    report = _report()
    disposition = report["final_attempt_disposition"]
    assert disposition["automatic_v2"] == "PROHIBITED"
    assert disposition["silent_packet_repair"] == "PROHIBITED"
    assert disposition["comparison_execution"] == "NOT_AUTHORIZED"
    assert disposition["fresh_selector_required"] is True
    assert len(disposition["bounded_future_choices"]) == 4
    assert report["selected_next_target"] == review.SELECTED_NEXT_TARGET


def test_scope_has_no_execution_or_repair_authority() -> None:
    scope = _report()["scope"]
    true_keys = {key for key, value in scope.items() if value is True}
    assert true_keys == {
        "independent_v1_packet_review_performed",
        "v1_packet_custody_verified",
        "thirty_three_frozen_gates_preserved",
        "blocked_final_contract_result_issued",
        "fresh_scientific_response_selector_authorized",
    }
    assert scope["comparison_contract_ready"] is False
    assert scope["comparison_execution_authorized"] is False
    assert scope["automatic_v2_authorized"] is False
    assert scope["stage_b_authorized"] is False


def test_human_review_records_exact_failures_and_boundary() -> None:
    text = (ROOT / review.HUMAN_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        review.VERDICT,
        review.PRINCIPAL_OUTCOME,
        "43 PASS",
        "5 FAIL",
        "C03",
        "C04",
        "C02",
        "C06",
        "C10",
        "two incompatible outcomes",
        "No automatic V2",
        review.SELECTED_NEXT_TARGET,
    ):
        assert token in text
