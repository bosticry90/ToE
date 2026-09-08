from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any

from formal.python.tools import (
    scalar_only_yukawa_production_cubature_vs_analytic_oracle_comparison_packet_review_v0
    as review,
)


ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = ROOT / review.REPORT_RELATIVE_PATH


def _report() -> dict[str, Any]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_review_regenerates_and_freezes_packet_custody() -> None:
    assert review.artifact_bytes() == REPORT_PATH.read_bytes()
    report = _report()
    assert report["target"] == review.TARGET
    assert report["verdict"] == review.VERDICT
    assert report["principal_review_outcome"] == review.PRINCIPAL_OUTCOME
    assert {
        row["relative_path"]: row["sha256"]
        for row in report["authority"]["frozen_packet_artifacts"]
    } == review.PACKET_HASHES
    for relative_path, expected in review.PACKET_HASHES.items():
        assert _sha256(ROOT / relative_path) == expected


def test_case_order_component_and_atomic_accounting_remain_accepted() -> None:
    audit = _report()["independent_case_and_accounting_audit"]
    assert audit["case_count"] == 8
    assert audit["case_ids_exact"] is True
    assert audit["legacy_case_count"] == 3
    assert audit["strict_nonoverlap"] is True
    assert audit["gap_reconstruction_max_error_m"] <= 2e-17
    assert audit["orders_exact"] is True
    assert audit["components_exact"] is True
    assert audit["atomic_cell_count_reproduced"] == 96


def test_historical_and_mirror_algorithms_are_not_identical_as_frozen() -> None:
    audit = _report()["independent_production_path_identity_audit"]
    assert audit["historical"]["uses_sequential_outer_accumulation"] is True
    assert audit["historical"]["uses_fixed_equal_radius_constants"] is True
    assert audit["mirror"]["uses_block_list_accumulation"] is True
    assert audit["mirror"]["pairwise_is_default"] is True
    assert audit["mirror"]["ordinary_mode_exists"] is True
    assert audit["mirror"]["parameterizes_unequal_radii"] is True
    assert audit["accumulation_algorithm_identical_as_frozen"] is False
    assert audit["physical_input_domain_identical_as_frozen"] is False


def test_legacy_equivalence_control_is_not_executable() -> None:
    audit = _report()["independent_production_path_identity_audit"]
    assert audit["packet_declares_legacy_equivalence_control"] is True
    assert audit["legacy_equivalence_tolerance_present"] is False
    assert audit["legacy_equivalence_failure_behavior_present"] is False
    assert audit["historical_decision_bearing_cases_separated_from_mirror_only_cases"] is False


def test_classification_contract_has_three_reproduced_defects() -> None:
    audit = _report()["independent_classification_audit"]
    assert audit["predicate_count"] == 9
    assert audit["accuracy_rule_complete"] is True
    assert audit["order48_not_reference"] is True
    assert audit["validated_predicate_multi_order"] is True
    assert audit["fixed_order_predicate_multi_order"] is True
    assert audit["slow_fit_method_frozen"] is False
    assert audit["economic_projection_rule_frozen"] is False
    assert audit["mutation_fingerprint_distance_and_tolerance_frozen"] is False
    assert audit["systematic_bias_component_grouping_frozen"] is False
    assert audit["timeout_suppresses_partial_scientific_labels"] is False


def test_control_routing_is_descriptive_not_executable() -> None:
    audit = _report()["independent_control_routing_audit"]
    assert audit["control_count"] == 10
    assert audit["ids_unique"] is True
    assert audit["live_pipeline_asserted"] is True
    assert audit["case_ids_frozen_per_control"] is False
    assert audit["orders_frozen_per_control"] is False
    assert audit["acceptance_tolerances_frozen_per_control"] is False
    assert audit["legacy_equivalence_control_is_one_of_ten"] is False
    assert audit["metadata_and_oracle_firewalls_present"] is True


def test_resource_envelope_passes_but_incomplete_precedence_does_not() -> None:
    audit = _report()["independent_resource_and_custody_audit"]
    assert audit["total_seconds"] == 1200
    assert audit["memory_mib"] == 4096
    assert audit["stage_count"] == 6
    assert audit["stage_cap_sum_seconds"] == 1120
    assert audit["per_order_cap_keys"] == [8, 16, 24, 32, 40, 48]
    assert audit["process_group_required"] is True
    assert audit["atomic_records_required"] is True
    assert audit["zero_survivors_required"] is True
    assert audit["fails_closed"] is True
    assert audit["full_record_set_required_for_scientific_classification"] is False


def test_exact_seven_review_gates_fail() -> None:
    gates = _report()["review_gates"]
    assert gates["gate_count"] == 40
    assert gates["pass_count"] == 33
    assert gates["failure_count"] == 7
    assert gates["failed_gate_ids"] == [
        "R12_HISTORICAL_AND_MIRROR_ACCUMULATION_IDENTICAL",
        "R13_HISTORICAL_AND_MIRROR_DECISION_SCOPE_SEPARATED",
        "R14_LEGACY_EQUIVALENCE_RULE_EXECUTABLE",
        "R24_SLOW_CONVERGENCE_FIT_AND_COST_RULE_EXECUTABLE",
        "R25_SYSTEMATIC_BIAS_AND_FINGERPRINT_RULES_EXECUTABLE",
        "R31_CONTROL_CASE_ORDER_AND_TOLERANCE_ROUTING",
        "R36_INCOMPLETE_RECORDS_SUPPRESS_SCIENTIFIC_CLASSIFICATION",
    ]


def test_diagnostics_and_bounded_repair_burden_are_exact() -> None:
    report = _report()
    assert tuple(report["diagnostics"]) == review.DIAGNOSTICS
    burden = report["bounded_repair_burden_for_fresh_selector"]
    assert "ORDINARY sequential accumulation" in burden["historical_path"]
    assert "mutation-fingerprint" in burden["classification"]
    assert "exact cases, orders" in burden["controls"]
    assert "all 96 required cells" in burden["incomplete_records"]
    assert burden["automatic_repair"] == "NOT_AUTHORIZED"


def test_blocked_review_authorizes_only_fresh_selector() -> None:
    report = _report()
    assert report["selected_next_target"] == review.SELECTED_NEXT_TARGET
    assert report["authority"]["authorized_comparison_execution_count"] == 0
    assert report["authority"]["performed_comparison_execution_count"] == 0
    scope = report["scope"]
    true_keys = {key for key, value in scope.items() if value is True}
    assert true_keys == {
        "independent_packet_review_performed",
        "packet_custody_verified",
        "blocked_contract_result_issued",
        "fresh_scientific_response_selector_authorized",
    }
    assert scope["comparison_contract_ready"] is False
    assert scope["comparison_execution_authorized"] is False
    assert scope["packet_repair_authorized"] is False
    assert scope["stage_b_authorized"] is False


def test_human_review_records_block_and_nonclaims() -> None:
    text = (ROOT / review.HUMAN_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        review.VERDICT,
        review.PRINCIPAL_OUTCOME,
        "33 PASS",
        "7 FAIL",
        "sequential outer accumulation",
        "NumPy pairwise accumulation",
        "all 96 scientific cells complete",
        "comparison executions authorized:\n0",
        review.SELECTED_NEXT_TARGET,
    ):
        assert token in text
