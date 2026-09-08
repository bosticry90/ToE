from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import post_scalar_only_yukawa_analytic_sphere_kernel_replacement_packet_v1_review_scientific_response_selection_v0 as selector


ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = ROOT / selector.REPORT_RELATIVE_PATH


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_selector_regenerates_and_freezes_exact_final_review() -> None:
    assert selector.artifact_bytes() == REPORT_PATH.read_bytes()
    report = _report()
    assert report["target"] == selector.TARGET
    assert report["verdict"] == selector.VERDICT
    assert report["selected_route"] == selector.SELECTED_ROUTE
    assert report["selected_next_target"] == selector.SELECTED_NEXT_TARGET
    assert {
        row["relative_path"]: row["sha256"]
        for row in report["authority"]["frozen_review_artifacts"]
    } == selector.REVIEW_HASHES


def test_review_interpretation_preserves_exact_partition() -> None:
    interpretation = _report()["review_interpretation"]
    assert interpretation["frozen_gate_count"] == 51
    assert interpretation["accepted_v1_repair_count"] == 6
    assert interpretation["failed_review_gate_ids"] == list(selector.FAILED_REVIEW_GATES)
    assert interpretation["analytic_formula_refuted"] is False
    assert interpretation["accepted_regression_or_derivative_data_reopened"] is False


def test_four_candidates_and_ten_criteria_are_exact() -> None:
    policy = _report()["selection_policy"]
    assert policy["candidate_count"] == 4
    assert policy["criterion_count"] == 10
    assert policy["criteria_weights"] == selector.CRITERIA
    assert len(_report()["ranking"]["rows"]) == 4


def test_kernel_agnostic_prerequisite_wins_frozen_ranking() -> None:
    ranking = _report()["ranking"]
    assert ranking["selected_candidate_id"] == selector.SELECTED_CANDIDATE_ID
    assert ranking["selected_score"] == 240
    assert ranking["runner_up_candidate_id"] == (
        "RETIRE_REPLACEMENT_IMPLEMENTATION_AND_PRESERVE_ANALYTIC_ORACLE_ONLY"
    )
    assert ranking["runner_up_score"] == 185
    assert ranking["winning_margin"] == 55


def test_selection_is_stable_in_all_thirty_variants() -> None:
    sensitivity = _report()["sensitivity_analysis"]
    assert sensitivity["variant_count"] == 30
    assert sensitivity["selected_candidate_stable_in_all_variants"] is True
    assert sensitivity["minimum_winning_margin"] > 0


def test_prerequisite_is_not_v2_and_is_kernel_agnostic() -> None:
    contract = _report()["validation_infrastructure_prerequisite_contract"]
    assert contract["status"] == "PACKET_PREPARATION_AUTHORIZED_NOT_PREPARED"
    assert contract["is_replacement_packet_v2"] is False
    assert contract["kernel_agnostic"] is True
    assert len(contract["allowed_contract_surfaces"]) == 6
    assert len(contract["forbidden_contract_surfaces"]) == 4
    assert contract["completion_consequence"].startswith("FRESH_SELECTOR_REQUIRED")


def test_allowed_surfaces_cover_the_five_infrastructure_blocks() -> None:
    allowed = _report()["validation_infrastructure_prerequisite_contract"]["allowed_contract_surfaces"]
    joined = " ".join(allowed)
    for token in ("CAPABILITY", "PREDICATE", "MUTATION", "DEPENDENCY_SCANNER", "CANONICAL"):
        assert token in joined


def test_anti_rabbit_hole_boundary_is_explicit() -> None:
    boundary = _report()["anti_rabbit_hole_boundary"]
    assert boundary["v1_remains_final_automatic_replacement_contract_repair"] is True
    assert boundary["automatic_v2_authorized"] is False
    assert boundary["prerequisite_is_separate_and_kernel_agnostic"] is True
    assert boundary["prerequisite_result_cannot_automatically_reopen_replacement_lane"] is True


def test_scope_authorizes_preparation_only() -> None:
    scope = _report()["scope"]
    true_keys = {key for key, value in scope.items() if value is True}
    assert true_keys == {
        "scientific_response_selection_executed", "final_v1_review_frozen",
        "fifty_one_accepted_gates_preserved", "six_completed_repairs_preserved",
        "five_failed_gates_interpreted_as_infrastructure_prerequisites",
        "validation_infrastructure_prerequisite_packet_preparation_authorized",
    }
    assert scope["prerequisite_packet_prepared_now"] is False
    assert scope["replacement_packet_v2_authorized"] is False
    assert scope["candidate_kernel_creation_authorized"] is False
    assert scope["candidate_kernel_execution_authorized"] is False
    assert scope["automatic_return_to_replacement_lane_authorized"] is False


def test_human_selector_records_outcome_boundary_and_authority() -> None:
    text = (ROOT / selector.HUMAN_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        selector.VERDICT, selector.SELECTED_ROUTE, "240", "185", "30 / 30",
        "not replacement packet V2", "No candidate kernel is created or executed",
        selector.SELECTED_NEXT_TARGET,
    ):
        assert token in text
