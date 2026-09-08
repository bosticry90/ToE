from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import post_scalar_only_yukawa_analytic_sphere_kernel_replacement_packet_v0_review_scientific_response_selection_v0 as selector


ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = ROOT / selector.REPORT_RELATIVE_PATH


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_selector_regenerates_and_freezes_exact_review() -> None:
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


def test_exact_review_interpretation_is_preserved() -> None:
    interpretation = _report()["review_interpretation"]
    assert interpretation["principal_block"] == "BLOCKED_REPLACEMENT_VALIDATION_INDEPENDENCE"
    assert interpretation["secondary_blocks"] == [
        "BLOCKED_REPLACEMENT_INTERFACE_IDENTITY",
        "BLOCKED_REPLACEMENT_DOMAIN_COVERAGE",
    ]
    assert interpretation["accepted_review_gates_frozen"] == 51
    assert interpretation["failed_review_gates"] == list(selector.FAILED_REVIEW_GATES)
    assert interpretation["analytic_formula_refuted"] is False


def test_four_candidates_and_ten_criteria_are_exact() -> None:
    policy = _report()["selection_policy"]
    assert policy["candidate_count"] == 4
    assert policy["criterion_count"] == 10
    assert policy["criteria_weights"] == selector.CRITERIA
    assert len(_report()["ranking"]["rows"]) == 4


def test_final_v1_repair_wins_by_frozen_score() -> None:
    ranking = _report()["ranking"]
    assert ranking["selected_candidate_id"] == "ELEVEN_GATE_REPLACEMENT_CONTRACT_REPAIR_V1"
    assert ranking["selected_score"] == 226
    assert ranking["runner_up_candidate_id"] == (
        "RETIRE_ANALYTIC_REPLACEMENT_AND_DEFER_TORSION_BALANCE_LANE"
    )
    assert ranking["runner_up_score"] == 185
    assert ranking["winning_margin"] == 41


def test_selection_is_stable_in_all_thirty_variants() -> None:
    sensitivity = _report()["sensitivity_analysis"]
    assert sensitivity["variant_count"] == 30
    assert sensitivity["selected_candidate_stable_in_all_variants"] is True
    assert sensitivity["minimum_winning_margin"] > 0
    assert all(
        row["selected_candidate_id"] == selector.SELECTED_CANDIDATE_ID
        for row in sensitivity["rows"]
    )


def test_v1_repair_scope_is_exactly_eleven_failed_gates() -> None:
    repair = _report()["v1_repair_contract"]
    assert repair["accepted_review_gate_count_frozen"] == 51
    assert repair["repair_gate_count"] == 11
    assert repair["repair_gate_ids"] == list(selector.FAILED_REVIEW_GATES)
    assert len(repair["required_repairs"]) == 11
    assert repair["all_other_surfaces"] == "FROZEN_NO_REDESIGN"
    assert repair["candidate_kernel_creation"].startswith("FORBIDDEN")


def test_derivative_reference_must_be_independent() -> None:
    rule = _report()["v1_repair_contract"]["derivative_reference_independence_rule"]
    assert "HIGH_PRECISION" in rule
    assert "MAY_NOT_CALL_THE_CANDIDATE_DERIVATIVE" in rule


def test_final_attempt_boundary_prohibits_automatic_v2() -> None:
    boundary = _report()["anti_rabbit_hole_boundary"]
    assert boundary["v1_is_final_automatic_replacement_contract_repair"] is True
    assert boundary["automatic_v2_authorized"] is False
    assert boundary["v1_review_block_requires_fresh_selector"] is True


def test_scope_authorizes_packet_preparation_only() -> None:
    scope = _report()["scope"]
    true_keys = {key for key, value in scope.items() if value is True}
    assert true_keys == {
        "scientific_response_selection_executed",
        "blocked_v0_review_frozen",
        "fifty_one_accepted_review_gates_frozen",
        "eleven_failed_gates_selected_for_contract_repair",
        "v1_packet_preparation_authorized",
    }
    assert scope["v1_packet_prepared_now"] is False
    assert scope["shadow_kernel_implementation_authorized"] is False
    assert scope["production_kernel_replacement_authorized"] is False
    assert scope["old_cubature_adjudicated"] is False
    assert scope["automatic_v2_authorized"] is False


def test_human_selector_records_exact_boundary_and_authority() -> None:
    text = (ROOT / selector.HUMAN_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        selector.VERDICT,
        selector.SELECTED_ROUTE,
        "226",
        "185",
        "30 / 30",
        "51 accepted review gates remain frozen",
        "eleven failed gates",
        "final automatic replacement-contract repair",
        "No candidate kernel is created",
        selector.SELECTED_NEXT_TARGET,
    ):
        assert token in text
