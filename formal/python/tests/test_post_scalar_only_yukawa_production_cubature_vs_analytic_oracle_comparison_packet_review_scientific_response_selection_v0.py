from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import (
    post_scalar_only_yukawa_production_cubature_vs_analytic_oracle_comparison_packet_review_scientific_response_selection_v0
    as selection,
)


ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = ROOT / selection.REPORT_RELATIVE_PATH


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_selector_regenerates_and_freezes_blocked_review_authority() -> None:
    assert selection.artifact_bytes() == REPORT_PATH.read_bytes()
    report = _report()
    assert report["target"] == selection.TARGET
    assert report["verdict"] == selection.VERDICT
    assert report["selected_route"] == selection.SELECTED_ROUTE
    assert report["selected_next_target"] == selection.SELECTED_NEXT_TARGET
    assert {
        row["relative_path"]: row["sha256"]
        for row in report["authority"]["frozen_review_artifacts"]
    } == selection.AUTHORITY_HASHES


def test_selector_interprets_block_as_contractual_not_scientific() -> None:
    interpretation = _report()["review_interpretation"]
    assert interpretation["review_verdict"] == (
        "BLOCKED_PRODUCTION_COMPARISON_CONTRACT_INCOMPLETE"
    )
    assert interpretation["principal_block"] == "BLOCKED_PRODUCTION_PATH_IDENTITY"
    assert interpretation["production_cubature_adjudicated"] is False
    assert interpretation["comparison_execution"] == "NOT_AUTHORIZED_NOT_PERFORMED"
    assert interpretation["accepted_oracle"] == "QUALIFIED_AND_ACCEPTED"


def test_five_candidates_and_eleven_criteria_select_narrow_v1_repair() -> None:
    report = _report()
    policy = report["selection_policy"]
    ranking = report["ranking"]
    assert policy["candidate_count"] == 5
    assert policy["criterion_count"] == 11
    assert ranking["selected_candidate_id"] == selection.SELECTED_CANDIDATE_ID
    assert ranking["selected_score"] == 220
    assert ranking["runner_up_candidate_id"] == "HISTORICAL_PATH_IDENTITY_ISOLATION_ONLY"
    assert ranking["runner_up_score"] == 168
    assert ranking["winning_margin"] == 52


def test_selection_is_stable_in_all_thirty_three_variants() -> None:
    sensitivity = _report()["sensitivity_analysis"]
    assert sensitivity["variant_count"] == 33
    assert sensitivity["selected_candidate_stable_in_all_variants"] is True
    assert sensitivity["minimum_winning_margin"] > 0


def test_thirty_three_gates_frozen_and_only_seven_repairable() -> None:
    freeze = _report()["review_gate_freeze"]
    assert freeze["accepted_gate_count"] == 33
    assert freeze["repairable_gate_count"] == 7
    assert freeze["accepted_gates"] == list(selection.ACCEPTED_REVIEW_GATES)
    assert freeze["repairable_gates"] == list(selection.REPAIRABLE_REVIEW_GATES)
    assert set(freeze["accepted_gates"]).isdisjoint(freeze["repairable_gates"])


def test_v1_scope_addresses_each_failed_interface_without_preparing_packet() -> None:
    contract = _report()["v1_preparation_contract"]
    assert contract["status"] == "PACKET_PREPARATION_AUTHORIZED_NOT_PREPARED"
    assert len(contract["editable_interfaces_only"]) == 5
    assert len(contract["historical_path_obligations"]) == 4
    assert len(contract["classification_obligations"]) == 4
    assert len(contract["control_obligations"]) == 3
    assert contract["incomplete_record_rule"].startswith("ALL_96_SCIENTIFIC_CELLS")
    assert len(contract["frozen_surfaces"]) == 7
    assert contract["review_outcomes"] == list(selection.V1_REVIEW_OUTCOMES)
    assert contract["comparison_execution_reserved_for_post_review_authority"] is True


def test_v1_is_last_automatic_comparison_contract_repair() -> None:
    boundary = _report()["anti_rabbit_hole_boundary"]
    assert boundary["v1_is_last_automatic_comparison_contract_repair"] is True
    assert boundary["automatic_v2_authorized"] is False
    assert boundary["new_foundational_v1_block_requires_fresh_selector"] is True
    assert len(boundary["future_choices_after_block"]) == 4


def test_all_twenty_selection_gates_pass() -> None:
    gates = _report()["selection_gates"]
    assert gates["gate_count"] == gates["pass_count"] == 20
    assert gates["failure_count"] == 0
    assert all(row["status"] == "PASS" for row in gates["rows"])


def test_scope_authorizes_packet_preparation_only() -> None:
    scope = _report()["scope"]
    true_keys = {key for key, value in scope.items() if value is True}
    assert true_keys == {
        "scientific_response_selection_executed",
        "accepted_review_gates_frozen",
        "v1_comparison_contract_packet_preparation_authorized",
        "final_automatic_comparison_contract_repair_boundary_frozen",
    }
    assert scope["comparison_execution_authorized"] is False
    assert scope["production_kernel_replacement_authorized"] is False
    assert scope["stage_b_authorized"] is False


def test_human_selection_records_route_boundary_and_next_authority() -> None:
    text = (ROOT / selection.HUMAN_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        selection.VERDICT,
        selection.SELECTED_ROUTE,
        "33 / 40 FROZEN",
        "7 / 40 ONLY",
        "all 96 scientific cells",
        "last automatic comparison-contract repair",
        selection.SELECTED_NEXT_TARGET,
    ):
        assert token in text
