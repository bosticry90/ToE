from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import (
    post_scalar_only_yukawa_production_cubature_vs_analytic_oracle_comparison_packet_v1_review_scientific_response_selection_v0
    as selection,
)


ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = ROOT / selection.REPORT_RELATIVE_PATH


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_selector_regenerates_and_freezes_final_review() -> None:
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


def test_final_block_is_not_interpreted_as_physical_failure() -> None:
    interpretation = _report()["review_interpretation"]
    assert interpretation["review_verdict"] == (
        "BLOCKED_PRODUCTION_COMPARISON_CONTRACT_INCOMPLETE"
    )
    assert interpretation["principal_block"] == "BLOCKED_MUTATION_ROUTING"
    assert interpretation["frozen_review_gates_preserved"] == 33
    assert interpretation["comparison_contract_ready"] is False
    assert interpretation["production_cubature_adjudicated"] is False
    assert interpretation["physical_model_refuted"] is False


def test_four_candidates_select_direct_analytic_replacement() -> None:
    report = _report()
    policy = report["selection_policy"]
    ranking = report["ranking"]
    assert policy["candidate_count"] == 4
    assert policy["criterion_count"] == 10
    assert ranking["selected_candidate_id"] == "DIRECT_ANALYTIC_KERNEL_REPLACEMENT"
    assert ranking["selected_score"] == 211
    assert ranking["runner_up_candidate_id"] == "CLOSE_SYNTHETIC_TORSION_BALANCE_LANE"
    assert ranking["runner_up_score"] == 154
    assert ranking["winning_margin"] == 57


def test_selection_is_stable_in_all_thirty_variants() -> None:
    sensitivity = _report()["sensitivity_analysis"]
    assert sensitivity["variant_count"] == 30
    assert sensitivity["selected_candidate_stable_in_all_variants"] is True
    assert sensitivity["minimum_winning_margin"] > 0


def test_replacement_packet_scope_is_energy_only_and_oracle_backed() -> None:
    contract = _report()["analytic_replacement_packet_preparation_contract"]
    assert contract["status"] == "PACKET_PREPARATION_AUTHORIZED_NOT_PREPARED"
    assert contract["replacement_scope"] == (
        "NONOVERLAPPING_HOMOGENEOUS_SPHERE_ENERGY_KERNEL_ONLY"
    )
    assert contract["accepted_oracle_source"] == (
        "ANALYTIC_SPHERE_ORACLE_QUALIFIED_AND_ACCEPTED"
    )
    assert len(contract["required_frozen_interfaces"]) == 9
    assert len(contract["required_validation_surfaces"]) == 8
    assert contract["torque_and_dft"].startswith("FROZEN_OUT_OF_SCOPE")
    assert contract["stage_a_rerun"] == "NOT_AUTHORIZED"
    assert contract["review_outcomes"] == list(selection.REPLACEMENT_REVIEW_OUTCOMES)
    assert contract["replacement_execution_reserved_for_post_review_authority"] is True


def test_old_comparison_path_is_retired_without_adjudication() -> None:
    contract = _report()["analytic_replacement_packet_preparation_contract"]
    assert contract["old_cubature_status"].startswith("RETAINED_READ_ONLY")
    assert contract["old_comparison_contract_status"].startswith("RETIRED")
    posture = _report()["current_posture"]
    assert posture["production_cubature"] == "UNADJUDICATED"
    assert posture["old_cubature_comparison_contract"].endswith("RETIRED")


def test_anti_rabbit_hole_boundary_preserves_no_v2() -> None:
    boundary = _report()["anti_rabbit_hole_boundary"]
    assert boundary["automatic_comparison_v2_authorized"] is False
    assert boundary["old_cubature_comparison_repair_closed"] is True
    assert boundary["replacement_packet_failure_requires_fresh_selector"] is True
    assert boundary["immediate_lane_closure_remains_available"] is True


def test_all_twenty_selection_gates_pass() -> None:
    gates = _report()["selection_gates"]
    assert gates["gate_count"] == gates["pass_count"] == 20
    assert gates["failure_count"] == 0
    assert all(row["status"] == "PASS" for row in gates["rows"])


def test_scope_authorizes_preparation_only() -> None:
    scope = _report()["scope"]
    true_keys = {key for key, value in scope.items() if value is True}
    assert true_keys == {
        "scientific_response_selection_executed",
        "final_v1_review_frozen",
        "analytic_replacement_packet_preparation_authorized",
        "old_cubature_automatic_comparison_path_retired",
    }
    assert scope["analytic_kernel_implemented_now"] is False
    assert scope["production_kernel_replacement_authorized"] is False
    assert scope["old_cubature_comparison_authorized"] is False
    assert scope["stage_b_authorized"] is False


def test_human_selection_records_route_and_current_authority() -> None:
    text = (ROOT / selection.HUMAN_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        selection.VERDICT,
        selection.SELECTED_ROUTE,
        "211",
        "154",
        "30 / 30",
        "old-cubature comparison path is retired",
        "energy kernel only",
        selection.SELECTED_NEXT_TARGET,
    ):
        assert token in text
