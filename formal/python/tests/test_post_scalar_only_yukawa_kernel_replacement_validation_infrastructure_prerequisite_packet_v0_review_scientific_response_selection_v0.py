from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import post_scalar_only_yukawa_kernel_replacement_validation_infrastructure_prerequisite_packet_v0_review_scientific_response_selection_v0 as selector


ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = ROOT / selector.REPORT_RELATIVE_PATH


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_selector_regenerates_and_pins_terminal_ready_review() -> None:
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


def test_review_interpretation_preserves_ready_without_overclaim() -> None:
    interpretation = _report()["review_interpretation"]
    assert interpretation["review_verdict"] == "VALIDATION_INFRASTRUCTURE_PREREQUISITE_READY"
    assert interpretation["review_pass_count"] == 48
    assert interpretation["review_failure_count"] == 0
    assert interpretation["contract_ready_for_exploratory_sandbox"] is True
    assert interpretation["infrastructure_implemented_or_qualified"] is False
    assert interpretation["analytic_kernel_scientifically_validated"] is False


def test_terminal_selector_has_exactly_the_two_authorized_options() -> None:
    policy = _report()["selection_policy"]
    assert policy["candidate_count"] == 2
    assert policy["options_exact"] == list(selector.EXACT_SELECTOR_OPTIONS)
    assert [row["route"] for row in _report()["ranking"]["rows"]] == list(
        selector.EXACT_SELECTOR_OPTIONS
    )


def test_sandbox_wins_frozen_ranking() -> None:
    ranking = _report()["ranking"]
    assert ranking["selected_candidate_id"] == selector.SELECTED_CANDIDATE_ID
    assert ranking["selected_score"] == 245
    assert ranking["runner_up_candidate_id"] == "RETIRE_OR_DEFER_ANALYTIC_REPLACEMENT_LANE"
    assert ranking["runner_up_score"] == 195
    assert ranking["winning_margin"] == 50


def test_sandbox_is_stable_in_all_thirty_variants() -> None:
    sensitivity = _report()["sensitivity_analysis"]
    assert sensitivity["variant_count"] == 30
    assert sensitivity["selected_candidate_stable_in_all_variants"] is True
    assert sensitivity["minimum_winning_margin"] > 0


def test_one_shot_sandbox_contract_is_exact() -> None:
    contract = _report()["sandbox_execution_contract"]
    assert contract["execution_count_authorized"] == 1
    assert contract["infrastructure_control_count"] == 12
    assert contract["kernel_regression_case_count"] == 8
    assert contract["mandatory_result_labels"] == list(selector.EXPLORATORY_LABELS)
    assert len(contract["kernel_outputs_per_case"]) == 4
    assert contract["resource_envelope"]["total_timeout_seconds"] == 300
    assert contract["resource_envelope"]["total_memory_mib"] == 1024


def test_terminal_boundary_forbids_new_governance_layer() -> None:
    boundary = _report()["terminal_boundary"]
    assert boundary["governance_spiral_closed"] is True
    assert boundary["infrastructure_v1_authorized"] is False
    assert boundary["repair_packet_authorized"] is False
    assert boundary["prerequisite_to_prerequisite_authorized"] is False
    assert boundary["sandbox_preparation_packet_authorized"] is False
    assert boundary["automatic_retry_authorized"] is False


def test_scope_authorizes_isolated_execution_but_no_production_or_science() -> None:
    scope = _report()["scope"]
    true_keys = {key for key, value in scope.items() if value is True}
    assert true_keys == {
        "scientific_response_selection_executed",
        "terminal_ready_review_frozen",
        "exact_two_option_constraint_preserved",
        "isolated_sandbox_implementation_authorized",
        "one_sandbox_execution_authorized",
    }
    assert scope["sandbox_implemented_now"] is False
    assert scope["sandbox_executed_now"] is False
    assert scope["production_source_or_dispatch_change_authorized"] is False
    assert scope["historical_cubature_adjudication_authorized"] is False
    assert scope["scientific_claim_authorized"] is False


def test_forbidden_surface_and_claim_labels_are_complete() -> None:
    report = _report()
    assert len(report["forbidden_during_sandbox"]) == 5
    joined = " ".join(report["forbidden_during_sandbox"])
    for token in ("PRODUCTION", "CUBATURE", "TORQUE", "STAGE_A", "SCIENTIFIC"):
        assert token in joined
    for label in selector.EXPLORATORY_LABELS:
        assert label in report["sandbox_execution_contract"]["mandatory_result_labels"]


def test_human_selector_records_scores_boundary_and_next_authority() -> None:
    text = (ROOT / selector.HUMAN_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        selector.VERDICT,
        selector.SELECTED_ROUTE,
        "245",
        "195",
        "30 / 30",
        "exactly one implementation and one execution",
        "No sandbox code is created or run by this selector",
        selector.SELECTED_NEXT_TARGET,
    ):
        assert token in text
