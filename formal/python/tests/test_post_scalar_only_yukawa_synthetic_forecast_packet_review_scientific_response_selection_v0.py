from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import (
    post_scalar_only_yukawa_synthetic_forecast_packet_review_scientific_response_selection_v0
    as selection,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = REPO_ROOT / selection.REPORT_RELATIVE_PATH


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_selection_regenerates_and_freezes_review_authority() -> None:
    assert selection.artifact_bytes() == REPORT_PATH.read_bytes()
    report = _report()
    assert report["target"] == selection.TARGET
    assert report["verdict"] == selection.VERDICT
    assert report["selected_candidate_id"] == selection.SELECTED_CANDIDATE_ID
    assert report["selected_next_target"] == selection.SELECTED_NEXT_TARGET
    assert {
        row["relative_path"]: row["sha256"]
        for row in report["authority"]["frozen_packet_review_artifacts"]
    } == selection.AUTHORITY_HASHES


def test_exactly_four_routes_and_eight_criteria_are_compared() -> None:
    policy = _report()["selection_policy"]
    assert policy["candidate_count"] == 4
    assert policy["criterion_count"] == 8
    assert policy["criterion_scale"].endswith("NOT_TRUTH_PROBABILITY")


def test_deterministic_stage_wins_and_simplified_forecast_is_runner_up() -> None:
    ranking = _report()["ranking"]
    assert ranking["selected_candidate_id"] == selection.SELECTED_CANDIDATE_ID
    assert ranking["selected_score"] == 145
    assert ranking["runner_up_candidate_id"] == "SIMPLIFIED_SYNTHETIC_FORECAST"
    assert ranking["runner_up_score"] == 103
    assert ranking["winning_margin"] == 42
    assert [row["weighted_score"] for row in ranking["rows"]] == [145, 103, 102, 85]


def test_selection_is_stable_in_all_twenty_four_variants() -> None:
    sensitivity = _report()["sensitivity_analysis"]
    assert sensitivity["variant_count"] == 24
    assert sensitivity["selected_candidate_stable_in_all_variants"] is True
    assert sensitivity["minimum_winning_margin"] > 0


def test_stage_a_has_exact_ten_deterministic_obligations() -> None:
    stage_a = _report()["selected_stage_a_contract"]
    assert stage_a["obligation_count"] == 10
    assert len(stage_a["obligations"]) == 10
    assert stage_a["gaussian_noise"] == "NONE"
    assert stage_a["monte_carlo_trials"] == "NONE"
    assert stage_a["sensitivity_forecast"] == "NONE"
    assert any("real-150" in row for row in stage_a["obligations"])
    assert any("Jacobian" in row for row in stage_a["obligations"])


def test_stage_b_is_deferred_until_accepted_stage_a() -> None:
    stage_b = _report()["deferred_stage_b"]
    assert stage_b["status"] == "DEFERRED_NOT_AUTHORIZED"
    assert stage_b["eligibility_condition"] == "INDEPENDENTLY_ACCEPTED_STAGE_A_RESULT"
    assert stage_b["future_target"] == (
        "prepare_scalar_only_yukawa_stochastic_sensitivity_forecast_packet_v0"
    )


def test_blocked_v0_review_and_internal_policy_are_retained() -> None:
    retained = _report()["retained_posture"]
    assert retained["blocked_packet_review_verdict"] == (
        "BLOCKED_SYNTHETIC_NOISE_OR_NUISANCE_CONTRACT"
    )
    assert retained["outbound_contact"] == "PROHIBITED_UNTIL_EXPLICITLY_REOPENED"
    assert retained["private_data_dependence"] == "PROHIBITED"
    assert retained["synthetic_data"] == "NONE_GENERATED"


def test_all_eighteen_selection_gates_pass() -> None:
    gates = _report()["selection_gates"]
    assert gates["gate_count"] == gates["pass_count"] == 18
    assert gates["failure_count"] == 0
    assert all(row["status"] == "PASS" for row in gates["rows"])


def test_scope_authorizes_only_deterministic_packet_preparation() -> None:
    scope = _report()["scope"]
    assert scope["scientific_response_selection_executed"] is True
    assert scope["deterministic_packet_preparation_authorized"] is True
    for key, value in scope.items():
        if key not in {
            "scientific_response_selection_executed",
            "deterministic_packet_preparation_authorized",
        }:
            assert value is False, key


def test_human_selection_records_decomposition_and_next_authority() -> None:
    text = (REPO_ROOT / selection.HUMAN_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        "DETERMINISTIC TORSION-BALANCE FORWARD-MODEL VALIDATION",
        "STOCHASTIC SENSITIVITY FORECAST — DEFERRED",
        "145",
        "24",
        "Gaussian noise:",
        selection.SELECTED_NEXT_TARGET,
    ):
        assert token in text

