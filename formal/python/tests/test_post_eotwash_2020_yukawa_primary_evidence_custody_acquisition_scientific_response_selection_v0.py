from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import (
    post_eotwash_2020_yukawa_primary_evidence_custody_acquisition_scientific_response_selection_v0
    as selection,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = REPO_ROOT / selection.REPORT_RELATIVE_PATH


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_selection_regenerates_and_freezes_accepted_review() -> None:
    assert selection.artifact_bytes() == REPORT_PATH.read_bytes()
    report = _report()
    assert report["target"] == selection.TARGET
    assert report["verdict"] == selection.VERDICT
    assert report["selected_candidate_id"] == selection.SELECTED_CANDIDATE_ID
    assert report["selected_next_target"] == selection.SELECTED_NEXT_TARGET
    assert {
        row["relative_path"]: row["sha256"]
        for row in report["authority"]["frozen_result_review_artifacts"]
    } == selection.AUTHORITY_HASHES


def test_exactly_four_routes_and_eight_criteria_are_compared() -> None:
    policy = _report()["selection_policy"]
    assert policy["candidate_count"] == 4
    assert policy["criterion_count"] == 8
    assert policy["criterion_scale"].endswith("NOT_TRUTH_PROBABILITY")


def test_contact_preparation_wins_and_synthetic_is_runner_up() -> None:
    ranking = _report()["ranking"]
    assert ranking["selected_candidate_id"] == selection.SELECTED_CANDIDATE_ID
    assert ranking["selected_score"] == 132
    assert ranking["runner_up_candidate_id"] == (
        "SCALAR_ONLY_YUKAWA_SYNTHETIC_FORWARD_MODEL_AND_SENSITIVITY_FORECAST"
    )
    assert ranking["runner_up_score"] == 89
    assert ranking["winning_margin"] == 43
    assert [row["weighted_score"] for row in ranking["rows"]] == [132, 89, 77, 75]


def test_selection_is_stable_in_all_twenty_four_variants() -> None:
    sensitivity = _report()["sensitivity_analysis"]
    assert sensitivity["variant_count"] == 24
    assert sensitivity["selected_candidate_stable_in_all_variants"] is True
    assert sensitivity["minimum_winning_margin"] > 0
    assert all(
        row["selected_candidate_id"] == selection.SELECTED_CANDIDATE_ID
        for row in sensitivity["rows"]
    )


def test_accepted_empirical_block_remains_unchanged() -> None:
    posture = _report()["retained_empirical_posture"]
    assert posture["experiment_suitable"] is True
    assert posture["fixed_signal"] == "A_Y=1/3"
    assert posture["acquisition_result"] == "AUTHORS_OR_CUSTODIAN_CONTACT_REQUIRED"
    assert posture["evidence_components_complete"] == 0
    assert posture["evidence_component_count"] == 6
    assert posture["independent_likelihood_executable"] is False
    assert posture["scalar_range_bound"] == "NONE"
    assert posture["alpha_constraint"] == "NONE"


def test_future_contact_packet_has_exact_eight_request_items() -> None:
    contract = _report()["selected_contact_packet_contract"]
    assert contract["status"] == "PREPARATION_AUTHORIZED_PACKET_NOT_PREPARED"
    assert contract["requested_item_count"] == 8
    assert len(contract["requested_items"]) == 8
    assert any("95x3" in item for item in contract["requested_items"])
    assert any("covariance" in item for item in contract["requested_items"])
    assert any("coverage" in item for item in contract["requested_items"])
    assert any("data-use" in item for item in contract["requested_items"])


def test_contact_packet_obligations_are_bounded_and_professional() -> None:
    obligations = _report()["selected_contact_packet_contract"][
        "future_packet_obligations"
    ]
    assert len(obligations) == 8
    assert any("public professional recipient" in row for row in obligations)
    assert any("does not challenge" in row for row in obligations)
    assert any("no unsolicited attachment" in row for row in obligations)
    assert any("before sending anything" in row for row in obligations)


def test_contact_is_neither_prepared_nor_authorized() -> None:
    contract = _report()["selected_contact_packet_contract"]
    assert contract["message_drafted_now"] is False
    assert contract["message_sent_now"] is False
    assert contract["contact_authorized"] is False
    assert contract["analysis_authorized"] is False
    assert contract["independent_packet_review_required"] is True


def test_deferred_routes_retain_exact_claim_boundaries() -> None:
    rows = _report()["deferred_route_boundaries"]
    assert rows["synthetic_forecast"] == (
        "IDEALIZED_OR_APPROXIMATE_APPARATUS_NOT_EOTWASH_EMPIRICAL_BOUND"
    )
    assert rows["published_reinterpretation"] == (
        "SUPPLIED_EMPIRICAL_CONSTRAINT_NOT_INDEPENDENTLY_REPRODUCED"
    )
    assert "COMPLETE_PUBLIC_DATA" in rows["alternative_experiment"]
    assert rows["all_deferred_not_rejected"] is True


def test_all_seventeen_selection_gates_pass() -> None:
    gates = _report()["selection_gates"]
    assert gates["gate_count"] == gates["pass_count"] == 17
    assert gates["failure_count"] == 0
    assert all(row["status"] == "PASS" for row in gates["rows"])


def test_scope_authorizes_only_contact_packet_preparation() -> None:
    scope = _report()["scope"]
    assert scope["scientific_response_selection_executed"] is True
    assert scope["contact_packet_preparation_authorized"] is True
    for key, value in scope.items():
        if key not in {
            "scientific_response_selection_executed",
            "contact_packet_preparation_authorized",
        }:
            assert value is False, key


def test_human_selection_records_ranking_boundaries_and_next_authority() -> None:
    text = (REPO_ROOT / selection.HUMAN_RELATIVE_PATH).read_text(
        encoding="utf-8"
    )
    for token in (
        selection.SELECTED_CANDIDATE_ID,
        selection.SELECTED_NEXT_TARGET,
        "132",
        "24 / 24",
        "SYNTHETIC FORECAST",
        "SUPPLIED EMPIRICAL CONSTRAINT",
        "NOT AUTHORIZED",
    ):
        assert token in text
