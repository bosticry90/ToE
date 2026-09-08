from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.tools import (
    post_scalar_only_quadratic_gravity_range_and_weak_field_constraint_packet_review_scientific_response_selection_v0
    as selection,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = REPO_ROOT / selection.REPORT_RELATIVE_PATH


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_selection_regenerates_exactly_and_preserves_review_custody() -> None:
    assert selection.artifact_bytes() == REPORT_PATH.read_bytes()
    before = {path: _sha256(REPO_ROOT / path) for path in selection.AUTHORITY_HASHES}
    selection.build_selection()
    after = {path: _sha256(REPO_ROOT / path) for path in selection.AUTHORITY_HASHES}
    assert before == after == selection.AUTHORITY_HASHES


def test_targeted_eotwash_acquisition_packet_preparation_is_selected() -> None:
    report = _report()
    assert report["target"] == selection.TARGET
    assert report["verdict"] == selection.VERDICT
    assert report["selected_candidate_id"] == selection.SELECTED_CANDIDATE_ID
    assert report["selected_next_target"] == selection.SELECTED_NEXT_TARGET
    assert report["selected_next_target_kind"] == selection.SELECTED_NEXT_TARGET_KIND


def test_exactly_four_routes_and_eight_criteria_are_compared() -> None:
    policy = _report()["selection_policy"]
    assert policy["candidate_count"] == 4
    assert policy["criterion_count"] == 8
    assert policy["maximum_weighted_score"] == 135
    assert set(policy["weights"]) == set(selection.CRITERIA)


def test_ranking_matches_declared_priority_order() -> None:
    rows = _report()["ranking"]["rows"]
    assert [row["candidate_id"] for row in rows] == [
        "TARGETED_EOTWASH_PRIMARY_EVIDENCE_AND_FORWARD_MODEL_ACQUISITION",
        "FULLY_PUBLIC_ALTERNATIVE_EXPERIMENT_SELECTION",
        "SUPPLIED_PUBLISHED_EOTWASH_CONSTRAINT_REINTERPRETATION",
        "TEMPORARILY_CLOSE_SCALAR_EMPIRICAL_LANE",
    ]
    assert [row["weighted_score"] for row in rows] == [133, 94, 84, 50]


def test_priority_scores_are_not_truth_probabilities() -> None:
    assert _report()["selection_policy"]["criterion_scale"] == (
        "0..5_RESEARCH_PRIORITY_NOT_TRUTH_PROBABILITY"
    )


def test_winner_is_stable_across_all_24_variants() -> None:
    sensitivity = _report()["sensitivity_analysis"]
    assert sensitivity["variant_count"] == 24
    assert sensitivity["selected_candidate_stable_in_all_variants"] is True
    assert sensitivity["minimum_winning_margin"] > 0
    assert all(
        row["selected_candidate_id"] == selection.SELECTED_CANDIDATE_ID
        for row in sensitivity["rows"]
    )


def test_confirmed_experimental_block_is_retained() -> None:
    block = _report()["retained_block"]
    assert block["experiment_scientifically_suitable"] is True
    assert block["fixed_signal"] == "A_Y=1/3"
    assert block["independent_project_fit_executable"] is False
    assert block["principal_block"] == "BLOCKED_PRIMARY_DATA_OR_COVARIANCE_INCOMPLETE"
    assert block["likelihood"] == "NOT_EXECUTED"
    assert block["scalar_range_bound"] == "NONE"
    assert block["alpha_constraint"] == "NONE"


def test_acquisition_packet_requires_all_six_content_components() -> None:
    packet = _report()["selected_acquisition_packet_contract"]
    assert packet["required_component_count"] == 6
    assert packet["required_components"] == [
        "complete 95x3 torque observations",
        "displacement and configuration metadata",
        "numerical uncertainty and covariance model",
        "five numerical nuisance priors",
        "executable extended-source torque implementation",
        "executable or fully specified boundary-coverage calibration",
    ]


def test_supplement_receipt_does_not_automatically_complete_contract() -> None:
    packet = _report()["selected_acquisition_packet_contract"]
    assert packet["supplement_receipt_automatically_completes_contract"] is False
    assert packet["dissertation_may_fill_missing_values_by_inference"] is False


def test_acquisition_packet_has_all_five_terminal_outcomes() -> None:
    outcomes = _report()["selected_acquisition_packet_contract"]["terminal_outcomes"]
    assert outcomes == [
        "PRIMARY_EVIDENCE_CONTRACT_COMPLETE",
        "SUPPLEMENT_ACQUIRED_BUT_FORWARD_MODEL_INCOMPLETE",
        "SUPPLEMENT_ACQUIRED_BUT_COVARIANCE_INCOMPLETE",
        "AUTHORS_OR_CUSTODIAN_CONTACT_REQUIRED",
        "PRIMARY_EVIDENCE_NOT_OBTAINABLE_WITHIN_BOUNDED_ROUTE",
    ]


def test_selected_route_authorizes_packet_preparation_not_acquisition_or_fit() -> None:
    packet = _report()["selected_acquisition_packet_contract"]
    assert packet["status"] == "PREPARATION_AUTHORIZED_EXECUTION_NOT_AUTHORIZED"
    assert packet["fit_execution_authorized"] is False
    assert packet["independent_review_required"] is True
    scope = _report()["scope"]
    assert scope["eotwash_acquisition_packet_preparation_authorized"] is True
    assert scope["eotwash_acquisition_packet_prepared_now"] is False
    assert scope["supplement_download_or_acquisition_authorized"] is False
    assert scope["author_or_custodian_contact_authorized"] is False


def test_other_routes_are_deferred_not_rejected() -> None:
    rows = _report()["ranking"]["rows"]
    assert all(row["disposition"] == "DEFERRED_NOT_REJECTED" for row in rows[1:])


def test_supplied_reinterpretation_does_not_become_independent_reproduction() -> None:
    rows = {row["candidate_id"]: row for row in _report()["ranking"]["rows"]}
    supplied = rows["SUPPLIED_PUBLISHED_EOTWASH_CONSTRAINT_REINTERPRETATION"]
    assert supplied["scores"]["likelihood_of_restoring_independent_fit"] == 0
    assert "without claiming independent reproduction" in supplied["scientific_endpoint"]


def test_alternative_experiment_requires_reproducibility_and_signal_match() -> None:
    rows = {row["candidate_id"]: row for row in _report()["ranking"]["rows"]}
    alternate = rows["FULLY_PUBLIC_ALTERNATIVE_EXPERIMENT_SELECTION"]
    assert alternate["scores"]["reproducibility_gain"] == 5
    assert "real sensitivity near A_Y=1/3" in alternate["scientific_endpoint"]


def test_all_fifteen_preparation_gates_pass() -> None:
    gates = _report()["preparation_gates"]
    assert gates["gate_count"] == gates["pass_count"] == 15
    assert gates["failure_count"] == 0
    assert all(row["status"] == "PASS" for row in gates["rows"])


def test_scope_authorizes_only_selection_and_packet_preparation() -> None:
    scope = _report()["scope"]
    allowed_true = {
        "scientific_response_selection_executed",
        "eotwash_acquisition_packet_preparation_authorized",
    }
    assert all(scope[key] is True for key in allowed_true)
    for key, value in scope.items():
        if key not in allowed_true:
            assert value is False, key


def test_claim_ceiling_forbids_contact_fit_bounds_and_theory_selection() -> None:
    claim = _report()["claim_ceiling"]
    for token in (
        "No supplement download",
        "author or custodian contact",
        "likelihood",
        "alpha bound",
        "scalar-branch adoption",
        "native gravitational principle",
        "gravitational action",
    ):
        assert token in claim


def test_current_posture_rotates_to_acquisition_packet_preparation_only() -> None:
    posture = _report()["current_posture"]
    assert posture["selection_stability"] == "FIRST_IN_24_OF_24_VARIANTS"
    assert posture["packet"] == "NOT_YET_PREPARED"
    assert posture["evidence_acquisition"] == "NOT_STARTED"
    assert posture["author_contact"] == "NOT_AUTHORIZED"
    assert posture["likelihood"] == "NOT_EXECUTED"
    assert posture["next_authority"] == selection.SELECTED_NEXT_TARGET
