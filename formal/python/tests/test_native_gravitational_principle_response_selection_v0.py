from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.tools import native_gravitational_principle_response_selection_v0 as selection


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = REPO_ROOT / selection.REPORT_RELATIVE_PATH


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_selection_regenerates_exactly_and_deterministically() -> None:
    assert selection.artifact_bytes() == selection.artifact_bytes() == REPORT_PATH.read_bytes()


def test_selection_preserves_every_frozen_authority_byte() -> None:
    before = {path: _sha256(REPO_ROOT / path) for path in selection.AUTHORITY_HASHES}
    selection.build_selection()
    after = {path: _sha256(REPO_ROOT / path) for path in selection.AUTHORITY_HASHES}
    assert before == after == selection.AUTHORITY_HASHES


def test_selection_consumes_exact_terminal_block_and_target() -> None:
    report = _report()
    assert report["target"] == selection.TARGET
    assert report["authority"]["terminal_contract_review"] == (
        "BLOCKED_NO_NATIVE_GRAVITATIONAL_PRINCIPLE"
    )
    assert report["authority"]["terminal_diagnostic"] == (
        "NO_BOUND_NATIVE_GRAVITATIONAL_PRINCIPLE_OR_POSTULATE"
    )
    assert report["authority"]["contract_design"] == (
        "PASS_COMPLETE_BOUNDED_REVIEW_CONTRACT"
    )


def test_requirements_and_no_go_route_is_selected() -> None:
    report = _report()
    assert report["verdict"] == (
        "SELECTED_NATIVE_GRAVITATIONAL_PRINCIPLE_REQUIREMENTS_AND_NO_GO_PREPARATION"
    )
    assert report["selected_next_target"] == selection.SELECTED_NEXT_TARGET
    assert report["ranking"]["selected_candidate_id"] == (
        "DEFINE_NATIVE_GRAVITATIONAL_PRINCIPLE_REQUIREMENTS_AND_NO_GO_ENVELOPE"
    )
    assert report["ranking"]["runner_up_candidate_id"] == (
        "EXPLICITLY_POSTULATE_NATIVE_GRAVITATIONAL_CANDIDATE"
    )


def test_scoring_contract_is_bounded_and_complete() -> None:
    policy = _report()["selection_policy"]
    assert policy["criterion_scale"] == "0..5"
    assert sum(policy["weights"].values()) == 20
    assert policy["maximum_weighted_score"] == 100
    assert policy["candidate_count"] == len(selection.CANDIDATES) == 4
    for row in _report()["ranking"]["rows"]:
        assert set(row["scores"]) == set(selection.CRITERIA)
        assert 0 <= row["weighted_score"] <= 100


def test_selection_scores_and_margin_are_exact() -> None:
    ranking = _report()["ranking"]
    assert ranking["selected_score"] == 98
    assert ranking["runner_up_score"] == 86
    assert ranking["selected_score"] - ranking["runner_up_score"] == 12


def test_selection_is_stable_in_all_twenty_four_variants() -> None:
    sensitivity = _report()["sensitivity_analysis"]
    assert sensitivity["variant_count"] == len(sensitivity["rows"]) == 24
    assert sensitivity["selected_candidate_stable_in_all_variants"] is True
    assert sensitivity["minimum_winning_margin"] == 6
    assert all(
        row["selected_candidate_id"]
        == "DEFINE_NATIVE_GRAVITATIONAL_PRINCIPLE_REQUIREMENTS_AND_NO_GO_ENVELOPE"
        for row in sensitivity["rows"]
    )


def test_selected_packet_freezes_selection_power_collapse_and_distinctiveness() -> None:
    obligation = _report()["selected_scientific_obligation"]
    assert obligation["pillar"] == "GR"
    assert len(obligation["packet_must_freeze"]) == 10
    joined = " ".join(obligation["packet_must_freeze"])
    for token in (
        "action-selection power",
        "standard-GR collapse",
        "distinctiveness",
        "new postulate",
    ):
        assert token in joined


def test_allowed_results_are_exact_and_do_not_prejudge_analysis() -> None:
    outcomes = _report()["selected_scientific_obligation"]["allowed_terminal_results"]
    assert outcomes == [
        "NATIVE_PRINCIPLE_SET_SELECTS_ACTION_FAMILY",
        "CURRENT_REQUIREMENTS_COLLAPSE_TO_STANDARD_GR",
        "ACTION_FAMILY_UNDERDETERMINED",
        "DISTINCTIVE_GRAVITATIONAL_POSTULATE_REQUIRED",
        "REQUIREMENT_SET_INCONSISTENT",
        "NO_GO_UNDER_MINIMAL_METRIC_LOCAL_ASSUMPTIONS",
    ]


def test_retained_boundaries_preserve_every_upstream_block() -> None:
    boundaries = _report()["retained_boundaries"]
    assert boundaries["minimal_gravitational_contract"] == "ACCEPTED"
    assert boundaries["native_gravitational_principle"] == "NOT_FOUND"
    assert boundaries["native_gravitational_action"] == "NOT_SELECTED"
    assert boundaries["standard_Einstein_Hilbert_sector"] == "SUPPLIED_COMPARATOR_ONLY"
    assert boundaries["C_k"] == "EXTERNAL_ADMISSIBILITY_AUDIT_ONLY"
    assert boundaries["gravitomagnetic_recovery"] == "BLOCKED_UPSTREAM"


def test_selection_authorizes_packet_preparation_only() -> None:
    scope = _report()["scope"]
    assert scope["response_selection_executed"] is True
    assert scope["packet_preparation_authorized"] is True
    for key, value in scope.items():
        if key not in {"response_selection_executed", "packet_preparation_authorized"}:
            assert value is False, key


def test_claim_ceiling_forbids_action_postulate_physics_tooling_and_automation() -> None:
    claim = _report()["claim_ceiling"]
    for token in (
        "creates no principle",
        "postulate",
        "action",
        "variation",
        "standard-GR result",
        "frame-dragging result",
        "general tooling",
        "automation",
    ):
        assert token in claim
