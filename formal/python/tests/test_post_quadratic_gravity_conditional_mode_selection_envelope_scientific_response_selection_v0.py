from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.tools import (
    post_quadratic_gravity_conditional_mode_selection_envelope_scientific_response_selection_v0 as selection,
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
    assert selection.artifact_bytes() == selection.artifact_bytes() == REPORT_PATH.read_bytes()
    before = {path: _sha256(REPO_ROOT / path) for path in selection.AUTHORITY_HASHES}
    selection.build_selection()
    after = {path: _sha256(REPO_ROOT / path) for path in selection.AUTHORITY_HASHES}
    assert before == after == selection.AUTHORITY_HASHES


def test_scalar_only_packet_preparation_is_selected() -> None:
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
    assert policy["maximum_weighted_score"] == 110
    assert set(policy["weights"]) == set(selection.CRITERIA)


def test_ranking_matches_declared_priority_order() -> None:
    ranking = _report()["ranking"]
    rows = ranking["rows"]
    assert [row["candidate_id"] for row in rows] == [
        "SCALAR_ONLY_VIABILITY_AND_NATIVE_RELEVANCE",
        "MINIMAL_MODE_POSTULATE_REQUIREMENTS_ANALYSIS",
        "SUPPLIED_0I_TO_ORBIT_COMPARATOR_TRANSPORT",
        "OUTSIDE_FAMILY_GHOST_AVOIDANCE_MECHANISM_SURVEY",
    ]
    assert [row["weighted_score"] for row in rows] == [110, 90, 89, 64]
    assert ranking["selected_score"] == 110
    assert ranking["runner_up_score"] == 90


def test_priority_scores_are_not_truth_probabilities() -> None:
    assert _report()["selection_policy"]["criterion_scale"] == (
        "0..5_RESEARCH_PRIORITY_NOT_TRUTH_PROBABILITY"
    )


def test_selected_route_is_stable_across_all_sensitivity_variants() -> None:
    sensitivity = _report()["sensitivity_analysis"]
    assert sensitivity["variant_count"] == 24
    assert sensitivity["selected_candidate_stable_in_all_variants"] is True
    assert sensitivity["minimum_winning_margin"] > 0
    assert all(
        row["selected_candidate_id"] == selection.SELECTED_CANDIDATE_ID
        for row in sensitivity["rows"]
    )


def test_beta_zero_is_only_a_conditionally_motivated_study_boundary() -> None:
    packet = _report()["selected_packet_contract"]
    assert packet["status"] == "SUPPLIED_COMPARISON_SUBFAMILY_CONDITIONALLY_MOTIVATED_NOT_SELECTED"
    assert packet["comparison_subfamily"] == "R+alpha R^2"
    assert packet["beta_status"] == "beta=0 STUDY_CONDITION_FROM_SUPPLIED_GHOST_AVOIDANCE_NOT_ADOPTED"
    assert packet["alpha_status"] == "SYMBOLIC_UNSELECTED"
    assert packet["execution_authorized"] is False
    assert packet["independent_packet_review_required"] is True


def test_packet_questions_cover_viability_and_native_relevance_without_preloading_answers() -> None:
    questions = _report()["selected_packet_contract"]["questions"]
    assert len(questions) == 8
    for phrase in (
        "stability",
        "source trace",
        "scalar range",
        "screening or decoupling",
        "native scalar relevance",
        "localized obstruction",
    ):
        assert any(phrase in question for question in questions)


def test_retained_scalar_facts_do_not_adopt_branch() -> None:
    facts = _report()["retained_conditional_facts"]
    assert facts["beta_zero_consequence"].startswith("additional negative-residue spin-2 pole absent")
    assert facts["scalar_mass_on_beta_zero"] == "m0^2=-1/(6 alpha)"
    assert facts["non_tachyonic_scalar_on_beta_zero"] == "alpha<0 under frozen conventions"
    assert facts["facts_adopt_beta_zero_or_scalar_branch"] is False


def test_other_routes_are_deferred_not_rejected_or_opened() -> None:
    rows = _report()["ranking"]["rows"]
    for row in rows[1:]:
        assert "DEFERRED" in row["disposition"]
        assert "NOT_REJECTED" in row["disposition"]
    scope = _report()["scope"]
    assert scope["outside_family_mechanism_opened"] is False
    assert scope["orbital_transport_authorized"] is False
    assert scope["new_postulate_proposed_or_authorized"] is False


def test_all_fourteen_preparation_gates_pass() -> None:
    gates = _report()["preparation_gates"]
    assert gates["gate_count"] == gates["pass_count"] == 14
    assert gates["failure_count"] == 0
    assert all(row["status"] == "PASS" for row in gates["rows"])


def test_scope_authorizes_packet_preparation_only() -> None:
    scope = _report()["scope"]
    allowed_true = {
        "scientific_response_selection_executed",
        "scalar_viability_packet_preparation_authorized",
    }
    assert all(scope[key] is True for key in allowed_true)
    for key, value in scope.items():
        if key not in allowed_true:
            assert value is False, key


def test_claim_ceiling_forbids_adoption_execution_and_downstream_work() -> None:
    claim = _report()["claim_ceiling"]
    for token in (
        "No beta=0 law",
        "scalar branch",
        "alpha value",
        "R+alpha R^2 action",
        "scalar viability claim",
        "native principle",
        "matter action",
        "orbital transport",
        "frame-dragging result",
        "V2 cell",
    ):
        assert token in claim


def test_human_selection_records_ranking_boundaries_and_stop() -> None:
    text = (REPO_ROOT / selection.HUMAN_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        selection.VERDICT,
        "Scalar-only viability and native relevance",
        "110",
        "90",
        "89",
        "64",
        "14 / 14 PASSED",
        "beta=0 adopted:                    NO",
        selection.SELECTED_NEXT_TARGET,
    ):
        assert token in text
