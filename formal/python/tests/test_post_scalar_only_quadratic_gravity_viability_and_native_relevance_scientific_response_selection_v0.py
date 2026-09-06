from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.tools import (
    post_scalar_only_quadratic_gravity_viability_and_native_relevance_scientific_response_selection_v0
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
    before = {
        path: _sha256(REPO_ROOT / path) for path in selection.AUTHORITY_HASHES
    }
    selection.build_selection()
    after = {
        path: _sha256(REPO_ROOT / path) for path in selection.AUTHORITY_HASHES
    }
    assert before == after == selection.AUTHORITY_HASHES


def test_bounded_scalar_phenomenology_packet_preparation_is_selected() -> None:
    report = _report()
    assert report["target"] == selection.TARGET
    assert report["verdict"] == selection.VERDICT
    assert report["selected_candidate_id"] == selection.SELECTED_CANDIDATE_ID
    assert report["selected_next_target"] == selection.SELECTED_NEXT_TARGET
    assert report["selected_next_target_kind"] == (
        selection.SELECTED_NEXT_TARGET_KIND
    )


def test_exactly_four_routes_and_eight_criteria_are_compared() -> None:
    policy = _report()["selection_policy"]
    assert policy["candidate_count"] == 4
    assert policy["criterion_count"] == 8
    assert policy["maximum_weighted_score"] == 125
    assert set(policy["weights"]) == set(selection.CRITERIA)


def test_ranking_matches_declared_priority_order() -> None:
    rows = _report()["ranking"]["rows"]
    assert [row["candidate_id"] for row in rows] == [
        "BOUND_SCALAR_ONLY_RANGE_AND_WEAK_FIELD_PHENOMENOLOGY",
        "SUPPLIED_0I_TO_ORBIT_COMPARATOR",
        "NATIVE_SCALAR_POSTULATE_REQUIREMENTS",
        "MINIMAL_MODE_REQUIREMENTS",
    ]
    assert [row["weighted_score"] for row in rows] == [119, 97, 82, 75]


def test_priority_scores_are_not_truth_probabilities() -> None:
    assert _report()["selection_policy"]["criterion_scale"] == (
        "0..5_RESEARCH_PRIORITY_NOT_TRUTH_PROBABILITY"
    )


def test_winner_is_stable_across_all_sensitivity_variants() -> None:
    sensitivity = _report()["sensitivity_analysis"]
    assert sensitivity["variant_count"] == 24
    assert sensitivity["selected_candidate_stable_in_all_variants"] is True
    assert sensitivity["minimum_winning_margin"] > 0
    assert all(
        row["selected_candidate_id"] == selection.SELECTED_CANDIDATE_ID
        for row in sensitivity["rows"]
    )


def test_accepted_scalar_mass_range_and_yukawa_map_are_retained() -> None:
    scalar = _report()["retained_scalar_comparison"]
    assert scalar["mass_squared"] == "m0^2=-1/(6 alpha)"
    assert scalar["range"] == "lambda0=1/m0=sqrt(-6 alpha)"
    assert scalar["Yukawa_relative_strength"] == (
        "1/3 IN_FROZEN_POINT_SOURCE_MODEL"
    )
    assert scalar["native_scalar_bridge_count"] == 0


def test_packet_preparation_caps_observables_and_selects_no_data() -> None:
    packet = _report()["selected_packet_contract"]
    assert packet["observable_class_cap"] == 2
    assert len(packet["candidate_observable_classes_not_yet_selected"]) == 2
    assert packet["dataset_selected_now"] is False
    assert packet["numerical_alpha_or_mass_bound_computed_now"] is False
    assert packet["execution_authorized"] is False
    assert packet["independent_packet_review_required"] is True


def test_packet_obligations_freeze_statistics_before_execution() -> None:
    obligations = _report()["selected_packet_contract"]["required_obligations"]
    for phrase in (
        "SI convention",
        "primary-source data",
        "uncertainties",
        "likelihood or exclusion rule",
        "Einstein and infinite-mass controls",
    ):
        assert any(phrase in row for row in obligations)


def test_other_routes_are_deferred_not_rejected() -> None:
    rows = _report()["ranking"]["rows"]
    assert all(row["disposition"] == "DEFERRED_NOT_REJECTED" for row in rows[1:])


def test_all_fourteen_preparation_gates_pass() -> None:
    gates = _report()["preparation_gates"]
    assert gates["gate_count"] == gates["pass_count"] == 14
    assert gates["failure_count"] == 0
    assert all(row["status"] == "PASS" for row in gates["rows"])


def test_scope_authorizes_packet_preparation_only() -> None:
    scope = _report()["scope"]
    allowed_true = {
        "scientific_response_selection_executed",
        "range_and_weak_field_packet_preparation_authorized",
    }
    assert all(scope[key] is True for key in allowed_true)
    for key, value in scope.items():
        if key not in allowed_true:
            assert value is False, key


def test_claim_ceiling_forbids_data_parameter_and_theory_selection() -> None:
    claim = _report()["claim_ceiling"]
    for token in (
        "No beta=0 law",
        "alpha value or bound",
        "scalar branch",
        "native scalar bridge",
        "dataset",
        "empirical result",
        "orbital result",
        "V2 cell",
    ):
        assert token in claim


def test_human_selection_records_ranking_controls_and_stop() -> None:
    text = (REPO_ROOT / selection.HUMAN_RELATIVE_PATH).read_text(
        encoding="utf-8"
    )
    for token in (
        selection.VERDICT,
        "Bounded scalar range and weak-field phenomenology",
        "119",
        "97",
        "82",
        "75",
        "14 / 14 PASSED",
        "beta=0 adopted:                    NO",
        selection.SELECTED_NEXT_TARGET,
    ):
        assert token in text
