from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.tools import post_quadratic_gravity_comparison_scientific_response_selection_v0 as selection


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


def test_selection_preserves_accepted_result_review_bytes() -> None:
    before = {path: _sha256(REPO_ROOT / path) for path in selection.AUTHORITY_HASHES}
    selection.build_selection()
    after = {path: _sha256(REPO_ROOT / path) for path in selection.AUTHORITY_HASHES}
    assert before == after == selection.AUTHORITY_HASHES


def test_exact_authority_and_accepted_result_are_consumed() -> None:
    report = _report()
    assert report["target"] == selection.TARGET
    assert report["authority"]["consumed_verdict"] == (
        "ACCEPTED_BOUNDED_SHARED_LINEARIZED_QUADRATIC_GRAVITY_COMPARISON_RESULT"
    )
    assert report["authority"]["consumed_review_gates"] == 16


def test_conditional_envelope_packet_is_selected() -> None:
    report = _report()
    assert report["verdict"] == selection.VERDICT
    assert report["selected_next_target"] == selection.SELECTED_NEXT_TARGET
    assert report["ranking"]["selected_candidate_id"] == (
        "PREPARE_CONDITIONAL_MODE_SELECTION_ENVELOPE"
    )
    assert report["ranking"]["runner_up_candidate_id"] == (
        "RESUME_METRIC_TO_ORBIT_AND_FRAME_DRAGGING_TRANSPORT"
    )


def test_scoring_is_bounded_and_winner_is_robust() -> None:
    report = _report()
    assert sum(report["selection_policy"]["weights"].values()) == 20
    assert report["selection_policy"]["maximum_weighted_score"] == 100
    assert report["ranking"]["selected_score"] == 100
    assert report["ranking"]["runner_up_score"] == 69
    sensitivity = report["sensitivity_analysis"]
    assert sensitivity["variant_count"] == 24
    assert sensitivity["selected_candidate_stable_in_all_variants"] is True
    assert sensitivity["minimum_winning_margin"] > 0


def test_tachyon_conditions_are_not_misreported_as_mode_removal() -> None:
    rows = {
        row["condition_id"]: row
        for row in _report()["conditional_mode_selection_envelope"]["rows"]
    }
    assert rows["NON_TACHYONIC_SCALAR"]["consequence"] == "Sigma=3 alpha+beta<0"
    assert rows["NON_TACHYONIC_SCALAR"]["qualification"] == (
        "DOES_NOT_REMOVE_SCALAR_OR_PROVE_FULL_STABILITY"
    )
    assert rows["NON_TACHYONIC_ADDITIONAL_SPIN_2"]["consequence"] == "beta>0"
    assert rows["NON_TACHYONIC_ADDITIONAL_SPIN_2"]["qualification"] == (
        "NEGATIVE_SATURATED_RESIDUE_REMAINS"
    )


def test_exact_extra_mode_removal_and_einstein_limit_are_correct() -> None:
    rows = {
        row["condition_id"]: row
        for row in _report()["conditional_mode_selection_envelope"]["rows"]
    }
    assert rows["NO_NEGATIVE_RESIDUE_ADDITIONAL_SPIN_2_POLE"]["consequence"] == "beta=0"
    assert rows["NO_ADDITIONAL_SCALAR_POLE"]["consequence"] == "Sigma=0"
    assert rows["NO_ADDITIONAL_MODES"]["consequence"] == (
        "beta=0 and Sigma=0 implies alpha=beta=0"
    )


def test_scalar_only_non_tachyonic_branch_is_correct() -> None:
    rows = {
        row["condition_id"]: row
        for row in _report()["conditional_mode_selection_envelope"]["rows"]
    }
    branch = rows["SCALAR_ALLOWED_SPIN_2_EXCLUDED_AND_SCALAR_NON_TACHYONIC"]
    assert branch["condition"] == "beta=0 and m0^2>0"
    assert branch["consequence"] == "beta=0 and alpha<0"


def test_long_range_and_exact_current_conditions_are_separated() -> None:
    rows = {
        row["condition_id"]: row
        for row in _report()["conditional_mode_selection_envelope"]["rows"]
    }
    assert rows["LONG_RANGE_EINSTEIN_RESPONSE_ONLY"]["exact_within_frozen_family"] is False
    current = rows["EXACT_UNMODIFIED_STATIONARY_0I_FOR_GENERIC_CURRENTS"]
    assert current["consequence"] == "beta=0"
    assert "EMPIRICAL_AGREEMENT" in current["qualification"]


def test_coincident_mass_is_not_a_cancellation_escape() -> None:
    rule = _report()["conditional_mode_selection_envelope"]["coincident_mass_rule"]
    for token in ("coincident simple poles", "orthogonal P2 and P0s", "no cancellation"):
        assert token in rule


def test_authority_classes_are_exact_and_no_condition_is_adopted() -> None:
    envelope = _report()["conditional_mode_selection_envelope"]
    assert envelope["authority_classes_required"] == [
        "PROJECT_BOUND_NATIVE_PRINCIPLE",
        "SUPPLIED_STANDARD_PHYSICS_CRITERION",
        "PROPOSED_NEW_POSTULATE",
        "EMPIRICAL_CONSTRAINT",
    ]
    assert envelope["condition_adopted_now"] is None


def test_twelve_preparation_gates_pass() -> None:
    gates = _report()["preparation_gates"]
    assert gates["gate_count"] == gates["pass_count"] == 12
    assert gates["failure_count"] == 0
    assert all(row["status"] == "PASS" for row in gates["rows"])


def test_selection_authorizes_packet_preparation_only() -> None:
    scope = _report()["scope"]
    assert scope["scientific_response_selection_executed"] is True
    assert scope["conditional_packet_preparation_authorized"] is True
    for key, value in scope.items():
        if key not in {
            "scientific_response_selection_executed",
            "conditional_packet_preparation_authorized",
        }:
            assert value is False, key


def test_claim_ceiling_forbids_promotion_and_downstream_work() -> None:
    claim = _report()["claim_ceiling"]
    for token in (
        "No condition",
        "native principle",
        "postulate",
        "coupling",
        "action",
        "outside-family mechanism",
        "empirical constraint",
        "orbital transport",
        "frame-dragging result",
        "V2 cell",
    ):
        assert token in claim

