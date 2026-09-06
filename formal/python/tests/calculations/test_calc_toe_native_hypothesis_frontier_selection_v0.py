from __future__ import annotations

from copy import deepcopy

import pytest

from formal.python.toe.calculations.calc_toe_native_hypothesis_frontier_selection_v0 import (
    SELECTED_HYPOTHESIS_ID,
    SELECTED_NEXT_TARGET,
    build_calculation,
)
from formal.python.tools import (
    toe_native_hypothesis_frontier_selection_result_review as result_review,
)
from formal.python.tools.qft_gr_quadratic_hyperbolicity_common import (
    QuadraticHyperbolicityError,
)


build_review = result_review.build_review


def test_selector_chooses_one_evidence_bound_native_path() -> None:
    calculation = build_calculation()
    selected = [
        row
        for row in calculation["candidate_matrix"]
        if row["decision"] == "SELECT"
    ]
    assert len(selected) == 1
    assert selected[0]["candidate_path"] == (
        "CCFT_COHERENCE_ONTOLOGY_AND_REPRESENTATION"
    )
    assert calculation["selected_native_hypothesis"]["hypothesis_id"] == (
        SELECTED_HYPOTHESIS_ID
    )
    assert calculation["selected_next_target"] == SELECTED_NEXT_TARGET
    assert all(calculation["evidence_checks"].values())


def test_future_program_is_only_a_bounded_proposal() -> None:
    calculation = build_calculation()
    proposal = calculation["future_bounded_program_proposal"]
    assert proposal["proposal_status"] == "PROPOSAL_ONLY_NOT_INSTALLED_OR_OPEN"
    assert proposal["authorized_stage_count_proposed"] == 5
    assert proposal["repair_attempt_count_proposed"] == 0
    assert proposal["no_subsidiary_scientific_targets_proposed"] is True
    assert [row["stage_number"] for row in proposal["semantic_stages_proposed"]] == [
        1,
        2,
        3,
        4,
        5,
    ]
    assert proposal["installation_entry_requirements"] == {
        "exactly_one_coherence_claim_frozen": True,
        "support_criterion_required": True,
        "disfavor_criterion_required": True,
        "block_criterion_required": True,
        "failure_to_freeze_one_claim_closes_preparation": True,
        "scientific_authority_required_after_governance_enablement": True,
    }
    assert calculation["claim_boundary"]["new_bounded_program_installed"] is False
    assert calculation["claim_boundary"]["new_attempt_opened"] is False


def test_selection_does_not_assume_a_field_action_or_seam() -> None:
    boundary = build_calculation()["claim_boundary"]
    assert boundary["coherence_representation_selected"] is False
    assert boundary["coherence_field_type_selected"] is False
    assert boundary["native_field_content_selected"] is False
    assert boundary["native_action_selected"] is False
    assert boundary["native_interaction_selected"] is False
    assert boundary["pillar_or_seam_calculation_executed"] is False


def test_independent_review_accepts_only_program_preparation() -> None:
    review = build_review()
    assert review["accepted"] is True
    assert review["failed_checks"] == []
    assert all(review["checks"].values())
    assert review["selected_next_target"] == SELECTED_NEXT_TARGET
    assert review["program_installation_authorized"] is False
    assert review["scientific_stage_open_authorized"] is False
    assert review["terminal_outcome"] == (
        "SELECT_CCFT_COHERENCE_ONTOLOGY_AND_REPRESENTATION"
    )


@pytest.mark.parametrize(
    ("field", "mutated_value"),
    [
        ("proposal_only", False),
        ("installed", True),
        ("authorized", True),
        ("open_event_created", True),
    ],
)
def test_independent_review_rejects_false_program_installation_state(
    monkeypatch: pytest.MonkeyPatch,
    field: str,
    mutated_value: bool,
) -> None:
    calculation = deepcopy(build_calculation())
    calculation["future_bounded_program_proposal"][field] = mutated_value
    original_read_json = result_review.read_json

    def read_json_with_mutation(path):
        if path == result_review.CALCULATION_PATH:
            return calculation
        return original_read_json(path)

    monkeypatch.setattr(result_review, "read_json", read_json_with_mutation)
    with pytest.raises(
        QuadraticHyperbolicityError,
        match="future_program_is_proposal_only",
    ):
        build_review()


def test_independent_review_rejects_mutated_program_envelope(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    calculation = deepcopy(build_calculation())
    proposal = calculation["future_bounded_program_proposal"]
    proposal["semantic_stages_proposed"][0]["semantic_stage_id"] = (
        "RENAMED_STAGE"
    )
    proposal["mandatory_exit_target_proposed"] = "renamed_exit"
    proposal["terminal_outcome_vocabulary_proposed"] = ["RENAMED_OUTCOME"]
    original_read_json = result_review.read_json

    def read_json_with_mutation(path):
        if path == result_review.CALCULATION_PATH:
            return calculation
        return original_read_json(path)

    monkeypatch.setattr(result_review, "read_json", read_json_with_mutation)
    with pytest.raises(
        QuadraticHyperbolicityError,
        match="future_program_proposal_shape_is_complete",
    ):
        build_review()


def test_independent_review_recomputes_decision_evidence(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original_read_json = result_review.read_json

    def read_json_with_mutation(path):
        payload = original_read_json(path)
        if path == result_review.NATIVE_GRAVITY_REVIEW_PATH:
            payload = deepcopy(payload)
            payload["retained_results"]["native_principle"] = "SELECTED"
        return payload

    monkeypatch.setattr(result_review, "read_json", read_json_with_mutation)
    with pytest.raises(
        QuadraticHyperbolicityError,
        match="independent_decision_evidence_checks_pass",
    ):
        build_review()
