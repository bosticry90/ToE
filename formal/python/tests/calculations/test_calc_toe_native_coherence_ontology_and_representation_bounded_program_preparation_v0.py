from __future__ import annotations

from copy import deepcopy

import pytest

from formal.python.toe.calculations.calc_toe_native_coherence_ontology_and_representation_bounded_program_preparation_v0 import (
    HYPOTHESIS_ID,
    MANDATORY_EXIT_TARGET,
    PROGRAM_ID,
    PROGRAM_TERMINAL_OUTCOMES,
    REPRESENTATION_FAMILIES,
    build_calculation,
)
from formal.python.tools import (
    toe_native_coherence_ontology_and_representation_bounded_program_preparation_result_review
    as result_review,
)
from formal.python.tools.qft_gr_quadratic_hyperbolicity_common import (
    QuadraticHyperbolicityError,
)


def test_preparation_defines_a_five_stage_proposal_only() -> None:
    calculation = build_calculation()
    proposal = calculation["program_proposal"]
    assert calculation["native_hypothesis_tested"] == HYPOTHESIS_ID
    assert proposal["program_id"] == PROGRAM_ID
    assert proposal["proposal_only"] is True
    assert proposal["installed"] is False
    assert proposal["authorized"] is False
    assert proposal["open_event_created"] is False
    assert proposal["attempt_count"] == 0
    assert proposal["authorized_stage_count_proposed"] == 5
    assert proposal["repair_attempt_count_proposed"] == 0
    assert proposal["no_subsidiary_scientific_targets_proposed"] is True
    assert proposal["mandatory_exit_target_proposed"] == MANDATORY_EXIT_TARGET


def test_program_compounds_in_the_accepted_dependency_order() -> None:
    stages = build_calculation()["program_proposal"]["semantic_stages_proposed"]
    assert [stage["semantic_stage_id"] for stage in stages] == [
        "CONTROLLED_COHERENCE_CLAIM_INVENTORY",
        "COHERENCE_OPERATIONAL_DEFINITION_TEST",
        "COHERENCE_REPRESENTATION_COMPARISON",
        "COHERENCE_OPERATIONAL_REPRESENTABILITY_DECISION",
        "MINIMAL_NATIVE_FIELD_HANDOFF",
    ]
    assert stages[4]["conditional"] is True
    assert all(
        stage["proposed_open_event_scope"][
            "substantive_stage_output_allowed"
        ]
        is False
        for stage in stages
    )


def test_stage_1_selects_one_claim_or_fails_closed() -> None:
    stage = build_calculation()["program_proposal"][
        "semantic_stages_proposed"
    ][0]
    assert (
        "exactly_one_claim_selected_for_stage_2_or_failed_closed"
        in stage["canonical_scope"]["required_outputs"]
    )
    assert (
        "symbolic similarity as evidence of physical identity"
        in stage["canonical_scope"]["prohibited_claims"]
    )


def test_representation_comparison_does_not_preselect_a_field() -> None:
    calculation = build_calculation()
    proposal = calculation["program_proposal"]
    assert proposal["representation_families_to_compare"] == (
        REPRESENTATION_FAMILIES
    )
    assert calculation["claim_boundary"]["coherence_representation_selected"] is False
    assert calculation["claim_boundary"]["coherence_field_selected"] is False
    assert calculation["claim_boundary"]["native_action_selected"] is False


def test_stage_4_uses_the_exact_terminal_vocabulary() -> None:
    proposal = build_calculation()["program_proposal"]
    stage = proposal["semantic_stages_proposed"][3]
    assert proposal["program_terminal_outcomes"] == PROGRAM_TERMINAL_OUTCOMES
    assert stage["canonical_scope"]["terminal_outcome_vocabulary"] == (
        PROGRAM_TERMINAL_OUTCOMES
    )


def test_preparation_preserves_closed_programs_and_discloses_debt() -> None:
    calculation = build_calculation()
    assert all(calculation["evidence_checks"].values())
    assert calculation["claim_boundary"]["closed_program_reopened"] is False
    assert calculation["validation_debt_boundary"][
        "exhaustive_python_passage_established"
    ] is False
    assert calculation["automatic_successor_selected"] is False


def test_independent_review_accepts_only_the_proposal() -> None:
    review = result_review.build_review()
    assert review["accepted"] is True
    assert review["failed_checks"] == []
    assert all(review["checks"].values())
    assert review["program_proposal_status"] == (
        "PREPARED_NOT_INSTALLED_AUTHORIZED_OR_OPEN"
    )
    assert review["representation_selected"] is False
    assert review["action_selected"] is False
    assert review["automatic_successor_selected"] is False


@pytest.mark.parametrize(
    ("field", "value"),
    [
        ("installed", True),
        ("authorized", True),
        ("open_event_created", True),
    ],
)
def test_review_rejects_false_lifecycle_state(
    monkeypatch: pytest.MonkeyPatch,
    field: str,
    value: bool,
) -> None:
    calculation = deepcopy(build_calculation())
    calculation["program_proposal"][field] = value
    original_read_json = result_review.read_json

    def read_json_with_mutation(path):
        if path == result_review.CALCULATION_PATH:
            return calculation
        return original_read_json(path)

    monkeypatch.setattr(result_review, "read_json", read_json_with_mutation)
    with pytest.raises(
        QuadraticHyperbolicityError,
        match="proposal_is_not_installed_authorized_or_open",
    ):
        result_review.build_review()


def test_review_rejects_scope_hash_mutation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    calculation = deepcopy(build_calculation())
    calculation["program_proposal"]["semantic_stages_proposed"][0][
        "canonical_scope_hash"
    ] = "0" * 64
    original_read_json = result_review.read_json

    def read_json_with_mutation(path):
        if path == result_review.CALCULATION_PATH:
            return calculation
        return original_read_json(path)

    monkeypatch.setattr(result_review, "read_json", read_json_with_mutation)
    with pytest.raises(
        QuadraticHyperbolicityError,
        match="canonical_scope_hashes_recompute",
    ):
        result_review.build_review()


def test_review_rejects_a_selected_representation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    calculation = deepcopy(build_calculation())
    calculation["claim_boundary"]["coherence_representation_selected"] = True
    original_read_json = result_review.read_json

    def read_json_with_mutation(path):
        if path == result_review.CALCULATION_PATH:
            return calculation
        return original_read_json(path)

    monkeypatch.setattr(result_review, "read_json", read_json_with_mutation)
    with pytest.raises(
        QuadraticHyperbolicityError,
        match="no_representation_or_physics_was_selected",
    ):
        result_review.build_review()
