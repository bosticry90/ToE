from __future__ import annotations

from formal.python.tools.toe_targeted_ccft_recovery_handoff_stage_closeout import review_result
from formal.python.tools.toe_targeted_ccft_recovery_handoff_stage_execution import (
    CONSTRUCTION_PREPARATION_TARGET,
    MANDATORY_EXIT_TARGET,
    OUTCOME,
    build_result,
)


def result() -> dict:
    return build_result(captured_at_utc="2026-08-02T03:00:00Z")


def test_positive_outcome_follows_from_four_exact_contracts() -> None:
    value = result()
    assert value["program_scientific_outcome"] == OUTCOME
    assert value["program_outcome_selection_basis"] == {
        "positive_threshold": 1,
        "exact_contracts_recovered": 4,
        "threshold_satisfied": True,
        "alternative_outcome_selected": False,
    }


def test_all_eighteen_contract_statuses_are_preserved() -> None:
    summary = result()["recovered_partial_conflicting_and_absent_contract_summary"]
    assert summary["checklist_total"] == 18
    assert sum(value for key, value in summary.items() if key in {
        "recovered_exact", "conflict_preserved", "exact_application_blocked_by_conflict",
        "exact_configuration_bound", "exact_incomplete_parameter_range",
        "only_nonexact_evidence", "no_relevant_evidence",
    }) == 18


def test_historical_recovery_ends_without_branch_selection() -> None:
    value = result()
    assert value["historical_recovery_boundary"]["ccft_v0_historical_recovery_complete"] is True
    assert value["historical_recovery_boundary"]["additional_archive_or_overflow_search_authorized"] is False
    assert value["branch_readiness_snapshot"]["branch_selected"] == "NONE"


def test_mandatory_exit_precedes_unauthorized_construction_handoff() -> None:
    value = result()
    assert value["immediate_successor"]["target"] == MANDATORY_EXIT_TARGET
    handoff = value["required_nonautomatic_construction_preparation_handoff"]
    assert handoff["target"] == CONSTRUCTION_PREPARATION_TARGET
    assert handoff["preparation_authorized"] is False
    assert handoff["mandatory_exit_must_complete_first"] is True


def test_independent_review_accepts_without_model_or_theorem_authority() -> None:
    value = result()
    review = review_result(value, "2026-08-02T03:01:00Z")
    assert review["accepted"] is True
    assert all(review["checks"].values())
    assert review["scientific_interpretation"]["ccft_v0_model_established"] is False
    assert review["scientific_interpretation"]["theorem_discovery_authorized"] is False
