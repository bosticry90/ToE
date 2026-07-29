from __future__ import annotations

from formal.python.tools.toe_native_hypothesis_frontier_selection_authority import (
    build_authority,
)
from formal.python.tools.toe_native_hypothesis_frontier_selection_authority_review import (
    build_review,
)


def test_authority_preserves_closed_programs_and_selects_one_decision() -> None:
    authority = build_authority()
    assert authority["authorized_target"] == (
        "select_next_native_toe_hypothesis_for_bounded_adjudication_v0"
    )
    assert authority["selector_contract"]["decision_count"] == 1
    assert authority["selector_contract"]["repair_attempt_count"] == 0
    assert authority["program_installation_authorized_here"] is False
    assert authority["scientific_calculation_authorized_here"] is False
    assert authority["closed_predecessors"]["quadratic"]["state"] == "CLOSED"
    assert authority["closed_predecessors"]["native_surrogate"]["state"] == "CLOSED"


def test_authority_review_is_independent_and_accepts_narrow_scope() -> None:
    review = build_review()
    assert review["accepted"] is True
    assert review["failed_checks"] == []
    assert all(review["checks"].values())
    assert review["closed_programs_reopened"] is False
    assert review["new_program_installed"] is False
