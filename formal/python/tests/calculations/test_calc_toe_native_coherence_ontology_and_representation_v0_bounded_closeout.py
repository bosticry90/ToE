from __future__ import annotations

from formal.python.toe.calculations import (
    calc_toe_native_coherence_ontology_and_representation_v0_bounded_closeout
    as calculation,
)
from formal.python.tools import (
    toe_native_coherence_ontology_and_representation_v0_bounded_closeout_review
    as review,
)
from formal.python.tools.qft_gr_quadratic_hyperbolicity_common import (
    canonical_json_bytes,
)


def test_closeout_and_review_are_deterministic() -> None:
    assert calculation.OUTPUT_PATH.read_bytes() == canonical_json_bytes(
        calculation.build_calculation()
    )
    assert review.OUTPUT_PATH.read_bytes() == canonical_json_bytes(
        review.build_review()
    )


def test_program_is_terminal_without_representation_or_calculation() -> None:
    payload = calculation.build_calculation()
    assert (
        payload["terminal_outcome"]
        == "EXISTING_COHERENCE_CLAIMS_INSUFFICIENTLY_DEFINED"
    )
    assert payload["program_closeout"]["attempted_stage_count"] == 2
    assert payload["program_closeout"]["repair_attempt_count"] == 0
    assert payload["program_closeout"]["unattempted_stage_ids"] == [
        "COHERENCE_REPRESENTATION_COMPARISON",
        "COHERENCE_OPERATIONAL_REPRESENTABILITY_DECISION",
        "MINIMAL_NATIVE_FIELD_HANDOFF",
    ]
    assert (
        payload["scientific_results"]["representation_status"]
        == "NOT_REACHED"
    )
    assert (
        payload["scientific_results"]["calculation_status"] == "NOT_REACHED"
    )
    assert payload["automatic_successor_selected"] is False
    assert payload["terminal_boundaries"][
        "future_coherence_route_requires_new_program_and_new_substantive_input"
    ]
