from __future__ import annotations

from formal.python.toe.calculations import (
    calc_toe_native_surrogate_v0_bounded_closeout as calculation,
)
from formal.python.tools import (
    toe_native_surrogate_v0_bounded_closeout_review as review,
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


def test_v0_is_terminal_without_action_or_automatic_v1() -> None:
    payload = calculation.build_calculation()
    assert payload["terminal_outcome"] == "NO_UNIQUE_TOE_DISCRIMINATOR_V0"
    assert payload["program_closeout"]["attempted_stage_count"] == 1
    assert payload["program_closeout"]["repair_attempt_count"] == 0
    assert payload["terminal_boundaries"]["portal_action_selected"] is False
    assert payload["terminal_boundaries"][
        "new_representation_or_action_requires_separate_v1"
    ] is True
