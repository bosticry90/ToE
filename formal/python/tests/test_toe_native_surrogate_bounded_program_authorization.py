from __future__ import annotations

from formal.python.tools import (
    toe_native_surrogate_bounded_program_authorization as authorization,
)
from formal.python.tools import (
    toe_native_surrogate_bounded_program_authorization_review as review,
)
from formal.python.tools.qft_gr_quadratic_hyperbolicity_common import (
    canonical_json_bytes,
)


def test_authorization_and_review_are_deterministic() -> None:
    assert authorization.OUTPUT_PATH.read_bytes() == canonical_json_bytes(
        authorization.build_authorization()
    )
    assert review.OUTPUT_PATH.read_bytes() == canonical_json_bytes(
        review.build_review()
    )


def test_native_stage_one_remains_unopened() -> None:
    payload = authorization.build_authorization()
    assert payload["program_state_after_authorization"] == "UNOPENED"
    assert payload["scientific_stage_attempted"] is False
    assert payload["scientific_output_created"] is False
    assert payload["selected_next_target"] == (
        "select_toe_native_coherence_representation_v0"
    )
