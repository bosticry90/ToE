from __future__ import annotations

from formal.python.toe.calculations import (
    calc_qft_gr_quadratic_toe_role_after_generic_frozen_result as calculation,
)
from formal.python.tools import (
    qft_gr_quadratic_toe_role_after_generic_frozen_result_review as review,
)
from formal.python.tools.qft_gr_quadratic_hyperbolicity_common import (
    canonical_json_bytes,
    read_json,
)


def test_role_result_and_review_are_current() -> None:
    assert calculation.OUTPUT_PATH.read_bytes() == canonical_json_bytes(
        calculation.build_calculation()
    )
    assert review.OUTPUT_PATH.read_bytes() == canonical_json_bytes(
        review.build_review()
    )


def test_role_and_mathematical_result_are_independent() -> None:
    artifact = read_json(calculation.OUTPUT_PATH)
    assert artifact["role_decision"]["toe_role"] == "REFERENCE_CONTROL_ONLY"
    assert artifact["role_decision"]["control_result"] == (
        "UNRESOLVED_AFTER_BOUNDED_ATTEMPT"
    )
    assert artifact["claim_boundary"]["quadratic_gravity_native_toe_sector"] is False
    assert artifact["claim_boundary"]["generic_finite_loss_refuted"] is False


def test_zero_repair_closeout_stops_after_three_attempts() -> None:
    closeout = read_json(calculation.OUTPUT_PATH)["bounded_program_closeout"]
    assert closeout["attempted_stage_count"] == 3
    assert closeout["repair_attempt_count"] == 0
    assert closeout["unattempted_stage_ids"] == [
        "CONSTRAINT_TANGENT_AND_PHYSICAL_QUOTIENT",
        "SUBPRINCIPAL_PROPAGATOR_GROWTH",
    ]


def test_native_program_requires_separate_authority() -> None:
    artifact = read_json(review.OUTPUT_PATH)
    assert artifact["accepted"] is True
    assert artifact["quadratic_program_terminal"] is True
    assert artifact["authority_rotation"][
        "further_quadratic_science_authorized"
    ] is False
    assert artifact["authority_rotation"]["native_program_installed"] is False
    assert artifact["selected_next_target"] == (
        "authorize_toe_native_surrogate_v0_bounded_program"
    )
