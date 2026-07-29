from __future__ import annotations

from formal.python.toe.calculations import (
    calc_qft_gr_quadratic_exact_generic_frozen_companion_operator_v1 as calculation,
)
from formal.python.tools import (
    qft_gr_quadratic_exact_generic_frozen_companion_operator_v1_result_review as review,
)
from formal.python.tools.qft_gr_quadratic_hyperbolicity_common import (
    canonical_json_bytes,
    read_json,
)


def test_calculation_and_review_artifacts_are_current() -> None:
    assert calculation.OUTPUT_PATH.read_bytes() == canonical_json_bytes(
        calculation.build_calculation()
    )
    assert review.OUTPUT_PATH.read_bytes() == canonical_json_bytes(
        review.build_review()
    )


def test_generic_companion_fails_closed_on_wave_slot_ambiguity() -> None:
    artifact = read_json(calculation.OUTPUT_PATH)
    audit = artifact["generic_companion_closure_audit"]
    assert audit["answer"] is False
    assert audit["terminal_outcome"] == "GENERIC_BACKGROUND_OPERATOR_NOT_CLOSED"
    assert audit["metric_wave_slot_audit"][
        "uses_dk_as_second_derivative_proxy"
    ]
    assert not audit["metric_wave_slot_audit"][
        "contains_independent_dh_or_d2h_slots"
    ]
    assert audit["scalar_wave_slot_audit"][
        "uses_du_as_second_derivative_proxy"
    ]
    assert not audit["scalar_wave_slot_audit"][
        "contains_independent_dq_or_d2q_slots"
    ]


def test_all_trace_charts_remain_unclosed_in_nine_variables() -> None:
    charts = read_json(calculation.OUTPUT_PATH)[
        "generic_companion_closure_audit"
    ]["tracefree_chart_closure"]["charts"]
    assert len(charts) == 10
    assert all(row["dependent_tangent_leaves_retained"] for row in charts)
    assert all(
        row["closed_in_its_nine_independent_spin_variables"] is False
        for row in charts
    )


def test_Minkowski_control_is_preserved_but_not_generalized() -> None:
    artifact = read_json(calculation.OUTPUT_PATH)
    regression = artifact["Minkowski_regression"]
    assert regression["matrix_shape"] == [128, 128]
    assert regression["nonzero_entry_count"] == 224
    assert regression["does_not_supply_generic_off_constraint_closure"] is True
    assert artifact["claim_boundary"][
        "exact_generic_frozen_companion_operator_derived"
    ] is False


def test_zero_repair_rule_selects_mandatory_role_gate() -> None:
    artifact = read_json(calculation.OUTPUT_PATH)
    assert artifact["terminal_result"] == "BLOCKED"
    assert artifact["mandatory_exit_target"] == review.MANDATORY_EXIT_TARGET
    assert artifact["prohibitions_respected"]["repair_target_created"] is False
    reviewed = read_json(review.OUTPUT_PATH)
    assert reviewed["accepted"] is True
    assert reviewed["terminal_result"] == "BLOCKED"
    assert reviewed["authority_rotation"]["quadratic_role_gate_mandatory"] is True
    assert reviewed["authority_rotation"]["quadratic_repair_authorized"] is False
