from __future__ import annotations

from formal.python.toe.calculations import (
    calc_toe_native_coherence_representation_v0 as calculation,
)
from formal.python.tools import (
    toe_native_coherence_representation_result_review as review,
)
from formal.python.tools.qft_gr_quadratic_hyperbolicity_common import (
    canonical_json_bytes,
)


def test_result_and_review_are_deterministic() -> None:
    assert calculation.OUTPUT_PATH.read_bytes() == canonical_json_bytes(
        calculation.build_calculation()
    )
    assert review.OUTPUT_PATH.read_bytes() == canonical_json_bytes(
        review.build_review()
    )


def test_stage_fails_closed_without_manufacturing_a_scalar_map() -> None:
    payload = calculation.build_calculation()
    assert payload["terminal_result"] == "BLOCKED"
    assert payload["terminal_outcome"] == (
        "BLOCKED_CCFT_TO_CONTINUUM_MAP_UNRESOLVED"
    )
    assert payload["claim_boundary"]["real_scalar_surrogate_accepted"] is False
    assert payload["claim_boundary"]["stage_2_authorized"] is False
    assert payload["v0_discriminator_result"] == (
        "NO_UNIQUE_TOE_DISCRIMINATOR_V0"
    )


def test_both_independent_symmetry_gates_block() -> None:
    payload = calculation.build_calculation()
    assert payload["phi_semantics"]["phi_symmetry_status"] == (
        "BLOCKED_TEST_MATTER_SYMMETRY_UNJUSTIFIED"
    )
    assert payload["chi_semantics"]["chi_symmetry_status"] == (
        "BLOCKED_COHERENCE_Z2_UNJUSTIFIED"
    )
