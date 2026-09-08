from __future__ import annotations

from formal.python.tools import (
    qft_gr_quadratic_hyperbolicity_bounded_reconciliation_selection as selection,
)
from formal.python.tools import (
    qft_gr_quadratic_hyperbolicity_bounded_reconciliation_selection_result_review
    as review,
)
from formal.python.tools.qft_gr_quadratic_hyperbolicity_common import (
    canonical_json_bytes,
    read_json,
)


def test_selection_and_review_artifacts_are_current() -> None:
    assert selection.OUTPUT_PATH.read_bytes() == canonical_json_bytes(
        selection.build_selection()
    )
    assert review.OUTPUT_PATH.read_bytes() == canonical_json_bytes(
        review.build_review()
    )


def test_bounded_reconciliation_is_selected_without_adoption() -> None:
    report = read_json(review.OUTPUT_PATH)
    assert report["accepted"] is True
    assert report["selected_route"] == "BOUNDED_RECONCILIATION_OR_REPLAY"
    assert report["selected_next_target"] == selection.SELECTED_NEXT_TARGET
    assert report["authority_rotation"][
        "preserved_descendant_adoption_authorized"
    ] is False
    assert report["authority_rotation"]["yukawa_work_authorized"] is False


def test_selection_defines_a_fresh_ordered_authority_path() -> None:
    artifact = read_json(selection.OUTPUT_PATH)
    assert artifact["authority_before_selection"]["scientific_target"] == (
        selection.FROZEN_JULY_12_TARGET
    )
    assert artifact["fresh_authority_path"] == [
        selection.SELECTED_NEXT_TARGET,
        "review_qft_gr_quadratic_hyperbolicity_admissible_source_and_frozen_theory_packet_v0_result",
        "derive_qft_gr_quadratic_physical_spin2_principal_block_v0",
        "review_qft_gr_quadratic_physical_spin2_principal_block_v0_result",
        "prepare_qft_gr_quadratic_auxiliary_harmonic_adapted_norm_well_posedness_packet_v0",
    ]
    assert artifact["preserved_observations"]["decision_bearing_use_authorized"] is False
    assert artifact["preserved_observations"]["validation_use_authorized"] is False


def test_review_recomputes_every_gate_independently() -> None:
    report = review.build_review()
    assert report["checks"]
    assert all(report["checks"].values())
    assert report["failed_checks"] == []
    assert report["reviewer_independence"]["imports_selection_generator"] is False
