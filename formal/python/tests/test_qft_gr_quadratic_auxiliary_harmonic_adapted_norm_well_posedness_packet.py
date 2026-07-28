from __future__ import annotations

from formal.python.tools import (
    qft_gr_quadratic_auxiliary_harmonic_adapted_norm_well_posedness_packet
    as packet,
)
from formal.python.tools import (
    qft_gr_quadratic_auxiliary_harmonic_adapted_norm_well_posedness_packet_result_review
    as review,
)
from formal.python.tools.qft_gr_quadratic_hyperbolicity_common import (
    canonical_json_bytes,
    read_json,
)


def test_packet_and_review_artifacts_are_current() -> None:
    assert packet.OUTPUT_PATH.read_bytes() == canonical_json_bytes(
        packet.build_packet()
    )
    assert review.OUTPUT_PATH.read_bytes() == canonical_json_bytes(
        review.build_review()
    )


def test_reduced_system_is_triangular_at_principal_order() -> None:
    artifact = read_json(packet.OUTPUT_PATH)
    system = artifact["candidate_reduced_system"]
    assert system["triangular_principal_order"] == [
        "R wave equation",
        "S_mn wave equation forced by the trace-free Hessian of R",
        "g_mn generalized-harmonic wave equation forced by R and S_mn",
    ]
    assert "2(3 alpha + beta)" in system["scalar_trace_equation"]
    assert "(2 alpha + beta)" in system[
        "trace_free_ricci_principal_equation"
    ]


def test_candidate_loss_and_regularities_are_not_promoted_to_theorem() -> None:
    artifact = read_json(packet.OUTPUT_PATH)
    adapted = artifact["adapted_norm_candidate"]
    assert adapted["candidate_pure_metric_derivative_loss"] == 1
    assert adapted["minimum_loss_established"] is False
    assert adapted["minimum_regularity_established"] is False
    assert adapted["nonlinear_closure_established"] is False
    assert adapted["continuous_dependence_established"] is False


def test_review_authorizes_only_exact_reduced_system_derivation() -> None:
    artifact = read_json(review.OUTPUT_PATH)
    assert artifact["accepted"] is True
    assert artifact["selected_next_target"] == review.EXPECTED_NEXT_TARGET
    rotation = artifact["authority_rotation"]
    assert rotation["auxiliary_harmonic_reduced_system_derivation_authorized"] is True
    assert rotation["adapted_norm_theorem_execution_authorized"] is False
    assert rotation["source_extension_authorized"] is False
    assert rotation["preserved_descendant_adoption_authorized"] is False
    assert rotation["yukawa_work_authorized"] is False
    assert all(review.build_review()["checks"].values())
