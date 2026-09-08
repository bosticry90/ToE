from __future__ import annotations

from formal.python.tools import (
    qft_gr_quadratic_hyperbolicity_admissible_source_and_frozen_theory_packet
    as packet,
)
from formal.python.tools import (
    qft_gr_quadratic_hyperbolicity_admissible_source_and_frozen_theory_packet_result_review
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


def test_review_authorizes_only_phase_a() -> None:
    artifact = read_json(review.OUTPUT_PATH)
    assert artifact["accepted"] is True
    assert artifact["selected_next_target"] == review.EXPECTED_NEXT_TARGET
    rotation = artifact["authority_rotation"]
    assert rotation["physical_principal_block_execution_authorized"] is True
    assert rotation["auxiliary_harmonic_formulation_execution_authorized"] is False
    assert rotation["adapted_norm_estimate_execution_authorized"] is False
    assert rotation["source_extension_authorized"] is False
    assert rotation["preserved_descendant_adoption_authorized"] is False
    assert rotation["yukawa_work_authorized"] is False


def test_preserved_input_is_byte_bound_but_not_adopted() -> None:
    artifact = read_json(packet.OUTPUT_PATH)
    candidate = artifact["preserved_candidate_input"]
    assert candidate["classification"] == "PRESERVED_NOT_ADOPTED"
    assert candidate["git_blob_oid"] == packet.PRESERVED_BLOB_OID
    assert candidate["sha256"] == packet.PRESERVED_BLOB_SHA256
    assert candidate["scientific_authority_conferred"] is False


def test_frozen_domains_separate_full_generic_and_spin2_minimum() -> None:
    artifact = read_json(packet.OUTPUT_PATH)
    domains = artifact["frozen_theory"]["coefficient_domains"]
    assert domains["G_principal"] == ["beta != 0", "3 alpha + beta != 0"]
    assert domains["G_Stelle"][-1] == "c_R != 0"
    assert domains["spin2_obstruction_minimal_domain"] == ["beta != 0"]
    assert artifact["source_scope"]["phase_a"] == "VACUUM"


def test_continuous_dependence_comparator_is_not_promoted_to_theorem() -> None:
    artifact = read_json(packet.OUTPUT_PATH)
    source = next(
        row
        for row in artifact["admissible_primary_sources"]
        if row["source_id"] == "ARXIV_1811_07869_V4"
    )
    assert "identified there as a conjecture" in source["claim_boundary"]
    assert all(review.build_review()["checks"].values())
