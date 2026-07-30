from formal.python.toe.calculations.calc_toe_native_coherence_authorized_evidence_scope_qualification_v0 import (
    build,
)
from formal.python.tools.toe_native_coherence_authorized_evidence_scope_qualification_result_review import (
    build as build_review,
)


def test_scope_qualification_is_narrow_and_non_reopening() -> None:
    result = build()
    scope = result["scope_qualification"]
    closed = result["preserved_closed_result"]
    assert (
        result["source_scope_facts"]["stage_1_distinct_authorized_source_count"]
        == 13
    )
    assert scope["repository_wide_evidence_sufficiency"] == "NOT_TESTED"
    assert scope["archive_wide_ccft_evidence_census"] == "NOT_PERFORMED"
    assert scope["every_repository_coherence_claim_exhausted"] is False
    assert closed["program_reopened"] is False
    assert closed["terminal_outcome_changed"] is False


def test_scope_qualification_preserves_negative_boundaries() -> None:
    result = build()
    not_established = result["scientific_boundary"]["not_established"]
    assert "the archive contains an operational definition" in not_established
    assert "CCFT is false" in not_established
    assert result["custody_controls"]["archive_material_promoted"] is False


def test_scope_qualification_review_is_independently_accepted() -> None:
    review = build_review()
    assert review["accepted"] is True
    assert not review["failed_checks"]
    assert all(review["checks"].values())
    assert review["scientific_result_changed"] is False
