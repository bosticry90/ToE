from __future__ import annotations

from formal.python.tools import (
    repository_clean_baseline_validation_stabilization_authorization as auth,
)


def test_phase_a_blocked_result_is_preserved_not_reclassified() -> None:
    result = auth.build_preservation()
    assert result["phase_a_outcome"] == "EVIDENCE_BLOCKED_BASELINE_VALIDATION"
    assert result["accepted_for_phase_b"] is False
    assert result["external_custody"]["byte_archive_remains_outside_git"] is True
    assert result["committed_source_reproducibility"] == "FAILED_INCOMPLETE"


def test_selector_has_only_the_prescribed_two_choices() -> None:
    preservation = auth.build_preservation()
    selector = auth.build_selector(preservation)
    assert selector["substantive_choices"] == [
        auth.SELECTED_ROUTE,
        auth.DEFERRED_ROUTE,
    ]
    assert selector["selected_route"] == auth.SELECTED_ROUTE
    assert selector["selected_maintenance_target"] == auth.STABILIZATION_TARGET


def test_packet_authorizes_one_bounded_cycle_and_requires_clean_diff() -> None:
    preservation = auth.build_preservation()
    packet = auth.build_packet(auth.build_selector(preservation))
    assert packet["cycle_limit"]["implementation_cycles"] == 1
    assert packet["cycle_limit"]["fresh_clone_validation_cycles"] == 1
    assert packet["cycle_limit"]["failed_result_auto_repair_authorized"] is False
    assert packet["source_cleanliness_invariant"]["after_every_validation_phase"] == (
        "TRACKED_SOURCE_DIFF_EMPTY"
    )


def test_packet_preserves_scientific_freeze_and_v2_content() -> None:
    preservation = auth.build_preservation()
    selector = auth.build_selector(preservation)
    packet = auth.build_packet(selector)
    scientific = packet["scientific_authority"]
    assert scientific["posture"] == "B-BLOCKED"
    assert scientific["resolved_unit_seam_rows"] == 0
    assert scientific["blocked_unit_seam_rows"] == 12
    assert scientific["blocked_seams"] == 5
    assert scientific["phase_2_authorized"] is False
    assert packet["v2_boundary"]["scientific_content_may_change"] is False
    assert "NO_SCIENTIFIC_REGISTRY_ROTATION" in packet["prohibited_work"]


def test_independent_review_accepts_exact_bounded_authorization() -> None:
    result = auth.build_review()
    assert result["accepted"] is True
    assert result["verdict"] == "ACCEPT"
    assert all(result["checks"].values())


def test_maintenance_authority_does_not_authorize_phase_b_c_or_science() -> None:
    preservation = auth.build_preservation()
    packet = auth.build_packet(auth.build_selector(preservation))
    authority = auth.build_maintenance_authority(packet)
    boundary = authority["boundary"]
    assert boundary["baseline_stabilization_authorized"] is True
    assert boundary["scientific_execution_authorized"] is False
    assert boundary["phase_b_authorized"] is False
    assert boundary["phase_c_authorized"] is False
    assert boundary["v2_enrollment_authorized"] is False
