from __future__ import annotations

from formal.python.tools import (
    repository_authority_custody_and_reproducibility_recovery_authorization as auth,
)
from formal.python.tools import (
    repository_authority_custody_and_reproducibility_recovery_authorization_review as review,
)


def test_recovery_authority_preserves_scientific_posture() -> None:
    selector = auth.build_selector()
    packet = auth.build_packet(selector)
    scientific = selector["scientific_authority"]
    assert scientific["posture"] == "B-BLOCKED"
    assert scientific["resolved_unit_seam_rows"] == 0
    assert scientific["blocked_unit_seam_rows"] == 12
    assert scientific["blocked_seams"] == 5
    assert scientific["phase_2_authorized"] is False
    assert packet["frozen_scientific_authority"] == scientific
    assert "NO_V2_REGENERATION" in packet["prohibitions"]


def test_recovery_authority_has_hard_phase_gates() -> None:
    packet = auth.build_packet(auth.build_selector())
    assert [row["phase"] for row in packet["phases"]] == ["A", "B", "C"]
    assert packet["phases"][0]["may_modify_audited_worktree"] is False
    assert packet["phases"][1]["may_start_before_phase_a_acceptance"] is False
    assert packet["phases"][2]["must_run_in_fresh_clone"] is True
    assert packet["phases"][2]["scientific_resumption_authorized_by_completion"] is False


def test_independent_review_accepts_the_frozen_authorization() -> None:
    result = review.build_review()
    assert result["accepted"] is True
    assert result["verdict"] == "ACCEPT"
    assert all(result["checks"].values())


def test_activated_maintenance_authority_does_not_rotate_science() -> None:
    packet = auth.build_packet(auth.build_selector())
    authority = auth.build_maintenance_authority(packet)
    assert authority["current_maintenance_target"] == auth.RECOVERY_TARGET
    assert authority["previous_maintenance_lane_disposition"] == "DEFERRED_NOT_RETIRED"
    assert authority["boundary"]["scientific_target_rotated"] is False
    assert authority["boundary"]["scientific_execution_authorized"] is False
    assert authority["boundary"]["phase_b_authorized"] is False
