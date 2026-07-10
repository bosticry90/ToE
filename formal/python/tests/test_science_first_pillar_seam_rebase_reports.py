from __future__ import annotations

import copy

import pytest

from formal.python.tests.strict_physics_state_helpers import (
    active_workstream,
    loop_registry,
)
from formal.python.tools.science_first_pillar_seam_rebase_reports import (
    ALLOWED_READINESS_STATUSES,
    FIRST_SPRINT_GUARDRAIL_TARGET,
    PILLAR_ENTRY_CRITERIA,
    PILLAR_MATURITY_CRITERIA,
    PREPARE_OUTCOME,
    REVIEW_OUTCOME,
    REVIEW_TARGET,
    SEAM_CRITERIA,
    SPRINT_INTERFACE_FIELDS,
    build_prepare_report,
    build_readiness_artifact,
    build_review_report,
    canonical_json_bytes,
    validate_readiness_artifact,
)


def test_readiness_artifact_is_compact_complete_and_deterministic() -> None:
    readiness = build_readiness_artifact(reviewed=False)
    validate_readiness_artifact(readiness)
    summary = readiness["summary_counts"]
    assert summary["pillar_count"] == 7
    assert summary["pillar_criterion_count"] == 10
    assert summary["pillar_row_count"] == 70
    assert summary["pillar_entry_row_count"] == 35
    assert summary["pillar_maturity_row_count"] == 35
    assert summary["seam_count"] == 5
    assert summary["seam_criterion_count"] == 8
    assert summary["seam_row_count"] == 40
    assert sum(summary["pillar_status_counts"].values()) == 70
    assert sum(summary["seam_status_counts"].values()) == 40
    assert set(summary["pillar_status_counts"]) == set(ALLOWED_READINESS_STATUSES)
    assert canonical_json_bytes(readiness) == canonical_json_bytes(
        build_readiness_artifact(reviewed=False)
    )


def test_readiness_separates_entry_maturity_and_level_five_criteria() -> None:
    readiness = build_readiness_artifact(reviewed=False)
    assert [row["criterion_id"] for row in readiness["pillar_entry_gating_criteria"]] == [
        row[0] for row in PILLAR_ENTRY_CRITERIA
    ]
    assert [row["criterion_id"] for row in readiness["pillar_maturity_criteria"]] == [
        row[0] for row in PILLAR_MATURITY_CRITERIA
    ]
    assert [
        row["criterion_id"]
        for row in readiness["seam_level_5_admissibility_criteria"]
    ] == [row[0] for row in SEAM_CRITERIA]
    assert readiness["summary_counts"]["exploratory_seam_entry_eligible_count"] == 0
    assert readiness["summary_counts"]["level_5_seam_admissible_count"] == 0


def test_readiness_declares_noncompeting_authority_roles() -> None:
    roles = build_readiness_artifact(reviewed=False)["authority_roles"]
    assert roles["formal/docs/paper/PILLAR_STATUS_MATRIX_v1.json"] == (
        "legacy operational/governance authority"
    )
    assert roles[
        "formal/docs/release/SCIENCE_FIRST_PILLAR_SEAM_READINESS_v0.json"
    ] == "current science-sprint readiness authority"
    assert roles["formal/docs/paper/FULL_PILLAR_TARGET_MAP_REBASE_v0.md"] == (
        "evidence inventory and input surface"
    )


def test_not_applicable_is_rejected_for_mandatory_entry_gate() -> None:
    readiness = build_readiness_artifact(reviewed=False)
    mutated = copy.deepcopy(readiness)
    row = mutated["pillar_readiness_rows"][0]
    row.update(
        {
            "status": "not_applicable",
            "justification": "synthetic test",
            "reviewed_by": "test",
        }
    )
    mutated["summary_counts"]["pillar_status_counts"]["met"] -= 1
    mutated["summary_counts"]["pillar_status_counts"]["not_applicable"] += 1
    with pytest.raises(ValueError, match="forbidden"):
        validate_readiness_artifact(mutated)


def test_not_applicable_requires_justification_reviewer_and_evidence() -> None:
    readiness = build_readiness_artifact(reviewed=False)
    mutated = copy.deepcopy(readiness)
    row = mutated["pillar_readiness_rows"][5]
    previous_status = row["status"]
    row["status"] = "not_applicable"
    mutated["summary_counts"]["pillar_status_counts"][previous_status] -= 1
    mutated["summary_counts"]["pillar_status_counts"]["not_applicable"] += 1
    with pytest.raises(ValueError, match="justification"):
        validate_readiness_artifact(mutated)


def test_sprint_interface_and_ccft_resume_gates_are_explicit() -> None:
    readiness = build_readiness_artifact(reviewed=False)
    assert readiness["required_sprint_interface"] == list(SPRINT_INTERFACE_FIELDS)
    assert len(readiness["ccft_resume_gates"]) == 8
    assert all(row["status"] != "met" for row in readiness["ccft_resume_gates"])
    assert readiness["ccft_lane_status"] == "paused_upstream_prerequisites"
    assert readiness["master_action_policy"]["canonicalization_allowed"] is False
    assert readiness["master_action_policy"]["promotion_allowed"] is False


def test_prepare_report_rotates_only_to_separate_review() -> None:
    readiness = build_readiness_artifact(reviewed=False)
    report = build_prepare_report(readiness)
    assert report["packet_result"] == PREPARE_OUTCOME
    assert report["selected_next_target"] == REVIEW_TARGET
    assert report["readiness_rows_embedded_in_loop_registry"] is False
    assert report["claim_boundary"]["pillar_completion_claimed"] is False
    assert report["claim_boundary"]["seam_admissibility_claimed"] is False


def test_review_report_selects_flat_limit_pretest_only() -> None:
    readiness = build_readiness_artifact(reviewed=True)
    report = build_review_report(readiness)
    assert report["packet_result"] == REVIEW_OUTCOME
    assert report["selected_next_target"] == FIRST_SPRINT_GUARDRAIL_TARGET
    assert report["first_science_sprint"]["claim_ceiling"] == (
        "Level 3 toy-model demonstration"
    )
    assert report["first_science_sprint"][
        "not_a_qft_gr_seam_admissibility_claim"
    ] is True


def test_loop_registry_contains_only_compact_readiness_pointers() -> None:
    registry = loop_registry()
    active = active_workstream(registry)
    assert registry["science_first_readiness_artifact_id"] == (
        "SCIENCE_FIRST_PILLAR_SEAM_READINESS_v0"
    )
    assert len(registry["science_first_readiness_artifact_sha256"]) == 64
    assert registry["science_first_readiness_summary_counts"]["pillar_row_count"] == 70
    assert registry["science_first_readiness_summary_counts"]["seam_row_count"] == 40
    assert registry["science_first_readiness_rows_embedded_in_registry"] == "no"
    assert registry["science_first_readiness_authority_status"] == (
        "accepted_current_science_sprint_readiness_authority"
    )
    assert "pillar_readiness_rows" not in registry
    assert "seam_readiness_rows" not in registry
    assert "pillar_readiness_rows" not in active
    assert "seam_readiness_rows" not in active
