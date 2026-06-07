from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
)


REPO_ROOT = find_repo_root(Path(__file__))
REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "StatusSurfaceCanonicalizationEnforcementPacketResultReview.lean"
)
ENFORCEMENT_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "StatusSurfaceCanonicalizationEnforcementPacket.lean"
)
AGGREGATE_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal.lean"
REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "STATUS_SURFACE_CANONICALIZATION_ENFORCEMENT_PACKET_RESULT_REVIEW_20260505_v0.json"
)
ENFORCEMENT_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "STATUS_SURFACE_CANONICALIZATION_ENFORCEMENT_PACKET_20260505_v0.json"
)
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LOOP_CONTROL_REGISTRY_v0.json"
CURRENT_SURFACES_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "CURRENT_AUTHORITATIVE_SURFACES_v0.md"
)
SEAM_REGISTRY_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MASTER_ACTION_SEAM_CONSTRAINT_REGISTRY_v0.md"
)
SEAM_INVENTORY_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MASTER_ACTION_CLASS_B_SEAM_INVENTORY_v0.md"
)

REPORT_ID = "STATUS_SURFACE_CANONICALIZATION_ENFORCEMENT_PACKET_RESULT_REVIEW_20260505_v0"
SURFACE_ID = "status_surface_canonicalization_enforcement_packet_result_review_v0"
CONSUMED_TARGET = "review_status_surface_canonicalization_enforcement_packet_result"
CONSUMED_TOKEN = "STATUS_SURFACE_CANONICALIZATION_ENFORCEMENT_PACKET_PREPARED"
RESULT_TOKEN = "STATUS_SURFACE_CANONICALIZATION_ENFORCEMENT_PACKET_RESULT_REVIEW_CONSUMED"
NEXT_TARGET = "select_next_post_status_surface_enforcement_bounded_attack"
RECOMMENDED_SELECTOR_TARGET = "return_to_full_pillar_target_map_next_lane_selection"
MIRROR_KEY = "MASTER_ACTION_CURRENT_CITATION_TARGET_v0"
HISTORICAL_TOKEN = "review_read_only_validation_hygiene_result"
ACTIVE_MIRRORS = (SEAM_REGISTRY_PATH, SEAM_INVENTORY_PATH)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def _rel(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _active_mirror_values(text: str) -> list[str]:
    return re.findall(rf"{MIRROR_KEY}:\s*([A-Za-z0-9_]+)", text)


def test_result_review_surface_consumes_enforcement_packet_and_rotates_to_selector() -> None:
    text = _read(REVIEW_PATH)
    aggregate_text = _read(AGGREGATE_PATH)

    for token in {
        SURFACE_ID,
        CONSUMED_TARGET,
        CONSUMED_TOKEN,
        RESULT_TOKEN,
        NEXT_TARGET,
        RECOMMENDED_SELECTOR_TARGET,
        "StatusSurfaceCanonicalizationEnforcementPacketResultReviewStatus",
        "statusSurfaceCanonicalizationEnforcementPacketResultReviewStatusV0",
        "status_surface_canonicalization_enforcement_packet_result_review_consumes_target_v0",
        "status_surface_canonicalization_enforcement_packet_result_review_consumes_packet_token_v0",
        "status_surface_canonicalization_enforcement_packet_result_review_result_token_v0",
        "status_surface_canonicalization_enforcement_packet_result_review_next_target_v0",
        "status_surface_canonicalization_enforcement_packet_result_review_consumed_only_v0",
        "status_surface_canonicalization_enforcement_packet_result_review_selector_rotation_v0",
        "status_surface_canonicalization_enforcement_packet_result_review_selector_choice_not_made_v0",
    }:
        assert token in text

    assert (
        "import ToeFormal.Derivation.StatusSurfaceCanonicalizationEnforcementPacketResultReview"
        in aggregate_text
    )


def test_result_review_preserves_enforcement_boundaries() -> None:
    text = _read(REVIEW_PATH)

    for token in {
        "status_surface_canonicalization_enforcement_packet_result_review_mirror_parity_preserved_v0",
        "status_surface_canonicalization_enforcement_packet_result_review_loop_registry_authority_v0",
        "status_surface_canonicalization_enforcement_packet_result_review_seam_registry_mirror_v0",
        "status_surface_canonicalization_enforcement_packet_result_review_class_b_inventory_mirror_v0",
        "status_surface_canonicalization_enforcement_packet_result_review_historical_tokens_allowed_v0",
        "status_surface_canonicalization_enforcement_packet_result_review_source_mirror_classes_preserved_v0",
        "status_surface_canonicalization_enforcement_packet_result_review_generated_read_only_v0",
        "status_surface_canonicalization_enforcement_packet_result_review_read_only_preserved_v0",
        "status_surface_canonicalization_enforcement_packet_result_review_freeze_preserved_v0",
        "status_surface_canonicalization_enforcement_packet_result_review_no_rewrite_here_v0",
        "status_surface_canonicalization_enforcement_packet_result_review_no_generated_mutation_here_v0",
        "status_surface_canonicalization_enforcement_packet_result_review_no_history_edit_here_v0",
        "status_surface_canonicalization_enforcement_packet_result_review_no_snapshot_migration_here_v0",
        "broad_status_surface_rewrite_executed_here := False",
        "generated_output_mutation_executed_here := False",
        "historical_packet_edit_executed_here := False",
        "snapshot_migration_or_deletion_executed_here := False",
    }:
        assert token in text


def test_result_review_preserves_checkpoint_and_nonclaims() -> None:
    text = _read(REVIEW_PATH)

    for token in {
        "status_surface_canonicalization_enforcement_packet_result_review_full_pytest_count_v0",
        "status_surface_canonicalization_enforcement_packet_result_review_full_pytest_skipped_v0",
        "status_surface_canonicalization_enforcement_packet_result_review_lean_jobs_v0",
        "status_surface_canonicalization_enforcement_packet_result_review_axiom_count_v0",
        "status_surface_canonicalization_enforcement_packet_result_review_default_nonalias_absent_v0",
        "status_surface_canonicalization_enforcement_packet_result_review_sample_rep32_retained_v0",
        "status_surface_canonicalization_enforcement_packet_result_review_qft_gr_not_authorized_v0",
        "status_surface_canonicalization_enforcement_packet_result_review_master_action_not_promoted_v0",
        "status_surface_canonicalization_enforcement_packet_result_review_no_pillar_completion_v0",
        "status_surface_canonicalization_enforcement_packet_result_review_no_seam_closure_v0",
        "status_surface_canonicalization_enforcement_packet_result_review_no_phase2_readiness_v0",
        "status_surface_canonicalization_enforcement_packet_result_review_no_empirical_adequacy_v0",
        "status_surface_canonicalization_enforcement_packet_result_review_no_canonical_toe_claim_v0",
        "status_surface_canonicalization_enforcement_packet_result_review_manifest_not_enrolled_v0",
    }:
        assert token in text


def test_result_review_report_records_scope_and_selector_handoff() -> None:
    report = _json(REPORT_PATH)

    assert report["schema_id"] == REPORT_ID
    assert report["classification"] == "P-POLICY/nonclaim"
    assert report["review_status"] == "consumed_narrow_enforcement_packet_result"
    assert report["current_target"] == CONSUMED_TARGET
    assert report["consumed_enforcement_packet_token"] == CONSUMED_TOKEN
    assert report["result_token"] == RESULT_TOKEN
    assert report["selected_next_target"] == NEXT_TARGET
    assert report["selected_next_target_kind"] == (
        "post_status_surface_enforcement_bounded_attack_selector"
    )
    assert report["review_surface"] == _rel(REVIEW_PATH)
    assert report["source_enforcement_surface"] == _rel(ENFORCEMENT_PATH)
    assert report["source_enforcement_report"] == _rel(ENFORCEMENT_REPORT_PATH)
    assert report["focused_gate"] == (
        "formal/python/tests/test_status_surface_canonicalization_enforcement_packet_result_review_gate.py"
    )
    assert report["authorized_effect"] == (
        "CONSUME_STATUS_SURFACE_CANONICALIZATION_ENFORCEMENT_PACKET_RESULT_AND_ROTATE_TO_SELECTOR"
    )
    assert report["enforcement_packet_consumed_only"] is True
    assert report["active_live_target_mirror_parity_remains_enforced"] is True
    assert report["selector_rotation_authorized"] is True
    assert report["selector_choice_made_here"] is False
    assert report["broad_status_surface_rewrite_executed"] is False
    assert report["generated_output_mutation_executed"] is False
    assert report["historical_packet_edit_executed"] is False
    assert report["snapshot_migration_or_deletion_executed"] is False


def test_result_review_report_records_selector_candidates() -> None:
    report = _json(REPORT_PATH)
    selector = report["post_status_surface_enforcement_selector"]

    assert selector["selector_target"] == NEXT_TARGET
    assert selector["candidate_target_count"] == 6
    assert selector["recommended_candidate_after_review"] == RECOMMENDED_SELECTOR_TARGET
    assert selector["selection_made_by_this_packet"] is False
    assert selector["candidate_targets"] == [
        RECOMMENDED_SELECTOR_TARGET,
        "prepare_next_proof_debt_ledger_discharge_item",
        "prepare_artifact_retention_migration_plan",
        "prepare_qm_stat_theorem_gap_reentry",
        "prepare_sr_cosmo_global_obstruction_followup",
        "prepare_status_surface_enforcement_followup_packet",
    ]


def test_result_review_report_records_validation_and_nonclaims() -> None:
    report = _json(REPORT_PATH)

    assert report["validation_checkpoint"] == {
        "full_pytest_passed": 6606,
        "full_pytest_skipped": 230,
        "full_pytest_is_prior_checkpoint_not_fresh_for_this_packet": False,
        "full_pytest_fresh_for_this_packet": True,
        "ordinary_validation_mode": "read_only_by_default",
        "read_only_proof": (
            "full pytest from result-review implementation, followed by clean diff checks"
        ),
        "read_only_proof_passed": True,
        "lean_build_target": "ToeFormal",
        "lean_build_jobs": 7984,
        "governance_suite_passed": True,
    }
    assert report["preserved_posture"]["real_axiom_count"] == 60
    assert report["preserved_posture"]["read_only_validation_preserved"] is True
    assert report["preserved_posture"]["artifact_freeze_preserved"] is True
    assert report["preserved_posture"]["qft_gr_source_map_closure_authorized"] is False
    assert report["nonclaim_boundaries"] == {
        "master_action_promotion_authorized": False,
        "pillar_completion_inferred": False,
        "seam_closure_claim": False,
        "phase2_readiness_claim": False,
        "empirical_adequacy_claim": False,
        "canonical_toe_claim": False,
        "qft_gr_source_map_closure_authorized": False,
        "governance_manifest_enrollment_authorized": False,
    }


def test_active_live_target_mirror_parity_survives_selector_rotation() -> None:
    registry = _json(REGISTRY_PATH)
    live_target = registry["current_target_state"]["live_next_target"]
    report = _json(REPORT_PATH)
    parity = report["active_live_target_mirror_parity"]

    assert NEXT_TARGET in registry["next_strict_target_coverage"]
    assert parity["canonical_source"] == _rel(REGISTRY_PATH)
    assert parity["canonical_json_pointer"] == "/current_target_state/live_next_target"
    assert parity["expected_live_target_after_review"] == NEXT_TARGET
    assert {
        row["surface"] for row in parity["active_public_mirror_fields"]
    } == {_rel(path) for path in ACTIVE_MIRRORS}
    assert {row["field"] for row in parity["active_public_mirror_fields"]} == {MIRROR_KEY}

    for path in ACTIVE_MIRRORS:
        text = _read(path)
        values = _active_mirror_values(text)
        assert values == [live_target], f"{path} active mirror values: {values!r}"
        assert HISTORICAL_TOKEN in text

    assert HISTORICAL_TOKEN in parity["historical_packet_history_tokens_allowed"]
    assert CONSUMED_TARGET in parity["historical_packet_history_tokens_allowed"]


def test_current_authoritative_surfaces_record_result_review_chain() -> None:
    report = _json(REPORT_PATH)
    classes = report["current_authority_surface_classes"]
    index_text = _read(CURRENT_SURFACES_PATH)

    assert classes["canonical_live_target_source"] == _rel(REGISTRY_PATH)
    assert classes["frontier_mirror"] == (
        "formal/toe_formal/ToeFormal/Derivation/CrossPillarClosureFrontier.lean"
    )
    assert set(classes["active_target_mirror_surfaces"]) == {
        _rel(SEAM_REGISTRY_PATH),
        _rel(SEAM_INVENTORY_PATH),
    }
    assert classes["historical_surfaces_remain_evidence_not_current_authority_unless_referenced"] is True
    assert classes["generated_output_surfaces_read_only_under_normal_validation"] is True

    for token in {
        "CURRENT_LIVE_NEXT_TARGET_v0: prepare_qft_gr_state_domain_object_assumption_reduction_packet",
        "PREVIOUS_LIVE_NEXT_TARGET_v0: review_qft_gr_state_domain_assumption_reduction_packet_result",
        "ACTIVE_LANE_v0: qft_gr_state_domain_assumption_reduction_packet_result_review",
        "CURRENT_LIVE_TARGET_AUTHORITY_v0: formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json",
        "CURRENT_LIVE_TARGET_FRONTIER_MIRROR_v0: formal/toe_formal/ToeFormal/Derivation/CrossPillarClosureFrontier.lean",
        "CURRENT_LIVE_TARGET_EVIDENCE_v0: formal/toe_formal/ToeFormal/Bridges/QFT_GR_StateDomainAssumptionReductionPacketResultReview.lean",
        "CANONICAL_CONTROL_SOURCES",
        "PUBLIC_SUMMARY_SURFACES",
        "ACTIVE_TARGET_MIRROR_SURFACES",
        "HISTORICAL_SUPERSEDED_SURFACES",
        CONSUMED_TOKEN,
        RESULT_TOKEN,
    }:
        assert token in index_text


def test_result_review_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "formal/python/tests/test_status_surface_canonicalization_enforcement_packet_result_review_gate.py"
    )
