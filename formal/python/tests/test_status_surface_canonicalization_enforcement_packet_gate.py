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
ENFORCEMENT_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "StatusSurfaceCanonicalizationEnforcementPacket.lean"
)
SELECTOR_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PostStatusSurfaceCanonicalizationBoundedAttackSelection.lean"
)
AGGREGATE_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal.lean"
REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "STATUS_SURFACE_CANONICALIZATION_ENFORCEMENT_PACKET_20260505_v0.json"
)
SELECTOR_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "POST_STATUS_SURFACE_CANONICALIZATION_BOUNDED_ATTACK_SELECTION_20260505_v0.json"
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

REPORT_ID = "STATUS_SURFACE_CANONICALIZATION_ENFORCEMENT_PACKET_20260505_v0"
SURFACE_ID = "status_surface_canonicalization_enforcement_packet_v0"
CONSUMED_TARGET = "prepare_status_surface_canonicalization_enforcement_packet"
CONSUMED_TOKEN = "POST_STATUS_SURFACE_CANONICALIZATION_NEXT_ATTACK_SELECTED"
RESULT_TOKEN = "STATUS_SURFACE_CANONICALIZATION_ENFORCEMENT_PACKET_PREPARED"
NEXT_TARGET = "review_status_surface_canonicalization_enforcement_packet_result"
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


def test_enforcement_packet_surface_records_narrow_enforcement() -> None:
    text = _read(ENFORCEMENT_PATH)
    aggregate_text = _read(AGGREGATE_PATH)

    for token in {
        SURFACE_ID,
        CONSUMED_TARGET,
        CONSUMED_TOKEN,
        RESULT_TOKEN,
        NEXT_TARGET,
        MIRROR_KEY,
        HISTORICAL_TOKEN,
        "StatusSurfaceCanonicalizationEnforcementPacketStatus",
        "statusSurfaceCanonicalizationEnforcementPacketStatusV0",
        "status_surface_canonicalization_enforcement_packet_consumes_target_v0",
        "status_surface_canonicalization_enforcement_packet_consumes_selector_token_v0",
        "status_surface_canonicalization_enforcement_packet_result_token_v0",
        "status_surface_canonicalization_enforcement_packet_next_target_v0",
        "status_surface_canonicalization_enforcement_packet_prepared_v0",
        "status_surface_canonicalization_enforcement_packet_live_target_mirror_parity_v0",
        "status_surface_canonicalization_enforcement_packet_loop_registry_authority_v0",
        "status_surface_canonicalization_enforcement_packet_mirror_surface_count_v0",
    }:
        assert token in text

    assert (
        "import ToeFormal.Derivation.StatusSurfaceCanonicalizationEnforcementPacket"
        in aggregate_text
    )


def test_enforcement_packet_preserves_read_only_and_nonrewrite_boundaries() -> None:
    text = _read(ENFORCEMENT_PATH)

    for token in {
        "status_surface_canonicalization_enforcement_packet_generated_read_only_v0",
        "status_surface_canonicalization_enforcement_packet_read_only_preserved_v0",
        "status_surface_canonicalization_enforcement_packet_freeze_preserved_v0",
        "status_surface_canonicalization_enforcement_packet_no_rewrite_here_v0",
        "status_surface_canonicalization_enforcement_packet_no_generated_mutation_here_v0",
        "status_surface_canonicalization_enforcement_packet_no_history_edit_here_v0",
        "status_surface_canonicalization_enforcement_packet_no_snapshot_migration_here_v0",
        "broad_status_surface_rewrite_executed_here := False",
        "generated_output_mutation_executed_here := False",
        "historical_packet_edit_executed_here := False",
        "snapshot_migration_or_deletion_executed_here := False",
    }:
        assert token in text


def test_enforcement_packet_preserves_checkpoint_and_nonclaims() -> None:
    text = _read(ENFORCEMENT_PATH)

    for token in {
        "status_surface_canonicalization_enforcement_packet_full_pytest_count_v0",
        "status_surface_canonicalization_enforcement_packet_full_pytest_skipped_v0",
        "status_surface_canonicalization_enforcement_packet_lean_jobs_v0",
        "status_surface_canonicalization_enforcement_packet_axiom_count_v0",
        "status_surface_canonicalization_enforcement_packet_default_nonalias_absent_v0",
        "status_surface_canonicalization_enforcement_packet_sample_rep32_retained_v0",
        "status_surface_canonicalization_enforcement_packet_qft_gr_not_authorized_v0",
        "status_surface_canonicalization_enforcement_packet_master_action_not_promoted_v0",
        "status_surface_canonicalization_enforcement_packet_no_pillar_completion_v0",
        "status_surface_canonicalization_enforcement_packet_no_seam_closure_v0",
        "status_surface_canonicalization_enforcement_packet_no_phase2_readiness_v0",
        "status_surface_canonicalization_enforcement_packet_no_empirical_adequacy_v0",
        "status_surface_canonicalization_enforcement_packet_no_canonical_toe_claim_v0",
        "status_surface_canonicalization_enforcement_packet_manifest_not_enrolled_v0",
    }:
        assert token in text


def test_enforcement_report_records_scope_and_boundaries() -> None:
    report = _json(REPORT_PATH)

    assert report["schema_id"] == REPORT_ID
    assert report["classification"] == "P-POLICY/nonclaim"
    assert report["packet_status"] == "prepared_narrow_enforcement_only"
    assert report["current_target"] == CONSUMED_TARGET
    assert report["consumed_selector_token"] == CONSUMED_TOKEN
    assert report["result_token"] == RESULT_TOKEN
    assert report["selected_next_target"] == NEXT_TARGET
    assert report["selected_next_target_kind"] == (
        "status_surface_canonicalization_enforcement_packet_result_review"
    )
    assert report["enforcement_surface"] == _rel(ENFORCEMENT_PATH)
    assert report["source_selector_surface"] == _rel(SELECTOR_PATH)
    assert report["source_selector_report"] == _rel(SELECTOR_REPORT_PATH)
    assert report["focused_gate"] == (
        "formal/python/tests/test_status_surface_canonicalization_enforcement_packet_gate.py"
    )
    assert report["authorized_effect"] == (
        "PREPARE_STATUS_SURFACE_CANONICALIZATION_ENFORCEMENT_PACKET"
    )
    assert report["enforcement_packet_prepared"] is True
    assert report["broad_status_surface_rewrite_executed"] is False
    assert report["generated_output_mutation_executed"] is False
    assert report["historical_packet_edit_executed"] is False
    assert report["snapshot_migration_or_deletion_executed"] is False


def test_enforcement_report_records_validation_and_nonclaims() -> None:
    report = _json(REPORT_PATH)

    assert report["validation_checkpoint"] == {
        "full_pytest_passed": 6597,
        "full_pytest_skipped": 230,
        "full_pytest_is_prior_checkpoint_not_fresh_for_this_packet": False,
        "full_pytest_fresh_for_this_packet": True,
        "ordinary_validation_mode": "read_only_by_default",
        "read_only_proof": "full pytest from clean commit followed by git diff --exit-code",
        "read_only_proof_passed": True,
        "lean_build_target": "ToeFormal",
        "lean_build_jobs": 7983,
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


def test_active_live_target_mirror_parity_is_enforced() -> None:
    registry = _json(REGISTRY_PATH)
    live_target = registry["current_target_state"]["live_next_target"]
    report = _json(REPORT_PATH)
    parity = report["active_live_target_mirror_parity"]

    assert NEXT_TARGET in registry["next_strict_target_coverage"]
    assert parity["canonical_source"] == _rel(REGISTRY_PATH)
    assert parity["canonical_json_pointer"] == "/current_target_state/live_next_target"
    assert parity["expected_live_target_after_packet"] == NEXT_TARGET
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


def test_current_authoritative_surfaces_classify_sources_and_mirrors() -> None:
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
        "CURRENT_LIVE_NEXT_TARGET_v0: execute_qft_gr_weak_strong_conservation_comparison_scope_assumption_reduction_attempt",
        "PREVIOUS_LIVE_NEXT_TARGET_v0: review_qft_gr_weak_strong_conservation_comparison_scope_assumption_reduction_packet_result",
        "ACTIVE_LANE_v0: execute_qft_gr_weak_strong_conservation_comparison_scope_assumption_reduction_attempt",
        "CURRENT_LIVE_TARGET_AUTHORITY_v0: formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json",
        "CURRENT_LIVE_TARGET_FRONTIER_MIRROR_v0: formal/toe_formal/ToeFormal/Derivation/CrossPillarClosureFrontier.lean",
        "CURRENT_LIVE_TARGET_EVIDENCE_v0: formal/toe_formal/ToeFormal/Bridges/QFT_GR_WeakStrongConservationComparisonScopeAssumptionReductionPacketResultReview.lean",
        "formal/toe_formal/ToeFormal/Derivation/StatusSurfaceCanonicalizationEnforcementPacket.lean",
        "CANONICAL_CONTROL_SOURCES",
        "PUBLIC_SUMMARY_SURFACES",
        "ACTIVE_TARGET_MIRROR_SURFACES",
        "HISTORICAL_SUPERSEDED_SURFACES",
        RESULT_TOKEN,
    }:
        assert token in index_text


def test_enforcement_packet_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "formal/python/tests/test_status_surface_canonicalization_enforcement_packet_gate.py"
    )
