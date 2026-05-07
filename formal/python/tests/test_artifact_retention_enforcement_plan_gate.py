from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
)


REPO_ROOT = find_repo_root(Path(__file__))
PLAN_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ArtifactRetentionEnforcementPlan.lean"
)
SOURCE_SELECTOR_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "FullPillarTargetMapNextLaneSelectionAfterReadOnlyHygiene.lean"
)
AGGREGATE_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal.lean"
REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "ARTIFACT_RETENTION_ENFORCEMENT_PLAN_20260505_v0.json"
)
SOURCE_SELECTOR_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTION_AFTER_READ_ONLY_HYGIENE_20260505_v0.json"
)
SOURCE_POLICY_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "REPOSITORY_ARTIFACT_RETENTION_POLICY_20260505_v0.md"
)

REPORT_ID = "ARTIFACT_RETENTION_ENFORCEMENT_PLAN_20260505_v0"
SURFACE_ID = "artifact_retention_enforcement_plan_v0"
CONSUMED_TARGET = "prepare_artifact_retention_enforcement_plan"
CONSUMED_TOKEN = "FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTED_AFTER_READ_ONLY_HYGIENE"
RESULT_TOKEN = "ARTIFACT_RETENTION_ENFORCEMENT_PLAN_PREPARED"
NEXT_TARGET = "review_artifact_retention_enforcement_plan_result"
EXPECTED_ZONE_CLASSES = {
    "LEGACY_TRACKED_SNAPSHOT_ZONE",
    "GENERATED_OUTPUT_ZONE",
    "UNTRACKED_TEMPORARY_WORKING_AREA",
    "HISTORICAL_QUARANTINE_AREA",
    "NONCANONICAL_BACKUP_AREA",
    "CANONICAL_SMALL_CONTROL_PLANE_ARTIFACTS",
    "NORMAL_TRACKED_SOURCE_SURFACES",
}
EXPECTED_ZONE_IDS = {
    "formal/tooling_snapshots",
    "formal/output",
    "scratch",
    "archive",
    "backup",
    "formal/docs/release/*.json",
    "Lean/Python/docs",
}
EXPECTED_RULES = {
    "NO_NEW_LARGE_TRACKED_SNAPSHOTS_WITHOUT_EXPLICIT_RETENTION_PACKET",
    "NO_TRACKED_GENERATED_OUTPUT_MUTATION_DURING_VALIDATION",
    "NO_SNAPSHOT_MIGRATION_OR_DELETION_IN_THIS_PACKET",
    "FUTURE_LARGE_ARTIFACT_ADDITIONS_REQUIRE_SIZE_AND_CLASSIFICATION_JUSTIFICATION",
    "EXISTING_TOOLING_SNAPSHOTS_MASS_ACKNOWLEDGED_BUT_DEFERRED",
}


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def _rel(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def test_artifact_retention_enforcement_plan_records_core_policy() -> None:
    text = _read(PLAN_PATH)
    aggregate_text = _read(AGGREGATE_PATH)

    for token in {
        SURFACE_ID,
        CONSUMED_TARGET,
        CONSUMED_TOKEN,
        RESULT_TOKEN,
        NEXT_TARGET,
        "ArtifactRetentionEnforcementPlanStatus",
        "ArtifactRetentionZone",
        "artifactRetentionEnforcementPlanZonesV0",
        "artifactRetentionEnforcementPlanRulesV0",
        "artifact_retention_enforcement_plan_consumes_target_v0",
        "artifact_retention_enforcement_plan_consumes_selector_token_v0",
        "artifact_retention_enforcement_plan_result_token_v0",
        "artifact_retention_enforcement_plan_next_target_v0",
        "artifact_retention_enforcement_plan_zones_classified_v0",
        "artifact_retention_enforcement_plan_zone_count_v0",
        "artifact_retention_enforcement_plan_rule_count_v0",
    } | EXPECTED_ZONE_CLASSES | EXPECTED_ZONE_IDS | EXPECTED_RULES:
        assert token in text

    assert "import ToeFormal.Derivation.ArtifactRetentionEnforcementPlan" in aggregate_text


def test_artifact_retention_enforcement_plan_freezes_without_migration() -> None:
    text = _read(PLAN_PATH)

    for token in {
        "artifact_retention_enforcement_plan_freezes_new_large_snapshots_v0",
        "artifact_retention_enforcement_plan_validation_output_mutation_forbidden_v0",
        "artifact_retention_enforcement_plan_large_artifact_justification_required_v0",
        "artifact_retention_enforcement_plan_existing_snapshot_mass_deferred_v0",
        "artifact_retention_enforcement_plan_migration_deletion_deferred_v0",
        "artifact_retention_enforcement_plan_no_migration_deletion_here_v0",
        "artifact_retention_enforcement_plan_release_json_allowed_v0",
        "artifact_retention_enforcement_plan_source_surfaces_allowed_v0",
        "snapshot_migration_or_deletion_executed_here := False",
        "PREPARE_ARTIFACT_RETENTION_ENFORCEMENT_PLAN_NO_MIGRATION",
    }:
        assert token in text


def test_artifact_retention_enforcement_plan_preserves_validation_and_nonclaims() -> None:
    text = _read(PLAN_PATH)

    for token in {
        "artifact_retention_enforcement_plan_pytest_read_only_v0",
        "artifact_retention_enforcement_plan_diff_proof_v0",
        "artifact_retention_enforcement_plan_full_pytest_count_v0",
        "artifact_retention_enforcement_plan_full_pytest_skipped_v0",
        "artifact_retention_enforcement_plan_lean_jobs_v0",
        "artifact_retention_enforcement_plan_axiom_count_v0",
        "artifact_retention_enforcement_plan_default_nonalias_absent_v0",
        "artifact_retention_enforcement_plan_sample_rep32_retained_v0",
        "artifact_retention_enforcement_plan_qft_gr_source_map_not_authorized_v0",
        "artifact_retention_enforcement_plan_master_action_not_promoted_v0",
        "artifact_retention_enforcement_plan_no_pillar_completion_v0",
        "artifact_retention_enforcement_plan_no_seam_closure_v0",
        "artifact_retention_enforcement_plan_no_phase2_readiness_v0",
        "artifact_retention_enforcement_plan_no_empirical_adequacy_v0",
        "artifact_retention_enforcement_plan_no_canonical_toe_claim_v0",
        "artifact_retention_enforcement_plan_manifest_not_enrolled_v0",
    }:
        assert token in text


def test_artifact_retention_enforcement_plan_report_records_zones_and_rules() -> None:
    report = _json(REPORT_PATH)

    assert report["schema_id"] == REPORT_ID
    assert report["current_target"] == CONSUMED_TARGET
    assert report["consumed_selector_token"] == CONSUMED_TOKEN
    assert report["result_token"] == RESULT_TOKEN
    assert report["selected_next_target"] == NEXT_TARGET
    assert report["plan_surface"] == _rel(PLAN_PATH)
    assert report["source_selector_surface"] == _rel(SOURCE_SELECTOR_PATH)
    assert report["source_selector_report"] == _rel(SOURCE_SELECTOR_REPORT_PATH)
    assert report["source_artifact_policy"] == _rel(SOURCE_POLICY_PATH)
    assert report["authorized_effect"] == (
        "PREPARE_ARTIFACT_RETENTION_ENFORCEMENT_PLAN_NO_MIGRATION"
    )
    assert report["migration_or_deletion_executed"] is False
    assert report["existing_snapshot_disposition"] == (
        "acknowledged_and_deferred_until_future_explicit_packet"
    )
    assert report["large_snapshot_default"] == (
        "no_new_large_tracked_snapshots_without_explicit_retention_packet"
    )
    assert report["validation_output_rule"] == (
        "no_tracked_generated_output_mutation_during_validation"
    )
    assert report["future_large_artifact_rule"] == (
        "size_and_classification_justification_required"
    )
    assert {row["zone_id"] for row in report["artifact_zones"]} == EXPECTED_ZONE_IDS
    assert {row["policy_class"] for row in report["artifact_zones"]} == EXPECTED_ZONE_CLASSES
    assert set(report["enforcement_rules"]) == EXPECTED_RULES


def test_artifact_retention_enforcement_plan_report_preserves_checkpoint_and_boundaries() -> None:
    report = _json(REPORT_PATH)
    checkpoint = report["validation_checkpoint"]

    assert checkpoint == {
        "full_pytest_passed": 6536,
        "full_pytest_skipped": 230,
        "full_pytest_is_prior_checkpoint_not_fresh_for_this_plan": True,
        "ordinary_validation_mode": "read_only_by_default",
        "read_only_proof": "full pytest from clean commit followed by git diff --exit-code",
        "read_only_proof_passed": True,
        "lean_build_target": "ToeFormal",
        "lean_build_jobs": 7977,
        "governance_suite_passed": True,
    }
    assert report["preserved_posture"]["real_axiom_count"] == 60
    assert report["preserved_posture"]["qft_gr_source_map_closure_authorized"] is False
    assert report["nonclaim_boundaries"] == {
        "snapshot_migration_or_deletion_executed": False,
        "master_action_promotion_authorized": False,
        "pillar_completion_inferred": False,
        "seam_closure_claim": False,
        "phase2_readiness_claim": False,
        "empirical_adequacy_claim": False,
        "canonical_toe_claim": False,
        "qft_gr_source_map_closure_authorized": False,
        "governance_manifest_enrollment_authorized": False,
    }
    assert report["next_action_after_plan_packet"] == NEXT_TARGET


def test_artifact_retention_enforcement_plan_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "formal/python/tests/test_artifact_retention_enforcement_plan_gate.py"
    )
