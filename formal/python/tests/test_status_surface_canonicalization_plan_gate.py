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
    / "StatusSurfaceCanonicalizationPlan.lean"
)
SOURCE_SELECTOR_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PostArtifactRetentionEnforcementBoundedAttackSelection.lean"
)
AGGREGATE_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal.lean"
REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "STATUS_SURFACE_CANONICALIZATION_PLAN_20260505_v0.json"
)
SOURCE_SELECTOR_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "POST_ARTIFACT_RETENTION_ENFORCEMENT_BOUNDED_ATTACK_SELECTION_20260505_v0.json"
)

REPORT_ID = "STATUS_SURFACE_CANONICALIZATION_PLAN_20260505_v0"
SURFACE_ID = "status_surface_canonicalization_plan_v0"
CONSUMED_TARGET = "prepare_status_surface_canonicalization_plan"
CONSUMED_TOKEN = "POST_ARTIFACT_RETENTION_ENFORCEMENT_NEXT_ATTACK_SELECTED"
RESULT_TOKEN = "STATUS_SURFACE_CANONICALIZATION_PLAN_PREPARED"
NEXT_TARGET = "review_status_surface_canonicalization_plan_result"
EXPECTED_CLASSES = {
    "CANONICAL_CONTROL_SOURCES",
    "PUBLIC_SUMMARY_SURFACES",
    "GENERATED_OUTPUT_SURFACES",
    "HISTORICAL_SUPERSEDED_SURFACES",
}
EXPECTED_RULES = {
    "ONLY_CANONICAL_SURFACES_DETERMINE_LIVE_TARGET_AND_CURRENT_AUTHORITY",
    "PUBLIC_SUMMARIES_MUST_MIRROR_CANONICAL_SURFACES",
    "HISTORICAL_RELEASE_DOCS_ARE_IMMUTABLE_EVIDENCE_NOT_CURRENT_AUTHORITY_UNLESS_REFERENCED_BY_REGISTRY_OR_FRONTIER",
    "NO_STALE_VALIDATION_COUNT_PROMOTION",
    "NO_MANUAL_OVERWRITE_OF_GENERATED_OUTPUTS_DURING_NORMAL_VALIDATION",
}
EXPECTED_SURFACES = {
    "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json",
    "formal/docs/release/*.json",
    "formal/docs/release/LEAN_AXIOM_SPEC_BACKED_LEDGER_v0.md",
    "formal/toe_formal/ToeFormal/Derivation/CrossPillarClosureFrontier.lean",
    "formal/docs/release/CURRENT_AUTHORITATIVE_SURFACES_v0.md",
    "README.md",
    "State_of_the_Theory.md",
    "formal/docs/paper/PHYSICS_ROADMAP_v0.md",
    "formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md",
    "formal/docs/paper/TOE_MASTER_ACTION_SEAM_CONSTRAINT_REGISTRY_v0.md",
    "formal/docs/paper/TOE_MASTER_ACTION_CLASS_B_SEAM_INVENTORY_v0.md",
    "formal/docs/paper/TOE_MATH_PHYSICS_INVENTORY_v0.md",
    "formal/output/*",
    "formal/output/reports/*",
    "generated validation summaries",
    "older release packets",
    "prior result reviews",
    "archived reports",
}


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def _rel(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def test_status_surface_canonicalization_plan_records_core_scope() -> None:
    text = _read(PLAN_PATH)
    aggregate_text = _read(AGGREGATE_PATH)

    for token in {
        SURFACE_ID,
        CONSUMED_TARGET,
        CONSUMED_TOKEN,
        RESULT_TOKEN,
        NEXT_TARGET,
        "StatusSurfaceCanonicalizationPlanStatus",
        "StatusSurfaceClass",
        "statusSurfaceCanonicalizationPlanClassesV0",
        "statusSurfaceCanonicalizationPlanRulesV0",
        "status_surface_canonicalization_plan_consumes_target_v0",
        "status_surface_canonicalization_plan_consumes_selector_token_v0",
        "status_surface_canonicalization_plan_result_token_v0",
        "status_surface_canonicalization_plan_next_target_v0",
        "status_surface_canonicalization_plan_surface_class_count_v0",
        "status_surface_canonicalization_plan_drift_rule_count_v0",
    } | EXPECTED_CLASSES | EXPECTED_RULES | EXPECTED_SURFACES:
        assert token in text

    assert "import ToeFormal.Derivation.StatusSurfaceCanonicalizationPlan" in aggregate_text


def test_status_surface_canonicalization_plan_classifies_surface_families() -> None:
    text = _read(PLAN_PATH)

    for token in {
        "status_surface_canonicalization_plan_canonical_classified_v0",
        "status_surface_canonicalization_plan_public_classified_v0",
        "status_surface_canonicalization_plan_generated_classified_v0",
        "status_surface_canonicalization_plan_historical_classified_v0",
        "status_surface_canonicalization_plan_canonical_authority_v0",
        "status_surface_canonicalization_plan_public_mirror_v0",
        "status_surface_canonicalization_plan_history_not_current_authority_v0",
    }:
        assert token in text


def test_status_surface_canonicalization_plan_defines_drift_rules_without_rewrite() -> None:
    text = _read(PLAN_PATH)

    for token in {
        "status_surface_canonicalization_plan_drift_rules_defined_v0",
        "status_surface_canonicalization_plan_no_stale_validation_promotion_v0",
        "status_surface_canonicalization_plan_no_generated_output_manual_overwrite_v0",
        "status_surface_canonicalization_plan_no_broad_rewrite_here_v0",
        "status_surface_canonicalization_plan_no_generated_output_mutation_here_v0",
        "status_surface_canonicalization_plan_no_historical_packet_edit_here_v0",
        "broad_status_surface_rewrite_executed_here := False",
        "generated_output_mutation_executed_here := False",
        "historical_packet_edit_executed_here := False",
        "PREPARE_STATUS_SURFACE_CANONICALIZATION_PLAN_NO_REWRITE",
    }:
        assert token in text


def test_status_surface_canonicalization_plan_preserves_posture_and_nonclaims() -> None:
    text = _read(PLAN_PATH)

    for token in {
        "status_surface_canonicalization_plan_artifact_freeze_preserved_v0",
        "status_surface_canonicalization_plan_read_only_validation_preserved_v0",
        "status_surface_canonicalization_plan_migration_deletion_deferred_v0",
        "status_surface_canonicalization_plan_full_pytest_count_v0",
        "status_surface_canonicalization_plan_full_pytest_skipped_v0",
        "status_surface_canonicalization_plan_lean_jobs_v0",
        "status_surface_canonicalization_plan_axiom_count_v0",
        "status_surface_canonicalization_plan_default_nonalias_absent_v0",
        "status_surface_canonicalization_plan_sample_rep32_retained_v0",
        "status_surface_canonicalization_plan_qft_gr_not_authorized_v0",
        "status_surface_canonicalization_plan_master_action_not_promoted_v0",
        "status_surface_canonicalization_plan_no_pillar_completion_v0",
        "status_surface_canonicalization_plan_no_seam_closure_v0",
        "status_surface_canonicalization_plan_no_phase2_readiness_v0",
        "status_surface_canonicalization_plan_no_empirical_adequacy_v0",
        "status_surface_canonicalization_plan_no_canonical_toe_claim_v0",
        "status_surface_canonicalization_plan_manifest_not_enrolled_v0",
        "lean_build_jobs_confirmed := 7980",
    }:
        assert token in text


def test_status_surface_canonicalization_plan_report_records_classes_and_rules() -> None:
    report = _json(REPORT_PATH)

    assert report["schema_id"] == REPORT_ID
    assert report["current_target"] == CONSUMED_TARGET
    assert report["consumed_selector_token"] == CONSUMED_TOKEN
    assert report["result_token"] == RESULT_TOKEN
    assert report["selected_next_target"] == NEXT_TARGET
    assert report["plan_surface"] == _rel(PLAN_PATH)
    assert report["source_selector_surface"] == _rel(SOURCE_SELECTOR_PATH)
    assert report["source_selector_report"] == _rel(SOURCE_SELECTOR_REPORT_PATH)
    assert report["focused_gate"] == (
        "formal/python/tests/test_status_surface_canonicalization_plan_gate.py"
    )
    assert report["authorized_effect"] == (
        "PREPARE_STATUS_SURFACE_CANONICALIZATION_PLAN_NO_REWRITE"
    )
    assert report["broad_status_surface_rewrite_executed"] is False
    assert report["generated_output_mutation_executed"] is False
    assert report["historical_packet_edit_executed"] is False
    assert {row["class_id"] for row in report["surface_classes"]} == EXPECTED_CLASSES
    observed_surfaces = {
        surface
        for row in report["surface_classes"]
        for surface in row["example_surfaces"]
    }
    assert observed_surfaces == EXPECTED_SURFACES
    assert set(report["drift_prevention_rules"]) == EXPECTED_RULES


def test_status_surface_canonicalization_plan_report_preserves_boundaries() -> None:
    report = _json(REPORT_PATH)
    checkpoint = report["validation_checkpoint"]
    enforcement = report["preserved_enforcement"]

    assert checkpoint == {
        "full_pytest_passed": 6536,
        "full_pytest_skipped": 230,
        "full_pytest_is_prior_checkpoint_not_fresh_for_this_plan": True,
        "ordinary_validation_mode": "read_only_by_default",
        "read_only_proof": "full pytest from clean commit followed by git diff --exit-code",
        "read_only_proof_passed": True,
        "lean_build_target": "ToeFormal",
        "lean_build_jobs": 7980,
        "governance_suite_passed": True,
    }
    assert enforcement["new_large_tracked_snapshots_frozen_by_default"] is True
    assert enforcement["ordinary_validation_mode"] == "read_only_by_default"
    assert enforcement["tracked_generated_output_mutation_forbidden_during_validation"] is True
    assert enforcement["snapshot_migration_or_deletion_deferred_to_future_packet"] is True
    assert enforcement["status_surface_rewrite_deferred_to_future_packet"] is True
    assert report["preserved_posture"]["real_axiom_count"] == 60
    assert report["preserved_posture"]["qft_gr_source_map_closure_authorized"] is False
    assert report["nonclaim_boundaries"] == {
        "broad_status_surface_rewrite_executed": False,
        "generated_output_mutation_executed": False,
        "historical_packet_edit_executed": False,
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


def test_status_surface_canonicalization_plan_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "formal/python/tests/test_status_surface_canonicalization_plan_gate.py"
    )
