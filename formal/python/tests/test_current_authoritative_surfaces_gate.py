from __future__ import annotations

from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
)


REPO_ROOT = find_repo_root(Path(__file__))
INDEX_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "CURRENT_AUTHORITATIVE_SURFACES_v0.md"
)
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LOOP_CONTROL_REGISTRY_v0.json"
FRONTIER_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "CrossPillarClosureFrontier.lean"
)
HYGIENE_SURFACE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ReadOnlyValidationHygiene.lean"
)
POST_HYGIENE_SELECTOR_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PostReadOnlyValidationHygieneBoundedAttackSelection.lean"
)
AFTER_HYGIENE_FULL_PILLAR_SELECTOR_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "FullPillarTargetMapNextLaneSelectionAfterReadOnlyHygiene.lean"
)
ARTIFACT_RETENTION_PLAN_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ArtifactRetentionEnforcementPlan.lean"
)
ARTIFACT_RETENTION_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ArtifactRetentionEnforcementPlanResultReview.lean"
)
POST_ARTIFACT_RETENTION_SELECTOR_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PostArtifactRetentionEnforcementBoundedAttackSelection.lean"
)
STATUS_SURFACE_CANONICALIZATION_PLAN_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "StatusSurfaceCanonicalizationPlan.lean"
)
STATUS_SURFACE_CANONICALIZATION_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "StatusSurfaceCanonicalizationPlanResultReview.lean"
)
POST_STATUS_SURFACE_CANONICALIZATION_SELECTOR_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PostStatusSurfaceCanonicalizationBoundedAttackSelection.lean"
)
STATUS_SURFACE_CANONICALIZATION_ENFORCEMENT_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "StatusSurfaceCanonicalizationEnforcementPacket.lean"
)
STATUS_SURFACE_CANONICALIZATION_ENFORCEMENT_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "StatusSurfaceCanonicalizationEnforcementPacketResultReview.lean"
)
POST_STATUS_SURFACE_ENFORCEMENT_SELECTOR_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PostStatusSurfaceEnforcementBoundedAttackSelection.lean"
)
AFTER_STATUS_SURFACE_ENFORCEMENT_FULL_PILLAR_SELECTOR_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "FullPillarTargetMapNextLaneSelectionAfterStatusSurfaceEnforcement.lean"
)
NEXT_PROOF_DEBT_ITEM_SELECTOR_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "NextProofDebtLedgerDischargeItem.lean"
)
SAMPLEREP32_DISCHARGE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Variational"
    / "FNRepNonAliasEquivalence01SampleRep32Discharge.lean"
)
SAMPLEREP32_DISCHARGE_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Variational"
    / "FNRepNonAliasEquivalence01SampleRep32DischargeResultReview.lean"
)
POST_FNREP_SAMPLEREP32_SELECTOR_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PostFNRepSampleRep32DischargeBoundedAttackSelection.lean"
)
AXIOM_LEDGER_AUDIT_REFRESH_AFTER_SAMPLEREP32_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "AxiomLedgerAuditRefreshAfterSampleRep32.lean"
)
AXIOM_LEDGER_AUDIT_REFRESH_AFTER_SAMPLEREP32_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "AxiomLedgerAuditRefreshAfterSampleRep32ResultReview.lean"
)
LEDGER_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LEAN_AXIOM_SPEC_BACKED_LEDGER_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_current_authoritative_surfaces_index_records_live_authority_chain() -> None:
    text = _read(INDEX_PATH)

    for token in {
        "CURRENT_AUTHORITATIVE_SURFACES_v0",
        "CURRENT_LIVE_NEXT_TARGET_v0: select_next_post_samplerep32_axiom_audit_bounded_attack",
        "PREVIOUS_LIVE_NEXT_TARGET_v0: review_axiom_ledger_audit_refresh_after_samplerep32_result",
        "ACTIVE_LANE_v0: axiom_ledger_audit_refresh_after_samplerep32_result_review",
        "CURRENT_LIVE_TARGET_AUTHORITY_v0: formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json",
        "CURRENT_LIVE_TARGET_FRONTIER_MIRROR_v0: formal/toe_formal/ToeFormal/Derivation/CrossPillarClosureFrontier.lean",
        "CURRENT_LIVE_TARGET_EVIDENCE_v0: formal/toe_formal/ToeFormal/Derivation/AxiomLedgerAuditRefreshAfterSampleRep32ResultReview.lean",
        "READ_ONLY_VALIDATION_HYGIENE_ENFORCED",
        "POST_READ_ONLY_VALIDATION_HYGIENE_NEXT_ATTACK_SELECTED",
        "FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTED_AFTER_READ_ONLY_HYGIENE",
        "ARTIFACT_RETENTION_ENFORCEMENT_PLAN_PREPARED",
        "ARTIFACT_RETENTION_ENFORCEMENT_PLAN_RESULT_REVIEW_CONSUMED",
        "POST_ARTIFACT_RETENTION_ENFORCEMENT_NEXT_ATTACK_SELECTED",
        "STATUS_SURFACE_CANONICALIZATION_PLAN_PREPARED",
        "STATUS_SURFACE_CANONICALIZATION_PLAN_RESULT_REVIEW_CONSUMED",
        "POST_STATUS_SURFACE_CANONICALIZATION_NEXT_ATTACK_SELECTED",
        "STATUS_SURFACE_CANONICALIZATION_ENFORCEMENT_PACKET_PREPARED",
        "STATUS_SURFACE_CANONICALIZATION_ENFORCEMENT_PACKET_RESULT_REVIEW_CONSUMED",
        "POST_STATUS_SURFACE_ENFORCEMENT_NEXT_ATTACK_SELECTED",
        "FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTED_AFTER_STATUS_SURFACE_ENFORCEMENT",
        "NEXT_PROOF_DEBT_LEDGER_DISCHARGE_ITEM_SELECTED",
        "FNREP_NONALIAS_SAMPLEREP32_DISCHARGED_LEAN_BACKED_CONSTRUCTOR",
        "FNREP_NONALIAS_SAMPLEREP32_DISCHARGE_RESULT_REVIEW_CONSUMED_LEAN_BACKED_CONSTRUCTOR",
        "POST_FNREP_SAMPLEREP32_DISCHARGE_NEXT_ATTACK_SELECTED",
        "AXIOM_LEDGER_AUDIT_REFRESH_CONFIRMED_59_REAL_AXIOMS",
        "AXIOM_LEDGER_AUDIT_REFRESH_AFTER_SAMPLEREP32_RESULT_REVIEW_CONSUMED_59_REAL_AXIOMS_CONFIRMED",
        "CANONICAL_CONTROL_SOURCES",
        "PUBLIC_SUMMARY_SURFACES",
        "ACTIVE_TARGET_MIRROR_SURFACES",
        "HISTORICAL_SUPERSEDED_SURFACES",
    }:
        assert token in text

    for path in {
        REGISTRY_PATH,
        FRONTIER_PATH,
        HYGIENE_SURFACE_PATH,
        POST_HYGIENE_SELECTOR_PATH,
        AFTER_HYGIENE_FULL_PILLAR_SELECTOR_PATH,
        ARTIFACT_RETENTION_PLAN_PATH,
        ARTIFACT_RETENTION_RESULT_REVIEW_PATH,
        POST_ARTIFACT_RETENTION_SELECTOR_PATH,
        STATUS_SURFACE_CANONICALIZATION_PLAN_PATH,
        STATUS_SURFACE_CANONICALIZATION_RESULT_REVIEW_PATH,
        POST_STATUS_SURFACE_CANONICALIZATION_SELECTOR_PATH,
        STATUS_SURFACE_CANONICALIZATION_ENFORCEMENT_PATH,
        STATUS_SURFACE_CANONICALIZATION_ENFORCEMENT_RESULT_REVIEW_PATH,
        POST_STATUS_SURFACE_ENFORCEMENT_SELECTOR_PATH,
        AFTER_STATUS_SURFACE_ENFORCEMENT_FULL_PILLAR_SELECTOR_PATH,
        NEXT_PROOF_DEBT_ITEM_SELECTOR_PATH,
        SAMPLEREP32_DISCHARGE_PATH,
        SAMPLEREP32_DISCHARGE_RESULT_REVIEW_PATH,
        POST_FNREP_SAMPLEREP32_SELECTOR_PATH,
        AXIOM_LEDGER_AUDIT_REFRESH_AFTER_SAMPLEREP32_PATH,
        AXIOM_LEDGER_AUDIT_REFRESH_AFTER_SAMPLEREP32_RESULT_REVIEW_PATH,
        LEDGER_PATH,
    }:
        assert str(path.relative_to(REPO_ROOT)).replace("\\", "/") in text


def test_current_authoritative_surfaces_index_records_current_axiom_and_nonclaim_state() -> None:
    text = _read(INDEX_PATH)

    for token in {
        "REAL_AXIOM_COUNT_v0: 59",
        "REAL_SORRY_OR_ADMIT_COUNT_v0: 0",
        "defaultNonAlias: absent_from_unresolved_axiom_debt_and_lean_backed",
        "sampleRep32: absent_from_unresolved_axiom_debt_and_lean_backed_constructor",
        "QFT_GR_SOURCE_MAP_CLOSURE_AUTHORIZED_v0: false",
        "MASTER_ACTION_PROMOTION_AUTHORIZED_v0: false",
        "PILLAR_COMPLETION_INFERRED_v0: false",
        "SEAM_CLOSURE_CLAIM_v0: false",
        "PHASE2_READINESS_CLAIM_v0: false",
        "EMPIRICAL_ADEQUACY_CLAIM_v0: false",
        "CANONICAL_TOE_CLAIM_v0: false",
    }:
        assert token in text


def test_current_authoritative_surfaces_index_records_validation_and_historical_classes() -> None:
    text = _read(INDEX_PATH)

    for token in {
        ".\\run_governance.ps1",
        ".\\run_pytest.ps1",
        ".\\run_lean.ps1",
        "git diff --check",
        "Manual fallback validation commands",
        "pwsh -NoProfile -ExecutionPolicy Bypass -File ./governance_suite.ps1",
        "./py.ps1 -m pytest formal/python/tests -q",
        "Push-Location formal/toe_formal; lake build ToeFormal; Pop-Location",
        "git diff --exit-code",
        "formal/tooling_snapshots",
        "scratch",
        "archive",
        "backup",
        "REPOSITORY_ARTIFACT_RETENTION_POLICY_20260505_v0",
        "POST_READ_ONLY_VALIDATION_HYGIENE_BOUNDED_ATTACK_SELECTION_20260505_v0",
        "FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTION_AFTER_READ_ONLY_HYGIENE_20260505_v0",
        "ARTIFACT_RETENTION_ENFORCEMENT_PLAN_20260505_v0",
        "ARTIFACT_RETENTION_ENFORCEMENT_PLAN_RESULT_REVIEW_20260505_v0",
        "POST_ARTIFACT_RETENTION_ENFORCEMENT_BOUNDED_ATTACK_SELECTION_20260505_v0",
        "STATUS_SURFACE_CANONICALIZATION_PLAN_20260505_v0",
        "STATUS_SURFACE_CANONICALIZATION_PLAN_RESULT_REVIEW_20260505_v0",
        "POST_STATUS_SURFACE_CANONICALIZATION_BOUNDED_ATTACK_SELECTION_20260505_v0",
        "STATUS_SURFACE_CANONICALIZATION_ENFORCEMENT_PACKET_20260505_v0",
        "STATUS_SURFACE_CANONICALIZATION_ENFORCEMENT_PACKET_RESULT_REVIEW_20260505_v0",
        "POST_STATUS_SURFACE_ENFORCEMENT_BOUNDED_ATTACK_SELECTION_20260505_v0",
        "FULL_PILLAR_TARGET_MAP_NEXT_LANE_SELECTION_AFTER_STATUS_SURFACE_ENFORCEMENT_20260508_v0",
        "NEXT_PROOF_DEBT_LEDGER_DISCHARGE_ITEM_20260505_v0",
        "PROOF_DEBT_DISCHARGE_FNREP_SAMPLEREP32_20260505_v0",
        "PROOF_DEBT_DISCHARGE_FNREP_SAMPLEREP32_RESULT_REVIEW_20260505_v0",
        "POST_FNREP_SAMPLEREP32_DISCHARGE_BOUNDED_ATTACK_SELECTION_20260505_v0",
        "AXIOM_LEDGER_AUDIT_REFRESH_AFTER_SAMPLEREP32_20260505_v0",
        "TOE_ALLOW_TRACKED_OUTPUT_WRITES=1",
    }:
        assert token in text


def test_current_authoritative_surfaces_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "formal/python/tests/test_current_authoritative_surfaces_gate.py"
    )
