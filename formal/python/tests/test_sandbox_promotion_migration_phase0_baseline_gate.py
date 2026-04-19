from __future__ import annotations

import json
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists() and (p / "README.md").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory and README.md).")


REPO_ROOT = find_repo_root(Path(__file__))
DECLARATION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "SANDBOX_PROMOTION_MIGRATION_PHASE0_DECLARATION_20260419_v0.md"
DOSSIER_PATH = REPO_ROOT / "formal" / "output" / "reports" / "sandbox_promotion_migration_phase0_baseline_dossier_20260419_v0.json"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_phase0_baseline_files_exist() -> None:
    assert DECLARATION_PATH.exists(), "Missing Phase 0 migration declaration."
    assert DOSSIER_PATH.exists(), "Missing Phase 0 baseline dossier."


def test_phase0_declaration_structure() -> None:
    text = _read(DECLARATION_PATH)
    required_sections = [
        "## Tranche name",
        "## Objective",
        "## Allowed files",
        "## Out of scope",
        "## Acceptance",
        "## Rollback anchor",
        "## Hard stop rule",
        "## Boundary freshness note",
    ]
    for section in required_sections:
        assert section in text, f"Missing declaration section: {section}"

    for path_ref in (
        "formal/output/reports/sandbox_promotion_migration_phase0_baseline_dossier_20260419_v0.json",
        "formal/python/tests/test_sandbox_promotion_migration_phase0_baseline_gate.py",
        "State_of_the_Theory.md",
        "formal/docs/paper/PHYSICS_ROADMAP_v0.md",
    ):
        assert path_ref in text


def test_phase0_baseline_dossier_schema() -> None:
    payload = _json(DOSSIER_PATH)
    assert payload["schema_id"] == "SANDBOX_PROMOTION_MIGRATION_PHASE0_BASELINE_DOSSIER_20260419_v0"
    assert payload["artifact_id"] == "sandbox_promotion_migration_phase0_baseline_dossier_20260419_v0"
    assert payload["status"] == "FORMAL_PHASE0_BASELINE_PINNED_NONLIVE"

    surfaces = payload["baseline_surfaces"]
    assert surfaces["sandbox_policy"] == "formal/docs/release/SANDBOX_PHYSICS_LANE_EXECUTION_POLICY_20260418_v0.md"
    assert surfaces["promotion_policy"] == "formal/docs/release/PROMOTION_GOVERNANCE_LANE_POLICY_20260418_v0.md"
    assert surfaces["lane_policy_gate"] == "formal/python/tests/test_sandbox_promotion_lane_policy_gate.py"
    assert surfaces["phase0_declaration"] == "formal/docs/release/SANDBOX_PROMOTION_MIGRATION_PHASE0_DECLARATION_20260419_v0.md"
    assert surfaces["phase0_gate"] == "formal/python/tests/test_sandbox_promotion_migration_phase0_baseline_gate.py"

    ledger = payload["phase_ledger"]
    assert ledger["phase0"] == "FORMAL_TRANCHE_OPEN_AND_BASELINE_DOSSIER_PINNED"
    assert ledger["phase1"] == "OBJECTIVELY_COMPLETE_POLICY_SPLIT_AND_MIRROR_BINDING_PINNED"
    assert ledger["phase2"] == "PARTIAL_ARTIFACT_CLASSIFICATION_AND_PROMOTION_BOUNDARY_APPLICATION_NOT_YET_PINNED"
    assert ledger["phase5"] == "PARTIAL_PROMOTION_MACHINERY_DIRECTION_IDENTIFIED_BUT_NOT_OBJECTIVELY_COMPLETE"

    baseline = payload["baseline_assessment"]
    assert baseline["objective_phase_complete"] == "phase1"
    assert baseline["partial_phases"] == ["phase2", "phase5"]
    assert baseline["incomplete_phases"] == ["phase0", "phase3", "phase4", "phase6", "phase7"]

    next_action = payload["next_action_contract"]
    assert next_action["next_action"] == "APPLY_ARTIFACT_CLASSIFICATION_AND_PROMOTION_PAYLOAD_REQUIREMENTS_TO_ONE_BOUNDED_PILOT_TRACK"
    assert (
        next_action["fail_closed_rule"]
        == "NO_PILOT_PROMOTION_OR_CANONICAL_MUTATION_WORK_UNTIL_PHASE0_BASELINE_IS_PINNED_AND_PHASE2_OBJECTIVE_SURFACES_EXIST"
    )


def test_phase0_mirror_tokens_present() -> None:
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    required_tokens = (
        "SANDBOX_PROMOTION_MIGRATION_PHASE0_STATUS_v0: FORMAL_TRANCHE_OPEN_AND_BASELINE_DOSSIER_PINNED",
        "SANDBOX_PROMOTION_MIGRATION_PHASE0_DECLARATION_v0: formal/docs/release/SANDBOX_PROMOTION_MIGRATION_PHASE0_DECLARATION_20260419_v0.md",
        "SANDBOX_PROMOTION_MIGRATION_PHASE0_BASELINE_DOSSIER_v0: formal/output/reports/sandbox_promotion_migration_phase0_baseline_dossier_20260419_v0.json",
        "SANDBOX_PROMOTION_MIGRATION_PHASE0_GATE_v0: formal/python/tests/test_sandbox_promotion_migration_phase0_baseline_gate.py",
        "SANDBOX_PROMOTION_MIGRATION_PHASE1_STATUS_v0: OBJECTIVELY_COMPLETE_POLICY_SPLIT_AND_MIRROR_BINDING_PINNED",
        "SANDBOX_PROMOTION_MIGRATION_PHASE2_STATUS_v0: OBJECTIVELY_COMPLETE_PROMOTION_PAYLOAD_WRAPPER_AND_CANONICAL_MUTATION_PROTOCOL_PINNED",
        "SANDBOX_PROMOTION_MIGRATION_PHASE3_STATUS_v0: OBJECTIVELY_COMPLETE_AUTHORITY_OWNER_MATRIX_AND_FAIL_CLOSED_CUTOVER_GATE_PINNED",
        "SANDBOX_PROMOTION_MIGRATION_PHASE4_STATUS_v0: OBJECTIVELY_COMPLETE_ARTIFACT_CLASSIFICATION_AND_METADATA_SCHEMA_PINNED",
        "SANDBOX_PROMOTION_MIGRATION_PHASE5_STATUS_v0: OBJECTIVELY_COMPLETE_BOUNDARY_ENFORCEMENT_FAMILY_AND_FAIL_CLOSED_CLOSEOUT_GATE_PINNED",
        "SANDBOX_PROMOTION_MIGRATION_PHASE6_STATUS_v0: OBJECTIVELY_COMPLETE_BOUNDED_PROMOTION_AUDIT_RUN_AND_GOVERNED_HOLD_OUTCOME_PINNED",
        "SANDBOX_PROMOTION_MIGRATION_PHASE7_STATUS_v0: OBJECTIVELY_COMPLETE_POST_PILOT_DECISION_PINNED_NONWIDENED_AFTER_GOVERNED_HOLD",
        "SANDBOX_PROMOTION_ARTIFACT_CLASSIFICATION_SCHEMA_v0: formal/docs/release/SANDBOX_ARTIFACT_CLASSIFICATION_METADATA_SCHEMA_20260419_v0.md",
        "SANDBOX_PROMOTION_PAYLOAD_REQUIREMENTS_v0: formal/docs/release/SANDBOX_PROMOTION_PAYLOAD_REQUIREMENTS_20260419_v0.md",
        "SANDBOX_PROMOTION_BOUNDED_PILOT_BINDING_v0: formal/docs/release/SANDBOX_PROMOTION_BOUNDED_PILOT_BINDING_COSMO_SR_CYCLE07_20260419_v0.json",
        "SANDBOX_PROMOTION_PHASE2_PHASE4_GATE_v0: formal/python/tests/test_sandbox_promotion_phase2_phase4_contract_gate.py",
        "SANDBOX_PROMOTION_PHASE2_PHASE6_DECLARATION_v0: formal/docs/release/SANDBOX_PROMOTION_MIGRATION_PHASE2_PHASE6_DECLARATION_20260419_v0.md",
        "SANDBOX_PROMOTION_CANONICAL_MUTATION_PROTOCOL_v0: formal/docs/release/SANDBOX_PROMOTION_CANONICAL_MUTATION_PROTOCOL_20260419_v0.md",
        "SANDBOX_PROMOTION_PILOT_PAYLOAD_RECORD_v0: formal/output/reports/sandbox_promotion_cosmo_sr_cycle07_payload_record_20260419_v0.json",
        "SANDBOX_PROMOTION_GOVERNED_REVIEW_WRAPPER_v0: formal/docs/release/SANDBOX_PROMOTION_GOVERNED_REVIEW_WRAPPER_COSMO_SR_CYCLE07_20260419_v0.json",
        "SANDBOX_PROMOTION_GOVERNED_REVIEW_TOOL_v0: formal/python/tools/sandbox_promotion_governed_review_wrapper_cosmo_sr_cycle07_report.py",
        "SANDBOX_PROMOTION_GOVERNED_REVIEW_REPORT_v0: formal/output/reports/sandbox_promotion_governed_review_wrapper_cosmo_sr_cycle07_20260419_v0.json",
        "SANDBOX_PROMOTION_PHASE2_PHASE6_GATE_v0: formal/python/tests/test_sandbox_promotion_governed_review_wrapper_cosmo_sr_cycle07_report.py",
        "SANDBOX_PROMOTION_POST_PILOT_DECISION_DECLARATION_v0: formal/docs/release/SANDBOX_PROMOTION_POST_PILOT_DECISION_COSMO_SR_CYCLE07_20260419_v0.json",
        "SANDBOX_PROMOTION_POST_PILOT_DECISION_TOOL_v0: formal/python/tools/sandbox_promotion_post_pilot_decision_cosmo_sr_cycle07_report.py",
        "SANDBOX_PROMOTION_POST_PILOT_DECISION_REPORT_v0: formal/output/reports/sandbox_promotion_post_pilot_decision_cosmo_sr_cycle07_20260419_v0.json",
        "SANDBOX_PROMOTION_MIGRATION_PHASE3_DECLARATION_v0: formal/docs/release/SANDBOX_PROMOTION_MIGRATION_PHASE3_AUTHORITY_OWNERSHIP_HARDENING_DECLARATION_20260419_v0.md",
        "SANDBOX_PROMOTION_PHASE3_IMPLEMENTATION_DECLARATION_v0: formal/docs/release/SANDBOX_PROMOTION_MIGRATION_PHASE3_IMPLEMENTATION_20260419_v0.md",
        "SANDBOX_PROMOTION_AUTHORITY_OWNERSHIP_MATRIX_v0: formal/docs/release/SANDBOX_PROMOTION_AUTHORITY_OWNERSHIP_MATRIX_20260419_v0.md",
        "SANDBOX_PROMOTION_AUTHORITY_CUTOVER_GATE_v0: formal/python/tests/test_sandbox_promotion_authority_ownership_cutover_gate.py",
        "SANDBOX_PROMOTION_PHASE5_IMPLEMENTATION_DECLARATION_v0: formal/docs/release/SANDBOX_PROMOTION_MIGRATION_PHASE5_IMPLEMENTATION_20260419_v0.md",
        "SANDBOX_PROMOTION_BOUNDARY_ENFORCEMENT_FAMILY_v0: formal/docs/release/SANDBOX_PROMOTION_BOUNDARY_ENFORCEMENT_FAMILY_20260419_v0.md",
        "SANDBOX_PROMOTION_BOUNDARY_ENFORCEMENT_REPORT_TOOL_v0: formal/python/tools/sandbox_promotion_boundary_enforcement_family_report.py",
        "SANDBOX_PROMOTION_BOUNDARY_ENFORCEMENT_REPORT_v0: formal/output/reports/sandbox_promotion_boundary_enforcement_family_20260419_v0.json",
        "SANDBOX_PROMOTION_PHASE5_CLOSEOUT_GATE_v0: formal/python/tests/test_sandbox_promotion_boundary_enforcement_family_gate.py",
        "SANDBOX_PROMOTION_PHASE7_PHASE3_GATE_v0: formal/python/tests/test_sandbox_promotion_post_pilot_decision_phase3_followthrough_gate.py",
        "SANDBOX_PROMOTION_ARCHITECTURE_NEXT_ACTION_v0: ROUTE_FUTURE_BOUNDED_WORK_THROUGH_COMPLETED_SANDBOX_PROMOTION_GOVERNANCE_STACK",
    )
    for token in required_tokens:
        assert token in state_text
        assert token in roadmap_text