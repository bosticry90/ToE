from __future__ import annotations

import json
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root

REPO_ROOT = find_repo_root(Path(__file__))
DECLARATION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "SANDBOX_PROMOTION_MIGRATION_PHASE2_PHASE4_DECLARATION_20260419_v0.md"
CLASSIFICATION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "SANDBOX_ARTIFACT_CLASSIFICATION_METADATA_SCHEMA_20260419_v0.md"
PAYLOAD_PATH = REPO_ROOT / "formal" / "docs" / "release" / "SANDBOX_PROMOTION_PAYLOAD_REQUIREMENTS_20260419_v0.md"
PILOT_BINDING_PATH = REPO_ROOT / "formal" / "docs" / "release" / "SANDBOX_PROMOTION_BOUNDED_PILOT_BINDING_COSMO_SR_CYCLE07_20260419_v0.json"
SANDBOX_POLICY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "SANDBOX_PHYSICS_LANE_EXECUTION_POLICY_20260418_v0.md"
PROMOTION_POLICY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PROMOTION_GOVERNANCE_LANE_POLICY_20260418_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_phase2_phase4_files_exist() -> None:
    for path in (
        DECLARATION_PATH,
        CLASSIFICATION_PATH,
        PAYLOAD_PATH,
        PILOT_BINDING_PATH,
    ):
        assert path.exists(), f"Missing required file: {path}"


def test_phase2_phase4_declaration_structure() -> None:
    text = _read(DECLARATION_PATH)
    for section in (
        "## Tranche name",
        "## Objective",
        "## Allowed files",
        "## Out of scope",
        "## Acceptance",
        "## Rollback anchor",
        "## Hard stop rule",
        "## Boundary freshness note",
    ):
        assert section in text


def test_schema_and_payload_tokens_present() -> None:
    classification_text = _read(CLASSIFICATION_PATH)
    payload_text = _read(PAYLOAD_PATH)

    for token in (
        "SANDBOX_ARTIFACT_CLASSIFICATION_SCHEMA_STATUS_v0: ACTIVE_NONLIVE_NONCLAIM",
        "SANDBOX_ARTIFACT_CLASSIFICATION_PRIMARY_CLASSES_v0: SUPPORT_ONLY_SANDBOX_ARTIFACT_PLUS_SCIENTIFIC_DELTA_SANDBOX_ARTIFACT_PLUS_PROMOTION_CANDIDATE_SANDBOX_ARTIFACT",
        "SANDBOX_ARTIFACT_CLASSIFICATION_METADATA_FIELDS_v0: ARTIFACT_ID_PLUS_ARTIFACT_CLASS_PLUS_DELTA_CLASS_PLUS_PROVENANCE_FAMILY_PLUS_DECLARED_SCOPE_PLUS_TARGET_BINDING_PLUS_CONTRADICTION_CHECK_PLUS_NONCLAIM_BOUNDARY_PLUS_PROMOTION_READINESS",
        "SANDBOX_ARTIFACT_CLASSIFICATION_PROMOTION_CANDIDATE_RULE_v0: SCIENTIFIC_DELTA_PLUS_CONTRADICTION_CHECK_PLUS_PROMOTION_READINESS_REQUIRED_FOR_PROMOTION_CANDIDATE_STATUS",
        "SANDBOX_ARTIFACT_CLASSIFICATION_GENERATION_DISCIPLINE_v0: METADATA_RECORD_MUST_BE_DECLARED_AT_ARTIFACT_CREATION_TIME",
        "SANDBOX_ARTIFACT_CLASSIFICATION_GATE_v0: formal/python/tests/test_sandbox_promotion_phase2_phase4_contract_gate.py",
    ):
        assert token in classification_text

    for token in (
        "SANDBOX_PROMOTION_PAYLOAD_REQUIREMENTS_STATUS_v0: ACTIVE_NONLIVE_NONCLAIM",
        "SANDBOX_PROMOTION_PAYLOAD_REQUIRED_FIELDS_v0: ARTIFACT_POINTER_PLUS_METADATA_RECORD_PLUS_TARGET_BINDING_PLUS_CONTRADICTION_CHECK_RESULT_PLUS_GOVERNED_TEST_SELECTION_PLUS_MUTATION_PLAN_PLUS_DECISION_BOUNDARY",
        "SANDBOX_PROMOTION_PAYLOAD_ELIGIBILITY_RULE_v0: ONLY_PROMOTION_CANDIDATE_SANDBOX_ARTIFACTS_WITH_NONNONE_DELTA_CLASS_MAY_ENTER_PROMOTION_REVIEW",
        "SANDBOX_PROMOTION_PAYLOAD_DECISION_SET_v0: PROMOTE_PLUS_HOLD_PLUS_REJECT_ONLY",
        "SANDBOX_PROMOTION_PAYLOAD_FAIL_CLOSED_RULE_v0: MISSING_METADATA_OR_TARGET_BINDING_OR_CONTRADICTION_CHECK_OR_MUTATION_PLAN_IS_HARD_FAIL",
        "SANDBOX_PROMOTION_PAYLOAD_PILOT_BINDING_v0: formal/docs/release/SANDBOX_PROMOTION_BOUNDED_PILOT_BINDING_COSMO_SR_CYCLE07_20260419_v0.json",
        "SANDBOX_PROMOTION_PAYLOAD_GATE_v0: formal/python/tests/test_sandbox_promotion_phase2_phase4_contract_gate.py",
    ):
        assert token in payload_text


def test_pilot_binding_schema() -> None:
    payload = _json(PILOT_BINDING_PATH)
    assert payload["schema_id"] == "SANDBOX_PROMOTION_BOUNDED_PILOT_BINDING_COSMO_SR_CYCLE07_20260419_v0"
    assert payload["status"] == "ACTIVE_NONLIVE_NONCLAIM"

    required_inputs = payload["required_inputs"]
    assert required_inputs["artifact_classification_schema"] == "formal/docs/release/SANDBOX_ARTIFACT_CLASSIFICATION_METADATA_SCHEMA_20260419_v0.md"
    assert required_inputs["promotion_payload_requirements"] == "formal/docs/release/SANDBOX_PROMOTION_PAYLOAD_REQUIREMENTS_20260419_v0.md"
    assert required_inputs["post_plan_cosmo_sr_tranche_declaration"] == "formal/docs/release/POST_PLAN_COSMO_SR_FIRST_LIVE_SEAM_TRANCHE_20260418_v0.json"
    assert required_inputs["post_plan_cosmo_sr_tranche_report"] == "formal/output/reports/post_plan_cosmo_sr_first_live_seam_tranche_20260418_v0.json"

    binding = payload["pilot_binding"]
    assert binding["pilot_track_id"] == "SANDBOX_PROMOTION_PILOT_COSMO_SR_CYCLE07"
    assert binding["target_row_id"] == "ROW-SEAM-COSMO-SR-001"
    assert binding["target_seam_id"] == "SEAM-COSMO-SR"
    assert binding["required_route_class"] == "EXECUTABLE_NOW"
    assert binding["required_artifact_class"] == "SCIENTIFIC_DELTA_SANDBOX_ARTIFACT"
    assert binding["required_delta_class"] == "SEAM_DELTA_CLASS"


def test_lane_policies_bind_to_phase2_phase4_contracts() -> None:
    sandbox_text = _read(SANDBOX_POLICY_PATH)
    promotion_text = _read(PROMOTION_POLICY_PATH)

    assert "SANDBOX_PHYSICS_LANE_METADATA_SCHEMA_v0: formal/docs/release/SANDBOX_ARTIFACT_CLASSIFICATION_METADATA_SCHEMA_20260419_v0.md" in sandbox_text
    assert "PROMOTION_GOVERNANCE_LANE_PAYLOAD_SCHEMA_v0: formal/docs/release/SANDBOX_PROMOTION_PAYLOAD_REQUIREMENTS_20260419_v0.md" in promotion_text
    assert "PROMOTION_GOVERNANCE_LANE_PILOT_BINDING_v0: formal/docs/release/SANDBOX_PROMOTION_BOUNDED_PILOT_BINDING_COSMO_SR_CYCLE07_20260419_v0.json" in promotion_text


def test_mirror_tokens_present() -> None:
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    for token in (
        "SANDBOX_PROMOTION_ARTIFACT_CLASSIFICATION_SCHEMA_v0: formal/docs/release/SANDBOX_ARTIFACT_CLASSIFICATION_METADATA_SCHEMA_20260419_v0.md",
        "SANDBOX_PROMOTION_PAYLOAD_REQUIREMENTS_v0: formal/docs/release/SANDBOX_PROMOTION_PAYLOAD_REQUIREMENTS_20260419_v0.md",
        "SANDBOX_PROMOTION_BOUNDED_PILOT_BINDING_v0: formal/docs/release/SANDBOX_PROMOTION_BOUNDED_PILOT_BINDING_COSMO_SR_CYCLE07_20260419_v0.json",
        "SANDBOX_PROMOTION_PHASE2_PHASE4_GATE_v0: formal/python/tests/test_sandbox_promotion_phase2_phase4_contract_gate.py",
        "SANDBOX_PROMOTION_MIGRATION_PHASE2_STATUS_v0: OBJECTIVELY_COMPLETE_PROMOTION_PAYLOAD_WRAPPER_AND_CANONICAL_MUTATION_PROTOCOL_PINNED",
        "SANDBOX_PROMOTION_MIGRATION_PHASE4_STATUS_v0: OBJECTIVELY_COMPLETE_ARTIFACT_CLASSIFICATION_AND_METADATA_SCHEMA_PINNED",
        "SANDBOX_PROMOTION_MIGRATION_PHASE5_STATUS_v0: OBJECTIVELY_COMPLETE_BOUNDARY_ENFORCEMENT_FAMILY_AND_FAIL_CLOSED_CLOSEOUT_GATE_PINNED",
        "SANDBOX_PROMOTION_ARCHITECTURE_NEXT_ACTION_v0: ROUTE_FUTURE_BOUNDED_WORK_THROUGH_COMPLETED_SANDBOX_PROMOTION_GOVERNANCE_STACK",
    ):
        assert token in state_text
        assert token in roadmap_text