from __future__ import annotations

from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root

REPO_ROOT = find_repo_root(Path(__file__))
PHYSICS_FIRST_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PHYSICS_FIRST_EXECUTION_RULE_v0.md"
SANDBOX_POLICY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "SANDBOX_PHYSICS_LANE_EXECUTION_POLICY_20260418_v0.md"
PROMOTION_POLICY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PROMOTION_GOVERNANCE_LANE_POLICY_20260418_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"


SANDBOX_POLICY_TOKENS = (
    "SANDBOX_PHYSICS_LANE_STATUS_v0: ACTIVE_NONLIVE_NONCLAIM",
    "SANDBOX_PHYSICS_LANE_MODE_v0: EXPLORATION_ONLY_WITH_MINIMAL_LIVE_GUARDRAILS",
    "SANDBOX_PHYSICS_LANE_ALLOWED_OUTPUTS_v0: HYPOTHESIS_LOCAL_DERIVATION_RETAIN_PRUNE_INCONCLUSIVE_AND_DESIGN_ONLY",
    "SANDBOX_PHYSICS_LANE_FORBIDDEN_OUTPUTS_v0: NO_CANONICAL_ROW_MUTATION_NO_RELEASE_GATE_TRUTH_CHANGE_NO_SEAM_CLASS_FLIP_NO_EXTERNAL_TRUTH_CLAIM",
    "SANDBOX_PHYSICS_LANE_LIVE_GUARDRAILS_v0: NONCLAIM_PLUS_PROVENANCE_PLUS_FAIL_CLOSED_CONTRADICTION_PLUS_DECLARED_SCOPE",
    "SANDBOX_PHYSICS_LANE_PHYSICS_FIRST_RULE_v0: DECLARE_SCIENTIFIC_DELTA_CLASS_OR_REMAIN_SUPPORT_ONLY_NONPROMOTABLE",
    "SANDBOX_PHYSICS_LANE_METADATA_SCHEMA_v0: formal/docs/release/SANDBOX_ARTIFACT_CLASSIFICATION_METADATA_SCHEMA_20260419_v0.md",
    "SANDBOX_PHYSICS_LANE_AUTHORITY_OWNER_v0: formal/docs/release/SANDBOX_PHYSICS_LANE_EXECUTION_POLICY_20260418_v0.md",
    "SANDBOX_PHYSICS_LANE_AUTHORITY_MATRIX_v0: formal/docs/release/SANDBOX_PROMOTION_AUTHORITY_OWNERSHIP_MATRIX_20260419_v0.md",
    "SANDBOX_PHYSICS_LANE_BOUNDARY_ENFORCEMENT_FAMILY_v0: formal/docs/release/SANDBOX_PROMOTION_BOUNDARY_ENFORCEMENT_FAMILY_20260419_v0.md",
    "SANDBOX_PHYSICS_LANE_BOUNDARY_v0: RESULTS_STAY_SANDBOX_ONLY_UNTIL_PROMOTION_GATE_SATISFIED",
    "SANDBOX_PHYSICS_LANE_GATE_v0: formal/python/tests/test_sandbox_promotion_lane_policy_gate.py",
)

PROMOTION_POLICY_TOKENS = (
    "PROMOTION_GOVERNANCE_LANE_STATUS_v0: ACTIVE_NONLIVE_NONCLAIM",
    "PROMOTION_GOVERNANCE_LANE_TRIGGER_v0: PROMOTABLE_SANDBOX_ARTIFACT_ONLY",
    "PROMOTION_GOVERNANCE_LANE_REQUIRED_INPUTS_v0: PROVENANCE_PLUS_SCOPE_PLUS_CONTRADICTION_CHECK_PLUS_TARGET_ROW_BINDING_PLUS_GOVERNED_TEST_SELECTION",
    "PROMOTION_GOVERNANCE_LANE_PAYLOAD_SCHEMA_v0: formal/docs/release/SANDBOX_PROMOTION_PAYLOAD_REQUIREMENTS_20260419_v0.md",
    "PROMOTION_GOVERNANCE_LANE_PILOT_BINDING_v0: formal/docs/release/SANDBOX_PROMOTION_BOUNDED_PILOT_BINDING_COSMO_SR_CYCLE07_20260419_v0.json",
    "PROMOTION_GOVERNANCE_LANE_REVIEW_WRAPPER_v0: formal/docs/release/SANDBOX_PROMOTION_GOVERNED_REVIEW_WRAPPER_COSMO_SR_CYCLE07_20260419_v0.json",
    "PROMOTION_GOVERNANCE_LANE_MUTATION_PROTOCOL_v0: formal/docs/release/SANDBOX_PROMOTION_CANONICAL_MUTATION_PROTOCOL_20260419_v0.md",
    "PROMOTION_GOVERNANCE_LANE_AUTHORITY_OWNER_v0: formal/docs/release/PROMOTION_GOVERNANCE_LANE_POLICY_20260418_v0.md",
    "PROMOTION_GOVERNANCE_LANE_AUTHORITY_MATRIX_v0: formal/docs/release/SANDBOX_PROMOTION_AUTHORITY_OWNERSHIP_MATRIX_20260419_v0.md",
    "PROMOTION_GOVERNANCE_LANE_CUTOVER_GATE_v0: formal/python/tests/test_sandbox_promotion_authority_ownership_cutover_gate.py",
    "PROMOTION_GOVERNANCE_LANE_BOUNDARY_ENFORCEMENT_FAMILY_v0: formal/docs/release/SANDBOX_PROMOTION_BOUNDARY_ENFORCEMENT_FAMILY_20260419_v0.md",
    "PROMOTION_GOVERNANCE_LANE_BOUNDARY_ENFORCEMENT_CLOSEOUT_GATE_v0: formal/python/tests/test_sandbox_promotion_boundary_enforcement_family_gate.py",
    "PROMOTION_GOVERNANCE_LANE_HARD_BOUNDARY_v0: NO_CANONICAL_PROMOTION_WITHOUT_PROMOTION_REVIEW",
    "PROMOTION_GOVERNANCE_LANE_PROMOTION_RULE_v0: CANONICAL_ROW_AND_SEAM_STATE_CHANGE_ONLY_AFTER_GOVERNED_PROMOTION_PASS",
    "PROMOTION_GOVERNANCE_LANE_FAILURE_RULE_v0: FAIL_CLOSED_ON_MISSING_PROVENANCE_SCOPE_OR_CONTRADICTION_EVIDENCE",
    "PROMOTION_GOVERNANCE_LANE_PHYSICS_FIRST_RULE_v0: SUPPORT_ONLY_SANDBOX_OUTPUTS_CANNOT_BECOME_ACTIVE_SCIENTIFIC_TRANCHE_WITHOUT_DELTA_CLASS",
    "PROMOTION_GOVERNANCE_LANE_GATE_v0: formal/python/tests/test_sandbox_promotion_lane_policy_gate.py",
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_lane_policy_surfaces_have_required_tokens() -> None:
    sandbox_text = _read(SANDBOX_POLICY_PATH)
    promotion_text = _read(PROMOTION_POLICY_PATH)

    for token in SANDBOX_POLICY_TOKENS:
        assert token in sandbox_text
    for token in PROMOTION_POLICY_TOKENS:
        assert token in promotion_text


def test_lane_policies_bind_to_physics_first_rule() -> None:
    physics_first_text = _read(PHYSICS_FIRST_PATH)
    sandbox_text = _read(SANDBOX_POLICY_PATH)
    promotion_text = _read(PROMOTION_POLICY_PATH)

    assert "support-only tranche is marked active" in physics_first_text
    assert "DECLARE_SCIENTIFIC_DELTA_CLASS_OR_REMAIN_SUPPORT_ONLY_NONPROMOTABLE" in sandbox_text
    assert "SUPPORT_ONLY_SANDBOX_OUTPUTS_CANNOT_BECOME_ACTIVE_SCIENTIFIC_TRANCHE_WITHOUT_DELTA_CLASS" in promotion_text


def test_canonical_surfaces_cross_pin_lane_policies() -> None:
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    for path_ref in (
        "formal/docs/release/SANDBOX_PHYSICS_LANE_EXECUTION_POLICY_20260418_v0.md",
        "formal/docs/release/PROMOTION_GOVERNANCE_LANE_POLICY_20260418_v0.md",
        "formal/docs/release/SANDBOX_ARTIFACT_CLASSIFICATION_METADATA_SCHEMA_20260419_v0.md",
        "formal/docs/release/SANDBOX_PROMOTION_PAYLOAD_REQUIREMENTS_20260419_v0.md",
        "formal/docs/release/SANDBOX_PROMOTION_BOUNDED_PILOT_BINDING_COSMO_SR_CYCLE07_20260419_v0.json",
        "formal/docs/release/SANDBOX_PROMOTION_GOVERNED_REVIEW_WRAPPER_COSMO_SR_CYCLE07_20260419_v0.json",
        "formal/docs/release/SANDBOX_PROMOTION_CANONICAL_MUTATION_PROTOCOL_20260419_v0.md",
        "formal/docs/release/SANDBOX_PROMOTION_POST_PILOT_DECISION_COSMO_SR_CYCLE07_20260419_v0.json",
        "formal/docs/release/SANDBOX_PROMOTION_MIGRATION_PHASE3_AUTHORITY_OWNERSHIP_HARDENING_DECLARATION_20260419_v0.md",
        "formal/docs/release/SANDBOX_PROMOTION_MIGRATION_PHASE3_IMPLEMENTATION_20260419_v0.md",
        "formal/docs/release/SANDBOX_PROMOTION_AUTHORITY_OWNERSHIP_MATRIX_20260419_v0.md",
        "formal/docs/release/SANDBOX_PROMOTION_MIGRATION_PHASE5_IMPLEMENTATION_20260419_v0.md",
        "formal/docs/release/SANDBOX_PROMOTION_BOUNDARY_ENFORCEMENT_FAMILY_20260419_v0.md",
        "formal/python/tests/test_sandbox_promotion_authority_ownership_cutover_gate.py",
        "formal/python/tools/sandbox_promotion_boundary_enforcement_family_report.py",
        "formal/output/reports/sandbox_promotion_boundary_enforcement_family_20260419_v0.json",
        "formal/python/tests/test_sandbox_promotion_boundary_enforcement_family_gate.py",
        "formal/python/tools/sandbox_promotion_post_pilot_decision_cosmo_sr_cycle07_report.py",
        "formal/output/reports/sandbox_promotion_post_pilot_decision_cosmo_sr_cycle07_20260419_v0.json",
        "formal/python/tests/test_sandbox_promotion_post_pilot_decision_phase3_followthrough_gate.py",
        "formal/python/tests/test_sandbox_promotion_lane_policy_gate.py",
    ):
        assert path_ref in state_text
        assert path_ref in roadmap_text

    for token in (
        "SANDBOX_PROMOTION_ARCHITECTURE_STATUS_v0: ACTIVE_NONLIVE_NONCLAIM",
        "SANDBOX_PROMOTION_ARCHITECTURE_MODEL_v0: SANDBOX_FIRST_PROMOTION_GATED_GOVERNANCE",
        "SANDBOX_PROMOTION_ARCHITECTURE_NEXT_ACTION_v0: ROUTE_FUTURE_BOUNDED_WORK_THROUGH_COMPLETED_SANDBOX_PROMOTION_GOVERNANCE_STACK",
    ):
        assert token in state_text
        assert token in roadmap_text


def test_lane_boundary_is_fail_closed() -> None:
    sandbox_text = _read(SANDBOX_POLICY_PATH)
    promotion_text = _read(PROMOTION_POLICY_PATH)

    assert "This policy does not authorize canonical promotion" in sandbox_text
    assert "Missing provenance, missing contradiction evidence, or missing target binding is a hard fail." in promotion_text
    assert "A passing sandbox result is not self-promoting." in promotion_text