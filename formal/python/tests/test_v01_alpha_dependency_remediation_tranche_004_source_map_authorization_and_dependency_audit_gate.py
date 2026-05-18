from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_dependency_remediation_tranche_004_source_map_authorization_and_dependency_audit_report import (
    AUDIT_ID,
    DEFAULT_CAPTURED_AT_UTC,
    LEAN_AUDIT_COMMAND,
    LEAN_AXIOM_PRINT_OUTPUT,
    LEAN_AXIOMS_USED,
    LEAN_IMPORT_MODULE,
    LEAN_SOURCE,
    LEAN_TARGET,
    MISSING_WITNESSES,
    NEXT_TARGET,
    OUTCOME_ID,
    PROJECT_AXIOMS_USED,
    REQUIRED_REMEDIATION_TYPE,
    SCHEMA_ID,
    SELECTED_DEPENDENCY,
    SELECTED_DEPENDENCY_CLASS,
    SELECTED_FINDING_ID,
    SELECTED_TRANCHE_ID,
    SOURCE_MAP_AUTHORIZATION_STATUS,
    SOURCE_MAP_AUTHORIZATION_SURFACE,
    SOURCE_MAP_NOT_AUTHORIZED_REASON,
    SUPPLIED_ONLY_LAYERS,
    TRANCHE_001_STATUS,
    TRANCHE_002_STATUS,
    TRANCHE_003_STATUS,
    build_audit,
)


REPO_ROOT = find_repo_root(Path(__file__))
RELEASE_DIR = REPO_ROOT / "formal" / "docs" / "release"
RESULT_REVIEW_PATH = (
    RELEASE_DIR
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_004_EXECUTION_PACKET_RESULT_REVIEW_20260515_v0.json"
)
AUDIT_PATH = (
    RELEASE_DIR
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_AND_DEPENDENCY_AUDIT_20260515_v0.json"
)
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "v01_alpha_dependency_remediation_tranche_004_source_map_authorization_and_dependency_audit_report.py"
)
PHYSICS_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
LEAN_AUDIT_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01DependencyRemediationTranche004SourceMapAuthorizationAndDependencyAudit.lean"
)
LEAN_INDEX_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Release" / "V01Index.lean"

FORBIDDEN_TRUE_KEYS = [
    "remediation_executed",
    "broader_remediation_executed",
    "documentation_prepared",
    "policy_adjudication_executed",
    "expert_re_review_executed",
    "blocker_movement_registered",
    "blocker_movement_authorized",
    "blocker_fully_remediated",
    "release_packet_assembled",
    "v01_alpha_marked_ready",
    "lean_theorem_debt_discharged",
    "axiom_spec_backed_debt_reduced",
    "axiom_spec_backed_debt_reduced_by_documentation",
    "proof_debt_reduced",
    "retained_assumptions_discharged",
    "theorem_discharge_authorized",
    "lane_reopen_authorized",
    "phase2_authorized",
    "seam_closure_authorized",
    "empirical_validation_authorized",
    "master_action_promotion_authorized",
    "claim_promotion_authorized",
    "computational_physics_execution_surface_opened",
]

RELEASE_BLOCKER_IDS = [
    "V01-ALPHA-DEP-REM-004",
    "V01-ALPHA-DEP-REM-005",
    "V01-ALPHA-DEP-REM-006",
]

OTHER_BLOCKER_IDS = [
    "V01-ALPHA-DEP-REM-005",
    "V01-ALPHA-DEP-REM-006",
]


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_v01_alpha_dependency_remediation_tranche_004_source_map_authorization_and_dependency_audit_files_exist() -> None:
    assert RESULT_REVIEW_PATH.exists()
    assert AUDIT_PATH.exists()
    assert TOOL_PATH.exists()
    assert LEAN_AUDIT_PATH.exists()
    assert LEAN_INDEX_PATH.exists()


def test_v01_alpha_dependency_remediation_tranche_004_source_map_authorization_and_dependency_audit_consumes_result_review() -> None:
    audit = _json(AUDIT_PATH)
    assert audit["schema_id"] == SCHEMA_ID
    assert audit["audit_id"] == AUDIT_ID
    assert audit["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert audit["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert audit["executed"] is True
    assert audit["accepted"] is True
    assert audit["outcome_id"] == OUTCOME_ID
    assert audit["consumes_tranche_004_execution_packet_result_review"] == (
        "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_004_EXECUTION_PACKET_RESULT_REVIEW_v0"
    )
    assert audit["consumes_tranche_004_execution_packet_result_review_pointer"] == (
        "formal/docs/release/"
        "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_004_EXECUTION_PACKET_RESULT_REVIEW_20260515_v0.json"
    )


def test_v01_alpha_dependency_remediation_tranche_004_source_map_authorization_and_dependency_audit_scope_is_single_dependency() -> None:
    audit = _json(AUDIT_PATH)
    assert audit["audit_scope"] == (
        "EXECUTE_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_AND_DEPENDENCY_AUDIT_ONLY_"
        "NO_REMEDIATION_OR_RELEASE_PROMOTION"
    )
    assert audit["tranche_001_status"] == TRANCHE_001_STATUS
    assert audit["tranche_002_status"] == TRANCHE_002_STATUS
    assert audit["tranche_003_status"] == TRANCHE_003_STATUS
    assert audit["selected_tranche_id"] == SELECTED_TRANCHE_ID
    assert audit["selected_remediation_finding_id"] == SELECTED_FINDING_ID
    assert audit["selected_dependency"] == SELECTED_DEPENDENCY
    assert audit["selected_dependency_class"] == SELECTED_DEPENDENCY_CLASS
    assert audit["required_remediation_type"] == REQUIRED_REMEDIATION_TYPE
    assert audit["selected_obligation_status_after_audit"] == (
        "release_blocking_pending_tranche_004_source_map_authorization_and_dependency_audit_result_review"
    )


def test_v01_alpha_dependency_remediation_tranche_004_source_map_authorization_and_dependency_audit_captures_source_map_posture() -> None:
    audit = _json(AUDIT_PATH)
    posture = audit["source_map_authorization_posture"]
    assert audit["source_map_authorization_audit_executed"] is True
    assert audit["source_map_authorization_posture_captured"] is True
    assert audit["authorization_evidence_captured"] is True
    assert posture["authorization_readout"] == SOURCE_MAP_AUTHORIZATION_SURFACE
    assert posture["authorization_status"] == SOURCE_MAP_AUTHORIZATION_STATUS
    assert posture["full_source_map_semantic_closure_authorized"] is False
    assert posture["source_map_closure_authorized"] is False
    assert posture["source_map_not_authorized"] is True
    assert posture["not_authorized_reason"] == SOURCE_MAP_NOT_AUTHORIZED_REASON
    assert posture["missing_witnesses"] == MISSING_WITNESSES
    assert posture["missing_witness_count"] == 10
    assert posture["supplied_only_layers"] == SUPPLIED_ONLY_LAYERS
    assert posture["supplied_only_layer_count"] == 9
    assert posture["qft_gr_seam_closed"] is False
    assert posture["phase2_authorized"] is False
    assert posture["master_action_promoted"] is False
    assert posture["empirical_claim"] is False


def test_v01_alpha_dependency_remediation_tranche_004_source_map_authorization_and_dependency_audit_captures_lean_posture() -> None:
    audit = _json(AUDIT_PATH)
    evidence = audit["lean_dependency_posture"]
    assert audit["lean_dependency_audit_executed"] is True
    assert audit["lean_dependency_evidence_captured"] is True
    assert evidence["lean_target"] == LEAN_TARGET
    assert evidence["lean_source"] == LEAN_SOURCE
    assert evidence["lean_import_module"] == LEAN_IMPORT_MODULE
    assert evidence["command"] == LEAN_AUDIT_COMMAND
    assert evidence["command_context"] == "lake env lean --stdin"
    assert evidence["raw_output"] == LEAN_AXIOM_PRINT_OUTPUT
    assert evidence["parsed_axioms"] == LEAN_AXIOMS_USED
    assert evidence["exact_axioms_or_dependencies_used"] == LEAN_AXIOMS_USED
    assert evidence["standard_lean_axioms_used"] == LEAN_AXIOMS_USED
    assert evidence["standard_lean_axiom_count"] == 0
    assert evidence["project_axioms_used"] == PROJECT_AXIOMS_USED
    assert evidence["project_axiom_count"] == 0
    assert evidence["project_local_axioms_present"] is False
    assert evidence["depends_on_no_axioms"] is True
    assert evidence["classification"] == "no_lean_axiom_dependency_detected"


def test_v01_alpha_dependency_remediation_tranche_004_source_map_authorization_and_dependency_audit_classifies_blocker_as_source_map_authorization_issue() -> None:
    audit = _json(AUDIT_PATH)
    assessment = audit["policy_or_documentation_issue_assessment"]
    assert assessment["classification"] == (
        "real_blocking_source_map_authorization_dependency_pending_result_review"
    )
    assert assessment["documentation_only_resolution_supported_by_audit"] is False
    assert assessment["standard_lean_dependency_policy_issue"] is False
    assert assessment["source_map_authorization_blocker_retained"] is True
    assert assessment["policy_adjudication_required_after_result_review"] is True
    assert assessment["expert_re_review_required_before_blocker_downgrade"] is True
    assert audit["expert_re_review_required"] is True
    assert audit["expert_re_review_executed"] is False


def test_v01_alpha_dependency_remediation_tranche_004_source_map_authorization_and_dependency_audit_carries_forward_blockers() -> None:
    audit = _json(AUDIT_PATH)
    rows = audit["release_blocking_obligations_carry_forward"]
    assert audit["release_blocking_obligation_count"] == 3
    assert [row["dependency_finding_id"] for row in rows] == RELEASE_BLOCKER_IDS

    other = audit["other_release_blocking_obligations"]
    assert audit["other_release_blocking_obligation_count"] == 2
    assert [row["dependency_finding_id"] for row in other] == OTHER_BLOCKER_IDS
    for row in other:
        assert row["status_carry_forward"] == "tracked_unmodified_not_audited_in_tranche_004"
        assert row["remediation_execution_status"] == "not_executed_v0"
        assert row["modified_by_tranche_004"] is False


def test_v01_alpha_dependency_remediation_tranche_004_source_map_authorization_and_dependency_audit_no_broader_remediation_or_movement() -> None:
    audit = _json(AUDIT_PATH)
    assert audit["tranche_004_audit_result_classification"] == (
        "source_map_authorization_and_dependency_audit_evidence_captured_pending_result_review"
    )
    assert audit["remediation_executed"] is False
    assert audit["broader_remediation_executed"] is False
    assert audit["blocker_movement_registered"] is False
    assert audit["blocker_movement_authorized"] is False
    assert audit["blocker_fully_remediated"] is False


def test_v01_alpha_dependency_remediation_tranche_004_source_map_authorization_and_dependency_audit_forbidden_effects_false() -> None:
    audit = _json(AUDIT_PATH)
    forbidden = audit["forbidden_effect_status"]
    assert sorted(forbidden) == sorted(FORBIDDEN_TRUE_KEYS)
    for key in FORBIDDEN_TRUE_KEYS:
        assert forbidden[key] is False

    assert audit["release_packet_assembled"] is False
    assert audit["v01_alpha_marked_ready"] is False
    assert audit["lean_theorem_debt_discharged"] is False
    assert audit["axiom_spec_backed_debt_reduced"] is False
    assert audit["axiom_spec_backed_debt_reduced_by_documentation"] is False
    assert audit["proof_debt_reduced"] is False
    assert audit["retained_assumptions_discharged"] is False
    assert audit["validation_claim_authorized"] is False


def test_v01_alpha_dependency_remediation_tranche_004_source_map_authorization_and_dependency_audit_next_target() -> None:
    audit = _json(AUDIT_PATH)
    assert audit["post_audit_adjudication_target"] == NEXT_TARGET
    assert audit["selected_next_target"] == NEXT_TARGET
    assert audit["selected_next_target_kind"] == (
        "tranche_004_source_map_authorization_and_dependency_audit_result_review_only"
    )
    assert audit["selection_count"] == 1
    assert audit["next_action_scope"] == (
        "REVIEW_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_AND_DEPENDENCY_AUDIT_EVIDENCE_"
        "ONLY_NO_BLOCKER_MOVEMENT_OR_RELEASE_PROMOTION"
    )
    assert {row["target"]: row["decision"] for row in audit["candidate_next_targets"]} == {
        "review_v01_alpha_dependency_remediation_tranche_004_source_map_authorization_and_dependency_audit_result": "selected",
        "prepare_v01_alpha_dependency_remediation_tranche_004_release_policy_adjudication_packet": "deferred",
        "prepare_v01_alpha_release_readiness_adjudication_packet": "deferred",
    }


def test_v01_alpha_dependency_remediation_tranche_004_source_map_authorization_and_dependency_audit_acceptance_and_determinism() -> None:
    audit = _json(AUDIT_PATH)
    for key, value in audit["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    generated_1 = build_audit(
        result_review_path=RESULT_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    generated_2 = build_audit(
        result_review_path=RESULT_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated_1 == generated_2
    assert audit == generated_1


def test_v01_alpha_dependency_remediation_tranche_004_source_map_authorization_and_dependency_audit_is_pinned() -> None:
    roadmap_text = _read(PHYSICS_ROADMAP_PATH)
    refs = [
        AUDIT_ID,
        "formal/docs/release/V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_AND_DEPENDENCY_AUDIT_20260515_v0.json",
        "formal/python/tools/v01_alpha_dependency_remediation_tranche_004_source_map_authorization_and_dependency_audit_report.py",
        "formal/python/tests/test_v01_alpha_dependency_remediation_tranche_004_source_map_authorization_and_dependency_audit_gate.py",
        OUTCOME_ID,
        NEXT_TARGET,
    ]
    for ref in refs:
        assert ref in roadmap_text

    lean_text = _read(LEAN_AUDIT_PATH)
    index_text = _read(LEAN_INDEX_PATH)
    assert OUTCOME_ID in lean_text
    assert "V01DependencyRemediationTranche004SourceMapAuthorizationAndDependencyAudit" in index_text
    assert (
        "v01_dependency_remediation_tranche_004_source_map_authorization_and_dependency_audit_does_not_move_blocker"
        in index_text
    )
