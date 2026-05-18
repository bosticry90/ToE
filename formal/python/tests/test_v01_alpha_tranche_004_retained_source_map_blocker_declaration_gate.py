from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_tranche_004_retained_source_map_blocker_declaration_report import (
    BLOCKER_REASON,
    CONSTRUCTION_ATTEMPT_CLASSIFICATION,
    CURRENT_BLOCKER,
    DECLARATION_CLASSIFICATION,
    DECLARATION_ID,
    DEFAULT_CAPTURED_AT_UTC,
    LEAN_AXIOMS_USED,
    NEXT_TARGET,
    OUTCOME_ID,
    PROJECT_AXIOMS_USED,
    REQUIRED_SOURCE_MAP_SEMANTIC_CLOSURE_CONDITIONS,
    REQUIRED_WITNESS_CHAIN_COMPONENTS,
    SCHEMA_ID,
    SELECTED_DEPENDENCY,
    SELECTED_DEPENDENCY_CLASS,
    SELECTED_FINDING_ID,
    SELECTED_TRANCHE_ID,
    TRANCHE_001_STATUS,
    TRANCHE_002_STATUS,
    TRANCHE_003_STATUS,
    build_declaration,
)


REPO_ROOT = find_repo_root(Path(__file__))
RELEASE_DIR = REPO_ROOT / "formal" / "docs" / "release"
RESULT_REVIEW_PATH = (
    RELEASE_DIR
    / "V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_ATTEMPT_RESULT_REVIEW_20260515_v0.json"
)
DECLARATION_PATH = (
    RELEASE_DIR / "V01_ALPHA_TRANCHE_004_RETAINED_SOURCE_MAP_BLOCKER_DECLARATION_20260515_v0.json"
)
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "v01_alpha_tranche_004_retained_source_map_blocker_declaration_report.py"
)
PHYSICS_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
LEAN_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01Tranche004RetainedSourceMapBlockerDeclaration.lean"
)
LEAN_INDEX_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Release" / "V01Index.lean"

FORBIDDEN_TRUE_KEYS = [
    "additional_construction_attempt_authorized",
    "additional_construction_attempt_executed",
    "source_map_authorization_status_adjudication_packet_preparation_authorized",
    "documented_nonblocking_status_authorized",
    "tranche_004_moved_to_documented_dependency_nonblocking",
    "source_map_closure_claimed",
    "source_map_semantic_closure_authorized",
    "qft_gr_seam_closed",
    "witness_chain_constructed",
    "partial_witness_chain_constructed",
    "source_map_witness_chain_evidence_constructed",
    "source_map_witness_chain_construction_successful",
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


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_v01_alpha_tranche_004_retained_source_map_blocker_declaration_files_exist() -> None:
    assert RESULT_REVIEW_PATH.exists()
    assert DECLARATION_PATH.exists()
    assert TOOL_PATH.exists()
    assert LEAN_DECLARATION_PATH.exists()
    assert LEAN_INDEX_PATH.exists()


def test_v01_alpha_tranche_004_retained_source_map_blocker_declaration_consumes_result_review() -> None:
    declaration = _json(DECLARATION_PATH)
    assert declaration["schema_id"] == SCHEMA_ID
    assert declaration["declaration_id"] == DECLARATION_ID
    assert declaration["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert declaration["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert declaration["accepted"] is True
    assert declaration["outcome_id"] == OUTCOME_ID
    assert declaration["consumes_construction_attempt_result_review"] == (
        "V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_ATTEMPT_RESULT_REVIEW_v0"
    )
    assert declaration["consumes_construction_attempt_result_review_pointer"] == (
        "formal/docs/release/"
        "V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_ATTEMPT_RESULT_REVIEW_20260515_v0.json"
    )


def test_v01_alpha_tranche_004_retained_source_map_blocker_declaration_scope() -> None:
    declaration = _json(DECLARATION_PATH)
    assert declaration["declaration_scope"] == (
        "PREPARE_TRANCHE_004_RETAINED_SOURCE_MAP_BLOCKER_DECLARATION_ONLY_NO_"
        "ADDITIONAL_CONSTRUCTION_SOURCE_MAP_CLOSURE_BLOCKER_MOVEMENT_OR_RELEASE_PROMOTION"
    )
    assert declaration["tranche_001_status"] == TRANCHE_001_STATUS
    assert declaration["tranche_002_status"] == TRANCHE_002_STATUS
    assert declaration["tranche_003_status"] == TRANCHE_003_STATUS
    assert declaration["tranche_004_status"] == (
        "retained_source_map_authorization_release_blocker_declared_pending_result_review"
    )
    assert declaration["selected_tranche_id"] == SELECTED_TRANCHE_ID
    assert declaration["selected_remediation_finding_id"] == SELECTED_FINDING_ID
    assert declaration["selected_dependency"] == SELECTED_DEPENDENCY
    assert declaration["selected_dependency_class"] == SELECTED_DEPENDENCY_CLASS


def test_v01_alpha_tranche_004_retained_source_map_blocker_declaration_preserves_fail_closed_attempt_result() -> None:
    declaration = _json(DECLARATION_PATH)
    assert declaration["construction_attempt_classification"] == CONSTRUCTION_ATTEMPT_CLASSIFICATION
    assert declaration["declaration_classification"] == DECLARATION_CLASSIFICATION
    assert declaration["retained_source_map_blocker_declaration_prepared"] is True
    retained = declaration["retained_blocker_declaration"]
    assert retained["declaration_kind"] == "retained_source_map_authorization_release_blocker"
    assert retained["selected_tranche_id"] == SELECTED_TRANCHE_ID
    assert retained["selected_dependency_finding_id"] == SELECTED_FINDING_ID
    assert retained["selected_dependency"] == SELECTED_DEPENDENCY
    assert retained["attempt_result"] == CONSTRUCTION_ATTEMPT_CLASSIFICATION
    assert retained["source_map_posture"] == CURRENT_BLOCKER
    assert retained["retained_reason"] == BLOCKER_REASON
    assert retained["declaration_review_required_before_next_lane_routing"] is True


def test_v01_alpha_tranche_004_retained_source_map_blocker_declaration_preserves_blocker_and_lean_posture() -> None:
    declaration = _json(DECLARATION_PATH)
    assert declaration["current_blocker"] == CURRENT_BLOCKER
    assert declaration["blocker_reason"] == BLOCKER_REASON
    assert declaration["source_map_authorization_status"]["authorization_status"] == CURRENT_BLOCKER
    assert declaration["source_map_authorization_status"]["full_source_map_semantic_closure_authorized"] is False
    assert declaration["source_map_authorization_status"]["not_authorized_reason"] == BLOCKER_REASON
    assert declaration["lean_audit_result"]["parsed_axioms"] == LEAN_AXIOMS_USED
    assert declaration["lean_audit_result"]["project_axioms_used"] == PROJECT_AXIOMS_USED
    assert declaration["lean_audit_result"]["project_axiom_count"] == 0
    assert declaration["lean_audit_result"]["depends_on_no_axioms"] is True
    assert declaration["project_axioms_used"] == PROJECT_AXIOMS_USED


def test_v01_alpha_tranche_004_retained_source_map_blocker_declaration_declares_release_blocking_retained_status() -> None:
    declaration = _json(DECLARATION_PATH)
    impact = declaration["release_impact"]
    assert declaration["retained_blocker"] is True
    assert declaration["retained_blocker_reason"] == BLOCKER_REASON
    assert declaration["remains_release_blocking"] is True
    assert declaration["release_readiness_blocked_by_tranche_004"] is True
    assert impact["tranche_004_remains_release_blocking"] is True
    assert impact["release_readiness_blocked_by_tranche_004"] is True
    assert impact["release_assembly_allowed"] is False
    assert impact["readiness_marking_allowed"] is False
    assert impact["continue_to_tranches_005_006_before_declaration_review"] is False
    assert impact["pause_release_readiness_decision_deferred_to_declaration_result_review"] is True


def test_v01_alpha_tranche_004_retained_source_map_blocker_declaration_preserves_missing_witness_and_no_closure() -> None:
    declaration = _json(DECLARATION_PATH)
    assert declaration["required_witness_chain_components"] == REQUIRED_WITNESS_CHAIN_COMPONENTS
    assert declaration["missing_witness_components"] == REQUIRED_WITNESS_CHAIN_COMPONENTS
    assert declaration["missing_witness_count"] == 10
    assert declaration["required_source_map_semantic_closure_conditions"] == (
        REQUIRED_SOURCE_MAP_SEMANTIC_CLOSURE_CONDITIONS
    )
    assert declaration["unsatisfied_source_map_semantic_closure_conditions"] == (
        REQUIRED_SOURCE_MAP_SEMANTIC_CLOSURE_CONDITIONS
    )
    assert declaration["unsatisfied_source_map_semantic_closure_condition_count"] == 5
    assert declaration["witness_chain_constructed"] is False
    assert declaration["partial_witness_chain_constructed"] is False
    assert declaration["source_map_witness_chain_evidence_constructed"] is False
    assert declaration["source_map_witness_chain_construction_successful"] is False
    assert declaration["source_map_closure_claimed"] is False
    assert declaration["source_map_semantic_closure_authorized"] is False
    assert declaration["qft_gr_seam_closed"] is False


def test_v01_alpha_tranche_004_retained_source_map_blocker_declaration_does_not_retry_or_move_tranche() -> None:
    declaration = _json(DECLARATION_PATH)
    assert declaration["additional_construction_attempt_authorized"] is False
    assert declaration["additional_construction_attempt_executed"] is False
    assert declaration["source_map_authorization_status_adjudication_packet_preparation_authorized"] is False
    assert declaration["tranche_004_moved_to_documented_dependency_nonblocking"] is False
    assert declaration["documented_nonblocking_status_authorized"] is False
    assert declaration["blocker_movement_authorized"] is False
    assert declaration["blocker_movement_registered"] is False
    assert declaration["blocker_fully_remediated"] is False


def test_v01_alpha_tranche_004_retained_source_map_blocker_declaration_keeps_remaining_blockers_tracked() -> None:
    declaration = _json(DECLARATION_PATH)
    rows = declaration["release_blocking_obligations_carry_forward"]
    assert declaration["release_blocking_obligation_count"] == 3
    assert [row["dependency_finding_id"] for row in rows] == RELEASE_BLOCKER_IDS
    selected = declaration["selected_release_blocking_obligation"]
    assert selected["dependency_finding_id"] == SELECTED_FINDING_ID
    assert selected["dependency"] == SELECTED_DEPENDENCY
    assert selected["dependency_class"] == SELECTED_DEPENDENCY_CLASS
    for row in rows:
        assert row["modified_by_tranche_003"] is False
        assert row["status_carry_forward"] == "tracked_unmodified_not_audited_in_tranche_003"

    other = declaration["other_release_blocking_obligations"]
    assert declaration["other_release_blocking_obligation_count"] == 2
    assert [row["dependency_finding_id"] for row in other] == [
        "V01-ALPHA-DEP-REM-005",
        "V01-ALPHA-DEP-REM-006",
    ]
    for row in other:
        assert row["modified_by_tranche_004"] is False
        assert row["status_carry_forward"] == "tracked_unmodified_not_audited_in_tranche_004"


def test_v01_alpha_tranche_004_retained_source_map_blocker_declaration_forbidden_effects_false() -> None:
    declaration = _json(DECLARATION_PATH)
    forbidden = declaration["forbidden_effect_status"]
    assert sorted(forbidden) == sorted(FORBIDDEN_TRUE_KEYS)
    for key in FORBIDDEN_TRUE_KEYS:
        assert forbidden[key] is False

    assert declaration["release_packet_assembled"] is False
    assert declaration["v01_alpha_marked_ready"] is False
    assert declaration["lean_theorem_debt_discharged"] is False
    assert declaration["axiom_spec_backed_debt_reduced"] is False
    assert declaration["axiom_spec_backed_debt_reduced_by_documentation"] is False
    assert declaration["proof_debt_reduced"] is False
    assert declaration["retained_assumptions_discharged"] is False
    assert declaration["validation_claim_authorized"] is False


def test_v01_alpha_tranche_004_retained_source_map_blocker_declaration_next_target() -> None:
    declaration = _json(DECLARATION_PATH)
    assert declaration["selected_next_target"] == NEXT_TARGET
    assert declaration["selected_next_target_kind"] == (
        "retained_source_map_blocker_declaration_result_review_only"
    )
    assert declaration["selection_count"] == 1
    assert declaration["next_action_scope"] == (
        "REVIEW_TRANCHE_004_RETAINED_SOURCE_MAP_BLOCKER_DECLARATION_ONLY_NO_SOURCE_"
        "MAP_CLOSURE_BLOCKER_MOVEMENT_RELEASE_PROMOTION_OR_READINESS_MARKING"
    )
    assert {row["target"]: row["decision"] for row in declaration["candidate_next_targets"]} == {
        "review_v01_alpha_tranche_004_retained_source_map_blocker_declaration_result": "selected",
        "pause_v01_alpha_release_readiness_due_to_retained_tranche_004_blocker": "deferred_until_declaration_result_review",
        "prepare_v01_alpha_dependency_remediation_next_tranche_selection_packet": "deferred_until_declaration_result_review",
    }


def test_v01_alpha_tranche_004_retained_source_map_blocker_declaration_acceptance_and_determinism() -> None:
    declaration = _json(DECLARATION_PATH)
    for key, value in declaration["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    generated_1 = build_declaration(
        result_review_path=RESULT_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    generated_2 = build_declaration(
        result_review_path=RESULT_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated_1 == generated_2
    assert declaration == generated_1


def test_v01_alpha_tranche_004_retained_source_map_blocker_declaration_is_pinned() -> None:
    roadmap_text = _read(PHYSICS_ROADMAP_PATH)
    refs = [
        DECLARATION_ID,
        "formal/docs/release/V01_ALPHA_TRANCHE_004_RETAINED_SOURCE_MAP_BLOCKER_DECLARATION_20260515_v0.json",
        "formal/python/tools/v01_alpha_tranche_004_retained_source_map_blocker_declaration_report.py",
        "formal/python/tests/test_v01_alpha_tranche_004_retained_source_map_blocker_declaration_gate.py",
        OUTCOME_ID,
        DECLARATION_CLASSIFICATION,
        NEXT_TARGET,
    ]
    for ref in refs:
        assert ref in roadmap_text

    lean_text = _read(LEAN_DECLARATION_PATH)
    index_text = _read(LEAN_INDEX_PATH)
    assert OUTCOME_ID in lean_text
    assert "V01Tranche004RetainedSourceMapBlockerDeclaration" in index_text
    assert (
        "v01_tranche_004_retained_source_map_blocker_declaration_declares_release_blocking"
        in index_text
    )
