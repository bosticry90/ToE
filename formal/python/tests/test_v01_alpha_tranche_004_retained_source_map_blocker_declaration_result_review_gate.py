from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_tranche_004_retained_source_map_blocker_declaration_result_review_report import (
    BLOCKER_REASON,
    CONSTRUCTION_ATTEMPT_CLASSIFICATION,
    CURRENT_BLOCKER,
    DECLARATION_CLASSIFICATION,
    DEFAULT_CAPTURED_AT_UTC,
    LEAN_AXIOMS_USED,
    NEXT_TARGET,
    OUTCOME_ID,
    PROJECT_AXIOMS_USED,
    REQUIRED_SOURCE_MAP_SEMANTIC_CLOSURE_CONDITIONS,
    REQUIRED_WITNESS_CHAIN_COMPONENTS,
    REVIEW_CLASSIFICATION,
    REVIEW_ID,
    ROUTING_DECISION,
    SCHEMA_ID,
    SELECTED_DEPENDENCY,
    SELECTED_DEPENDENCY_CLASS,
    SELECTED_FINDING_ID,
    SELECTED_TRANCHE_ID,
    TRANCHE_001_STATUS,
    TRANCHE_002_STATUS,
    TRANCHE_003_STATUS,
    build_result_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
RELEASE_DIR = REPO_ROOT / "formal" / "docs" / "release"
DECLARATION_PATH = (
    RELEASE_DIR / "V01_ALPHA_TRANCHE_004_RETAINED_SOURCE_MAP_BLOCKER_DECLARATION_20260515_v0.json"
)
RESULT_REVIEW_PATH = (
    RELEASE_DIR
    / "V01_ALPHA_TRANCHE_004_RETAINED_SOURCE_MAP_BLOCKER_DECLARATION_RESULT_REVIEW_20260515_v0.json"
)
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "v01_alpha_tranche_004_retained_source_map_blocker_declaration_result_review_report.py"
)
PHYSICS_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
LEAN_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01Tranche004RetainedSourceMapBlockerDeclarationResultReview.lean"
)
LEAN_INDEX_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Release" / "V01Index.lean"

FORBIDDEN_TRUE_KEYS = [
    "next_tranche_selection_packet_prepared_by_review",
    "release_readiness_pause_registered_by_review",
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


def test_v01_alpha_tranche_004_retained_source_map_blocker_declaration_result_review_files_exist() -> None:
    assert DECLARATION_PATH.exists()
    assert RESULT_REVIEW_PATH.exists()
    assert TOOL_PATH.exists()
    assert LEAN_RESULT_REVIEW_PATH.exists()
    assert LEAN_INDEX_PATH.exists()


def test_v01_alpha_tranche_004_retained_source_map_blocker_declaration_result_review_consumes_declaration() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["schema_id"] == SCHEMA_ID
    assert review["review_id"] == REVIEW_ID
    assert review["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert review["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert review["accepted"] is True
    assert review["outcome_id"] == OUTCOME_ID
    assert review["consumes_retained_blocker_declaration"] == (
        "V01_ALPHA_TRANCHE_004_RETAINED_SOURCE_MAP_BLOCKER_DECLARATION_v0"
    )
    assert review["consumes_retained_blocker_declaration_pointer"] == (
        "formal/docs/release/"
        "V01_ALPHA_TRANCHE_004_RETAINED_SOURCE_MAP_BLOCKER_DECLARATION_20260515_v0.json"
    )


def test_v01_alpha_tranche_004_retained_source_map_blocker_declaration_result_review_scope() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["review_scope"] == (
        "REVIEW_TRANCHE_004_RETAINED_SOURCE_MAP_BLOCKER_DECLARATION_RESULT_ONLY_NO_"
        "SOURCE_MAP_CLOSURE_BLOCKER_MOVEMENT_RELEASE_PROMOTION_OR_READINESS_MARKING"
    )
    assert review["tranche_001_status"] == TRANCHE_001_STATUS
    assert review["tranche_002_status"] == TRANCHE_002_STATUS
    assert review["tranche_003_status"] == TRANCHE_003_STATUS
    assert review["tranche_004_status"] == (
        "retained_source_map_authorization_release_blocker_accepted_carry_forward_"
        "pending_tranche_005_selection"
    )
    assert review["selected_tranche_id"] == SELECTED_TRANCHE_ID
    assert review["selected_remediation_finding_id"] == SELECTED_FINDING_ID
    assert review["selected_dependency"] == SELECTED_DEPENDENCY
    assert review["selected_dependency_class"] == SELECTED_DEPENDENCY_CLASS


def test_v01_alpha_tranche_004_retained_source_map_blocker_declaration_result_review_accepts_retained_blocker() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["construction_attempt_classification"] == CONSTRUCTION_ATTEMPT_CLASSIFICATION
    assert review["declaration_classification"] == DECLARATION_CLASSIFICATION
    assert review["review_classification"] == REVIEW_CLASSIFICATION
    assert review["retained_blocker_declaration_result_accepted"] is True
    assert review["retained_blocker"] is True
    assert review["retained_blocker_reason"] == BLOCKER_REASON
    assert review["remains_release_blocking"] is True
    assert review["release_readiness_blocked_by_tranche_004"] is True


def test_v01_alpha_tranche_004_retained_source_map_blocker_declaration_result_review_preserves_blocker_and_lean_posture() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["current_blocker"] == CURRENT_BLOCKER
    assert review["blocker_reason"] == BLOCKER_REASON
    assert review["source_map_authorization_status"]["authorization_status"] == CURRENT_BLOCKER
    assert review["source_map_authorization_status"]["full_source_map_semantic_closure_authorized"] is False
    assert review["source_map_authorization_status"]["not_authorized_reason"] == BLOCKER_REASON
    assert review["lean_audit_result"]["parsed_axioms"] == LEAN_AXIOMS_USED
    assert review["lean_audit_result"]["project_axioms_used"] == PROJECT_AXIOMS_USED
    assert review["lean_audit_result"]["project_axiom_count"] == 0
    assert review["lean_audit_result"]["depends_on_no_axioms"] is True
    assert review["project_axioms_used"] == PROJECT_AXIOMS_USED


def test_v01_alpha_tranche_004_retained_source_map_blocker_declaration_result_review_preserves_no_closure_or_witness_chain() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["required_witness_chain_components"] == REQUIRED_WITNESS_CHAIN_COMPONENTS
    assert review["missing_witness_components"] == REQUIRED_WITNESS_CHAIN_COMPONENTS
    assert review["missing_witness_count"] == 10
    assert review["required_source_map_semantic_closure_conditions"] == (
        REQUIRED_SOURCE_MAP_SEMANTIC_CLOSURE_CONDITIONS
    )
    assert review["unsatisfied_source_map_semantic_closure_conditions"] == (
        REQUIRED_SOURCE_MAP_SEMANTIC_CLOSURE_CONDITIONS
    )
    assert review["unsatisfied_source_map_semantic_closure_condition_count"] == 5
    assert review["witness_chain_constructed"] is False
    assert review["partial_witness_chain_constructed"] is False
    assert review["source_map_witness_chain_evidence_constructed"] is False
    assert review["source_map_witness_chain_construction_successful"] is False
    assert review["source_map_closure_claimed"] is False
    assert review["source_map_semantic_closure_authorized"] is False
    assert review["qft_gr_seam_closed"] is False


def test_v01_alpha_tranche_004_retained_source_map_blocker_declaration_result_review_does_not_move_tranche_004() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["tranche_004_moved_to_documented_dependency_nonblocking"] is False
    assert review["documented_nonblocking_status_authorized"] is False
    assert review["blocker_movement_authorized"] is False
    assert review["blocker_movement_registered"] is False
    assert review["blocker_fully_remediated"] is False
    assert review["additional_construction_attempt_authorized"] is False
    assert review["additional_construction_attempt_executed"] is False
    assert review["source_map_authorization_status_adjudication_packet_preparation_authorized"] is False
    assert review["documentation_alone_can_clear_blocker"] is False


def test_v01_alpha_tranche_004_retained_source_map_blocker_declaration_result_review_keeps_remaining_blockers_tracked() -> None:
    review = _json(RESULT_REVIEW_PATH)
    rows = review["release_blocking_obligations_carry_forward"]
    assert review["release_blocking_obligation_count"] == 3
    assert [row["dependency_finding_id"] for row in rows] == RELEASE_BLOCKER_IDS
    selected = review["selected_release_blocking_obligation"]
    assert selected["dependency_finding_id"] == SELECTED_FINDING_ID
    assert selected["dependency"] == SELECTED_DEPENDENCY
    assert selected["dependency_class"] == SELECTED_DEPENDENCY_CLASS
    for row in rows:
        assert row["modified_by_tranche_003"] is False
        assert row["status_carry_forward"] == "tracked_unmodified_not_audited_in_tranche_003"

    other = review["other_release_blocking_obligations"]
    assert review["other_release_blocking_obligation_count"] == 2
    assert [row["dependency_finding_id"] for row in other] == [
        "V01-ALPHA-DEP-REM-005",
        "V01-ALPHA-DEP-REM-006",
    ]
    for row in other:
        assert row["modified_by_tranche_004"] is False
        assert row["status_carry_forward"] == "tracked_unmodified_not_audited_in_tranche_004"


def test_v01_alpha_tranche_004_retained_source_map_blocker_declaration_result_review_selects_continuation_branch() -> None:
    review = _json(RESULT_REVIEW_PATH)
    decision = review["routing_decision"]
    assert review["routing_decision_token"] == ROUTING_DECISION
    assert decision["selected_branch"] == ROUTING_DECISION
    assert decision["retained_tranche_004_release_blocker_carry_forward_required"] is True
    assert decision["continue_to_tranche_005_006_queue"] is True
    assert decision["pause_release_readiness_due_to_retained_tranche_004_blocker"] is False
    assert decision["release_readiness_remains_blocked_by_tranche_004"] is True
    assert decision["release_hold_branch"] == "deferred_not_selected"
    assert review["continued_remediation_queue_selected"] is True
    assert review["release_readiness_pause_selected"] is False
    assert review["next_tranche_selection_packet_prepared_by_review"] is False


def test_v01_alpha_tranche_004_retained_source_map_blocker_declaration_result_review_forbidden_effects_false() -> None:
    review = _json(RESULT_REVIEW_PATH)
    forbidden = review["forbidden_effect_status"]
    assert sorted(forbidden) == sorted(FORBIDDEN_TRUE_KEYS)
    for key in FORBIDDEN_TRUE_KEYS:
        assert forbidden[key] is False

    assert review["release_packet_assembled"] is False
    assert review["v01_alpha_marked_ready"] is False
    assert review["lean_theorem_debt_discharged"] is False
    assert review["axiom_spec_backed_debt_reduced"] is False
    assert review["axiom_spec_backed_debt_reduced_by_documentation"] is False
    assert review["proof_debt_reduced"] is False
    assert review["retained_assumptions_discharged"] is False
    assert review["validation_claim_authorized"] is False


def test_v01_alpha_tranche_004_retained_source_map_blocker_declaration_result_review_next_target() -> None:
    review = _json(RESULT_REVIEW_PATH)
    assert review["selected_next_target"] == NEXT_TARGET
    assert review["selected_next_target_kind"] == (
        "next_tranche_selection_packet_preparation_after_tranche_004_retained_blocker"
    )
    assert review["selection_count"] == 1
    assert review["next_action_scope"] == (
        "PREPARE_NEXT_TRANCHE_SELECTION_PACKET_AFTER_TRANCHE_004_RETAINED_BLOCKER_"
        "DECLARATION_ONLY_NO_REMEDIATION_EXECUTION_RELEASE_PROMOTION_OR_READINESS_MARKING"
    )
    assert {row["target"]: row["decision"] for row in review["candidate_next_targets"]} == {
        "prepare_v01_alpha_dependency_remediation_next_tranche_selection_packet_after_tranche_004_retained_blocker_declaration": "selected",
        "pause_v01_alpha_release_readiness_due_to_retained_tranche_004_blocker": "deferred_not_selected",
    }


def test_v01_alpha_tranche_004_retained_source_map_blocker_declaration_result_review_acceptance_and_determinism() -> None:
    review = _json(RESULT_REVIEW_PATH)
    for key, value in review["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    generated_1 = build_result_review(
        declaration_path=DECLARATION_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    generated_2 = build_result_review(
        declaration_path=DECLARATION_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated_1 == generated_2
    assert review == generated_1


def test_v01_alpha_tranche_004_retained_source_map_blocker_declaration_result_review_is_pinned() -> None:
    roadmap_text = _read(PHYSICS_ROADMAP_PATH)
    refs = [
        REVIEW_ID,
        "formal/docs/release/V01_ALPHA_TRANCHE_004_RETAINED_SOURCE_MAP_BLOCKER_DECLARATION_RESULT_REVIEW_20260515_v0.json",
        "formal/python/tools/v01_alpha_tranche_004_retained_source_map_blocker_declaration_result_review_report.py",
        "formal/python/tests/test_v01_alpha_tranche_004_retained_source_map_blocker_declaration_result_review_gate.py",
        OUTCOME_ID,
        ROUTING_DECISION,
        NEXT_TARGET,
    ]
    for ref in refs:
        assert ref in roadmap_text

    lean_text = _read(LEAN_RESULT_REVIEW_PATH)
    index_text = _read(LEAN_INDEX_PATH)
    assert OUTCOME_ID in lean_text
    assert "V01Tranche004RetainedSourceMapBlockerDeclarationResultReview" in index_text
    assert (
        "v01_tranche_004_retained_source_map_blocker_declaration_result_review_selects_continuation"
        in index_text
    )
